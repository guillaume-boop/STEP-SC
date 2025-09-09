// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Test.sol";
import "../src/AssetToken.sol";
import "../src/ITFManager.sol";
import "../src/Treasury.sol";
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract MockERC20 is ERC20 {
    constructor() ERC20("Mock USD", "mUSD") {
        _mint(msg.sender, 1e30);
    }
    function mint(address to, uint256 amt) external {
        _mint(to, amt);
    }
}

contract BadAT is ERC20 {
    address public _manager;
    constructor(address m) ERC20("Bad","BAD") { _manager = m; }
    function getManager() external view returns(address){ return _manager; }
}

contract TooManyDecimals is ERC20 {
    constructor() ERC20("X","X") {}
    function decimals() public pure override returns(uint8){ return 19; }
}

contract MockUSDC is ERC20 {
    constructor() ERC20("Mock USDC", "mUSDC") {}
    function decimals() public pure override returns (uint8) { return 6; }
    function mint(address to, uint256 amt) external { _mint(to, amt); }
}

contract FailingERC20 is ERC20 {
    constructor() ERC20("Failing USD", "fUSD") {}
    function mint(address to, uint256 amt) external { _mint(to, amt); }
    function transferFrom(address, address, uint256) public pure override returns (bool) {
        return false;
    }
}

contract ITFManagerTest is Test {
    AssetToken assetToken;
    ITFManager manager;
    Treasury treasuryContract;
    MockERC20 base;

    string constant NAME = "STEP Paris";
    string constant SYMBOL = "ITF-PARIS";
    uint256 constant SUPPLY = 500;

    address tokenTreasury = address(0xA11CE);
    address oracle = address(0xBEEF);
    address investor = address(0xCEEF);

    uint256 initialNav = 2e18;
    uint256 initialFee = 50;

    function setUp() public {
        assetToken = new AssetToken(NAME, SYMBOL, SUPPLY, tokenTreasury);
        base = new MockERC20();
        base.mint(investor, 1_000e18);
        treasuryContract = new Treasury(address(base), address(this));
        manager = new ITFManager(address(base), address(treasuryContract), oracle, initialNav, initialFee);

        assetToken.setManager(address(manager));
        vm.prank(tokenTreasury);
        assetToken.transfer(address(manager), SUPPLY * 1e18);
        manager.setAssetToken(address(assetToken));
        treasuryContract.transferOwnership(address(manager));
    }

    function test_Constructor_SetsStateCorrectly() public {
        assertEq(address(manager.baseAsset()), address(base));
        assertEq(manager.treasury(), address(treasuryContract));
        assertEq(manager.oracle(), oracle);
        assertEq(manager.nav(), initialNav);
        assertEq(manager.feeBps(), initialFee);
        assertEq(manager.owner(), address(this));
        assertEq(address(manager.assetToken()), address(assetToken));
    }

    function test_Constructor_RevertIf_BaseAssetZero() public {
        vm.expectRevert(ITFManager.BaseAssetZero.selector);
        new ITFManager(address(0), address(treasuryContract), oracle, initialNav, initialFee);
    }

    function test_Constructor_RevertIf_TreasuryZero() public {
        vm.expectRevert(ITFManager.TreasuryZero.selector);
        new ITFManager(address(base), address(0), oracle, initialNav, initialFee);
    }

    function test_Constructor_RevertIf_OracleZero() public {
        vm.expectRevert(ITFManager.OracleZero.selector);
        new ITFManager(address(base), address(treasuryContract), address(0), initialNav, initialFee);
    }

    function test_Constructor_RevertIf_NavZero() public {
        vm.expectRevert(ITFManager.NavZero.selector);
        new ITFManager(address(base), address(treasuryContract), oracle, 0, initialFee);
    }

    function test_Constructor_RevertIf_FeeTooHigh() public {
        vm.expectRevert(ITFManager.FeeTooHigh.selector);
        new ITFManager(address(base), address(treasuryContract), oracle, initialNav, 10_001);
    }

    function test_SetOracle_OnlyOwner() public {
        vm.prank(investor);
        vm.expectRevert();
        manager.setOracle(address(0xBEEF));
    }

    function test_SetOracle_UpdatesAndEmits() public {
        address newOracle = address(0xBEEF);
        vm.expectEmit(true, true, false, true, address(manager));
        emit ITFManager.OracleChanged(oracle, newOracle);
        manager.setOracle(newOracle);
        assertEq(manager.oracle(), newOracle);
    }

    function test_SetFee_OnlyOwner() public {
        vm.prank(investor);
        vm.expectRevert();
        manager.setFee(100);
    }

    function test_SetFee_RevertIf_TooHigh() public {
        vm.expectRevert(ITFManager.FeeTooHigh.selector);
        manager.setFee(10_001);
    }

    function test_SetFee_UpdatesAndEmits() public {
        vm.expectEmit(true, true, false, true, address(manager));
        emit ITFManager.FeeChanged(initialFee, 123);
        manager.setFee(123);
        assertEq(manager.feeBps(), 123);
    }

    function test_SetTreasury_OnlyOwner() public {
        vm.prank(investor);
        vm.expectRevert();
        manager.setTreasury(address(0xD00D));
    }

    function test_SetTreasury_RevertIf_Zero() public {
        vm.expectRevert();
        manager.setTreasury(address(0));
    }

    function test_SetTreasury_UpdatesAndEmits() public {
        Treasury newTreasury = new Treasury(address(base), address(this));
        address newTreasuryAddr = address(newTreasury);
        vm.expectEmit(true, true, false, true, address(manager));
        emit ITFManager.TreasuryChanged(address(treasuryContract), newTreasuryAddr);
        manager.setTreasury(newTreasuryAddr);
        assertEq(manager.treasury(), newTreasuryAddr);
    }

    function test_UpdateNav_OnlyOracle() public {
        vm.prank(investor);
        vm.expectRevert();
        manager.updateNav(3e18);
    }

    function test_UpdateNav_RevertIf_Zero() public {
        vm.prank(oracle);
        vm.expectRevert();
        manager.updateNav(0);
    }

    function test_UpdateNav_UpdatesAndEmits() public {
        vm.prank(oracle);
        vm.expectEmit(true, true, false, true, address(manager));
        emit ITFManager.NavUpdated(initialNav, 3e18);
        manager.updateNav(3e18);
        assertEq(manager.nav(), 3e18);
    }

    function test_Invest_Works() public {
        uint256 amountIn = 20e18;
        vm.prank(investor);
        base.approve(address(manager), amountIn);
        vm.prank(investor);
        uint256 out = manager.invest(amountIn);
        assertGt(out, 0);
        assertEq(assetToken.balanceOf(investor), out);
        assertEq(base.balanceOf(address(treasuryContract)), amountIn);
    }

    function test_Redeem_Works() public {
        uint256 amountIn = 20e18;
        vm.prank(investor);
        base.approve(address(manager), amountIn);
        vm.prank(investor);
        uint256 outTokens = manager.invest(amountIn);
        vm.prank(investor);
        assetToken.approve(address(manager), outTokens);
        uint256 bal0 = base.balanceOf(investor);
        vm.prank(investor);
        manager.redeem(outTokens);
        assertEq(assetToken.balanceOf(investor), 0);
        assertGt(base.balanceOf(investor) - bal0, 0);
    }

    function test_Pause_Blocks_Invest_Redeem() public {
        manager.pause();

        vm.prank(investor);
        base.approve(address(manager), 10e18);

        vm.expectRevert();
        vm.prank(investor);
        manager.invest(10e18);

        vm.prank(address(manager));
        assetToken.transfer(investor, 1e18);
        vm.prank(investor);
        assetToken.approve(address(manager), 1e18);

        vm.expectRevert();
        vm.prank(investor);
        manager.redeem(1e18);

        manager.unpause();

        vm.prank(investor);
        base.approve(address(manager), 10e18);
        vm.prank(investor);
        uint256 out = manager.invest(10e18);
        assertGt(out, 0);
    }

    function test_SetAssetToken_RevertIf_Zero() public {
        ITFManager m = new ITFManager(address(base), address(treasuryContract), oracle, initialNav, initialFee);
        vm.expectRevert(ITFManager.AssetTokenZero.selector);
        m.setAssetToken(address(0));
    }

    function test_SetAssetToken_RevertIf_InvalidManager() public {
        ITFManager m = new ITFManager(address(base), address(treasuryContract), oracle, initialNav, initialFee);
        BadAT bad = new BadAT(address(0xDEAD));
        vm.expectRevert(ITFManager.InvalidAssetTokenManager.selector);
        m.setAssetToken(address(bad));
    }

    function test_SetAssetToken_RevertIf_AlreadySet() public {
        AssetToken at2 = new AssetToken(NAME, SYMBOL, SUPPLY, tokenTreasury);
        ITFManager m = new ITFManager(
            address(base),
            address(treasuryContract),
            oracle,
            initialNav,
            initialFee
        );

        at2.setManager(address(m));
        vm.prank(tokenTreasury);
        at2.transfer(address(m), SUPPLY * 1e18);

        m.setAssetToken(address(at2));

        vm.expectRevert(ITFManager.AssetTokenAlreadySet.selector);
        m.setAssetToken(address(at2));
    }


    function test_SetMaxNavAge_UpdatesAndEmits() public {
        uint64 newAge = 3600;
        vm.expectEmit(true, true, false, true, address(manager));
        emit ITFManager.NavMaxAgeChanged(manager.maxNavAge(), newAge);
        manager.setMaxNavAge(newAge);
        assertEq(manager.maxNavAge(), newAge);
    }

    function test_Invest_RevertIf_TokensOutZero() public {
        manager.setFee(0);
        uint256 tiny = 1; // 1 wei de baseAsset -> netIn18 * 1e18 / nav == 0
        vm.prank(investor);
        base.approve(address(manager), tiny);
        vm.prank(investor);
        vm.expectRevert(ITFManager.TokensOutZero.selector);
        manager.invest(tiny);
    }

    function test_Redeem_RevertIf_AmountZero() public {
        vm.prank(investor);
        vm.expectRevert(ITFManager.AmountInZero.selector);
        manager.redeem(0);
    }

    function test_Redeem_RevertIf_StaleNAV() public {
        uint256 amountIn = 10e18;
        vm.prank(investor);
        base.approve(address(manager), amountIn);
        vm.prank(investor);
        uint256 out = manager.invest(amountIn);
        manager.setMaxNavAge(60);
        vm.warp(block.timestamp + 61);
        vm.prank(investor);
        assetToken.approve(address(manager), out);
        vm.prank(investor);
        vm.expectRevert(ITFManager.StaleNav.selector);
        manager.redeem(out);
    }

    function test_Constructor_RevertIf_BaseDecimalsTooHigh() public {
        TooManyDecimals x = new TooManyDecimals();
        vm.expectRevert(ITFManager.BaseDecimalsTooHigh.selector);
        new ITFManager(address(x), address(treasuryContract), oracle, initialNav, initialFee);
    }

    }
