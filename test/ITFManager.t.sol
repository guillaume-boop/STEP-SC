// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Test.sol";
import "../src/AssetToken.sol";
import "../src/ITFManager.sol";
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

// --- Mock for test
contract MockERC20 is ERC20 {
    constructor() ERC20("Mock USD", "mUSD") {
        _mint(msg.sender, 1e30);
    }

    function mint(address to, uint256 amt) external {
        _mint(to, amt);
    }
}

contract MockUSDC is ERC20 {
    constructor() ERC20("Mock USDC", "mUSDC") { }

    function decimals() public pure override returns (uint8) {
        return 6;
    }

    function mint(address to, uint256 amt) external {
        _mint(to, amt);
    }
}

// --- Mocks for failing test
contract FailingERC20 is ERC20 {
    constructor() ERC20("Failing USD", "fUSD") { }

    function mint(address to, uint256 amt) external {
        _mint(to, amt);
    }

    function transferFrom(address, address, uint256) public pure override returns (bool) {
        return false;
    }
}

contract ITFManagerTest is Test {
    AssetToken assetToken;
    ITFManager manager;
    MockERC20 base;

    string constant NAME = "STEP Paris";
    string constant SYMBOL = "ITF-PARIS";
    uint256 constant SUPPLY = 500e18;

    address tokenTreasury = address(0xA11CE);
    address treasury = address(0xFEE);
    address oracle = address(0xBEEF);
    address investor = address(0xCEEF);

    uint256 initialNav = 2e18;
    uint256 initialFee = 50;

    function setUp() public {
        // Tokens
        assetToken = new AssetToken(NAME, SYMBOL, SUPPLY, tokenTreasury);
        base = new MockERC20();
        base.mint(investor, 1_000e18);
        base.mint(treasury, 0);

        // Manager
        manager = new ITFManager(
            address(assetToken),
            address(base),
            treasury,
            oracle,
            initialNav, // 2e18
            initialFee // 50 bps
        );

        vm.prank(tokenTreasury);
        assetToken.approve(address(manager), type(uint256).max);
        base.mint(address(manager), 1_000e18);
    }

    // --- Constructor

    function test_Constructor_SetsStateCorrectly() public {
        assertEq(address(manager.assetToken()), address(assetToken));
        assertEq(address(manager.baseAsset()), address(base));
        assertEq(manager.treasury(), treasury);
        assertEq(manager.oracle(), oracle);
        assertEq(manager.nav(), initialNav);
        assertEq(manager.feeBps(), initialFee);
        assertEq(manager.owner(), address(this));
    }

    function test_Constructor_RevertIf_AssetTokenZero() public {
        vm.expectRevert(ITFManager.AssetTokenZero.selector);
        new ITFManager(address(0), address(base), treasury, oracle, initialNav, initialFee);
    }

    function test_Constructor_RevertIf_BaseAssetZero() public {
        vm.expectRevert(ITFManager.BaseAssetZero.selector);
        new ITFManager(address(assetToken), address(0), treasury, oracle, initialNav, initialFee);
    }

    function test_Constructor_RevertIf_TreasuryZero() public {
        vm.expectRevert(ITFManager.TreasuryZero.selector);
        new ITFManager(
            address(assetToken), address(base), address(0), oracle, initialNav, initialFee
        );
    }

    function test_Constructor_RevertIf_OracleZero() public {
        vm.expectRevert(ITFManager.OracleZero.selector);
        new ITFManager(
            address(assetToken), address(base), treasury, address(0), initialNav, initialFee
        );
    }

    function test_Constructor_RevertIf_NavZero() public {
        vm.expectRevert(ITFManager.NavZero.selector);
        new ITFManager(address(assetToken), address(base), treasury, oracle, 0, initialFee);
    }

    function test_Constructor_RevertIf_FeeTooHigh() public {
        vm.expectRevert(ITFManager.FeeTooHigh.selector);
        new ITFManager(address(assetToken), address(base), treasury, oracle, initialNav, 10_001);
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
        address newTreasury = address(0xD00D);
        vm.expectEmit(true, true, false, true, address(manager));
        emit ITFManager.TreasuryChanged(treasury, newTreasury);
        manager.setTreasury(newTreasury);
        assertEq(manager.treasury(), newTreasury);
    }

    // --- Oracle
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

    function test_Invest_CalculatesTokensOut_Floor_AndTransfers() public {
        uint256 amountIn = 11e18; // brut
        uint256 fee = (amountIn * initialFee) / 10_000; // 50 bps
        uint256 netIn = amountIn - fee; // 10.945e18
        uint256 expectedOut = (netIn * 1e18) / initialNav; // 5.4725e18
        expectedOut = (expectedOut / 1e18) * 1e18; // floor => 5e18

        vm.prank(investor);
        base.approve(address(manager), amountIn);

        uint256 m0 = base.balanceOf(address(manager));
        uint256 t0 = base.balanceOf(treasury);
        uint256 itf0 = assetToken.balanceOf(investor);

        vm.recordLogs();

        vm.prank(investor);
        uint256 out = manager.invest(amountIn);

        assertEq(out, expectedOut, "tokensOut mismatch");
        assertEq(assetToken.balanceOf(investor) - itf0, expectedOut, "ITF to investor");
        assertEq(base.balanceOf(address(manager)) - m0, netIn, "base to manager (netIn)");
        assertEq(base.balanceOf(treasury) - t0, fee, "fee to treasury");

        Vm.Log[] memory entries = vm.getRecordedLogs();
        bytes32 sig = keccak256("Invest(address,uint256,uint256)");
        bool found;
        address evInvestor;
        uint256 evAmount;
        uint256 evTokens;

        for (uint256 i = 0; i < entries.length; i++) {
            if (entries[i].topics.length > 0 && entries[i].topics[0] == sig) {
                found = true;
                if (entries[i].topics.length == 2) {
                    evInvestor = address(uint160(uint256(entries[i].topics[1])));
                    (evAmount, evTokens) = abi.decode(entries[i].data, (uint256, uint256));
                } else {
                    (evInvestor, evAmount, evTokens) =
                        abi.decode(entries[i].data, (address, uint256, uint256));
                }
                break;
            }
        }

        // Asserts event
        assertTrue(found, "Invest event not found");
        assertEq(evInvestor, investor, "event investor mismatch");
        assertEq(evAmount, amountIn, "event amount should be gross");
        assertEq(evTokens, expectedOut, "event tokensOut mismatch");
    }

    function test_Redeem_CalculatesNet_AppliesFee_BurnsTokens_TransfersBase() public {
        vm.prank(tokenTreasury);
        assetToken.transfer(investor, 10e18);

        vm.prank(investor);
        assetToken.approve(address(manager), 10e18);

        uint256 expectedGross = 20e18;
        uint256 expectedFee = (expectedGross * initialFee) / 10_000;
        uint256 expectedNet = expectedGross - expectedFee;

        uint256 bal0 = base.balanceOf(investor);

        vm.expectEmit(true, false, false, true, address(manager));
        emit ITFManager.Redeem(investor, 10e18, expectedNet);

        vm.prank(investor);
        uint256 out = manager.redeem(10e18);

        assertEq(out, expectedNet);
        assertEq(base.balanceOf(investor) - bal0, expectedNet);
        assertEq(base.balanceOf(treasury), expectedFee);
        assertEq(assetToken.balanceOf(investor), 0);
    }

    function test_Invest_RevertIf_AmountZero() public {
        vm.expectRevert(ITFManager.AmountInZero.selector);
        manager.invest(0);
    }

    function test_Invest_RevertIf_TokensOutZero() public {
        uint256 small = 1e18; // < nav (2e18), net encore plus petit avec fee
        vm.prank(investor);
        base.approve(address(manager), small);
        vm.expectRevert(ITFManager.TokensOutZero.selector);
        vm.prank(investor);
        manager.invest(small);
    }

    function test_Invest_RevertIf_BaseTransferFromFail() public {
        FailingERC20 bad = new FailingERC20();
        bad.mint(investor, 10e18);

        ITFManager badManager = new ITFManager(
            address(assetToken), address(bad), treasury, oracle, initialNav, initialFee
        );

        vm.prank(tokenTreasury);
        assetToken.approve(address(badManager), type(uint256).max);

        vm.prank(investor);
        bad.approve(address(badManager), 10e18);

        vm.expectRevert();
        vm.prank(investor);
        badManager.invest(5e18);
    }

    function test_SetOracle_RevertIf_Zero() public {
        vm.expectRevert();
        manager.setOracle(address(0));
    }

    function test_SetFee_RevertIf_TooHigh_ExactBoundary() public {
        vm.expectRevert(ITFManager.FeeTooHigh.selector);
        manager.setFee(10_001);
    }

    function test_Invest_FeeZero_Path() public {
        manager.setFee(0);
        uint256 amountIn = 11e18;

        vm.prank(investor);
        base.approve(address(manager), amountIn);

        uint256 m0 = base.balanceOf(address(manager));
        uint256 t0 = base.balanceOf(treasury);
        uint256 itf0 = assetToken.balanceOf(investor);

        vm.prank(investor);
        uint256 out = manager.invest(amountIn);

        assertEq(out, 5e18);
        assertEq(assetToken.balanceOf(investor) - itf0, 5e18);
        assertEq(base.balanceOf(address(manager)) - m0, amountIn, "manager should get all (no fee)");
        assertEq(base.balanceOf(treasury) - t0, 0, "no fee");
    }

    function test_Pause_Blocks_Invest_Redeem() public {
        manager.pause();

        vm.prank(investor);
        base.approve(address(manager), 10e18);

        vm.expectRevert();
        vm.prank(investor);
        manager.invest(10e18);

        vm.prank(tokenTreasury);
        assetToken.transfer(investor, 1e18);
        vm.prank(investor);
        assetToken.approve(address(manager), 1e18);

        vm.expectRevert();
        vm.prank(investor);
        manager.redeem(1e18);

        manager.unpause();

        vm.prank(investor);
        uint256 out = manager.invest(10e18);
        assertGt(out, 0);
    }

    function test_Invest_RevertIf_StaleNAV() public {
        manager.setMaxNavAge(60); // 1 min
        vm.warp(block.timestamp + 61);

        vm.prank(investor);
        base.approve(address(manager), 10e18);

        vm.expectRevert(ITFManager.StaleNav.selector);
        vm.prank(investor);
        manager.invest(10e18);
    }

    function test_Invest_OkAfter_UpdateNav() public {
        manager.setMaxNavAge(60);
        vm.warp(block.timestamp + 61);

        vm.prank(oracle);
        manager.updateNav(2e18);

        uint256 amountIn = 10e18;
        vm.prank(investor);
        base.approve(address(manager), amountIn);

        vm.prank(investor);
        uint256 out = manager.invest(amountIn);
        assertGt(out, 0);
    }

    function test_Invest_USDC6_Calcul_Floor_AndTransfers() public {
        // Déploie un baseAsset en 6 décimales
        MockUSDC usdc = new MockUSDC();
        // Donne du solde à l’investor et au manager
        usdc.mint(investor, 1_000_000_000); // 1,000 USDC (6d)
        // Nouveau manager avec USDC 6d
        ITFManager m2 = new ITFManager(
            address(assetToken),
            address(usdc),
            treasury,
            oracle,
            initialNav, // 2e18
            initialFee // 50 bps
        );
        // Approve du trésor d’ITF au nouveau manager
        vm.prank(tokenTreasury);
        assetToken.approve(address(m2), type(uint256).max);

        // amountIn = 11 USDC (6d)
        uint256 amountIn = 11_000_000; // 11.000000
        uint256 fee = (amountIn * initialFee) / 10_000; // 0.5% = 55_000
        uint256 netIn = amountIn - fee; // 10_94500

        // Conversion vers 18d: * 1e12
        uint256 netIn18 = uint256(netIn) * 1e12; // 10.945e18
        // tokensOut = floor((netIn18 * 1e18 / nav) / 1e18) * 1e18
        uint256 raw = (netIn18 * 1e18) / initialNav; // /2 => 5.4725e18
        uint256 expectedOut = (raw / 1e18) * 1e18; // floor -> 5e18

        vm.prank(investor);
        usdc.approve(address(m2), amountIn);

        uint256 manager0 = usdc.balanceOf(address(m2));
        uint256 treasury0 = usdc.balanceOf(treasury);
        uint256 itf0 = assetToken.balanceOf(investor);

        vm.prank(investor);
        uint256 out = m2.invest(amountIn);

        assertEq(out, expectedOut, "tokensOut mismatch (6d)");
        assertEq(assetToken.balanceOf(investor) - itf0, expectedOut, "ITF to investor");
        assertEq(usdc.balanceOf(address(m2)) - manager0, netIn, "base to manager (netIn 6d)");
        assertEq(usdc.balanceOf(treasury) - treasury0, fee, "fee to treasury (6d)");
    }

    function test_Redeem_USDC6_Calcul_FeeAndTransfers() public {
        // Base 6d
        MockUSDC usdc = new MockUSDC();
        // Manager 6d
        ITFManager m2 = new ITFManager(
            address(assetToken),
            address(usdc),
            treasury,
            oracle,
            initialNav, // 2e18
            initialFee // 50 bps
        );
        vm.prank(tokenTreasury);
        assetToken.approve(address(m2), type(uint256).max);

        // Seed: le manager doit avoir du baseAsset pour payer le redeem
        usdc.mint(address(m2), 1_000_000_000); // 1,000 USDC

        // Donne 10 ITF à l’investor
        vm.prank(tokenTreasury);
        assetToken.transfer(investor, 10e18);
        vm.prank(investor);
        assetToken.approve(address(m2), 10e18);

        // Gross (18d) = 10e18 * 2e18 / 1e18 = 20e18
        // fee18 = 20e18 * 50 / 10000 = 0.1e18
        // net18 = 19.9e18
        // Convert 18d -> 6d : / 1e12
        uint256 expectedGross6 = 20e18 / 1e12; // 20_000_000
        uint256 expectedFee6 = (expectedGross6 * initialFee) / 10_000; // 100_000
        uint256 expectedNet6 = expectedGross6 - expectedFee6; // 19_900_000

        uint256 user0 = usdc.balanceOf(investor);
        uint256 treas0 = usdc.balanceOf(treasury);

        vm.prank(investor);
        uint256 out = m2.redeem(10e18);

        assertEq(out, expectedNet6, "amountOut (6d)");
        assertEq(usdc.balanceOf(investor) - user0, expectedNet6, "user gets net (6d)");
        assertEq(usdc.balanceOf(treasury) - treas0, expectedFee6, "treasury gets fee (6d)");
        assertEq(
            assetToken.balanceOf(investor), 0, "tokens burned (transferred back to tokenTreasury)"
        );
    }
}
