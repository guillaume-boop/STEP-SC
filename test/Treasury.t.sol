// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Test.sol";
import "../src/Treasury.sol";
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract TMockUSD is ERC20 {
    constructor() ERC20("Mock USD","mUSD"){ _mint(msg.sender, 1e30); }
    function mint(address to, uint256 amt) external { _mint(to, amt); }
}

contract FailingTransferFrom is ERC20 {
    constructor() ERC20("FailTF","FTF"){ _mint(msg.sender, 1e30); }
    function mint(address to, uint256 amt) external { _mint(to, amt); }
    function transferFrom(address, address, uint256) public pure override returns (bool) { return false; }
}

contract FailingTransfer is ERC20 {
    constructor() ERC20("FailT","FT"){ _mint(msg.sender, 1e30); }
    function mint(address to, uint256 amt) external { _mint(to, amt); }
    function transfer(address, uint256) public pure override returns (bool) { return false; }
}

contract TreasuryTest is Test {
    TMockUSD usd;
    Treasury tre;
    address owner_ = address(this);
    address alice = address(0xA11CE);
    address bob   = address(0xB0B);

    function setUp() public {
        usd = new TMockUSD();
        tre = new Treasury(address(usd), owner_);
        usd.mint(alice, 1_000e18);
    }

    function test_Constructor_Revert_StableZero() public {
        vm.expectRevert(bytes("Treasury: stable token address zero"));
        new Treasury(address(0), owner_);
    }

    function test_Deposit_Succeeds() public {
        vm.prank(alice);
        usd.approve(address(tre), 100e18);
        vm.prank(alice);
        tre.deposit(100e18);
        assertEq(usd.balanceOf(address(tre)), 100e18);
    }

    function test_Deposit_Revert_AmountZero() public {
        vm.prank(alice);
        vm.expectRevert(bytes("Treasury: invalid amount"));
        tre.deposit(0);
    }

    function test_Deposit_Revert_TransferFromFail() public {
        FailingTransferFrom ftf = new FailingTransferFrom();
        Treasury tre2 = new Treasury(address(ftf), owner_);
        ftf.mint(alice, 10e18);
        vm.prank(alice);
        ftf.approve(address(tre2), 10e18);
        vm.prank(alice);
        vm.expectRevert(bytes("Treasury: transfer failed"));
        tre2.deposit(10e18);
    }

    function test_Withdraw_OnlyOwner() public {
        vm.prank(alice);
        usd.approve(address(tre), 10e18);
        vm.prank(alice);
        tre.deposit(10e18);
        vm.prank(alice);
        vm.expectRevert(); 
        tre.withdraw(alice, 1e18);
    }

    function test_Withdraw_Revert_InvalidRecipient() public {
        vm.prank(alice);
        usd.approve(address(tre), 10e18);
        vm.prank(alice);
        tre.deposit(10e18);
        vm.expectRevert(bytes("Treasury: invalid recipient"));
        tre.withdraw(address(0), 1e18);
    }

    function test_Withdraw_Revert_InvalidAmount() public {
        vm.expectRevert(bytes("Treasury: invalid amount"));
        tre.withdraw(alice, 0);
    }

    function test_Withdraw_Revert_Insufficient() public {
        vm.expectRevert(bytes("Treasury: insufficient balance"));
        tre.withdraw(alice, 1e18);
    }

    function test_Withdraw_Revert_TransferFail() public {
        FailingTransfer ft = new FailingTransfer();
        Treasury tre2 = new Treasury(address(ft), owner_);
        ft.mint(address(tre2), 5e18);
        vm.expectRevert(bytes("Treasury: transfer failed"));
        tre2.withdraw(bob, 1e18);
    }

    function test_Withdraw_Succeeds() public {
        vm.prank(alice);
        usd.approve(address(tre), 10e18);
        vm.prank(alice);
        tre.deposit(10e18);
        uint256 a0 = usd.balanceOf(bob);
        tre.withdraw(bob, 3e18);
        assertEq(usd.balanceOf(bob) - a0, 3e18);
        assertEq(usd.balanceOf(address(tre)), 7e18);
    }
}
