// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Test.sol";
import "../src/AssetToken.sol";

contract AssetTokenTest is Test {
    AssetToken token;

    string constant NAME = "STEP Paris";
    string constant SYMBOL = "ITF-PARIS";
    uint256 constant SUPPLY = 500;
    address manager = address(0xA11CE);
    address alice = address(0xB0B);
    address bob = address(0xC0B);

    function setUp() public {
        token = new AssetToken(NAME, SYMBOL, SUPPLY, manager);
    }

    function test_Constructor_MintsToManagerAndSetsMetadata() public {
        assertEq(token.name(), NAME);
        assertEq(token.symbol(), SYMBOL);
        assertEq(token.decimals(), 18);
        assertEq(token.totalSupply(), SUPPLY * 1e18);
        assertEq(token.balanceOf(manager), SUPPLY * 1e18);
    }

    function test_Constructor_RevertIf_SupplyZero() public {
        vm.expectRevert(AssetToken.SupplyZero.selector);
        new AssetToken(NAME, SYMBOL, 0, manager);
    }

    function test_Constructor_RevertIf_ManagerZero() public {
        vm.expectRevert(AssetToken.ManagerZero.selector);
        new AssetToken(NAME, SYMBOL, SUPPLY, address(0));
    }

    function test_Transfer_Works() public {
        vm.prank(manager);
        token.transfer(alice, 10e18);
        assertEq(token.balanceOf(alice), 10e18);
        assertEq(token.balanceOf(manager), (SUPPLY * 1e18) - 10e18);
    }

    function test_Allowance_Approve_TransferFrom() public {
        vm.prank(manager);
        token.approve(bob, 5e18);

        vm.prank(bob);
        token.transferFrom(manager, bob, 5e18);

        assertEq(token.balanceOf(bob), 5e18);
        assertEq(token.balanceOf(manager), (SUPPLY * 1e18) - 5e18);
        assertEq(token.allowance(manager, bob), 0);
    }

    function test_SetManager_OnlyOwner() public {
        vm.prank(alice);
        vm.expectRevert();
        token.setManager(alice);
    }

    function test_SetManager_RevertIf_Zero() public {
        vm.expectRevert(AssetToken.ManagerZero.selector);
        token.setManager(address(0));
    }

    function test_SetManager_RevertIf_Same() public {
        vm.expectRevert(AssetToken.ManagerUnchanged.selector);
        token.setManager(manager);
    }

    function test_SetManager_UpdatesAndEmits() public {
        address newManager = address(0xDEAD);

        vm.expectEmit(true, true, false, true, address(token));
        emit AssetToken.ManagerChanged(manager, newManager);

        token.setManager(newManager);
        assertEq(token.getManager(), newManager);
    }

    function test_TotalSupply_ConstantAfterTransfers() public {
        vm.startPrank(manager);
        token.transfer(alice, 20e18);
        token.transfer(bob, 30e18);
        vm.stopPrank();

        vm.prank(alice);
        token.transfer(bob, 10e18);

        assertEq(token.totalSupply(), SUPPLY * 1e18);
    }
}
