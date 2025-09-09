// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Test.sol";
import "../src/MockUSD.sol";

contract MockUSDTest is Test {
    function test_MetadataAndDeal() public {
        MockUSD m = new MockUSD();
        assertEq(m.name(), "Mock USD");
        assertEq(m.symbol(), "mUSD");
        assertEq(m.decimals(), 18);

        deal(address(m), address(this), 123e18);

        assertEq(m.balanceOf(address(this)), 123e18);
    }
}
