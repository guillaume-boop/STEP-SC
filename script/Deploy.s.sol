// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Script.sol";
import "../src/AssetToken.sol";
import "../src/ITFManager.sol";
import "../src/Treasury.sol";
import "../src/MockUSD.sol";

contract Deploy is Script {
    struct Cfg {
        address baseAsset;
        address oracle;
        string  name;
        string  symbol;
        uint256 supply;
        uint256 initialNav;
        uint256 feeBps;
    }

    function _load() internal view returns (Cfg memory c) {
        c.oracle     = vm.envAddress("ORACLE");
        c.name       = vm.envString("TOKEN_NAME");
        c.symbol     = vm.envString("TOKEN_SYMBOL");
        c.supply     = vm.parseUint(vm.envString("TOKEN_SUPPLY"));
        c.initialNav = vm.parseUint(vm.envString("INITIAL_NAV_WEI"));
        c.feeBps     = vm.parseUint(vm.envString("FEE_BPS"));

        string memory baseStr = vm.envOr("BASE_ASSET_ADDR", string(""));
        if (bytes(baseStr).length > 0) c.baseAsset = vm.parseAddress(baseStr);
        else                           c.baseAsset = address(0);
    }

    function run() external {
        Cfg memory c = _load();

        vm.startBroadcast();

        address base;
        if (c.baseAsset == address(0)) {
            MockUSD musd = new MockUSD();
            base = address(musd);
        } else {
            base = c.baseAsset;
        }

        Treasury tre = new Treasury(base, msg.sender);

        ITFManager manager = new ITFManager(
            base,
            address(tre),
            c.oracle,
            c.initialNav,
            c.feeBps
        );

        AssetToken itf = new AssetToken(
            c.name,
            c.symbol,
            c.supply,
            address(manager)
        );

        manager.setAssetToken(address(itf));
        tre.transferOwnership(address(manager));

        vm.stopBroadcast();

        console2.log("=== DEPLOY OK ===");
        console2.log("BaseAsset      :", base);
        console2.log("Treasury       :", address(tre));
        console2.log("ITFManager     :", address(manager));
        console2.log("AssetToken     :", address(itf));
        console2.log("Initial NAV    :", c.initialNav);
        console2.log("Fee Bps        :", c.feeBps);
    }
}
