// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Script.sol";
import "../src/AssetToken.sol";
import "../src/ITFManager.sol";

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

// MockUSD for test
contract MockUSD is ERC20 {
    constructor() ERC20("Mock USD", "mUSD") {
        _mint(msg.sender, 1e24); // 1,000,000 mUSD (18d) pour le déployeur
    }
}

contract DeploySepolia is Script {
    function run() external {
        uint256 pk       = vm.envUint("PRIVATE_KEY");
        address treasury = vm.envAddress("TREASURY");
        address oracle   = vm.envAddress("ORACLE");

        string memory itfName   = vm.envOr("ITF_NAME",   string("STEP Paris"));
        string memory itfSymbol = vm.envOr("ITF_SYMBOL", string("ITF-PARIS"));
        uint256 itfSupply       = vm.envOr("ITF_SUPPLY", uint256(500e18));
        uint256 initialNav      = vm.envOr("INITIAL_NAV", uint256(2e18));
        uint256 feeBps          = vm.envOr("FEE_BPS",    uint256(50));
        string memory baseStr   = vm.envOr("BASE_ASSET_ADDR", string(""));

        vm.startBroadcast(pk);

        IERC20 baseAsset;
        if (bytes(baseStr).length == 42) {
            baseAsset = IERC20(vm.parseAddress(baseStr));
        } else {
            baseAsset = IERC20(address(new MockUSD()));
        }

        address tokenTreasury = vm.addr(pk);
        AssetToken assetToken = new AssetToken(
            itfName,
            itfSymbol,
            itfSupply,
            tokenTreasury
        );

        ITFManager manager = new ITFManager(
            address(assetToken),
            address(baseAsset),
            treasury,
            oracle,
            initialNav,
            feeBps
        );

        assetToken.approve(address(manager), type(uint256).max);

        string memory path = "deployments/sepolia.json";
        string memory json = string.concat(
            "{\n",
            '  "network": "sepolia",\n',
            '  "assetToken": "', vm.toString(address(assetToken)), '",\n',
            '  "baseAsset": "', vm.toString(address(baseAsset)), '",\n',
            '  "itfManager": "', vm.toString(address(manager)), '",\n',
            '  "treasury": "', vm.toString(treasury), '",\n',
            '  "oracle": "', vm.toString(oracle), '",\n',
            '  "deployer": "', vm.toString(vm.addr(pk)), '",\n',
            '  "block": ', vm.toString(block.number), "\n",
            "}\n"
        );
        vm.writeFile(path, json);

        vm.stopBroadcast();
    }
}
