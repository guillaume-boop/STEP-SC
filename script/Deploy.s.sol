// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Script.sol";
import "../src/AssetToken.sol";
import "../src/ITFManager.sol";
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

// MockUSD for test if no BASE_ASSET_ADDR provided
contract MockUSD is ERC20 {
    constructor() ERC20("Mock USD", "mUSD") {
        _mint(msg.sender, 1e24); // 1,000,000 mUSD (18d)
    }
}

contract DeploySepolia is Script {
    struct Config {
        address treasury;
        address oracle;
        string itfName;
        string itfSymbol;
        uint256 itfSupply;
        uint256 initialNav;
        uint256 feeBps;
        address baseAssetAddr; // optional; address(0) => deploy MockUSD
    }

    function run() external {
        (uint256 pk, Config memory c) = _load();

        vm.startBroadcast(pk);

        // Base asset: use provided address or deploy mock
        address baseAssetAddr = c.baseAssetAddr != address(0)
            ? c.baseAssetAddr
            : address(new MockUSD());

        // Deploy AssetToken (supply minted to tokenTreasury = deployer)
        address tokenTreasury = vm.addr(pk);
        AssetToken assetToken = new AssetToken(
            c.itfName,
            c.itfSymbol,
            c.itfSupply,
            tokenTreasury
        );

        // Deploy ITFManager
        ITFManager manager = new ITFManager(
            address(assetToken),
            baseAssetAddr,
            c.treasury,
            c.oracle,
            c.initialNav,
            c.feeBps
        );

        // Approve manager to distribute ITF to investors
        assetToken.approve(address(manager), type(uint256).max);

        _writeJson(
            address(assetToken),
            baseAssetAddr,
            address(manager),
            c.treasury,
            c.oracle,
            vm.addr(pk)
        );

        vm.stopBroadcast();
    }

    function _load() internal returns (uint256 pk, Config memory c) {
        pk = vm.envUint("PRIVATE_KEY");
        c.treasury = vm.envAddress("TREASURY");
        c.oracle   = vm.envAddress("ORACLE");

        c.itfName   = vm.envOr("ITF_NAME",   string("STEP Paris"));
        c.itfSymbol = vm.envOr("ITF_SYMBOL", string("ITF-PARIS"));
        c.itfSupply = vm.envOr("ITF_SUPPLY", uint256(500e18));
        c.initialNav= vm.envOr("INITIAL_NAV",uint256(2e18));
        c.feeBps    = vm.envOr("FEE_BPS",    uint256(50));

        string memory baseStr = vm.envOr("BASE_ASSET_ADDR", string(""));
        if (bytes(baseStr).length == 42) {
            c.baseAssetAddr = vm.parseAddress(baseStr);
        } else {
            c.baseAssetAddr = address(0);
        }
    }

    function _writeJson(
        address assetTokenAddr,
        address baseAssetAddr,
        address managerAddr,
        address treasuryAddr,
        address oracleAddr,
        address deployerAddr
    ) internal {
        // Assure le dossier existe (si besoin, crée-le manuellement avec `mkdir -p deployments`)
        string memory root = "deploy";
        vm.serializeString(root, "network", "sepolia");
        vm.serializeAddress(root, "assetToken", assetTokenAddr);
        vm.serializeAddress(root, "baseAsset", baseAssetAddr);
        vm.serializeAddress(root, "itfManager", managerAddr);
        vm.serializeAddress(root, "treasury", treasuryAddr);
        vm.serializeAddress(root, "oracle", oracleAddr);
        vm.serializeAddress(root, "deployer", deployerAddr);
        string memory out = vm.serializeUint(root, "block", block.number);
        vm.writeJson(out, "deployments/sepolia.json");
    }
}
