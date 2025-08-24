// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import "@openzeppelin/contracts/utils/Pausable.sol";
import { SafeERC20, IERC20 } from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import "./AssetToken.sol";

contract ITFManager is Ownable, ReentrancyGuard, Pausable {
    using SafeERC20 for IERC20;

    AssetToken public assetToken;
    IERC20 public baseAsset;
    address public treasury;
    address public oracle;
    uint256 public nav;
    uint256 public feeBps;
    uint64 public navUpdatedAt;
    uint64 public maxNavAge = 1 days;
    uint8 public immutable baseDecimals;
    uint256 private immutable scale;

    event NavUpdated(uint256 oldNav, uint256 newNav);
    event Invest(address indexed investor, uint256 amountIn, uint256 tokensOut);
    event Redeem(address indexed investor, uint256 tokensIn, uint256 amountOut);
    event OracleChanged(address indexed oldOracle, address indexed newOracle);
    event FeeChanged(uint256 oldFee, uint256 newFee);
    event TreasuryChanged(address indexed oldTreasury, address indexed newTreasury);
    event NavMaxAgeChanged(uint64 oldAge, uint64 newAge);

    error AssetTokenZero();
    error BaseAssetZero();
    error TreasuryZero();
    error OracleZero();
    error NavZero();
    error FeeTooHigh();
    error NotOracle();
    error AmountInZero();
    error TokensOutZero();
    error StaleNav();
    error BaseDecimalsTooHigh();

    constructor(
        address assetToken_,
        address baseAsset_,
        address treasury_,
        address oracle_,
        uint256 initialNav,
        uint256 feeBps_
    ) Ownable(msg.sender) {
        if (assetToken_ == address(0)) revert AssetTokenZero();
        if (baseAsset_ == address(0)) revert BaseAssetZero();
        if (treasury_ == address(0)) revert TreasuryZero();
        if (oracle_ == address(0)) revert OracleZero();
        if (initialNav == 0) revert NavZero();
        if (feeBps_ > 10_000) revert FeeTooHigh();

        assetToken = AssetToken(assetToken_);
        baseAsset = IERC20(baseAsset_);
        treasury = treasury_;
        oracle = oracle_;
        nav = initialNav;
        feeBps = feeBps_;

        uint8 dec = ERC20(address(baseAsset)).decimals();
        if (dec > 18) revert BaseDecimalsTooHigh();
        baseDecimals = dec;
        scale = 10 ** (18 - dec);

        navUpdatedAt = uint64(block.timestamp);
    }

    function pause() external onlyOwner {
        _pause();
    }

    function unpause() external onlyOwner {
        _unpause();
    }

    // --- Admin
    function setOracle(address newOracle) external onlyOwner {
        if (newOracle == address(0)) revert OracleZero();
        address old = oracle;
        oracle = newOracle;
        emit OracleChanged(old, newOracle);
    }

    function setFee(uint256 newFeeBps) external onlyOwner {
        if (newFeeBps > 10_000) revert FeeTooHigh();
        uint256 old = feeBps;
        feeBps = newFeeBps;
        emit FeeChanged(old, newFeeBps);
    }

    function setTreasury(address newTreasury) external onlyOwner {
        if (newTreasury == address(0)) revert TreasuryZero();
        address old = treasury;
        treasury = newTreasury;
        emit TreasuryChanged(old, newTreasury);
    }

    function setMaxNavAge(uint64 newAge) external onlyOwner {
        uint64 old = maxNavAge;
        maxNavAge = newAge;
        emit NavMaxAgeChanged(old, newAge);
    }

    // --- Oracle
    function updateNav(uint256 newNav) external {
        if (msg.sender != oracle) revert NotOracle();
        if (newNav == 0) revert NavZero();
        uint256 old = nav;
        nav = newNav;
        navUpdatedAt = uint64(block.timestamp); // <= nouveau
        emit NavUpdated(old, newNav);
    }
    // --- Users

    modifier navFresh() {
        if (block.timestamp - navUpdatedAt > maxNavAge) revert StaleNav();
        _;
    }

    function invest(uint256 amountIn)
        external
        nonReentrant
        whenNotPaused
        navFresh
        returns (uint256 tokensOut)
    {
        if (amountIn == 0) revert AmountInZero();
        if (nav == 0) revert NavZero();

        uint256 fee = (amountIn * feeBps) / 10_000;
        uint256 netIn = amountIn - fee;

        uint256 netIn18 = _to18(netIn);
        uint256 raw = (netIn18 * 1e18) / nav;
        tokensOut = (raw / 1e18) * 1e18;
        if (tokensOut == 0) revert TokensOutZero();

        baseAsset.safeTransferFrom(msg.sender, address(this), netIn);
        if (fee != 0) baseAsset.safeTransferFrom(msg.sender, treasury, fee);

        address tokenTreasury = assetToken.getManager();
        IERC20(address(assetToken)).safeTransferFrom(tokenTreasury, msg.sender, tokensOut);

        emit Invest(msg.sender, amountIn, tokensOut);
    }

    function redeem(uint256 tokensIn)
        external
        nonReentrant
        whenNotPaused
        navFresh
        returns (uint256 amountOut)
    {
        if (tokensIn == 0) revert AmountInZero();

        uint256 gross18 = (tokensIn * nav) / 1e18; // 18d
        uint256 fee18 = (gross18 * feeBps) / 10_000; // 18d
        uint256 net18 = gross18 - fee18; // 18d

        amountOut = _from18(net18);
        uint256 fee = _from18(fee18);

        address tokenTreasury = assetToken.getManager();
        IERC20(address(assetToken)).safeTransferFrom(msg.sender, tokenTreasury, tokensIn);

        baseAsset.safeTransfer(msg.sender, amountOut);
        if (fee > 0) baseAsset.safeTransfer(treasury, fee);

        emit Redeem(msg.sender, tokensIn, amountOut);
    }

    function _to18(uint256 amt) internal view returns (uint256) {
        if (baseDecimals == 18) return amt;
        return amt * scale;
    }

    function _from18(uint256 amt18) internal view returns (uint256) {
        if (baseDecimals == 18) return amt18;
        return amt18 / scale;
    }
}
