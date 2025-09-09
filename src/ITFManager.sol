// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import "@openzeppelin/contracts/utils/Pausable.sol";
import { SafeERC20, IERC20 } from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import { ERC20 } from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "./AssetToken.sol";
import "./Treasury.sol";

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
    uint8  public immutable baseDecimals;
    uint256 private immutable scale;

    event NavUpdated(uint256 oldNav, uint256 newNav);
    event Invest(address indexed investor, uint256 amountIn, uint256 tokensOut);
    event Redeem(address indexed investor, uint256 tokensIn, uint256 amountOut);
    event OracleChanged(address indexed oldOracle, address indexed newOracle);
    event FeeChanged(uint256 oldFee, uint256 newFee);
    event TreasuryChanged(address indexed oldTreasury, address indexed newTreasury);
    event NavMaxAgeChanged(uint64 oldAge, uint64 newAge);
    event AssetTokenBound(address token);

    error AssetTokenZero();
    error AssetTokenAlreadySet();
    error InvalidAssetTokenManager();
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
        address _baseAsset,
        address _treasury,
        address _oracle,
        uint256 initialNav,
        uint256 _feeBps
    ) Ownable(msg.sender) {
        if (_baseAsset == address(0)) revert BaseAssetZero();
        if (_treasury  == address(0)) revert TreasuryZero();
        if (_oracle    == address(0)) revert OracleZero();
        if (initialNav == 0)           revert NavZero();
        if (_feeBps > 10_000)          revert FeeTooHigh();

        baseAsset = IERC20(_baseAsset);
        treasury  = _treasury;
        oracle    = _oracle;
        nav       = initialNav;
        feeBps    = _feeBps;

        uint8 dec = ERC20(address(baseAsset)).decimals();
        if (dec > 18) revert BaseDecimalsTooHigh();
        baseDecimals = dec;
        scale        = 10 ** (18 - dec);

        navUpdatedAt = uint64(block.timestamp);
    }

    function setAssetToken(address token) external onlyOwner {
        if (address(assetToken) != address(0)) revert AssetTokenAlreadySet();
        if (token == address(0))               revert AssetTokenZero();
        AssetToken at = AssetToken(token);
        if (at.getManager() != address(this))  revert InvalidAssetTokenManager();
        assetToken = at;
        emit AssetTokenBound(token);
    }

    function pause() external onlyOwner { _pause(); }
    function unpause() external onlyOwner { _unpause(); }

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

    function updateNav(uint256 newNav) external {
        if (msg.sender != oracle) revert NotOracle();
        if (newNav == 0)           revert NavZero();
        uint256 old = nav;
        nav = newNav;
        navUpdatedAt = uint64(block.timestamp);
        emit NavUpdated(old, newNav);
    }

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
        if (address(assetToken) == address(0)) revert AssetTokenZero();

        uint256 fee   = (amountIn * feeBps) / 10_000;
        uint256 netIn = amountIn - fee;

        uint256 netIn18 = _to18(netIn);
        tokensOut = (netIn18 * 1e18) / nav;
        if (tokensOut == 0) revert TokensOutZero();

        baseAsset.safeTransferFrom(msg.sender, treasury, amountIn);
        IERC20(address(assetToken)).safeTransfer(msg.sender, tokensOut);

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
        if (address(assetToken) == address(0)) revert AssetTokenZero();

        uint256 gross18 = (tokensIn * nav) / 1e18;
        uint256 fee18   = (gross18 * feeBps) / 10_000;
        uint256 net18   = gross18 - fee18;

        amountOut = _from18(net18);
        uint256 fee = _from18(fee18);

        IERC20(address(assetToken)).safeTransferFrom(msg.sender, address(this), tokensIn);
        Treasury(treasury).withdraw(msg.sender, amountOut);
        if (fee > 0) Treasury(treasury).withdraw(owner(), fee);

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
