# STEP Smart Contracts

This package contains the smart contracts for the STEP platform — tokenized real estate ETFs (ITFs) deployed on Sepolia testnet.

## Units & Conventions

- **NAV**: `uint256` scaled to `1e18`.  
  Example: `2e18` means NAV = 2.0 (2 baseAsset units per ITF).
- **ITF Token**: ERC20, 18 decimals, supply fixed at deployment, floored to multiples of `1e18` on invest.
- **Fees**: `feeBps` in basis points (bps).  
  Example: `50` = 0.5%, `100` = 1%.
- **Stale NAV**: `maxNavAge` (default = 1 day).  
  If NAV is older than this threshold, `invest` and `redeem` revert with `StaleNav`.

## Key Contracts

- **AssetToken.sol**  
  ERC20 representing a single ITF. Minted once at deployment to a treasury address. Immutable supply.

- **ITFManager.sol**  
  Manages NAV, fees, investments, and redemptions. Holds the base asset, distributes AssetTokens, and applies fee logic.

## Events

- `Invest(address investor, uint256 amountIn, uint256 tokensOut)`  
  Emitted on investment. `amountIn` = gross baseAsset deposited, `tokensOut` = ITF tokens minted (floored).

- `Redeem(address investor, uint256 tokensIn, uint256 amountOut)`  
  Emitted on redemption. `amountOut` = net baseAsset returned (fees deducted).

- `NavUpdated(uint256 oldNav, uint256 newNav)`  
  Emitted when the oracle updates the NAV.

- `NavMaxAgeChanged(uint64 oldAge, uint64 newAge)`  
  Emitted when the max NAV age parameter is updated.

- `OracleChanged(address oldOracle, address newOracle)`  
- `FeeChanged(uint256 oldFee, uint256 newFee)`  
- `TreasuryChanged(address oldTreasury, address newTreasury)`

## Errors

- `AssetTokenZero()`, `BaseAssetZero()`, `TreasuryZero()`, `OracleZero()`  
- `NavZero()`, `FeeTooHigh()`, `NotOracle()`  
- `AmountInZero()`, `TokensOutZero()`, `StaleNav()`

## Deployment (Sepolia)

Deployment is done using Foundry scripts.  
Addresses will be stored in `deployments/sepolia.json` after broadcasting.

```json
{
  "network": "sepolia",
  "assetToken": "0x...",
  "baseAsset": "0x...",
  "itfManager": "0x...",
  "treasury": "0x...",
  "oracle": "0x...",
  "block": 0,
  "tx": "0x..."
}
