// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract Treasury is Ownable {
    IERC20 public immutable stable;

    constructor(address _stable, address initialOwner) Ownable(initialOwner) {
        require(_stable != address(0), "Treasury: stable token address zero");
        stable = IERC20(_stable);
    }

    function deposit(uint256 amount) external {
        require(amount > 0, "Treasury: invalid amount");
        require(stable.transferFrom(msg.sender, address(this), amount), "Treasury: transfer failed");
    }

    function withdraw(address to, uint256 amount) external onlyOwner {
        require(to != address(0), "Treasury: invalid recipient");
        require(amount > 0, "Treasury: invalid amount");
        require(stable.balanceOf(address(this)) >= amount, "Treasury: insufficient balance");
        require(stable.transfer(to, amount), "Treasury: transfer failed");
    }

    function balance() external view returns (uint256) {
        return stable.balanceOf(address(this));
    }
}
