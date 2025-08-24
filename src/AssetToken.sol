// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract AssetToken is ERC20, Ownable {
    error SupplyZero();
    error ManagerZero();
    error ManagerUnchanged();

    address private _manager;

    event ManagerChanged(address indexed oldManager, address indexed newManager);

    constructor(string memory _name, string memory _symbol, uint256 _supply, address manager_)
        ERC20(_name, _symbol)
        Ownable(msg.sender)
    {
        if (_supply == 0) revert SupplyZero();
        if (manager_ == address(0)) revert ManagerZero();

        _manager = manager_;
        _mint(manager_, _supply);
    }

    function getManager() external view returns (address manager) {
        return _manager;
    }

    function setManager(address newManager) external onlyOwner {
        if (newManager == address(0)) revert ManagerZero();
        if (newManager == _manager) revert ManagerUnchanged();

        address old = _manager;
        _manager = newManager;
        emit ManagerChanged(old, newManager);
    }
}
