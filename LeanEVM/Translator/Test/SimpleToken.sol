// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SimpleToken {
    mapping(address => uint256) public balances;
    uint256 public totalSupply;

    function transfer(address to, uint256 amount) public {
        require(balances[msg.sender] >= amount, "insufficient balance");
        balances[msg.sender] -= amount;
        balances[to] += amount;
    }

    function mint(address to, uint256 amount) public {
        balances[to] += amount;
        totalSupply += amount;
    }

    function balanceOf(address account) public view {
        return balances[account];
    }
}
