// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

// AUTO-GENERATED POC: DO NOT USE IN PRODUCTION
contract DumbTokenSpec {
    mapping(address => uint256) public balance;
    uint256 public totalSupply;

    // Invariants (not enforced on-chain in this POC):
    // - NonNegativeBalances: forall account: balance[account] >= 0
    // - SupplyConservation: sum(balance) == totalSupply

    function Transfer(address from, address to, uint256 amount) external {
        uint256 old_balance_from = balance[from];
        uint256 old_balance_to = balance[to];
        uint256 old_totalSupply = totalSupply;


        // Implementation hint: apply the minimal state diff
        balance[from] = old_balance_from - amount;
        balance[to] = old_balance_to + amount;

        assert(balance[from] == old_balance_from - amount);
        assert(balance[to] == old_balance_to + amount);
        // TODO: enforce quantified postcondition: forall addr != from && addr != to:
        assert(balance[addr] == old(balance[addr]));

        // Reference to preserve supply conservation if applicable
        assert(totalSupply == old_totalSupply);
    }

}