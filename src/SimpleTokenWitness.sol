// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {SimpleToken} from "./SimpleToken.sol";

/// @notice Wrapper to model a "forall other address" constraint via a witness parameter.
contract SimpleTokenWitness is SimpleToken {
    constructor(address owner, uint256 supply) SimpleToken(owner, supply) {}

    function transferWitness(address to, uint256 amount, address other) public {
        super.transfer(to, amount);
        other;
    }
}
