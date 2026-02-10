// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./YulTestBase.sol";
import "../../examples/solidity/SimpleStorage.sol";

interface ISimpleStorage {
    function store(uint256 value) external;
    function retrieve() external view returns (uint256);
}

contract SimpleStorageYulTest is YulTestBase {
    ISimpleStorage private yul;
    SimpleStorage private solidityImpl;

    function setUp() public {
        yul = ISimpleStorage(deployYul("SimpleStorage"));
        solidityImpl = new SimpleStorage();
    }

    function testStoreAndRetrieve() public {
        solidityImpl.store(42);
        yul.store(42);
        assertEq(solidityImpl.retrieve(), yul.retrieve());
    }

    function testOverwrite() public {
        solidityImpl.store(7);
        yul.store(7);
        solidityImpl.store(999);
        yul.store(999);
        assertEq(solidityImpl.retrieve(), yul.retrieve());
    }
}
