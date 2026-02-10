// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./YulTestBase.sol";
import "../../examples/solidity/Counter.sol";

interface ICounter {
    function increment() external;
    function decrement() external;
    function getCount() external view returns (uint256);
}

contract CounterYulTest is YulTestBase {
    ICounter private yul;
    Counter private solidityImpl;

    function setUp() public {
        yul = ICounter(deployYul("Counter"));
        solidityImpl = new Counter();
    }

    function testIncrementDecrement() public {
        solidityImpl.increment();
        solidityImpl.increment();
        solidityImpl.decrement();

        yul.increment();
        yul.increment();
        yul.decrement();

        assertEq(solidityImpl.getCount(), yul.getCount());
    }
}
