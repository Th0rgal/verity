// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./YulTestBase.sol";
import "../../examples/solidity/SafeCounter.sol";

interface ISafeCounter {
    function increment() external;
    function decrement() external;
    function getCount() external view returns (uint256);
}

contract SafeCounterYulTest is YulTestBase {
    ISafeCounter private yul;
    SafeCounter private solidityImpl;

    function setUp() public {
        yul = ISafeCounter(deployYul("SafeCounter"));
        solidityImpl = new SafeCounter();
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

    function testUnderflowReverts() public {
        vm.expectRevert();
        yul.decrement();

        vm.expectRevert();
        solidityImpl.decrement();
    }
}
