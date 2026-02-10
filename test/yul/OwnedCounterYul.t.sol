// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./YulTestBase.sol";
import "../../examples/solidity/OwnedCounter.sol";

interface IOwnedCounter {
    function increment() external;
    function decrement() external;
    function getCount() external view returns (uint256);
    function getOwner() external view returns (address);
    function transferOwnership(address newOwner) external;
}

contract OwnedCounterYulTest is YulTestBase {
    IOwnedCounter private yul;
    OwnedCounter private solidityImpl;
    address private alice = address(0xA11CE);
    address private bob = address(0xB0B);

    function setUp() public {
        yul = IOwnedCounter(deployYulWithArgs("OwnedCounter", abi.encode(alice)));
        solidityImpl = new OwnedCounter(alice);
    }

    function testOwnerCanIncrement() public {
        vm.prank(alice);
        solidityImpl.increment();
        vm.prank(alice);
        yul.increment();
        assertEq(solidityImpl.getCount(), yul.getCount());
    }

    function testNonOwnerCannotIncrement() public {
        vm.prank(bob);
        vm.expectRevert();
        yul.increment();

        vm.prank(bob);
        vm.expectRevert();
        solidityImpl.increment();
    }

    function testTransferOwnership() public {
        vm.prank(alice);
        solidityImpl.transferOwnership(bob);
        vm.prank(alice);
        yul.transferOwnership(bob);
        assertEq(solidityImpl.getOwner(), yul.getOwner());
    }
}
