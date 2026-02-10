// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./YulTestBase.sol";
import "../../examples/solidity/Owned.sol";

interface IOwned {
    function transferOwnership(address newOwner) external;
    function getOwner() external view returns (address);
}

contract OwnedYulTest is YulTestBase {
    IOwned private yul;
    Owned private solidityImpl;
    address private alice = address(0xA11CE);
    address private bob = address(0xB0B);

    function setUp() public {
        yul = IOwned(deployYulWithArgs("Owned", abi.encode(alice)));
        solidityImpl = new Owned(alice);
    }

    function testInitialOwner() public {
        assertEq(solidityImpl.getOwner(), alice);
        assertEq(yul.getOwner(), alice);
    }

    function testTransferOwnership() public {
        vm.prank(alice);
        solidityImpl.transferOwnership(bob);

        vm.prank(alice);
        yul.transferOwnership(bob);

        assertEq(solidityImpl.getOwner(), yul.getOwner());
    }

    function testNonOwnerCannotTransfer() public {
        vm.prank(bob);
        vm.expectRevert();
        yul.transferOwnership(bob);

        vm.prank(bob);
        vm.expectRevert();
        solidityImpl.transferOwnership(bob);
    }
}
