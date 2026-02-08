// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/SimpleTokenWitnessSpecHarness.sol";

contract SimpleTokenWitnessSpecHarnessTest is Test {
    SimpleTokenWitnessSpecHarness private token;

    address private constant ALICE = address(0xA11CE);
    address private constant BOB = address(0xB0B);
    address private constant CAROL = address(0xCA001);

    function setUp() public {
        token = new SimpleTokenWitnessSpecHarness(ALICE, 1_000e18);
        vm.prank(ALICE);
        token.transferWitness_spec(BOB, 200e18, CAROL);
    }

    function testTransferWitnessHappy() public {
        vm.prank(ALICE);
        token.transferWitness_spec(BOB, 100e18, CAROL);

        assertEq(token.balance(ALICE), 700e18);
        assertEq(token.balance(BOB), 300e18);
        assertEq(token.balance(CAROL), 0);
        assertEq(token.totalSupply(), 1_000e18);
    }

    function testTransferWitnessRejectsOtherIsSender() public {
        vm.prank(ALICE);
        vm.expectRevert();
        token.transferWitness_spec(BOB, 1e18, ALICE);
    }

    function testTransferWitnessRejectsOtherIsReceiver() public {
        vm.prank(ALICE);
        vm.expectRevert();
        token.transferWitness_spec(BOB, 1e18, BOB);
    }
}
