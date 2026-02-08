// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/BrokenSimpleTokenSpecHarness.sol";

contract BrokenSimpleTokenSpecHarnessTest is Test {
    BrokenSimpleTokenSpecHarness private token;

    address private constant OWNER = address(0xA11CE);
    address private constant BOB = address(0xB0B);

    function setUp() public {
        token = new BrokenSimpleTokenSpecHarness(OWNER, 1_000e18);
    }

    function testTransferSpecDetectsBrokenImplementation() public {
        vm.prank(OWNER);
        vm.expectRevert(stdError.assertionError);
        token.transfer_spec(BOB, 100e18);
    }
}
