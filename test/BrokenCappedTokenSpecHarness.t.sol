// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/BrokenCappedTokenSpecHarness.sol";

contract BrokenCappedTokenSpecHarnessTest is Test {
    BrokenCappedTokenSpecHarness private token;

    address private constant OWNER = address(0xA11CE);

    function setUp() public {
        token = new BrokenCappedTokenSpecHarness(OWNER, 0, 100e18);
    }

    function testMintSpecDetectsBrokenSupplyUpdate() public {
        vm.prank(OWNER);
        vm.expectRevert(stdError.assertionError);
        token.mint_spec(60e18);
    }
}
