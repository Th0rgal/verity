// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/MintableTokenSpecHarness.sol";

contract MintableTokenSpecHarnessTest is Test {
    MintableTokenSpecHarness private token;

    address private constant OWNER = address(0xA11CE);
    address private constant BOB = address(0xB0B);

    function setUp() public {
        token = new MintableTokenSpecHarness(OWNER, 1_000e18);
    }

    function testMintSpecHappy() public {
        vm.prank(OWNER);
        token.mint_spec(250e18);

        assertEq(token.totalSupply(), 1_250e18);
        assertEq(token.balance(OWNER), 1_250e18);
    }

    function testMintSpecRejectsNonOwner() public {
        vm.prank(BOB);
        vm.expectRevert();
        token.mint_spec(1e18);
    }
}
