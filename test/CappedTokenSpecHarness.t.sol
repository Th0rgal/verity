// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/CappedTokenSpecHarness.sol";

contract CappedTokenSpecHarnessTest is Test {
    CappedTokenSpecHarness private token;

    address private constant OWNER = address(0xA11CE);
    address private constant BOB = address(0xB0B);

    function setUp() public {
        token = new CappedTokenSpecHarness(OWNER, 1_000e18, 2_000e18);
    }

    function testMintSpecHappy() public {
        vm.prank(OWNER);
        token.mint_spec(500e18);

        assertEq(token.totalSupply(), 1_500e18);
        assertEq(token.balance(OWNER), 1_500e18);
        assertEq(token.maxSupply(), 2_000e18);
    }

    function testMintSpecRejectsNonOwner() public {
        vm.prank(BOB);
        vm.expectRevert();
        token.mint_spec(1e18);
    }

    function testMintSpecRejectsCapExceeded() public {
        vm.prank(OWNER);
        vm.expectRevert();
        token.mint_spec(2_000e18);
    }
}
