// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyImmutableSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyImmutableSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("ImmutableSmoke", abi.encode(uint256(1), alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: supplyCap returns the declared constant or immutable value
    function testAuto_SupplyCap_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("supplyCap()"));
        require(ok, "supplyCap reverted unexpectedly");
        assertEq(ret.length, 32, "supplyCap ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, (uint256(1) + 2), "supplyCap should preserve the expected value");
    }
    // Property 2: treasuryAddr returns the declared constant or immutable value
    function testAuto_TreasuryAddr_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("treasuryAddr()"));
        require(ok, "treasuryAddr reverted unexpectedly");
        assertEq(ret.length, 32, "treasuryAddr ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, alice, "treasuryAddr should preserve the expected value");
    }
    // Property 3: shadowed returns the direct parameter value
    function testAuto_Shadowed_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("shadowed(uint256)", uint256(1)));
        require(ok, "shadowed reverted unexpectedly");
        assertEq(ret.length, 32, "shadowed ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "shadowed should preserve the expected value");
    }
}
