// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyNewtypeSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyNewtypeSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("NewtypeSmoke", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: mint has no unexpected revert
    function testAuto_Mint_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("mint(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "mint reverted unexpectedly");
    }
    // Property 2: setMinter has no unexpected revert
    function testAuto_SetMinter_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setMinter(address)", alice));
        require(ok, "setMinter reverted unexpectedly");
    }
    // Property 3: getNextTokenId reads storage slot 0 and decodes the result
    function testAuto_GetNextTokenId_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getNextTokenId()"));
        require(ok, "getNextTokenId reverted unexpectedly");
        assertEq(ret.length, 32, "getNextTokenId ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getNextTokenId should return storage slot 0");
    }
}
