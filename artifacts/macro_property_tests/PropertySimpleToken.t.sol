// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySimpleTokenTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/SimpleToken/SimpleToken.lean
 */
contract PropertySimpleTokenTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("SimpleToken", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: mint has no unexpected revert
    function testAuto_Mint_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("mint(address,uint256)", alice, uint256(1)));
        require(ok, "mint reverted unexpectedly");
    }
    // Property 2: transfer has no unexpected revert
    function testAuto_Transfer_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("transfer(address,uint256)", alice, uint256(1)));
        require(ok, "transfer reverted unexpectedly");
    }
    // Property 3: TODO decode and assert `balanceOf` result
    function testTODO_BalanceOf_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(ok, "balanceOf reverted unexpectedly");
        assertEq(ret.length, 32, "balanceOf ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: totalSupply reads storage slot 2 and decodes the result
    function testAuto_TotalSupply_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(2)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("totalSupply()"));
        require(ok, "totalSupply reverted unexpectedly");
        assertEq(ret.length, 32, "totalSupply ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "totalSupply should return storage slot 2");
    }
    // Property 5: owner reads storage slot 0 and decodes the result
    function testAuto_Owner_ReadsConfiguredStorage() public {
        address expected = alice;
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("owner()"));
        require(ok, "owner reverted unexpectedly");
        assertEq(ret.length, 32, "owner ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "owner should return storage slot 0");
    }
}
