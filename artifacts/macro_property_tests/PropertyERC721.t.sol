// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyERC721Test
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/ERC721/ERC721.lean
 */
contract PropertyERC721Test is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("ERC721", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: balanceOf reads the configured mapping value
    function testAuto_BalanceOf_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 3), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(ok, "balanceOf reverted unexpectedly");
        assertEq(ret.length, 32, "balanceOf ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "balanceOf should decode the configured mapping value");
    }
    // Property 2: ownerOf decodes a non-zero configured owner word
    function testAuto_OwnerOf_DecodesConfiguredOwnerWord() public {
        address expected = address(0xBEEF);
        vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 4), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("ownerOf(uint256)", uint256(1)));
        require(ok, "ownerOf reverted unexpectedly");
        assertEq(ret.length, 32, "ownerOf ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "ownerOf should decode the configured owner word");
    }
    // Property 3: getApproved decodes the configured secondary mapping value after the existence precondition
    function testAuto_GetApproved_DecodesConfiguredSecondaryMapping() public {
        address ownerWord = alice;
        vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 4), bytes32(uint256(uint160(ownerWord))));
        address expected = alice;
        vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 5), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getApproved(uint256)", uint256(1)));
        require(ok, "getApproved reverted unexpectedly");
        assertEq(ret.length, 32, "getApproved ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "getApproved should decode the configured secondary mapping value");
    }
    // Property 4: isApprovedForAll returns true for a non-zero configured mapping word
    function testAuto_IsApprovedForAll_DetectsNonZeroMappingWord() public {
        vm.store(target, _nestedMappingSlot(bytes32(uint256(uint160(alice))), bytes32(uint256(uint160(alice))), 6), bytes32(uint256(1)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("isApprovedForAll(address,address)", alice, alice));
        require(ok, "isApprovedForAll reverted unexpectedly");
        assertEq(ret.length, 32, "isApprovedForAll ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertTrue(actual, "isApprovedForAll should return true when the configured word is non-zero");
    }
    // Property 5: approve has no unexpected revert
    function testAuto_Approve_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("approve(address,uint256)", alice, uint256(1)));
        require(ok, "approve reverted unexpectedly");
    }
    // Property 6: setApprovalForAll has no unexpected revert
    function testAuto_SetApprovalForAll_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setApprovalForAll(address,bool)", alice, true));
        require(ok, "setApprovalForAll reverted unexpectedly");
    }
    // Property 7: mint returns the minted token id and persists the success-path writes
    function testAuto_Mint_ReturnsMintedTokenIdAndUpdatesState() public {
        address toAddr = alice;
        address expectedOwner = alice;
        uint256 mintedTokenId = uint256(1);
        uint256 currentSupply = uint256(2);
        uint256 recipientBalance = uint256(3);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(uint160(expectedOwner))));
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(currentSupply)));
        vm.store(target, bytes32(uint256(2)), bytes32(uint256(mintedTokenId)));
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(toAddr))), 3), bytes32(uint256(recipientBalance)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("mint(address)", alice));
        require(ok, "mint reverted unexpectedly");
        assertEq(ret.length, 32, "mint ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, mintedTokenId, "mint should return the seeded next token id");
        assertEq(
            vm.load(target, _mappingSlot(bytes32(uint256(actual)), 4)),
            bytes32(uint256(uint160(toAddr))),
            "mint should persist the new owner word"
        );
        assertEq(
            vm.load(target, _mappingSlot(bytes32(uint256(uint160(toAddr))), 3)),
            bytes32(uint256((uint256(3) + 1))),
            "mint should increment the recipient balance"
        );
        assertEq(
            vm.load(target, bytes32(uint256(1))),
            bytes32(uint256((uint256(2) + 1))),
            "mint should increment totalSupply"
        );
        assertEq(
            vm.load(target, bytes32(uint256(2))),
            bytes32(uint256(mintedTokenId + 1)),
            "mint should increment nextTokenId"
        );
    }
    // Property 8: transferFrom has no unexpected revert
    function testAuto_TransferFrom_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("transferFrom(address,address,uint256)", alice, alice, uint256(1)));
        require(ok, "transferFrom reverted unexpectedly");
    }
}
