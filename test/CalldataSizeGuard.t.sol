// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title CalldataSizeGuardTest
 * @notice Tests that all compiled contracts reject calls with truncated calldata.
 * @dev Validates fix for issue #176: generated Yul must check calldatasize()
 *      and revert when calldata is shorter than expected.
 *
 *      Expected minimum calldatasize per param count:
 *      - 0 params: 4 bytes (selector only)
 *      - 1 param:  36 bytes (4 + 32)
 *      - 2 params: 68 bytes (4 + 64)
 */
contract CalldataSizeGuardTest is YulTestBase {
    address counter;
    address ledger;
    address simpleStorage;
    address safeCounter;
    address owned;
    address ownedCounter;
    address simpleToken;

    address alice = address(0xA11CE);
    address bob = address(0xB0B);

    function setUp() public {
        counter = deployYul("Counter");
        ledger = deployYul("Ledger");
        simpleStorage = deployYul("SimpleStorage");
        safeCounter = deployYul("SafeCounter");
        owned = deployYulWithArgs("Owned", abi.encode(alice));
        ownedCounter = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        simpleToken = deployYulWithArgs("SimpleToken", abi.encode(alice));
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Helper: send raw calldata to a contract
    //═══════════════════════════════════════════════════════════════════════════

    function _callRaw(address target, bytes memory data) internal returns (bool) {
        (bool success,) = target.call(data);
        return success;
    }

    //═══════════════════════════════════════════════════════════════════════════
    // 0-param functions: require exactly 4 bytes (selector)
    //═══════════════════════════════════════════════════════════════════════════

    function testCalldataSize_Counter_Increment_TooShort() public {
        // 3 bytes: too short for selector
        assertFalse(_callRaw(counter, hex"d09de0"), "3 bytes should revert");
    }

    function testCalldataSize_Counter_Increment_Exact() public {
        // 4 bytes: exact selector
        assertTrue(_callRaw(counter, abi.encodeWithSignature("increment()")), "4 bytes should succeed");
    }

    function testCalldataSize_Counter_GetCount_TooShort() public {
        assertFalse(_callRaw(counter, hex"a87d94"), "3 bytes should revert");
    }

    function testCalldataSize_Counter_GetCount_Exact() public {
        assertTrue(_callRaw(counter, abi.encodeWithSignature("getCount()")), "4 bytes should succeed");
    }

    function testCalldataSize_SafeCounter_Decrement_TooShort() public {
        assertFalse(_callRaw(safeCounter, hex"2baece"), "3 bytes should revert");
    }

    function testCalldataSize_SafeCounter_Decrement_Exact() public {
        // First increment so decrement doesn't underflow
        _callRaw(safeCounter, abi.encodeWithSignature("increment()"));
        assertTrue(_callRaw(safeCounter, abi.encodeWithSignature("decrement()")), "4 bytes should succeed");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // 1-param functions: require 36 bytes (4 + 32)
    //═══════════════════════════════════════════════════════════════════════════

    function testCalldataSize_SimpleStorage_Store_TooShort() public {
        // 35 bytes: selector + 31 bytes (missing last byte of param)
        bytes memory short = new bytes(35);
        short[0] = 0x60; short[1] = 0x57; short[2] = 0x36; short[3] = 0x1d; // store selector
        assertFalse(_callRaw(simpleStorage, short), "35 bytes should revert for 1-param function");
    }

    function testCalldataSize_SimpleStorage_Store_Exact() public {
        assertTrue(
            _callRaw(simpleStorage, abi.encodeWithSignature("store(uint256)", 42)),
            "36 bytes should succeed"
        );
    }

    function testCalldataSize_SimpleStorage_Store_SelectorOnly() public {
        // Just 4 bytes (selector only, no param)
        assertFalse(_callRaw(simpleStorage, hex"6057361d"), "4 bytes should revert for 1-param function");
    }

    function testCalldataSize_Owned_TransferOwnership_TooShort() public {
        bytes memory short = new bytes(20); // selector + partial address
        short[0] = 0xf2; short[1] = 0xfd; short[2] = 0xe3; short[3] = 0x8b; // transferOwnership selector
        vm.prank(alice);
        assertFalse(_callRaw(owned, short), "20 bytes should revert for 1-param function");
    }

    function testCalldataSize_Owned_TransferOwnership_Exact() public {
        vm.prank(alice);
        assertTrue(
            _callRaw(owned, abi.encodeWithSignature("transferOwnership(address)", bob)),
            "36 bytes should succeed"
        );
    }

    function testCalldataSize_Ledger_Deposit_SelectorOnly() public {
        assertFalse(_callRaw(ledger, hex"b6b55f25"), "4 bytes should revert for 1-param function");
    }

    function testCalldataSize_Ledger_Deposit_Exact() public {
        assertTrue(
            _callRaw(ledger, abi.encodeWithSignature("deposit(uint256)", 100)),
            "36 bytes should succeed"
        );
    }

    function testCalldataSize_Ledger_GetBalance_TooShort() public {
        assertFalse(_callRaw(ledger, hex"f8b2cb4f"), "4 bytes should revert for 1-param function");
    }

    function testCalldataSize_Ledger_GetBalance_Exact() public {
        assertTrue(
            _callRaw(ledger, abi.encodeWithSignature("getBalance(address)", alice)),
            "36 bytes should succeed"
        );
    }

    //═══════════════════════════════════════════════════════════════════════════
    // 2-param functions: require 68 bytes (4 + 64)
    //═══════════════════════════════════════════════════════════════════════════

    function testCalldataSize_Ledger_Transfer_TooShort() public {
        // 36 bytes: only first param, missing second
        bytes memory oneParam = abi.encodeWithSignature("transfer(address,uint256)", bob);
        bytes memory short = new bytes(36);
        for (uint i = 0; i < 36; i++) short[i] = oneParam[i];
        assertFalse(_callRaw(ledger, short), "36 bytes should revert for 2-param function");
    }

    function testCalldataSize_Ledger_Transfer_SelectorOnly() public {
        assertFalse(_callRaw(ledger, hex"a9059cbb"), "4 bytes should revert for 2-param function");
    }

    function testCalldataSize_Ledger_Transfer_Exact() public {
        // First deposit so transfer has balance
        _callRaw(ledger, abi.encodeWithSignature("deposit(uint256)", 100));
        assertTrue(
            _callRaw(ledger, abi.encodeWithSignature("transfer(address,uint256)", bob, 50)),
            "68 bytes should succeed"
        );
    }

    function testCalldataSize_SimpleToken_Mint_SelectorOnly() public {
        assertFalse(_callRaw(simpleToken, hex"40c10f19"), "4 bytes should revert for 2-param function");
    }

    function testCalldataSize_SimpleToken_Mint_Exact() public {
        vm.prank(alice);
        assertTrue(
            _callRaw(simpleToken, abi.encodeWithSignature("mint(address,uint256)", bob, 1000)),
            "68 bytes should succeed"
        );
    }

    function testCalldataSize_SimpleToken_Transfer_TooShort() public {
        bytes memory short = new bytes(67); // 1 byte short of 68
        short[0] = 0xa9; short[1] = 0x05; short[2] = 0x9c; short[3] = 0xbb; // transfer selector
        vm.prank(alice);
        assertFalse(_callRaw(simpleToken, short), "67 bytes should revert for 2-param function");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Empty calldata: should revert for all contracts (hits default case)
    //═══════════════════════════════════════════════════════════════════════════

    function testCalldataSize_EmptyCalldata_Counter() public {
        assertFalse(_callRaw(counter, ""), "empty calldata should revert");
    }

    function testCalldataSize_EmptyCalldata_Ledger() public {
        assertFalse(_callRaw(ledger, ""), "empty calldata should revert");
    }

    function testCalldataSize_EmptyCalldata_SimpleToken() public {
        assertFalse(_callRaw(simpleToken, ""), "empty calldata should revert");
    }
}
