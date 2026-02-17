// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title CallValueGuardTest
 * @notice Tests that all compiled contracts reject calls with ETH value.
 * @dev Validates fix for issue #187: generated Yul must check callvalue()
 *      and revert for non-payable functions.
 */
contract CallValueGuardTest is YulTestBase {
    address counter;
    address ledger;
    address simpleStorage;
    address safeCounter;
    address owned;
    address ownedCounter;
    address simpleToken;

    address alice = address(0xA11CE);

    function setUp() public {
        counter = deployYul("Counter");
        ledger = deployYul("Ledger");
        simpleStorage = deployYul("SimpleStorage");
        safeCounter = deployYul("SafeCounter");
        owned = deployYulWithArgs("Owned", abi.encode(alice));
        ownedCounter = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        simpleToken = deployYulWithArgs("SimpleToken", abi.encode(alice));

        // Fund alice for sending ETH
        vm.deal(alice, 10 ether);
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Counter
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_Counter_Increment() public {
        // Without ETH: should succeed
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        assertTrue(success, "increment without value should succeed");

        // With ETH: should revert
        vm.prank(alice);
        (bool reverted,) = counter.call{value: 1 wei}(abi.encodeWithSignature("increment()"));
        assertFalse(reverted, "increment with value should revert");
    }

    function testCallValueGuard_Counter_Decrement() public {
        // First increment so decrement doesn't underflow
        (bool s,) = counter.call(abi.encodeWithSignature("increment()"));
        require(s, "setup increment failed");

        vm.prank(alice);
        (bool reverted,) = counter.call{value: 1 wei}(abi.encodeWithSignature("decrement()"));
        assertFalse(reverted, "decrement with value should revert");
    }

    function testCallValueGuard_Counter_GetCount() public {
        vm.prank(alice);
        (bool reverted,) = counter.call{value: 1 wei}(abi.encodeWithSignature("getCount()"));
        assertFalse(reverted, "getCount with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Ledger
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_Ledger_Deposit() public {
        vm.prank(alice);
        (bool reverted,) = ledger.call{value: 1 wei}(abi.encodeWithSignature("deposit(uint256)", 100));
        assertFalse(reverted, "deposit with value should revert");
    }

    function testCallValueGuard_Ledger_Withdraw() public {
        vm.prank(alice);
        (bool reverted,) = ledger.call{value: 1 wei}(abi.encodeWithSignature("withdraw(uint256)", 0));
        assertFalse(reverted, "withdraw with value should revert");
    }

    function testCallValueGuard_Ledger_Transfer() public {
        vm.prank(alice);
        (bool reverted,) = ledger.call{value: 1 wei}(
            abi.encodeWithSignature("transfer(address,uint256)", address(0xB0B), 0)
        );
        assertFalse(reverted, "transfer with value should revert");
    }

    function testCallValueGuard_Ledger_GetBalance() public {
        vm.prank(alice);
        (bool reverted,) = ledger.call{value: 1 wei}(
            abi.encodeWithSignature("getBalance(address)", alice)
        );
        assertFalse(reverted, "getBalance with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // SimpleStorage
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_SimpleStorage_Store() public {
        vm.prank(alice);
        (bool reverted,) = simpleStorage.call{value: 1 wei}(
            abi.encodeWithSignature("store(uint256)", 42)
        );
        assertFalse(reverted, "store with value should revert");
    }

    function testCallValueGuard_SimpleStorage_Retrieve() public {
        vm.prank(alice);
        (bool reverted,) = simpleStorage.call{value: 1 wei}(
            abi.encodeWithSignature("retrieve()")
        );
        assertFalse(reverted, "retrieve with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // SafeCounter
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_SafeCounter_Increment() public {
        vm.prank(alice);
        (bool reverted,) = safeCounter.call{value: 1 wei}(
            abi.encodeWithSignature("increment()")
        );
        assertFalse(reverted, "safeCounter increment with value should revert");
    }

    function testCallValueGuard_SafeCounter_Decrement() public {
        // First increment
        (bool s,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(s, "setup increment failed");

        vm.prank(alice);
        (bool reverted,) = safeCounter.call{value: 1 wei}(
            abi.encodeWithSignature("decrement()")
        );
        assertFalse(reverted, "safeCounter decrement with value should revert");
    }

    function testCallValueGuard_SafeCounter_GetCount() public {
        vm.prank(alice);
        (bool reverted,) = safeCounter.call{value: 1 wei}(
            abi.encodeWithSignature("getCount()")
        );
        assertFalse(reverted, "safeCounter getCount with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Owned
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_Owned_GetOwner() public {
        vm.prank(alice);
        (bool reverted,) = owned.call{value: 1 wei}(
            abi.encodeWithSignature("getOwner()")
        );
        assertFalse(reverted, "getOwner with value should revert");
    }

    function testCallValueGuard_Owned_TransferOwnership() public {
        vm.prank(alice);
        (bool reverted,) = owned.call{value: 1 wei}(
            abi.encodeWithSignature("transferOwnership(address)", address(0xB0B))
        );
        assertFalse(reverted, "transferOwnership with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // OwnedCounter
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_OwnedCounter_Increment() public {
        vm.prank(alice);
        (bool reverted,) = ownedCounter.call{value: 1 wei}(
            abi.encodeWithSignature("increment()")
        );
        assertFalse(reverted, "ownedCounter increment with value should revert");
    }

    function testCallValueGuard_OwnedCounter_GetCount() public {
        vm.prank(alice);
        (bool reverted,) = ownedCounter.call{value: 1 wei}(
            abi.encodeWithSignature("getCount()")
        );
        assertFalse(reverted, "ownedCounter getCount with value should revert");
    }

    function testCallValueGuard_OwnedCounter_GetOwner() public {
        vm.prank(alice);
        (bool reverted,) = ownedCounter.call{value: 1 wei}(
            abi.encodeWithSignature("getOwner()")
        );
        assertFalse(reverted, "ownedCounter getOwner with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // SimpleToken
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_SimpleToken_Mint() public {
        vm.prank(alice);
        (bool reverted,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("mint(address,uint256)", address(0xB0B), 100)
        );
        assertFalse(reverted, "mint with value should revert");
    }

    function testCallValueGuard_SimpleToken_Transfer() public {
        vm.prank(alice);
        (bool reverted,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("transfer(address,uint256)", address(0xB0B), 0)
        );
        assertFalse(reverted, "token transfer with value should revert");
    }

    function testCallValueGuard_SimpleToken_BalanceOf() public {
        vm.prank(alice);
        (bool reverted,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("balanceOf(address)", alice)
        );
        assertFalse(reverted, "balanceOf with value should revert");
    }

    function testCallValueGuard_SimpleToken_TotalSupply() public {
        vm.prank(alice);
        (bool reverted,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("totalSupply()")
        );
        assertFalse(reverted, "totalSupply with value should revert");
    }

    function testCallValueGuard_SimpleToken_Owner() public {
        vm.prank(alice);
        (bool reverted,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("owner()")
        );
        assertFalse(reverted, "token owner with value should revert");
    }
}
