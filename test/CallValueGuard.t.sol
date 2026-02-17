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
        (bool sent,) = counter.call{value: 1 wei}(abi.encodeWithSignature("increment()"));
        assertFalse(sent, "increment with value should revert");
    }

    function testCallValueGuard_Counter_Decrement() public {
        // First increment so decrement doesn't underflow
        (bool s,) = counter.call(abi.encodeWithSignature("increment()"));
        require(s, "setup increment failed");

        vm.prank(alice);
        (bool sent,) = counter.call{value: 1 wei}(abi.encodeWithSignature("decrement()"));
        assertFalse(sent, "decrement with value should revert");
    }

    function testCallValueGuard_Counter_GetCount() public {
        vm.prank(alice);
        (bool sent,) = counter.call{value: 1 wei}(abi.encodeWithSignature("getCount()"));
        assertFalse(sent, "getCount with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Ledger
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_Ledger_Deposit() public {
        vm.prank(alice);
        (bool sent,) = ledger.call{value: 1 wei}(abi.encodeWithSignature("deposit(uint256)", 100));
        assertFalse(sent, "deposit with value should revert");
    }

    function testCallValueGuard_Ledger_Withdraw() public {
        vm.prank(alice);
        (bool sent,) = ledger.call{value: 1 wei}(abi.encodeWithSignature("withdraw(uint256)", 0));
        assertFalse(sent, "withdraw with value should revert");
    }

    function testCallValueGuard_Ledger_Transfer() public {
        vm.prank(alice);
        (bool sent,) = ledger.call{value: 1 wei}(
            abi.encodeWithSignature("transfer(address,uint256)", address(0xB0B), 0)
        );
        assertFalse(sent, "transfer with value should revert");
    }

    function testCallValueGuard_Ledger_GetBalance() public {
        vm.prank(alice);
        (bool sent,) = ledger.call{value: 1 wei}(
            abi.encodeWithSignature("getBalance(address)", alice)
        );
        assertFalse(sent, "getBalance with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // SimpleStorage
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_SimpleStorage_Store() public {
        vm.prank(alice);
        (bool sent,) = simpleStorage.call{value: 1 wei}(
            abi.encodeWithSignature("store(uint256)", 42)
        );
        assertFalse(sent, "store with value should revert");
    }

    function testCallValueGuard_SimpleStorage_Retrieve() public {
        vm.prank(alice);
        (bool sent,) = simpleStorage.call{value: 1 wei}(
            abi.encodeWithSignature("retrieve()")
        );
        assertFalse(sent, "retrieve with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // SafeCounter
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_SafeCounter_Increment() public {
        vm.prank(alice);
        (bool sent,) = safeCounter.call{value: 1 wei}(
            abi.encodeWithSignature("increment()")
        );
        assertFalse(sent, "safeCounter increment with value should revert");
    }

    function testCallValueGuard_SafeCounter_Decrement() public {
        // First increment
        (bool s,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(s, "setup increment failed");

        vm.prank(alice);
        (bool sent,) = safeCounter.call{value: 1 wei}(
            abi.encodeWithSignature("decrement()")
        );
        assertFalse(sent, "safeCounter decrement with value should revert");
    }

    function testCallValueGuard_SafeCounter_GetCount() public {
        vm.prank(alice);
        (bool sent,) = safeCounter.call{value: 1 wei}(
            abi.encodeWithSignature("getCount()")
        );
        assertFalse(sent, "safeCounter getCount with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Owned
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_Owned_GetOwner() public {
        vm.prank(alice);
        (bool sent,) = owned.call{value: 1 wei}(
            abi.encodeWithSignature("getOwner()")
        );
        assertFalse(sent, "getOwner with value should revert");
    }

    function testCallValueGuard_Owned_TransferOwnership() public {
        vm.prank(alice);
        (bool sent,) = owned.call{value: 1 wei}(
            abi.encodeWithSignature("transferOwnership(address)", address(0xB0B))
        );
        assertFalse(sent, "transferOwnership with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // OwnedCounter
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_OwnedCounter_Increment() public {
        vm.prank(alice);
        (bool sent,) = ownedCounter.call{value: 1 wei}(
            abi.encodeWithSignature("increment()")
        );
        assertFalse(sent, "ownedCounter increment with value should revert");
    }

    function testCallValueGuard_OwnedCounter_GetCount() public {
        vm.prank(alice);
        (bool sent,) = ownedCounter.call{value: 1 wei}(
            abi.encodeWithSignature("getCount()")
        );
        assertFalse(sent, "ownedCounter getCount with value should revert");
    }

    function testCallValueGuard_OwnedCounter_GetOwner() public {
        vm.prank(alice);
        (bool sent,) = ownedCounter.call{value: 1 wei}(
            abi.encodeWithSignature("getOwner()")
        );
        assertFalse(sent, "ownedCounter getOwner with value should revert");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // SimpleToken
    //═══════════════════════════════════════════════════════════════════════════

    function testCallValueGuard_SimpleToken_Mint() public {
        vm.prank(alice);
        (bool sent,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("mint(address,uint256)", address(0xB0B), 100)
        );
        assertFalse(sent, "mint with value should revert");
    }

    function testCallValueGuard_SimpleToken_Transfer() public {
        vm.prank(alice);
        (bool sent,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("transfer(address,uint256)", address(0xB0B), 0)
        );
        assertFalse(sent, "token transfer with value should revert");
    }

    function testCallValueGuard_SimpleToken_BalanceOf() public {
        vm.prank(alice);
        (bool sent,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("balanceOf(address)", alice)
        );
        assertFalse(sent, "balanceOf with value should revert");
    }

    function testCallValueGuard_SimpleToken_TotalSupply() public {
        vm.prank(alice);
        (bool sent,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("totalSupply()")
        );
        assertFalse(sent, "totalSupply with value should revert");
    }

    function testCallValueGuard_SimpleToken_Owner() public {
        vm.prank(alice);
        (bool sent,) = simpleToken.call{value: 1 wei}(
            abi.encodeWithSignature("owner()")
        );
        assertFalse(sent, "token owner with value should revert");
    }
}
