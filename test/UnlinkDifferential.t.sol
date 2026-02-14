// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";
import "../examples/solidity/UnlinkPool.sol";

/**
 * @title UnlinkDifferential
 * @notice Differential testing + gas benchmarks for the Unlink privacy protocol.
 *
 * Compares two implementations that model the Lean EDSL semantics:
 *   1. Solidity reference (examples/solidity/UnlinkPool.sol)
 *   2. Hand-written Yul  (compiler/yul/UnlinkPool.yul)
 *
 * Both use the same simplified scaffolds as the proven Lean code:
 *   - hashNote = npk + token + amount
 *   - verifyProof = true
 *   - insertLeaves: root = oldRoot + count
 *
 * This proves the Yul translation faithfully reproduces the Solidity behavior,
 * and the gas comparison shows the overhead (or savings) of each layer.
 */
contract UnlinkDifferential is YulTestBase {
    UnlinkPool solImpl;
    address yulImpl;

    function setUp() public {
        solImpl = new UnlinkPool();
        yulImpl = deployYul("UnlinkPool");
    }

    // ---------------------------------------------------------------
    // Helpers
    // ---------------------------------------------------------------

    function _makeNote(uint256 npk, uint256 token, uint256 amount)
        internal pure returns (UnlinkPool.Note memory)
    {
        return UnlinkPool.Note(npk, token, amount);
    }

    function _makeNotes1(uint256 npk, uint256 token, uint256 amount)
        internal pure returns (UnlinkPool.Note[] memory)
    {
        UnlinkPool.Note[] memory notes = new UnlinkPool.Note[](1);
        notes[0] = _makeNote(npk, token, amount);
        return notes;
    }

    function _makeNotes3()
        internal pure returns (UnlinkPool.Note[] memory)
    {
        UnlinkPool.Note[] memory notes = new UnlinkPool.Note[](3);
        notes[0] = _makeNote(100, 200, 50);
        notes[1] = _makeNote(101, 201, 60);
        notes[2] = _makeNote(102, 202, 70);
        return notes;
    }

    function _makeTxn(
        uint256 merkleRoot_,
        uint256[] memory nullifiers,
        uint256[] memory commitments,
        UnlinkPool.Note memory withdrawal
    ) internal pure returns (UnlinkPool.Transaction memory) {
        return UnlinkPool.Transaction(merkleRoot_, nullifiers, commitments, withdrawal);
    }

    function _u256Array1(uint256 a) internal pure returns (uint256[] memory) {
        uint256[] memory arr = new uint256[](1);
        arr[0] = a;
        return arr;
    }

    function _u256Array2(uint256 a, uint256 b) internal pure returns (uint256[] memory) {
        uint256[] memory arr = new uint256[](2);
        arr[0] = a;
        arr[1] = b;
        return arr;
    }

    function _zeroNote() internal pure returns (UnlinkPool.Note memory) {
        return UnlinkPool.Note(0, 0, 0);
    }

    // ---------------------------------------------------------------
    // Differential: deposit
    // ---------------------------------------------------------------

    function testDiff_Deposit_Single() public {
        UnlinkPool.Note[] memory notes = _makeNotes1(10, 20, 30);

        // Solidity
        solImpl.deposit(notes);
        uint256 solRoot = solImpl.getMerkleRoot();
        uint256 solIndex = solImpl.getNextLeafIndex();

        // Yul
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok, "Yul deposit failed");
        (, bytes memory retRoot) = yulImpl.call(abi.encodeCall(UnlinkPool.getMerkleRoot, ()));
        (, bytes memory retIdx) = yulImpl.call(abi.encodeCall(UnlinkPool.getNextLeafIndex, ()));
        uint256 yulRoot = abi.decode(retRoot, (uint256));
        uint256 yulIndex = abi.decode(retIdx, (uint256));

        assertEq(solRoot, yulRoot, "Root mismatch after deposit");
        assertEq(solIndex, yulIndex, "LeafIndex mismatch after deposit");
    }

    function testDiff_Deposit_Multiple() public {
        UnlinkPool.Note[] memory notes = _makeNotes3();

        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok, "Yul deposit failed");

        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Root mismatch");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Index mismatch");
    }

    function testDiff_Deposit_Empty_Reverts() public {
        UnlinkPool.Note[] memory empty = new UnlinkPool.Note[](0);

        vm.expectRevert();
        solImpl.deposit(empty);

        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (empty)));
        assertFalse(ok, "Yul should revert on empty deposit");
    }

    function testDiff_Deposit_ZeroAmount_Reverts() public {
        UnlinkPool.Note[] memory notes = _makeNotes1(10, 20, 0);

        vm.expectRevert();
        solImpl.deposit(notes);

        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertFalse(ok, "Yul should revert on zero amount");
    }

    // ---------------------------------------------------------------
    // Differential: transact
    // ---------------------------------------------------------------

    function testDiff_Transact_Basic() public {
        // Setup: deposit first to create a valid root
        UnlinkPool.Note[] memory notes = _makeNotes1(10, 20, 30);
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);

        uint256 root = solImpl.getMerkleRoot();

        // Build transaction
        uint256[] memory nulls = _u256Array1(42);
        uint256[] memory comms = _u256Array1(99);
        UnlinkPool.Transaction memory txn = _makeTxn(root, nulls, comms, _zeroNote());

        // Solidity
        solImpl.transact(txn);

        // Yul
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertTrue(ok, "Yul transact failed");

        // Compare state
        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Root mismatch after transact");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Index mismatch after transact");
        assertTrue(solImpl.isNullifierSpent(42), "Sol nullifier not spent");
        assertTrue(_yulIsNullifierSpent(42), "Yul nullifier not spent");
    }

    function testDiff_Transact_WithdrawalCoherence() public {
        // Deposit
        UnlinkPool.Note[] memory notes = _makeNotes1(10, 20, 30);
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);

        uint256 root = solImpl.getMerkleRoot();

        // Withdrawal note: npk=5, token=6, amount=7 => hash = 18
        UnlinkPool.Note memory withdrawal = _makeNote(5, 6, 7);
        uint256 withdrawalHash = 5 + 6 + 7; // = 18

        uint256[] memory nulls = _u256Array1(50);
        uint256[] memory comms = _u256Array1(withdrawalHash); // last commitment = withdrawal hash

        UnlinkPool.Transaction memory txn = _makeTxn(root, nulls, comms, withdrawal);

        solImpl.transact(txn);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertTrue(ok, "Yul transact with withdrawal failed");

        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Root mismatch");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Index mismatch");
    }

    function testDiff_Transact_BadWithdrawal_Reverts() public {
        // Deposit
        UnlinkPool.Note[] memory notes = _makeNotes1(10, 20, 30);
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);

        uint256 root = solImpl.getMerkleRoot();

        // Withdrawal note hash = 18, but last commitment = 999 (mismatch)
        UnlinkPool.Note memory withdrawal = _makeNote(5, 6, 7);
        uint256[] memory nulls = _u256Array1(60);
        uint256[] memory comms = _u256Array1(999);

        UnlinkPool.Transaction memory txn = _makeTxn(root, nulls, comms, withdrawal);

        vm.expectRevert();
        solImpl.transact(txn);

        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertFalse(ok, "Yul should revert on bad withdrawal");
    }

    function testDiff_Transact_DoubleSpend_Reverts() public {
        // Deposit
        UnlinkPool.Note[] memory notes = _makeNotes1(10, 20, 30);
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);

        uint256 root = solImpl.getMerkleRoot();

        uint256[] memory nulls = _u256Array1(77);
        uint256[] memory comms = _u256Array1(88);
        UnlinkPool.Transaction memory txn = _makeTxn(root, nulls, comms, _zeroNote());

        // First transact: should succeed
        solImpl.transact(txn);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertTrue(ok);

        // Second transact with same nullifier: should revert
        // Need to use new root since root changed
        uint256 newRoot = solImpl.getMerkleRoot();
        txn = _makeTxn(newRoot, nulls, comms, _zeroNote());

        vm.expectRevert();
        solImpl.transact(txn);

        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertFalse(ok, "Yul should revert on double spend");
    }

    function testDiff_Transact_InvalidRoot_Reverts() public {
        uint256[] memory nulls = _u256Array1(1);
        uint256[] memory comms = _u256Array1(2);
        UnlinkPool.Transaction memory txn = _makeTxn(999, nulls, comms, _zeroNote());

        vm.expectRevert();
        solImpl.transact(txn);

        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertFalse(ok, "Yul should revert on invalid root");
    }

    function testDiff_Transact_MultiNullifier() public {
        // Deposit
        UnlinkPool.Note[] memory notes = _makeNotes3();
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);

        uint256 root = solImpl.getMerkleRoot();

        uint256[] memory nulls = _u256Array2(111, 222);
        uint256[] memory comms = _u256Array2(333, 444);
        UnlinkPool.Transaction memory txn = _makeTxn(root, nulls, comms, _zeroNote());

        solImpl.transact(txn);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertTrue(ok, "Yul multi-nullifier transact failed");

        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Root mismatch");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Index mismatch");
        assertTrue(solImpl.isNullifierSpent(111), "Sol null 111 not spent");
        assertTrue(solImpl.isNullifierSpent(222), "Sol null 222 not spent");
        assertTrue(_yulIsNullifierSpent(111), "Yul null 111 not spent");
        assertTrue(_yulIsNullifierSpent(222), "Yul null 222 not spent");
    }

    // ---------------------------------------------------------------
    // Differential: sequence of operations
    // ---------------------------------------------------------------

    function testDiff_FullSequence() public {
        // Deposit 1
        UnlinkPool.Note[] memory notes1 = _makeNotes1(10, 20, 30);
        solImpl.deposit(notes1);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes1)));
        assertTrue(ok);

        uint256 root1 = solImpl.getMerkleRoot();
        assertEq(root1, _yulGetRoot(), "Root mismatch after deposit 1");

        // Deposit 2
        UnlinkPool.Note[] memory notes2 = _makeNotes3();
        solImpl.deposit(notes2);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes2)));
        assertTrue(ok);

        uint256 root2 = solImpl.getMerkleRoot();
        assertEq(root2, _yulGetRoot(), "Root mismatch after deposit 2");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Index mismatch after deposits");

        // Transact using root1 (historical root should still be valid)
        uint256[] memory nulls = _u256Array1(500);
        uint256[] memory comms = _u256Array1(600);
        UnlinkPool.Transaction memory txn = _makeTxn(root1, nulls, comms, _zeroNote());

        solImpl.transact(txn);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertTrue(ok, "Historical root should work");

        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Root mismatch after transact");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Index mismatch after transact");

        // Transact using root2 (also historical, should work)
        uint256[] memory nulls2 = _u256Array1(700);
        uint256[] memory comms2 = _u256Array1(800);
        txn = _makeTxn(root2, nulls2, comms2, _zeroNote());

        solImpl.transact(txn);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertTrue(ok, "Second historical root should work");

        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Final root mismatch");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Final index mismatch");
    }

    // ---------------------------------------------------------------
    // Gas Benchmarks
    // ---------------------------------------------------------------

    function testGas_Deposit_Single() public {
        UnlinkPool.Note[] memory notes = _makeNotes1(10, 20, 30);

        uint256 gasSol = gasleft();
        solImpl.deposit(notes);
        gasSol = gasSol - gasleft();

        uint256 gasYul = gasleft();
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        gasYul = gasYul - gasleft();
        assertTrue(ok);

        emit log_named_uint("Gas Solidity deposit(1 note)", gasSol);
        emit log_named_uint("Gas Yul      deposit(1 note)", gasYul);
        emit log_named_uint("Gas savings (Yul vs Sol)", gasSol > gasYul ? gasSol - gasYul : 0);
    }

    function testGas_Deposit_Three() public {
        UnlinkPool.Note[] memory notes = _makeNotes3();

        uint256 gasSol = gasleft();
        solImpl.deposit(notes);
        gasSol = gasSol - gasleft();

        uint256 gasYul = gasleft();
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        gasYul = gasYul - gasleft();
        assertTrue(ok);

        emit log_named_uint("Gas Solidity deposit(3 notes)", gasSol);
        emit log_named_uint("Gas Yul      deposit(3 notes)", gasYul);
        emit log_named_uint("Gas savings (Yul vs Sol)", gasSol > gasYul ? gasSol - gasYul : 0);
    }

    function testGas_Transact_SingleNullifier() public {
        // Setup
        UnlinkPool.Note[] memory notes = _makeNotes1(10, 20, 30);
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);
        uint256 root = solImpl.getMerkleRoot();

        uint256[] memory nulls = _u256Array1(42);
        uint256[] memory comms = _u256Array1(99);
        UnlinkPool.Transaction memory txn = _makeTxn(root, nulls, comms, _zeroNote());

        // Use separate copies for each call since state changes
        uint256 gasSol = gasleft();
        solImpl.transact(txn);
        gasSol = gasSol - gasleft();

        uint256 gasYul = gasleft();
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        gasYul = gasYul - gasleft();
        assertTrue(ok);

        emit log_named_uint("Gas Solidity transact(1 null, 1 comm)", gasSol);
        emit log_named_uint("Gas Yul      transact(1 null, 1 comm)", gasYul);
        emit log_named_uint("Gas savings (Yul vs Sol)", gasSol > gasYul ? gasSol - gasYul : 0);
    }

    function testGas_Transact_TwoNullifiers() public {
        // Setup
        UnlinkPool.Note[] memory notes = _makeNotes3();
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);
        uint256 root = solImpl.getMerkleRoot();

        uint256[] memory nulls = _u256Array2(111, 222);
        uint256[] memory comms = _u256Array2(333, 444);
        UnlinkPool.Transaction memory txn = _makeTxn(root, nulls, comms, _zeroNote());

        uint256 gasSol = gasleft();
        solImpl.transact(txn);
        gasSol = gasSol - gasleft();

        uint256 gasYul = gasleft();
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        gasYul = gasYul - gasleft();
        assertTrue(ok);

        emit log_named_uint("Gas Solidity transact(2 null, 2 comm)", gasSol);
        emit log_named_uint("Gas Yul      transact(2 null, 2 comm)", gasYul);
        emit log_named_uint("Gas savings (Yul vs Sol)", gasSol > gasYul ? gasSol - gasYul : 0);
    }

    // ---------------------------------------------------------------
    // Fuzz: deposit with random notes
    // ---------------------------------------------------------------

    function testFuzz_Deposit(uint256 npk, uint256 token, uint256 amount) public {
        vm.assume(amount > 0);

        UnlinkPool.Note[] memory notes = _makeNotes1(npk, token, amount);

        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok, "Yul deposit failed");

        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Root mismatch");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Index mismatch");
    }

    function testFuzz_DepositThenTransact(
        uint256 npk, uint256 token, uint256 amount,
        uint256 nullifier, uint256 commitment
    ) public {
        vm.assume(amount > 0);

        // Deposit
        UnlinkPool.Note[] memory notes = _makeNotes1(npk, token, amount);
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);

        uint256 root = solImpl.getMerkleRoot();

        // Transact
        uint256[] memory nulls = _u256Array1(nullifier);
        uint256[] memory comms = _u256Array1(commitment);
        UnlinkPool.Transaction memory txn = _makeTxn(root, nulls, comms, _zeroNote());

        solImpl.transact(txn);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertTrue(ok, "Yul transact failed");

        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Root mismatch");
        assertEq(solImpl.getNextLeafIndex(), _yulGetIndex(), "Index mismatch");
        assertEq(solImpl.isNullifierSpent(nullifier), _yulIsNullifierSpent(nullifier), "Nullifier mismatch");
    }

    function testFuzz_DoubleSpendReverts(
        uint256 npk, uint256 token, uint256 amount,
        uint256 nullifier, uint256 comm1, uint256 comm2
    ) public {
        vm.assume(amount > 0);

        // Deposit
        UnlinkPool.Note[] memory notes = _makeNotes1(npk, token, amount);
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);

        // First transact
        uint256 root = solImpl.getMerkleRoot();
        UnlinkPool.Transaction memory txn1 = _makeTxn(
            root, _u256Array1(nullifier), _u256Array1(comm1), _zeroNote()
        );
        solImpl.transact(txn1);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn1)));
        assertTrue(ok);

        // Second transact with same nullifier should revert on both
        uint256 newRoot = solImpl.getMerkleRoot();
        UnlinkPool.Transaction memory txn2 = _makeTxn(
            newRoot, _u256Array1(nullifier), _u256Array1(comm2), _zeroNote()
        );

        vm.expectRevert();
        solImpl.transact(txn2);

        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn2)));
        assertFalse(ok, "Yul should revert on double spend");
    }

    function testFuzz_WithdrawalCoherence(
        uint256 wNpk, uint256 wToken, uint256 wAmount,
        uint256 nullifier
    ) public {
        vm.assume(wAmount > 0);

        // Deposit to create a root
        UnlinkPool.Note[] memory notes = _makeNotes1(1, 2, 3);
        solImpl.deposit(notes);
        (bool ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.deposit, (notes)));
        assertTrue(ok);

        uint256 root = solImpl.getMerkleRoot();
        uint256 wHash = wNpk + wToken + wAmount;

        // Valid withdrawal: last commitment = hash of withdrawal note
        UnlinkPool.Note memory withdrawal = _makeNote(wNpk, wToken, wAmount);
        UnlinkPool.Transaction memory txn = _makeTxn(
            root, _u256Array1(nullifier), _u256Array1(wHash), withdrawal
        );

        solImpl.transact(txn);
        (ok,) = yulImpl.call(abi.encodeCall(UnlinkPool.transact, (txn)));
        assertTrue(ok, "Valid withdrawal should succeed");

        assertEq(solImpl.getMerkleRoot(), _yulGetRoot(), "Root mismatch");
    }

    // ---------------------------------------------------------------
    // Yul view helpers
    // ---------------------------------------------------------------

    function _yulGetRoot() internal returns (uint256) {
        (, bytes memory ret) = yulImpl.call(abi.encodeCall(UnlinkPool.getMerkleRoot, ()));
        return abi.decode(ret, (uint256));
    }

    function _yulGetIndex() internal returns (uint256) {
        (, bytes memory ret) = yulImpl.call(abi.encodeCall(UnlinkPool.getNextLeafIndex, ()));
        return abi.decode(ret, (uint256));
    }

    function _yulIsNullifierSpent(uint256 n) internal returns (bool) {
        (, bytes memory ret) = yulImpl.call(abi.encodeCall(UnlinkPool.isNullifierSpent, (n)));
        return abi.decode(ret, (bool));
    }

    function _yulIsRootSeen(uint256 r) internal returns (bool) {
        (, bytes memory ret) = yulImpl.call(abi.encodeCall(UnlinkPool.isRootSeen, (r)));
        return abi.decode(ret, (bool));
    }
}
