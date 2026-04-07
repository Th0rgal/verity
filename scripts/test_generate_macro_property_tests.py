#!/usr/bin/env python3

from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import generate_macro_property_tests as gen


class ParseContractsTests(unittest.TestCase):
    def test_parse_two_contracts(self) -> None:
        src = textwrap.dedent(
            """
            verity_contract Counter where
              storage
                count : Uint256 := slot 0

              function increment () : Unit := do
                pure ()

              function getCount () : Uint256 := do
                return 0

            verity_contract Owned where
              storage
                owner : Address := slot 0

              function getOwner () : Address := do
                return 0
            """
        )
        parsed = gen.parse_contracts(src, Path("dummy.lean"))
        self.assertEqual(sorted(parsed.keys()), ["Counter", "Owned"])
        self.assertEqual([f.name for f in parsed["Counter"].functions], ["increment", "getCount"])
        self.assertEqual(parsed["Counter"].functions[1].return_type, "Uint256")
        self.assertEqual(parsed["Counter"].storage_slots, {"count": 0})

    def test_parse_params(self) -> None:
        out = gen._split_params("to : Address, amount : Uint256")
        self.assertEqual([(p.name, p.lean_type) for p in out], [("to", "Address"), ("amount", "Uint256")])

    def test_parse_constructor(self) -> None:
        src = textwrap.dedent(
            """
            verity_contract Owned where
              constructor (initialOwner : Address) := do
                pure ()

              function owner () : Address := do
                return 0
            """
        )
        parsed = gen.parse_contracts(src, Path("dummy.lean"))
        owned = parsed["Owned"]
        self.assertIsNotNone(owned.constructor)
        assert owned.constructor is not None
        self.assertEqual(
            [(p.name, p.lean_type) for p in owned.constructor.params],
            [("initialOwner", "Address")],
        )

    def test_parse_function_body_and_storage_slots(self) -> None:
        src = textwrap.dedent(
            """
            verity_contract SimpleStorage where
              storage
                storedData : Uint256 := slot 0

              function retrieve () : Uint256 := do
                let current ← getStorage storedData
                return current
            """
        )
        parsed = gen.parse_contracts(src, Path("dummy.lean"))
        contract = parsed["SimpleStorage"]
        self.assertEqual(contract.storage_slots, {"storedData": 0})
        self.assertEqual(contract.storage_types, {"storedData": "Uint256"})
        self.assertEqual(
            contract.functions[0].body,
            ("let current ← getStorage storedData", "return current"),
        )

    def test_parse_constants_and_immutables(self) -> None:
        src = textwrap.dedent(
            """
            verity_contract Constantish where
              storage

              constants
                treasury : Address := (wordToAddress 42)

              immutables
                paused : Bool := true

              function treasuryAddr () : Address := do
                return treasury
            """
        )
        parsed = gen.parse_contracts(src, Path("dummy.lean"))
        contract = parsed["Constantish"]
        self.assertIn("treasury", contract.constants)
        self.assertIn("paused", contract.immutables)
        self.assertEqual(
            gen._binding_type_and_expr(contract.constants["treasury"]),
            ("Address", "(wordToAddress 42)"),
        )
        self.assertEqual(
            gen._binding_type_and_expr(contract.immutables["paused"]),
            ("Bool", "true"),
        )

    def test_parse_contracts_ignores_guard_msgs_negative_fixtures(self) -> None:
        src = textwrap.dedent(
            """
            verity_contract HappyPath where
              storage
                counter : Uint256 := slot 0

              function read () : Uint256 := do
                return 0

            #guard_msgs in
            verity_contract NegativeFixture where
              storage
                counter : Uint256 := slot 0

              function read () : Uint256 := do
                return 0
            end NegativeFixture
            """
        )
        parsed = gen.parse_contracts(src, Path("dummy.lean"))
        self.assertEqual(sorted(parsed.keys()), ["HappyPath"])

    def test_parse_contracts_stops_function_body_at_top_level_defs(self) -> None:
        src = textwrap.dedent(
            """
            verity_contract StringSmoke where
              storage
                sentinel : Uint256 := slot 0

              function echoSecondString (_prefix : String, message : String) : String := do
                returnBytes message

            def helper : Bool :=
              true
            """
        )
        parsed = gen.parse_contracts(src, Path("dummy.lean"))
        self.assertEqual(parsed["StringSmoke"].functions[0].body, ("returnBytes message",))


class RenderTests(unittest.TestCase):
    def test_render_unit_and_non_unit_tests(self) -> None:
        contract = gen.ContractDecl(
            name="Sample",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl("touch", (), "Unit"),
                gen.FunctionDecl("read", (gen.ParamDecl("who", "Address"),), "Uint256"),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_Touch_NoUnexpectedRevert()", rendered)
        self.assertIn("function testTODO_Read_DecodeAndAssert()", rendered)
        self.assertIn('abi.encodeWithSignature("read(address)", alice)', rendered)
        self.assertIn(
            'assertEq(ret.length, 32, "read ABI return length mismatch (expected 32 bytes)");',
            rendered,
        )

    def test_render_array_param_adds_helper(self) -> None:
        contract = gen.ContractDecl(
            name="ArrayConsumer",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "consume",
                    (gen.ParamDecl("values", "Array Uint256"),),
                    "Unit",
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("_singletonUintArray", rendered)
        self.assertIn('abi.encodeWithSignature("consume(uint256[])", _singletonUintArray(1))', rendered)

    def test_render_bytes32_array_param_adds_helper(self) -> None:
        contract = gen.ContractDecl(
            name="ArrayConsumer",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "consume",
                    (gen.ParamDecl("values", "Array Bytes32"),),
                    "Unit",
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("_singletonBytes32Array", rendered)
        self.assertIn(
            'abi.encodeWithSignature("consume(bytes32[])", _singletonBytes32Array(bytes32(uint256(0xBEEF))))',
            rendered,
        )

    def test_render_string_param_uses_solidity_string_signature(self) -> None:
        contract = gen.ContractDecl(
            name="StringConsumer",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl("mystery", (gen.ParamDecl("x", "String"),), "Unit"),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn('abi.encodeWithSignature("mystery(string)", "verity")', rendered)

    def test_render_address_array_param_adds_helper(self) -> None:
        contract = gen.ContractDecl(
            name="ArrayAddressConsumer",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl("consume", (gen.ParamDecl("values", "Array Address"),), "Unit"),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("_singletonAddressArray", rendered)
        self.assertIn('abi.encodeWithSignature("consume(address[])", _singletonAddressArray(alice))', rendered)

    def test_render_bool_array_param_adds_helper(self) -> None:
        contract = gen.ContractDecl(
            name="ArrayBoolConsumer",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl("consume", (gen.ParamDecl("values", "Array Bool"),), "Unit"),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("_singletonBoolArray", rendered)
        self.assertIn('abi.encodeWithSignature("consume(bool[])", _singletonBoolArray(true))', rendered)

    def test_render_dynamic_element_array_still_fails_closed(self) -> None:
        contract = gen.ContractDecl(
            name="ArrayBytesConsumer",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl("consume", (gen.ParamDecl("values", "Array Bytes"),), "Unit"),
            ),
            storage_slots={},
        )
        with self.assertRaisesRegex(ValueError, "unsupported Lean array element type"):
            gen.render_contract_test(contract)

    def test_render_dynamic_return_shape_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ReturnsBytes",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(gen.FunctionDecl("blob", (), "Bytes"),),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn(
            'require(ret.length >= 64, "blob ABI return payload unexpectedly short");',
            rendered,
        )

    def test_render_string_return_shape_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ReturnsString",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(gen.FunctionDecl("echo", (), "String"),),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn(
            'require(ret.length >= 64, "echo ABI return payload unexpectedly short");',
            rendered,
        )

    def test_render_bool_return_shape_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ReturnsBool",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(gen.FunctionDecl("isReady", (), "Bool"),),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn(
            'assertEq(ret.length, 32, "isReady ABI return length mismatch (expected 32 bytes)");',
            rendered,
        )

    def test_render_unknown_return_type_fails_closed(self) -> None:
        contract = gen.ContractDecl(
            name="UnknownReturn",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(gen.FunctionDecl("mystery", (), "Widget"),),
            storage_slots={},
        )
        with self.assertRaisesRegex(ValueError, "unsupported Lean type"):
            gen.render_contract_test(contract)

    def test_render_constructor_uses_deploy_with_args(self) -> None:
        contract = gen.ContractDecl(
            name="Owned",
            constructor=gen.ConstructorDecl(params=(gen.ParamDecl("initialOwner", "Address"),)),
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(gen.FunctionDecl("owner", (), "Address"),),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn('target = deployYulWithArgs("Owned", abi.encode(alice));', rendered)


    def test_render_tuple_param_sol_signature(self) -> None:
        contract = gen.ContractDecl(
            name="TupleConsumer",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "submit",
                    (gen.ParamDecl("cfg", "Tuple [Address, Address, Uint256]"),),
                    "Unit",
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn('"submit((address,address,uint256))"', rendered)
        self.assertIn(
            "abi.decode(abi.encode(alice, alice, uint256(1)), (address, address, uint256))",
            rendered,
        )

    def test_example_value_tuple_uses_tuple_typed_expression(self) -> None:
        self.assertEqual(
            gen._example_value("Tuple [Uint8, Bytes32, Bytes32]"),
            "abi.decode(abi.encode(uint8(27), bytes32(uint256(0xBEEF)), bytes32(uint256(0xBEEF))), (uint8, bytes32, bytes32))",
        )

    def test_render_tuple_return_shape_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="TupleReturn",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "getPair",
                    (),
                    "Tuple [Uint256, Uint256]",
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn(
            'require(ret.length >= 64, "getPair ABI tuple return payload unexpectedly short");',
            rendered,
        )

    def test_render_storage_getter_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="SimpleStorage",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "retrieve",
                    (),
                    "Uint256",
                    body=("let current ← getStorage storedData", "return current"),
                ),
            ),
            storage_slots={"storedData": 0},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_Retrieve_ReadsConfiguredStorage()", rendered)
        self.assertIn("vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));", rendered)
        self.assertIn('assertEq(actual, expected, "retrieve should return storage slot 0");', rendered)

    def test_render_storage_array_length_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StorageArraySmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "size",
                    (),
                    "Uint256",
                    body=("let size ← getStorageArrayLength queue", "return size"),
                ),
            ),
            storage_slots={"queue": 0},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_Size_ReadsConfiguredStorageArrayLength()", rendered)
        self.assertIn("vm.store(target, bytes32(uint256(0)), bytes32(expected));", rendered)
        self.assertIn('assertEq(actual, expected, "size should return the configured array length");', rendered)

    def test_render_storage_array_element_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StorageAddressArraySmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "firstOwner",
                    (),
                    "Address",
                    body=("let owner ← getStorageArrayElement owners 0", "return owner"),
                ),
            ),
            storage_slots={"owners": 3},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_FirstOwner_ReadsConfiguredStorageArrayElement()", rendered)
        self.assertIn("vm.store(target, bytes32(uint256(3)), bytes32(uint256(1)));", rendered)
        self.assertIn(
            "vm.store(target, bytes32(uint256(keccak256(abi.encode(uint256(3)))) + 0), bytes32(uint256(uint160(expected))));",
            rendered,
        )
        self.assertIn(
            'assertEq(actual, expected, "firstOwner should return the configured array element");',
            rendered,
        )

    def test_render_constant_return_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="Uint8Smoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(gen.FunctionDecl("sigV", (), "Uint8", body=("return 27",)),),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_SigV_ReturnsDeclaredConstant()", rendered)
        self.assertIn("uint8 actual = abi.decode(ret, (uint8));", rendered)
        self.assertIn('assertEq(actual, 27, "sigV should return the declared constant");', rendered)

    def test_render_direct_param_return_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StatelessSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "echoWord",
                    (gen.ParamDecl("value", "Uint256"),),
                    "Uint256",
                    body=("return value",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_EchoWord_ReturnsDirectParam()", rendered)
        self.assertIn("uint256 actual = abi.decode(ret, (uint256));", rendered)
        self.assertIn('assertEq(actual, uint256(1), "echoWord should preserve the expected value");', rendered)

    def test_render_direct_constant_address_return_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ConstantSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "treasuryAddr",
                    (),
                    "Address",
                    body=("return treasury",),
                ),
            ),
            storage_slots={},
            constants={"treasury": gen.ValueDecl("treasury", "Address", "(wordToAddress 42)")},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_TreasuryAddr_ReturnsDeclaredBinding()", rendered)
        self.assertIn("address actual = abi.decode(ret, (address));", rendered)
        self.assertIn(
            'assertEq(actual, address(uint160(42)), "treasuryAddr should preserve the expected value");',
            rendered,
        )

    def test_render_direct_constructor_derived_immutable_return_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ImmutableSmoke",
            constructor=gen.ConstructorDecl(params=(gen.ParamDecl("seed", "Uint256"),)),
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "supplyCap",
                    (),
                    "Uint256",
                    body=("return seededSupply",),
                ),
            ),
            storage_slots={},
            immutables={"seededSupply": gen.ValueDecl("seededSupply", "Uint256", "(add seed 2)")},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_SupplyCap_ReturnsDeclaredBinding()", rendered)
        self.assertIn("uint256 actual = abi.decode(ret, (uint256));", rendered)
        self.assertIn(
            'assertEq(actual, 3, "supplyCap should preserve the expected value");',
            rendered,
        )

    def test_render_return_bytes_direct_param_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StringSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "echoString",
                    (gen.ParamDecl("message", "String"),),
                    "String",
                    body=("returnBytes message",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_EchoString_ReturnsDirectDynamicParam()", rendered)
        self.assertIn("string actual = abi.decode(ret, (string));", rendered)
        self.assertIn('assertEq(actual, "verity", "echoString should preserve the expected value");', rendered)

    def test_render_return_storage_words_bytes32_param_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StorageWordsSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "extSloadsLike",
                    (gen.ParamDecl("slots", "Array Bytes32"),),
                    "Array Uint256",
                    body=("returnStorageWords slots",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_ExtSloadsLike_ReturnsCanonicalStorageWords()", rendered)
        self.assertIn("uint256[] memory actual = abi.decode(ret, (uint256[]));", rendered)
        self.assertIn(
            'assertEq(actual[0], uint256(bytes32(uint256(0xBEEF))), "extSloadsLike should return the canonical word for the configured input");',
            rendered,
        )

    def test_render_return_storage_words_address_param_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StorageWordsAddressSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "extSloadsLike",
                    (gen.ParamDecl("slots", "Array Address"),),
                    "Array Uint256",
                    body=("returnStorageWords slots",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_ExtSloadsLike_ReturnsCanonicalStorageWords()", rendered)
        self.assertIn(
            'assertEq(actual[0], uint256(uint160(alice)), "extSloadsLike should return the canonical word for the configured input");',
            rendered,
        )

    def test_render_return_storage_words_bool_param_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StorageWordsBoolSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "extSloadsLike",
                    (gen.ParamDecl("slots", "Array Bool"),),
                    "Array Uint256",
                    body=("returnStorageWords slots",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_ExtSloadsLike_ReturnsCanonicalStorageWords()", rendered)
        self.assertIn(
            'assertEq(actual[0], (true ? 1 : 0), "extSloadsLike should return the canonical word for the configured input");',
            rendered,
        )

    def test_render_msg_sender_return_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StatelessSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "whoAmI",
                    (),
                    "Address",
                    body=("let sender ← msgSender", "return sender"),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_WhoAmI_ReturnsMsgSender()", rendered)
        self.assertIn("address actual = abi.decode(ret, (address));", rendered)
        self.assertIn('assertEq(actual, alice, "whoAmI should preserve the expected value");', rendered)

    def test_render_typed_immutable_returns_infer_assertions(self) -> None:
        contract = gen.ContractDecl(
            name="TypedImmutableSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl("isPaused", (), "Bool", body=("return paused",)),
                gen.FunctionDecl("feeScale", (), "Uint8", body=("return feeBps",)),
                gen.FunctionDecl("domainSeparator", (), "Bytes32", body=("return domainTag",)),
            ),
            storage_slots={},
            immutables={
                "paused": gen.ValueDecl("paused", "Bool", "true"),
                "feeBps": gen.ValueDecl("feeBps", "Uint8", "7"),
                "domainTag": gen.ValueDecl("domainTag", "Bytes32", "42"),
            },
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_IsPaused_ReturnsDeclaredBinding()", rendered)
        self.assertIn('assertEq(actual, true, "isPaused should preserve the expected value");', rendered)
        self.assertIn("function testAuto_FeeScale_ReturnsDeclaredBinding()", rendered)
        self.assertIn('assertEq(actual, 7, "feeScale should preserve the expected value");', rendered)
        self.assertIn("function testAuto_DomainSeparator_ReturnsDeclaredBinding()", rendered)
        self.assertIn(
            'assertEq(actual, bytes32(uint256(42)), "domainSeparator should preserve the expected value");',
            rendered,
        )

    def test_render_tuple_return_values_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="TupleSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "getPair",
                    (gen.ParamDecl("key", "Uint256"),),
                    "Tuple [Uint256, Uint256]",
                    body=("returnValues [key, key]",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_GetPair_DecodesTupleResult()", rendered)
        self.assertIn("(uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));", rendered)
        self.assertIn('assertEq(actual0, uint256(1), "getPair tuple element 0 mismatch");', rendered)
        self.assertIn('assertEq(actual1, uint256(1), "getPair tuple element 1 mismatch");', rendered)

    def test_render_tuple_return_literal_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="TupleSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "getPair",
                    (gen.ParamDecl("key", "Uint256"),),
                    "Tuple [Uint256, Uint256]",
                    body=("return (key, key)",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_GetPair_ReturnsInferredTupleResult()", rendered)
        self.assertIn(
            '(uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));',
            rendered,
        )
        self.assertIn(
            'assertEq(actual0, uint256(1), "getPair tuple element 0 should preserve the inferred result");',
            rendered,
        )
        self.assertIn(
            'assertEq(actual1, uint256(1), "getPair tuple element 1 should preserve the inferred result");',
            rendered,
        )

    def test_render_nested_constant_arithmetic_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ConstantSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "feeOn",
                    (gen.ParamDecl("amount", "Uint256"),),
                    "Uint256",
                    body=("let fee := div (mul amount mintFeeBps) basisPoints", "return fee"),
                ),
            ),
            storage_slots={},
            constants={
                "basisPoints": gen.ValueDecl("basisPoints", "Uint256", "10000"),
                "mintFeeBps": gen.ValueDecl("mintFeeBps", "Uint256", "30"),
            },
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_FeeOn_ReturnsInferredStraightLineResult()", rendered)
        self.assertIn("uint256 actual = abi.decode(ret, (uint256));", rendered)
        self.assertIn(
            'assertEq(actual, 0, "feeOn should preserve the inferred result");',
            rendered,
        )

    def test_render_storage_read_arithmetic_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="DirectHelperCallSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "readTotalPlus",
                    (gen.ParamDecl("extra", "Uint256"),),
                    "Uint256",
                    body=("let current ← getStorage total", "return (add current extra)"),
                ),
            ),
            storage_slots={"total": 0},
            storage_types={"total": "Uint256"},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_ReadTotalPlus_ReturnsInferredStraightLineResult()", rendered)
        self.assertIn("uint256 expected = uint256(1);", rendered)
        self.assertIn("vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));", rendered)
        self.assertIn(
            'assertEq(actual, (expected + uint256(1)), "readTotalPlus should preserve the inferred result");',
            rendered,
        )

    def test_render_storage_read_tuple_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="DirectHelperCallSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "snapshot",
                    (),
                    "Tuple [Uint256, Uint256, Uint256]",
                    body=(
                        "let current ← getStorage total",
                        "let left ← getStorage lastLeft",
                        "let right ← getStorage lastRight",
                        "return (current, left, right)",
                    ),
                ),
            ),
            storage_slots={"total": 0, "lastLeft": 1, "lastRight": 2},
            storage_types={"total": "Uint256", "lastLeft": "Uint256", "lastRight": "Uint256"},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_Snapshot_ReturnsInferredTupleResult()", rendered)
        self.assertIn("uint256 expected = uint256(1);", rendered)
        self.assertIn("uint256 expected1 = uint256(1);", rendered)
        self.assertIn("uint256 expected2 = uint256(1);", rendered)
        self.assertIn(
            'assertEq(actual2, expected2, "snapshot tuple element 2 should preserve the inferred result");',
            rendered,
        )

    def test_render_mutating_accumulator_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="Counter",
            constructor=None,
            source=gen.ROOT / "Contracts/Counter/Counter.lean",
            functions=(
                gen.FunctionDecl(
                    "previewAddTwice",
                    (gen.ParamDecl("delta", "Uint256"),),
                    "Uint256",
                    body=(
                        "let base ← getStorage count",
                        "let mut acc := base",
                        "acc := add acc delta",
                        "acc := add acc delta",
                        "return acc",
                    ),
                ),
            ),
            storage_slots={"count": 0},
            storage_types={"count": "Uint256"},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_PreviewAddTwice_ReturnsInferredStraightLineResult()", rendered)
        self.assertIn(
            'assertEq(actual, ((expected + uint256(1)) + uint256(1)), "previewAddTwice should preserve the inferred result");',
            rendered,
        )

    def test_render_preview_ops_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="Counter",
            constructor=None,
            source=gen.ROOT / "Contracts/Counter/Counter.lean",
            functions=(
                gen.FunctionDecl(
                    "previewOps",
                    (
                        gen.ParamDecl("x", "Uint256"),
                        gen.ParamDecl("y", "Uint256"),
                        gen.ParamDecl("z", "Uint256"),
                    ),
                    "Uint256",
                    body=(
                        "let product := mul x y",
                        "let quotient := div product z",
                        "let remainder := mod product z",
                        "let lowBits := bitAnd product 255",
                        "let mixed := bitOr lowBits (bitXor x y)",
                        "let shifted := shl 2 mixed",
                        "let unshifted := shr 1 shifted",
                        "let bounded := min (max quotient remainder) unshifted",
                        "let scaledDown := mulDivDown bounded x z",
                        "let scaledUp := mulDivUp bounded y z",
                        "let wadDown := wMulDown scaledDown scaledUp",
                        "let wadUp := wDivUp wadDown z",
                        "let chosen := ite (x > y) wadUp (sub wadUp 1)",
                        "return chosen",
                    ),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_PreviewOps_ReturnsInferredStraightLineResult()", rendered)
        self.assertIn(
            'abi.encodeWithSignature("previewOps(uint256,uint256,uint256)", uint256(2), uint256(1), uint256(1))',
            rendered,
        )
        self.assertNotIn("testTODO_PreviewOps_DecodeAndAssert", rendered)
        self.assertIn("(uint256(2) > uint256(1)) ? ", rendered)
        self.assertIn("? ", rendered)

    def test_render_signed_builtin_smoke_infers_assertions(self) -> None:
        contract = gen.ContractDecl(
            name="SignedBuiltinSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "signedDiv",
                    (
                        gen.ParamDecl("lhs", "Uint256"),
                        gen.ParamDecl("rhs", "Uint256"),
                    ),
                    "Uint256",
                    body=("return (sdiv lhs rhs)",),
                ),
                gen.FunctionDecl(
                    "signedMod",
                    (
                        gen.ParamDecl("lhs", "Uint256"),
                        gen.ParamDecl("rhs", "Uint256"),
                    ),
                    "Uint256",
                    body=("return (smod lhs rhs)",),
                ),
                gen.FunctionDecl(
                    "signedLt",
                    (
                        gen.ParamDecl("lhs", "Uint256"),
                        gen.ParamDecl("rhs", "Uint256"),
                    ),
                    "Bool",
                    body=("return (slt lhs rhs)",),
                ),
                gen.FunctionDecl(
                    "signedGt",
                    (
                        gen.ParamDecl("lhs", "Uint256"),
                        gen.ParamDecl("rhs", "Uint256"),
                    ),
                    "Bool",
                    body=("return (sgt lhs rhs)",),
                ),
                gen.FunctionDecl(
                    "arithmeticShift",
                    (
                        gen.ParamDecl("shift", "Uint256"),
                        gen.ParamDecl("value", "Uint256"),
                    ),
                    "Uint256",
                    body=("return (sar shift value)",),
                ),
                gen.FunctionDecl("signExtended", (), "Uint256", body=("return extendedByte",)),
                gen.FunctionDecl("shiftedMask", (), "Uint256", body=("return arithmeticShifted",)),
                gen.FunctionDecl(
                    "signedDivSurface",
                    (
                        gen.ParamDecl("lhs", "Int256"),
                        gen.ParamDecl("rhs", "Int256"),
                    ),
                    "Int256",
                    body=("return (lhs / rhs)",),
                ),
                gen.FunctionDecl(
                    "signedModSurface",
                    (
                        gen.ParamDecl("lhs", "Int256"),
                        gen.ParamDecl("rhs", "Int256"),
                    ),
                    "Int256",
                    body=("return (lhs % rhs)",),
                ),
                gen.FunctionDecl(
                    "signedDivViaLocal",
                    (
                        gen.ParamDecl("raw", "Uint256"),
                        gen.ParamDecl("denom", "Int256"),
                    ),
                    "Int256",
                    body=("let signedRaw := toInt256 raw", "return (signedRaw / denom)"),
                ),
                gen.FunctionDecl(
                    "castToInt",
                    (gen.ParamDecl("value", "Uint256"),),
                    "Int256",
                    body=("return (toInt256 value)",),
                ),
                gen.FunctionDecl(
                    "castToUint",
                    (gen.ParamDecl("value", "Int256"),),
                    "Uint256",
                    body=("return (toUint256 value)",),
                ),
                gen.FunctionDecl("minusOne", (), "Int256", body=("return negativeOne",)),
            ),
            storage_slots={},
            constants={
                "extendedByte": gen.ValueDecl("extendedByte", "Uint256", "(signextend 0 255)"),
                "arithmeticShifted": gen.ValueDecl("arithmeticShifted", "Uint256", "(sar 255 (sub 0 1))"),
                "negativeOne": gen.ValueDecl("negativeOne", "Int256", "(toInt256 (sub 0 1))"),
            },
        )
        rendered = gen.render_contract_test(contract)
        self.assertNotIn("testTODO_SignedDiv_DecodeAndAssert", rendered)
        self.assertNotIn("testTODO_SignedGt_DecodeAndAssert", rendered)
        self.assertNotIn("testTODO_SignExtended_DecodeAndAssert", rendered)
        self.assertNotIn("testTODO_MinusOne_DecodeAndAssert", rendered)
        self.assertIn(
            'assertEq(actual, uint256(int256(uint256(1)) / int256(uint256(1))), "signedDiv should return the declared constant");',
            rendered,
        )
        self.assertIn(
            'assertEq(actual, (int256(uint256(1)) < int256(uint256(1))), "signedLt should return the declared constant");',
            rendered,
        )
        self.assertIn(
            'assertEq(actual, type(uint256).max, "signExtended should preserve the expected value");',
            rendered,
        )
        self.assertIn(
            'assertEq(actual, int256(-1), "minusOne should preserve the expected value");',
            rendered,
        )

    def test_render_signed_literal_div_mod_use_evm_rounding(self) -> None:
        contract = gen.ContractDecl(
            name="SignedLiteralMathSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl("truncDiv", (), "Int256", body=("return negativeDiv",)),
                gen.FunctionDecl("truncMod", (), "Int256", body=("return negativeMod",)),
            ),
            storage_slots={},
            constants={
                "negativeThree": gen.ValueDecl("negativeThree", "Int256", "(toInt256 (sub 0 3))"),
                "negativeDiv": gen.ValueDecl("negativeDiv", "Int256", "(div negativeThree 2)"),
                "negativeMod": gen.ValueDecl("negativeMod", "Int256", "(mod negativeThree 2)"),
            },
        )
        self.assertEqual(
            gen._resolve_value_expr(contract, "(div negativeThree 2)", "Int256", {}),
            "int256(-1)",
        )
        self.assertEqual(
            gen._resolve_value_expr(contract, "(mod negativeThree 2)", "Int256", {}),
            "int256(-1)",
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn(
            'assertEq(actual, int256(-1), "truncDiv should preserve the expected value");',
            rendered,
        )
        self.assertIn(
            'assertEq(actual, int256(-1), "truncMod should preserve the expected value");',
            rendered,
        )
        self.assertNotIn("int256(-2)", rendered)

    def test_render_erc20_helper_snapshot_reads_use_mocked_calls(self) -> None:
        contract = gen.ContractDecl(
            name="ERC20HelperSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "snapshotBalance",
                    (
                        gen.ParamDecl("token", "Address"),
                        gen.ParamDecl("owner", "Address"),
                    ),
                    "Uint256",
                    body=(
                        "let balance ← balanceOf token owner",
                        "setStorage lastBalance balance",
                        "return balance",
                    ),
                ),
                gen.FunctionDecl(
                    "snapshotAllowance",
                    (
                        gen.ParamDecl("token", "Address"),
                        gen.ParamDecl("owner", "Address"),
                        gen.ParamDecl("spender", "Address"),
                    ),
                    "Uint256",
                    body=(
                        "let current ← allowance token owner spender",
                        "setStorage lastAllowance current",
                        "return current",
                    ),
                ),
                gen.FunctionDecl(
                    "snapshotSupply",
                    (gen.ParamDecl("token", "Address"),),
                    "Uint256",
                    body=(
                        "let supply ← totalSupply token",
                        "setStorage lastSupply supply",
                        "return supply",
                    ),
                ),
            ),
            storage_slots={"lastBalance": 0, "lastAllowance": 1, "lastSupply": 2},
            storage_types={
                "lastBalance": "Uint256",
                "lastAllowance": "Uint256",
                "lastSupply": "Uint256",
            },
        )
        rendered = gen.render_contract_test(contract)
        self.assertNotIn("testTODO_SnapshotBalance_DecodeAndAssert", rendered)
        self.assertIn(
            'vm.mockCall(alice, abi.encodeWithSignature("balanceOf(address)", alice), abi.encode(expected));',
            rendered,
        )
        self.assertIn(
            'vm.mockCall(alice, abi.encodeWithSignature("allowance(address,address)", alice, alice), abi.encode(expected));',
            rendered,
        )
        self.assertIn(
            'vm.mockCall(alice, abi.encodeWithSignature("totalSupply()"), abi.encode(expected));',
            rendered,
        )
        self.assertIn(
            'assertEq(vm.load(target, bytes32(uint256(2))), bytes32(uint256(expected)), "snapshotSupply should persist the mocked external read");',
            rendered,
        )

    def test_render_generic_ecm_snapshot_read_uses_mocked_call(self) -> None:
        contract = gen.ContractDecl(
            name="GenericECMReadSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "snapshotQuote",
                    (
                        gen.ParamDecl("oracle", "Address"),
                        gen.ParamDecl("asset", "Address"),
                    ),
                    "Uint256",
                    body=(
                        "let quote ← ecmCall",
                        "(fun resultVar => Compiler.Modules.Oracle.oracleReadUint256Module resultVar 0x12345678 1)",
                        "[oracle, asset]",
                        "setStorage lastQuote quote",
                        "return quote",
                    ),
                ),
            ),
            storage_slots={"lastQuote": 0},
            storage_types={"lastQuote": "Uint256"},
        )
        rendered = gen.render_contract_test(contract)
        self.assertNotIn("testTODO_SnapshotQuote_DecodeAndAssert", rendered)
        self.assertIn(
            'vm.mockCall(alice, abi.encodeWithSelector(bytes4(0x12345678), alice), abi.encode(expected));',
            rendered,
        )
        self.assertIn(
            'assertEq(vm.load(target, bytes32(uint256(0))), bytes32(uint256(expected)), "snapshotQuote should persist the mocked external read");',
            rendered,
        )

    def test_render_string_eq_predicate_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StringEqSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "same",
                    (
                        gen.ParamDecl("lhs", "String"),
                        gen.ParamDecl("rhs", "String"),
                    ),
                    "Bool",
                    body=("return (lhs == rhs)",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_Same_ComparesDirectDynamicParamsEq()", rendered)
        self.assertIn("bool expected = true;", rendered)
        self.assertIn('assertTrue(actual, "same should return true for the configured string comparison");', rendered)

    def test_render_bytes_neq_predicate_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="BytesEqSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "different",
                    (
                        gen.ParamDecl("lhs", "Bytes"),
                        gen.ParamDecl("rhs", "Bytes"),
                    ),
                    "Bool",
                    body=("return (lhs != rhs)",),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_Different_ComparesDirectDynamicParamsNeq()", rendered)
        self.assertIn("bool expected = false;", rendered)
        self.assertIn('assertFalse(actual, "different should return false for the configured bytes comparison");', rendered)

    def test_render_string_eq_branch_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StringEqSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "choose",
                    (
                        gen.ParamDecl("lhs", "String"),
                        gen.ParamDecl("rhs", "String"),
                    ),
                    "Uint256",
                    body=("if lhs == rhs then", "return 1", "else", "return 0"),
                ),
            ),
            storage_slots={},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_Choose_SelectsDynamicComparisonBranch()", rendered)
        self.assertIn('assertEq(actual, 1, "choose should return the configured branch value");', rendered)

    def test_render_mapping_getter_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="UintMapSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "getValue",
                    (gen.ParamDecl("key", "Uint256"),),
                    "Uint256",
                    body=("let current ← getMappingUint values key", "return current"),
                ),
            ),
            storage_slots={"values": 0},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_GetValue_ReadsConfiguredMapping()", rendered)
        self.assertIn("vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 0), bytes32(uint256(expected)));", rendered)
        self.assertIn('assertEq(actual, expected, "getValue should decode the configured mapping value");', rendered)

    def test_render_mapping_n_getter_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="MappingChainSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "getApproval",
                    (
                        gen.ParamDecl("owner", "Address"),
                        gen.ParamDecl("spender", "Address"),
                        gen.ParamDecl("delegate_", "Address"),
                    ),
                    "Uint256",
                    body=("let current ← getMappingN approvals [owner, spender, delegate_]", "return current"),
                ),
            ),
            storage_slots={"approvals": 0},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_GetApproval_ReadsConfiguredMapping()", rendered)
        self.assertIn(
            "vm.store(target, keccak256(abi.encode(bytes32(uint256(uint160(alice))), keccak256(abi.encode(bytes32(uint256(uint160(alice))), _mappingSlot(bytes32(uint256(uint160(alice))), 0))))), bytes32(uint256(expected)));",
            rendered,
        )
        self.assertIn(
            'assertEq(actual, expected, "getApproval should decode the configured mapping value");',
            rendered,
        )

    def test_render_mapping_n_address_to_word_keys_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="MixedMappingChainSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "getApproval",
                    (
                        gen.ParamDecl("owner", "Address"),
                        gen.ParamDecl("tokenId", "Uint256"),
                        gen.ParamDecl("delegate_", "Address"),
                    ),
                    "Uint256",
                    body=(
                        "let current ← getMappingN approvals [addressToWord owner, tokenId, addressToWord delegate_]",
                        "return current",
                    ),
                ),
            ),
            storage_slots={"approvals": 0},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_GetApproval_ReadsConfiguredMapping()", rendered)
        self.assertIn(
            "vm.store(target, keccak256(abi.encode(bytes32(uint256(uint160(alice))), keccak256(abi.encode(bytes32(uint256(uint256(1))), _mappingSlot(bytes32(uint256(uint160(alice))), 0))))), bytes32(uint256(expected)));",
            rendered,
        )
        self.assertIn(
            'assertEq(actual, expected, "getApproval should decode the configured mapping value");',
            rendered,
        )

    def test_render_struct_member_getter_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StructMappingSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "delegateOf",
                    (gen.ParamDecl("user", "Address"),),
                    "Address",
                    body=('let delegate_ ← structMember "positions" user "delegate"', "return delegate_"),
                ),
            ),
            storage_slots={"positions": 0},
            storage_types={
                "positions": "MappingStruct(Address,[supplyShares @word 0 packed(0,128), borrowShares @word 0 packed(128,128), delegate @word 1])"
            },
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_DelegateOf_ReadsConfiguredStructMember()", rendered)
        self.assertIn(
            "vm.store(target, bytes32(uint256(_mappingSlot(bytes32(uint256(uint160(alice))), 0)) + 1), bytes32(uint256(uint160(expected))));",
            rendered,
        )
        self.assertIn(
            'assertEq(actual, expected, "delegateOf should decode the configured struct member");',
            rendered,
        )

    def test_render_struct_member_straight_line_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StructMappingSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "totalPositionShares",
                    (gen.ParamDecl("user", "Address"),),
                    "Uint256",
                    body=(
                        'let supply ← structMember "positions" user "supplyShares"',
                        'let borrow ← structMember "positions" user "borrowShares"',
                        "return (add supply borrow)",
                    ),
                ),
            ),
            storage_slots={"positions": 0},
            storage_types={
                "positions": "MappingStruct(Address,[supplyShares @word 0 packed(0,128), borrowShares @word 0 packed(128,128), delegate @word 1])"
            },
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn(
            "function testAuto_TotalPositionShares_ReturnsInferredStraightLineResult()",
            rendered,
        )
        self.assertIn(
            "vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 0), bytes32(uint256(expected) | (uint256(expected1) << 128)));",
            rendered,
        )
        self.assertIn(
            'assertEq(actual, (expected + expected1), "totalPositionShares should preserve the inferred result");',
            rendered,
        )

    def test_render_nested_struct_member_getter_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="StructMappingSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Smoke.lean",
            functions=(
                gen.FunctionDecl(
                    "approvalOf",
                    (
                        gen.ParamDecl("owner", "Address"),
                        gen.ParamDecl("spender", "Address"),
                    ),
                    "Uint256",
                    body=('let amount ← structMember2 "approvals" owner spender "allowance"', "return amount"),
                ),
            ),
            storage_slots={"approvals": 1},
            storage_types={
                "approvals": "MappingStruct2(Address,Address,[allowance @word 0 packed(0,128), nonce @word 1])"
            },
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_ApprovalOf_ReadsConfiguredStructMember()", rendered)
        self.assertIn(
            "vm.store(target, _nestedMappingSlot(bytes32(uint256(uint160(alice))), bytes32(uint256(uint160(alice))), 1), bytes32(uint256(expected)));",
            rendered,
        )
        self.assertIn(
            'assertEq(actual, expected, "approvalOf should decode the configured struct member");',
            rendered,
        )

    def test_render_mapping_predicate_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="MappingWordSmoke",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "isWord1NonZero",
                    (gen.ParamDecl("key", "Uint256"),),
                    "Bool",
                    body=("let word ← getMappingWord words key 1", "return (word != 0)"),
                ),
            ),
            storage_slots={"words": 0},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_IsWord1NonZero_DetectsNonZeroMappingWord()", rendered)
        self.assertIn("vm.store(target, _mappingWordSlot(bytes32(uint256(uint256(1))), 0, 1), bytes32(uint256(1)));", rendered)
        self.assertIn(
            'assertTrue(actual, "isWord1NonZero should return true when the configured word is non-zero");',
            rendered,
        )

    def test_render_nested_mapping_predicate_without_parentheses_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ERC721",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "isApprovedForAll",
                    (
                        gen.ParamDecl("ownerAddr", "Address"),
                        gen.ParamDecl("operator", "Address"),
                    ),
                    "Bool",
                    body=("let flag ← getMapping2 operatorApprovals ownerAddr operator", "return flag != 0"),
                ),
            ),
            storage_slots={"operatorApprovals": 6},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_IsApprovedForAll_DetectsNonZeroMappingWord()", rendered)
        self.assertIn(
            "vm.store(target, _nestedMappingSlot(bytes32(uint256(uint160(alice))), bytes32(uint256(uint160(alice))), 6), bytes32(uint256(1)));",
            rendered,
        )
        self.assertIn(
            'assertTrue(actual, "isApprovedForAll should return true when the configured word is non-zero");',
            rendered,
        )

    def test_render_word_to_address_mapping_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ERC721",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "ownerOf",
                    (gen.ParamDecl("tokenId", "Uint256"),),
                    "Address",
                    body=(
                        "let ownerWord ← getMappingUint owners tokenId",
                        'require (ownerWord != 0) "Token does not exist"',
                        "return wordToAddress ownerWord",
                    ),
                ),
            ),
            storage_slots={"owners": 4},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_OwnerOf_DecodesConfiguredOwnerWord()", rendered)
        self.assertIn("vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 4), bytes32(uint256(uint160(expected))));", rendered)
        self.assertIn('assertEq(actual, expected, "ownerOf should decode the configured owner word");', rendered)

    def test_render_secondary_mapping_after_precondition_infers_assertion(self) -> None:
        contract = gen.ContractDecl(
            name="ERC721",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl(
                    "getApproved",
                    (gen.ParamDecl("tokenId", "Uint256"),),
                    "Address",
                    body=(
                        "let ownerWord ← getMappingUint owners tokenId",
                        'require (ownerWord != 0) "Token does not exist"',
                        "let approvedAddr ← getMappingUintAddr tokenApprovals tokenId",
                        "return approvedAddr",
                    ),
                ),
            ),
            storage_slots={"owners": 4, "tokenApprovals": 5},
        )
        rendered = gen.render_contract_test(contract)
        self.assertIn("function testAuto_GetApproved_DecodesConfiguredSecondaryMapping()", rendered)
        self.assertIn("vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 4), bytes32(uint256(uint160(ownerWord))));", rendered)
        self.assertIn("vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 5), bytes32(uint256(uint160(expected))));", rendered)
        self.assertIn(
            'assertEq(actual, expected, "getApproved should decode the configured secondary mapping value");',
            rendered,
        )

    def test_parse_tuple_params(self) -> None:
        out = gen._split_params("cfg : Tuple [Address, Uint256], amount : Uint256")
        self.assertEqual(
            [(p.name, p.lean_type) for p in out],
            [("cfg", "Tuple [Address, Uint256]"), ("amount", "Uint256")],
        )

    def test_sol_type_tuple(self) -> None:
        self.assertEqual(
            gen._sol_type("Tuple [Address, Address, Uint256]"),
            "(address,address,uint256)",
        )

    def test_sol_type_tuple_with_uint8(self) -> None:
        self.assertEqual(
            gen._sol_type("Tuple [Uint8, Bytes32, Bytes32]"),
            "(uint8,bytes32,bytes32)",
        )

    def test_example_value_uint8(self) -> None:
        self.assertEqual(gen._example_value("Uint8"), "uint8(27)")


class CollectContractsTests(unittest.TestCase):
    def test_duplicate_contract_name_errors(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            a = root / "A.lean"
            b = root / "B.lean"
            a.write_text("verity_contract X where\n  storage\n    a : Uint256 := slot 0\n", encoding="utf-8")
            b.write_text("verity_contract X where\n  storage\n    b : Uint256 := slot 0\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate contract 'X'"):
                gen.collect_contracts([a, b])

    def test_discover_macro_contract_sources_recurses(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "Nested").mkdir(parents=True, exist_ok=True)
            top = root / "Top.lean"
            nested = root / "Nested" / "Inner.lean"
            skip = root / "README.md"
            top.write_text("verity_contract Top where\n  storage\n", encoding="utf-8")
            nested.write_text("verity_contract Inner where\n  storage\n", encoding="utf-8")
            skip.write_text("not lean", encoding="utf-8")

            found = gen.discover_macro_contract_sources(root)
            self.assertEqual(found, [nested, top])


if __name__ == "__main__":
    unittest.main()
