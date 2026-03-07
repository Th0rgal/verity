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
        self.assertEqual(
            contract.functions[0].body,
            ("let current ← getStorage storedData", "return current"),
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

    def test_render_unknown_type_fails_closed(self) -> None:
        contract = gen.ContractDecl(
            name="UnknownType",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl("mystery", (gen.ParamDecl("x", "String"),), "Unit"),
            ),
            storage_slots={},
        )
        with self.assertRaisesRegex(ValueError, "unsupported Lean type"):
            gen.render_contract_test(contract)

    def test_render_non_uint_array_fails_closed(self) -> None:
        contract = gen.ContractDecl(
            name="ArrayAddressConsumer",
            constructor=None,
            source=gen.ROOT / "Contracts/Sample/Sample.lean",
            functions=(
                gen.FunctionDecl("consume", (gen.ParamDecl("values", "Array Address"),), "Unit"),
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
            functions=(gen.FunctionDecl("mystery", (), "String"),),
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
        self.assertIn("abi.encode(alice, alice, uint256(1))", rendered)

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
