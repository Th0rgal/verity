#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from generate_contract import (
    ContractConfig,
    Field,
    Function,
    Param,
    gen_all_lean_imports,
    gen_basic_proofs,
    gen_invariants,
    gen_example,
    gen_compiler_spec,
    gen_spec,
    gen_property_tests,
    parse_fields,
    parse_functions,
    scaffold_files,
)


class GenerateContractIdentifierValidationTests(unittest.TestCase):
    def _assert_exits_with_error(self, fn, *args: object) -> str:
        buf = io.StringIO()
        with redirect_stderr(buf):
            with self.assertRaises(SystemExit) as ctx:
                fn(*args)
        self.assertEqual(ctx.exception.code, 1)
        return buf.getvalue()

    def test_parse_fields_rejects_hyphenated_identifier(self) -> None:
        err = self._assert_exits_with_error(parse_fields, "bad-name:uint256")
        self.assertIn("Invalid field identifier 'bad-name'", err)

    def test_parse_fields_rejects_leading_digit_identifier(self) -> None:
        err = self._assert_exits_with_error(parse_fields, "1field:uint256")
        self.assertIn("Invalid field identifier '1field'", err)

    def test_parse_fields_rejects_reserved_identifier(self) -> None:
        err = self._assert_exits_with_error(parse_fields, "contract:uint256")
        self.assertIn("Invalid field identifier 'contract'", err)
        self.assertIn("reserved", err)

    def test_parse_functions_rejects_hyphenated_identifier(self) -> None:
        err = self._assert_exits_with_error(
            parse_functions,
            "set-value(uint256),getValue()",
            [],
        )
        self.assertIn("Invalid function identifier 'set-value'", err)

    def test_parse_functions_rejects_leading_digit_identifier(self) -> None:
        err = self._assert_exits_with_error(
            parse_functions,
            "1setter(uint256)",
            [],
        )
        self.assertIn("Invalid function identifier '1setter'", err)

    def test_parse_functions_rejects_reserved_identifier(self) -> None:
        err = self._assert_exits_with_error(parse_functions, "return(uint256)", [])
        self.assertIn("Invalid function identifier 'return'", err)
        self.assertIn("reserved", err)

    def test_parse_fields_and_functions_accept_valid_identifiers(self) -> None:
        fields = parse_fields("storedData:uint256,owner_address:address")
        funcs = parse_functions("setStoredData(uint256),getStoredData()", fields)
        self.assertEqual([f.name for f in fields], ["storedData", "owner_address"])
        self.assertEqual([f.name for f in funcs], ["setStoredData", "getStoredData"])

    def test_parse_fields_rejects_unknown_field_type(self) -> None:
        err = self._assert_exits_with_error(parse_fields, "flag:bool")
        self.assertIn("Unsupported field type 'bool'", err)

    def test_parse_fields_accepts_supported_mapping_field_types(self) -> None:
        fields = parse_fields("balances:mapping(address),scores:mapping(uint256)")
        self.assertEqual([f.ty for f in fields], ["mapping", "mapping_uint"])


class GenerateContractFunctionSignatureValidationTests(unittest.TestCase):
    def _assert_parse_functions_error(self, spec: str) -> str:
        buf = io.StringIO()
        with redirect_stderr(buf):
            with self.assertRaises(SystemExit) as ctx:
                parse_functions(spec, [])
        self.assertEqual(ctx.exception.code, 1)
        return buf.getvalue()

    def test_rejects_unbalanced_parentheses_in_function_list(self) -> None:
        err = self._assert_parse_functions_error("foo(uint256)),bar(")
        self.assertIn("Malformed function list", err)
        self.assertIn("unexpected ')'", err)

    def test_rejects_unknown_parameter_type(self) -> None:
        err = self._assert_parse_functions_error("foo(bytes32)")
        self.assertIn("Unsupported parameter type 'bytes32'", err)

    def test_rejects_extra_closing_parenthesis(self) -> None:
        err = self._assert_parse_functions_error("foo(uint256))")
        self.assertIn("unexpected ')'", err)

    def test_rejects_empty_signature_entry(self) -> None:
        err = self._assert_parse_functions_error("foo(uint256),,bar(address)")
        self.assertIn("empty signature between commas", err)

    def test_rejects_trailing_comma(self) -> None:
        err = self._assert_parse_functions_error("foo(uint256),")
        self.assertIn("empty signature at end of list", err)

    def test_parses_valid_typed_signatures(self) -> None:
        funcs = parse_functions("transfer(address,uint256),getBalance(address)", [])
        self.assertEqual([f.name for f in funcs], ["transfer", "getBalance"])
        self.assertEqual([p.ty for p in funcs[0].params], ["address", "uint256"])
        self.assertEqual([p.ty for p in funcs[1].params], ["address"])


class GenerateContractGetterPropertyScaffoldTests(unittest.TestCase):
    def test_getter_scaffold_is_explicit_todo_placeholder(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[Function(name="getStoredValue", params=[])],
        )

        out = gen_property_tests(cfg)
        self.assertIn(
            "function testTODO_GetStoredValue_GetterNeedsSpecAssertions() public {",
            out,
        )
        self.assertIn("Property TODO: getStoredValue_meets_spec", out)
        self.assertIn("revert(\"TODO: implement getter property assertions\");", out)
        self.assertNotIn("bytes memory data", out)
        self.assertNotIn("assertEq(readStorage(0), slot0Before", out)

    def test_non_getter_scaffold_keeps_meets_spec_template(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[
                Function(
                    name="setStoredValue",
                    params=[Param(name="value", ty="uint256")],
                )
            ],
        )

        out = gen_property_tests(cfg)
        self.assertIn("function testProperty_SetStoredValue_MeetsSpec() public {", out)
        self.assertIn("Property: setStoredValue_meets_spec", out)
        self.assertIn("assertEq(", out)
        self.assertIn("scaffold default: slot 0 unchanged", out)


class GenerateCompilationModelScaffoldTests(unittest.TestCase):
    def test_specs_are_not_vacuous_true(self) -> None:
        cfg = ContractConfig(
            name="AuditVacuous",
            fields=[Field(name="x", ty="uint256")],
            functions=[
                Function(name="setX", params=[Param(name="value", ty="uint256")]),
                Function(name="getX", params=[]),
                Function(name="isReady", params=[]),
            ],
        )

        out = gen_spec(cfg)
        self.assertNotIn(" : Prop :=\n  True", out)
        self.assertIn("def setX_spec (value : Uint256) (s s' : ContractState) : Prop :=", out)
        self.assertIn("sameExceptEvents s s'", out)
        self.assertIn("def getX_spec (result : Uint256) (s : ContractState) : Prop :=", out)
        self.assertIn("result = s.storage 0", out)
        self.assertIn("def isReady_spec (result : Bool) (s : ContractState) : Prop :=", out)
        self.assertIn("result = false", out)


class GenerateContractExampleGetterScaffoldTests(unittest.TestCase):
    def test_scalar_address_getter_reads_address_storage(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="owner", ty="address")],
            functions=[Function(name="getOwner", params=[])],
        )

        out = gen_example(cfg)
        self.assertIn("def getOwner : Contract Address := do", out)
        self.assertIn("let currentValue ← getStorageAddr owner", out)
        self.assertIn("return currentValue", out)

    def test_scalar_uint_getter_reads_uint_storage(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="totalSupply", ty="uint256")],
            functions=[Function(name="getTotalSupply", params=[])],
        )

        out = gen_example(cfg)
        self.assertIn("def getTotalSupply : Contract Uint256 := do", out)
        self.assertIn("let currentValue ← getStorage totalSupply", out)
        self.assertIn("return currentValue", out)

    def test_mapping_getter_reads_mapping_entry(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="balances", ty="mapping")],
            functions=[Function(name="getBalance", params=[Param(name="account", ty="address")])],
        )

        out = gen_example(cfg)
        self.assertIn("def getBalance (account : Address) : Contract Uint256 := do", out)
        self.assertIn("let currentValue ← getMapping balances account", out)
        self.assertIn("return currentValue", out)

    def test_uint_mapping_getter_reads_uint_mapping_entry(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="values", ty="mapping_uint")],
            functions=[Function(name="getValue", params=[Param(name="id", ty="uint256")])],
        )

        out = gen_example(cfg)
        self.assertIn("def getValue (id : Uint256) : Contract Uint256 := do", out)
        self.assertIn("let currentValue ← getMappingUint values id", out)
        self.assertIn("return currentValue", out)


class GenerateContractSpecGetterTests(unittest.TestCase):
    def test_address_getter_spec_tracks_address_slot(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="owner", ty="address")],
            functions=[Function(name="getOwner", params=[])],
        )

        out = gen_spec(cfg)
        self.assertIn("def getOwner_spec (result : Address) (s : ContractState) : Prop :=", out)
        self.assertIn("result = s.storageAddr 0", out)

    def test_mapping_getter_spec_tracks_mapping_entry(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="balances", ty="mapping")],
            functions=[Function(name="getBalance", params=[Param(name="account", ty="address")])],
        )

        out = gen_spec(cfg)
        self.assertIn(
            "def getBalance_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=",
            out,
        )
        self.assertIn("result = s.storageMap 0 account", out)

    def test_uint_mapping_getter_spec_tracks_uint_mapping_entry(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="values", ty="mapping_uint")],
            functions=[Function(name="getValue", params=[Param(name="id", ty="uint256")])],
        )

        out = gen_spec(cfg)
        self.assertIn(
            "def getValue_spec (id : Uint256) (result : Uint256) (s : ContractState) : Prop :=",
            out,
        )
        self.assertIn("result = s.storageMapUint 0 id", out)


class GenerateContractInvariantScaffoldTests(unittest.TestCase):
    def test_address_mapping_invariant_uses_address_keyed_storage_map(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="balances", ty="mapping")],
            functions=[],
        )

        out = gen_invariants(cfg)
        self.assertIn("def balances_mapping_isolated", out)
        self.assertIn("∀ addr : Address, s'.storageMap slot addr = s.storageMap slot addr", out)

    def test_uint_mapping_invariant_uses_uint_keyed_storage_map(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[Field(name="values", ty="mapping_uint")],
            functions=[],
        )

        out = gen_invariants(cfg)
        self.assertIn("def values_mapping_isolated", out)
        self.assertIn(
            "∀ key : Uint256, s'.storageMapUint slot key = s.storageMapUint slot key",
            out,
        )
        self.assertNotIn("storageMap slot", out)
        self.assertNotIn("∀ addr : Address", out)


class GenerateContractCompilerSpecGetterTests(unittest.TestCase):
    def test_unknown_getter_target_field_fails(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[
                Field(name="owner", ty="address"),
                Field(name="totalSupply", ty="uint256"),
            ],
            functions=[Function(name="getSupply", params=[])],
        )

        buf = io.StringIO()
        with redirect_stderr(buf):
            with self.assertRaises(SystemExit) as ctx:
                gen_compiler_spec(cfg)
        self.assertEqual(ctx.exception.code, 1)
        err = buf.getvalue()
        self.assertIn("Cannot infer target field for getter 'getSupply'", err)

    def test_matching_getter_target_field_is_used(self) -> None:
        cfg = ContractConfig(
            name="AuditDemo",
            fields=[
                Field(name="owner", ty="address"),
                Field(name="totalSupply", ty="uint256"),
            ],
            functions=[Function(name="getTotalSupply", params=[])],
        )

        rendered = gen_compiler_spec(cfg)
        self.assertIn('Stmt.return (Expr.storage "totalSupply")', rendered)


class GenerateContractBasicProofScaffoldTests(unittest.TestCase):
    def test_basic_proof_scaffold_has_no_sorry(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[
                Function(name="getStoredValue", params=[]),
                Function(
                    name="setStoredValue",
                    params=[Param(name="value", ty="uint256")],
                ),
            ],
        )

        out = gen_basic_proofs(cfg)
        self.assertNotIn("sorry", out)
        self.assertNotIn(".fst", out)
        self.assertNotIn(".snd", out)
        self.assertIn("simp [getStoredValue_spec]", out)
        self.assertIn("simp [setStoredValue_spec]", out)
        self.assertIn("match (getStoredValue).run s with", out)
        self.assertIn("| ContractResult.success result _ => getStoredValue_spec result s", out)
        self.assertIn("| ContractResult.revert _ _ => True := by", out)
        self.assertIn("match (setStoredValue value).run s with", out)
        self.assertIn("| ContractResult.success _ s' => setStoredValue_spec value s s'", out)


class GenerateContractStructureScaffoldTests(unittest.TestCase):
    def test_scaffold_files_do_not_include_legacy_spec_correctness(self) -> None:
        cfg = ContractConfig(
            name="AuditProbe",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[
                Function(
                    name="setStoredValue",
                    params=[Param(name="value", ty="uint256")],
                )
            ],
        )
        paths = {str(path) for path, _ in scaffold_files(cfg)}

        self.assertNotIn(
            str((SCRIPT_DIR.parent / "Compiler" / "Proofs" / "SpecCorrectness" / "AuditProbe.lean")),
            paths,
        )

    def test_all_lean_imports_do_not_include_ast_module(self) -> None:
        cfg = ContractConfig(
            name="AuditProbe",
            fields=[Field(name="storedValue", ty="uint256")],
            functions=[Function(name="getStoredValue", params=[])],
        )
        imports = gen_all_lean_imports(cfg)
        self.assertNotIn("import Verity.AST.AuditProbe", imports)


class GenerateContractCompilerSpecMappingGetterTests(unittest.TestCase):
    def _assert_compiler_spec_error(self, cfg: ContractConfig) -> str:
        buf = io.StringIO()
        with redirect_stderr(buf):
            with self.assertRaises(SystemExit) as ctx:
                gen_compiler_spec(cfg)
        self.assertEqual(ctx.exception.code, 1)
        return buf.getvalue()

    def test_rejects_mapping_getter_without_key_param(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="balances", ty="mapping")],
            functions=[Function(name="getBalance", params=[])],
        )
        err = self._assert_compiler_spec_error(cfg)
        self.assertIn("Mapping getter 'getBalance' for field 'balances' requires", err)
        self.assertIn("type 'address'", err)

    def test_rejects_mapping_getter_with_wrong_key_type(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="balances", ty="mapping")],
            functions=[Function(name="getBalance", params=[Param(name="key", ty="uint256")])],
        )
        err = self._assert_compiler_spec_error(cfg)
        self.assertIn("requires first parameter type 'address'", err)
        self.assertIn("got 'uint256'", err)

    def test_allows_address_mapping_getter_with_address_key(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="balances", ty="mapping")],
            functions=[Function(name="getBalance", params=[Param(name="account", ty="address")])],
        )
        out = gen_compiler_spec(cfg)
        self.assertIn('Stmt.return (Expr.mapping "balances" (Expr.param "account"))', out)

    def test_allows_uint_mapping_getter_with_uint_key(self) -> None:
        cfg = ContractConfig(
            name="Demo",
            fields=[Field(name="data", ty="mapping_uint")],
            functions=[Function(name="getData", params=[Param(name="id", ty="uint256")])],
        )
        out = gen_compiler_spec(cfg)
        self.assertIn('Stmt.return (Expr.mapping "data" (Expr.param "id"))', out)


if __name__ == "__main__":
    unittest.main()
