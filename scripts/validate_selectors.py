#!/usr/bin/env python3
"""
Validate that function selectors in Compiler/Selectors.lean match keccak256 hashes.

This script:
1. Extracts selector definitions from Lean code
2. Computes keccak256 hash for each function signature
3. Compares computed values with expected values
4. Exits with error if any mismatch is found

Used in CI to ensure selector axiom usage is correct.
"""

import re
import sys
from pathlib import Path
from typing import Dict

ROOT = Path(__file__).resolve().parent.parent

# Import the existing keccak256 implementation
sys.path.insert(0, str(Path(__file__).resolve().parent))
from keccak256 import keccak_256


def compute_selector(signature: str) -> str:
    """Compute function selector (first 4 bytes of keccak256 hash)."""
    hash_bytes = keccak_256(signature.encode('utf-8'))
    selector_bytes = hash_bytes[:4]
    return '0x' + selector_bytes.hex()


def extract_selectors_from_lean(filepath: str) -> Dict[str, str]:
    """
    Extract function selectors from Lean code.

    Returns dict mapping function_name -> signature
    e.g., {"transfer": "transfer(address,uint256)"}
    """
    selectors = {}

    with open(filepath, 'r') as f:
        content = f.read()

    # Match: noncomputable def transfer_selector : Nat := keccak256_first_4_bytes "transfer(address,uint256)"
    pattern = r'noncomputable\s+def\s+(\w+)_selector\s*:.*keccak256_first_4_bytes\s+"([^"]+)"'

    for match in re.finditer(pattern, content):
        func_name = match.group(1)
        signature = match.group(2)
        selectors[func_name] = signature

    return selectors


def main():
    lean_file = str(ROOT / 'Compiler' / 'Selectors.lean')

    print("🔍 Extracting selectors from Lean code...")
    selectors = extract_selectors_from_lean(lean_file)

    if not selectors:
        print("❌ ERROR: No selectors found in Lean code!")
        sys.exit(1)

    print(f"Found {len(selectors)} selectors\n")

    # Known correct values (from solc)
    expected_values = {
        "transfer": "0xa9059cbb",
        "approve": "0x095ea7b3",
        "transferFrom": "0x23b872dd",
        "balanceOf": "0x70a08231",
        "allowance": "0xdd62ed3e",
        "increment": "0xd09de08a",
        "decrement": "0x2baeceb7",
        "get": "0x6d4ce63c",
        "set": "0x60fe47b1",
        "transferOwnership": "0xf2fde38b",
    }

    print("✅ Computing and validating selectors...")
    print("=" * 70)

    errors = []

    for func_name, signature in selectors.items():
        computed = compute_selector(signature)
        expected = expected_values.get(func_name)

        if expected is None:
            print(f"⚠️  {func_name:20s} {signature:40s} -> {computed}")
            print(f"   WARNING: No expected value to compare against")
        elif computed == expected:
            print(f"✅ {func_name:20s} {signature:40s} -> {computed}")
        else:
            print(f"❌ {func_name:20s} {signature:40s}")
            print(f"   Computed: {computed}")
            print(f"   Expected: {expected}")
            errors.append((func_name, signature, computed, expected))

    print("=" * 70)

    if errors:
        print(f"\n❌ VALIDATION FAILED: {len(errors)} selector(s) have mismatches!\n")
        for func_name, signature, computed, expected in errors:
            print(f"  {func_name}: {signature}")
            print(f"    Computed: {computed}")
            print(f"    Expected: {expected}")
        sys.exit(1)
    else:
        print(f"\n✅ SUCCESS: All {len(selectors)} selectors validated correctly!")
        print("All keccak256 computations match expected values.")
        sys.exit(0)


if __name__ == '__main__':
    main()
