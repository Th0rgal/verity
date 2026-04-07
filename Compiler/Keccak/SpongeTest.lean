import Compiler.Keccak.Sponge

/-!
# KeccakEngine Smoke Tests

This file contains formal and empirical checks to ensure the unrolled engine
behaves exactly as the NIST and Ethereum specifications dictate.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace KeccakEngine.Test

/-! ## Endianness & Memory Tests -/

def mock_bytes : ByteArray := ⟨#[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80]⟩

theorem endianness_is_correct : bytesToWordLE mock_bytes 0 = 0x8000000000000001#64 := by rfl

def mock_state : Array (BitVec 64) := Array.replicate 25 (0#64)
def new_state := absorbBlock mock_state mock_bytes 0

theorem absorb_is_correct : new_state[0]! = 0x8000000000000001#64 ∧ new_state[1]! = 0#64 := by decide


/-! ## Padding Tests (Edge Cases) -/

def danger_leftover : ByteArray := ⟨Array.replicate 135 (0 : UInt8)⟩
def danger_padded := padBlock danger_leftover .ethereum

theorem padding_edge_case_is_correct :
  danger_padded.data.size = 136 ∧ danger_padded.data[135]! = 0x81 := by native_decide

def empty_leftover : ByteArray := ⟨#[]⟩
def empty_padded := padBlock empty_leftover .nist

theorem padding_empty_case_is_correct :
  empty_padded.data[0]! = 0x06 ∧ empty_padded.data[135]! = 0x80 := by native_decide


/-! ## NIST/Ethereum Official Vectors -/

def empty_string_bytes : ByteArray := ⟨#[]⟩
def expected_keccak_empty : ByteArray :=
  ⟨#[0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
     0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
     0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
     0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70]⟩

theorem keccak_empty_is_correct : keccak256 empty_string_bytes = expected_keccak_empty := by native_decide


/-! ## EVM ABI Selector Test (The Axiom Killer) -/

theorem transfer_selector_correct :
  keccak256_selector "transfer(address,uint256)" = 0xa9059cbb#32 := by native_decide

end KeccakEngine.Test
