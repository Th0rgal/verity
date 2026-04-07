import Init.Data.BitVec

set_option autoImplicit false

/-!
# Domain-Specific SLP (Straight-Line Program) for Keccak-256

This module defines an AST (Abstract Syntax Tree) for basic Keccak bitwise operations
and a Tracer monad to unroll the Keccak-f[1600] permutation into a flat circuit.
This bypasses Lean's elaborator memory limitations when evaluating loops at compile-time.
-/

namespace KeccakEngine

/--
Primitive instruction set for the Keccak circuit.
Operates on virtual memory addresses (array indices) instead of mutated state.
-/
inductive Instr where
  | xor        (a b : Nat)
  | xor_const  (a : Nat) (c : BitVec 64)
  | and        (a b : Nat)
  | not        (a : Nat)
  | rotl       (a : Nat) (n : Nat)
  deriving Repr, Inhabited, DecidableEq

/--
Evaluates a single instruction, appending the result to the memory tape.
Uses `!` to ensure no runtime bounds checking overhead.
-/
@[always_inline, inline]
def evalInstr (mem : Array (BitVec 64)) (inst : Instr) : Array (BitVec 64) :=
  match inst with
  | .xor a b       => mem.push (mem[a]! ^^^ mem[b]!)
  | .xor_const a c => mem.push (mem[a]! ^^^ c)
  | .and a b       => mem.push (mem[a]! &&& mem[b]!)
  | .not a         => mem.push (~~~mem[a]!)
  | .rotl a n      => mem.push ((mem[a]!).rotateLeft n)

/-!
### Circuit Generator (Tracer)
-/

abbrev TracerM := StateM (Array Instr)

/-- Emits an instruction to the circuit and returns its new virtual memory address. -/
def emit (inst : Instr) : TracerM Nat := do
  let circuit ← get
  let new_idx := 25 + circuit.size
  set (circuit.push inst)
  return new_idx

def trXor (a b : Nat)            : TracerM Nat := emit (.xor a b)
def trXorConst (a : Nat) (c : BitVec 64) : TracerM Nat := emit (.xor_const a c)
def trAnd (a b : Nat)            : TracerM Nat := emit (.and a b)
def trNot (a : Nat)              : TracerM Nat := emit (.not a)
def trRotl (a n : Nat)           : TracerM Nat := emit (.rotl a n)

/-!
### Keccak Constants
-/

private def roundConstants : Array (BitVec 64) :=
  #[0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808a#64,
    0x8000000080008000#64, 0x000000000000808b#64, 0x0000000080000001#64,
    0x8000000080008081#64, 0x8000000000008009#64, 0x000000000000008a#64,
    0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000a#64,
    0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64,
    0x8000000000008003#64, 0x8000000000008002#64, 0x8000000000000080#64,
    0x000000000000800a#64, 0x800000008000000a#64, 0x8000000080008081#64,
    0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64]

private def rotationValues : Array Nat :=
  #[0, 1, 62, 28, 27,
    36, 44, 6, 55, 20,
    3, 10, 43, 25, 39,
    41, 45, 15, 21, 8,
    18, 2, 61, 56, 14]

/-!
### Algorithm Translation
-/

def traceTheta (A : Array Nat) : TracerM (Array Nat) := do
  let mut C := Array.replicate 5 0
  let mut D := Array.replicate 5 0
  for x in [:5] do
    let mut cx := A[x]!
    for y in [1:5] do cx ← trXor cx (A[x + 5 * y]!)
    C := C.set! x cx
  for x in [:5] do
    let rot ← trRotl C[(x + 1) % 5]! 1
    let dx ← trXor C[(x + 4) % 5]! rot
    D := D.set! x dx
  let mut newA := A
  for x in [:5] do
    for y in [:5] do
      let idx := x + 5 * y
      let ax ← trXor A[idx]! D[x]!
      newA := newA.set! idx ax
  return newA

def traceRhoPi (A : Array Nat) : TracerM (Array Nat) := do
  let mut A' := Array.replicate 25 0
  for x in [:5] do
    for y in [:5] do
      let i := (x + 3 * y) % 5 + 5 * x
      let rot := rotationValues[i]!
      let rot_idx ← if rot == 0 then pure A[i]! else trRotl A[i]! rot
      A' := A'.set! (x + 5 * y) rot_idx
  return A'

def traceChi (A' : Array Nat) : TracerM (Array Nat) := do
  let mut A := Array.replicate 25 0
  for x in [:5] do
    for y in [:5] do
      let idx := x + 5 * y
      let a_next1 := A'[(x + 1) % 5 + 5 * y]!
      let a_next2 := A'[(x + 2) % 5 + 5 * y]!
      let not_next1 ← trNot a_next1
      let and_res ← trAnd not_next1 a_next2
      let ax ← trXor A'[idx]! and_res
      A := A.set! idx ax
  return A

def traceIota (A : Array Nat) (round : Nat) : TracerM (Array Nat) := do
  let rc := roundConstants[round]!
  let a0 ← trXorConst A[0]! rc
  let A := A.set! 0 a0
  return A

def traceKeccakP (A : Array Nat) : TracerM (Array Nat) := do
  let mut A := A
  for round in [:24] do
    A ← traceTheta A
    A ← traceRhoPi A
    A ← traceChi A
    A ← traceIota A round
  return A

/-!
### State Extraction and Code Generation
-/

def initial_vstate : Array Nat :=
  #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]

def keccak_gen_result := traceKeccakP initial_vstate |>.run #[]
def final_vstate : Array Nat := keccak_gen_result.fst
def full_keccak_circuit : Array Instr := keccak_gen_result.snd

def instrToCode : Instr → String
  | .xor a b => s!"  Instr.xor {a} {b}"
  | .xor_const a c => s!"  Instr.xor_const {a} {c.toNat}#64"
  | .and a b => s!"  Instr.and {a} {b}"
  | .not a => s!"  Instr.not {a}"
  | .rotl a n => s!"  Instr.rotl {a} {n}"

/-- Generates the unrolled circuit and writes it to `CircuitData.lean`. -/
def generateCircuitFile : IO Unit := do
  let mut out := "import KeccakEngine.Circuit\n\n"
  out := out ++ "set_option maxRecDepth 100000\n"
  out := out ++ "set_option maxHeartbeats 0\n\n"
  out := out ++ "namespace KeccakEngine\n\n"

  let instructionsPerRound := 155

  for r in [:24] do
    out := out ++ s!"def sha3_round_{r} : Array Instr := #[\n"
    let mut lines : Array String := #[]
    let startIdx := r * instructionsPerRound
    let endIdx := (r + 1) * instructionsPerRound
    for i in [startIdx : endIdx] do
      lines := lines.push (instrToCode full_keccak_circuit[i]!)
    out := out ++ (String.intercalate ",\n" lines.toList)
    out := out ++ "\n]\n\n"

  out := out ++ "end KeccakEngine\n"

  IO.FS.writeFile "Compiler/Keccak/CircuitData.lean" out
  IO.println "CircuitData.lean successfully generated!"

end KeccakEngine
