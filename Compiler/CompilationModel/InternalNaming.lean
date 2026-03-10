namespace Compiler.CompilationModel

/-- Prefix prepended to internal function names in generated Yul to avoid
    collision with external function names and EVM/Yul builtins.
    Used by compileExpr, compileStmt, and compileInternalFunction. -/
def internalFunctionPrefix : String := "internal_"

/-- Build the Yul-level name for an internal function. -/
def internalFunctionYulName (name : String) : String :=
  s!"{internalFunctionPrefix}{name}"

private def usedNamesTotalLength (usedNames : List String) : Nat :=
  usedNames.foldl (fun acc name => acc + name.length) 0 + 1

/-- Length budget large enough to make `freshSuffix usedNames` longer than any
individual used name. -/
private abbrev freshSuffixLen (usedNames : List String) : Nat :=
  usedNamesTotalLength usedNames

/-- Deterministic suffix whose length alone guarantees freshness against
`usedNames`. -/
private def freshSuffix (usedNames : List String) : String :=
  String.mk (List.replicate (freshSuffixLen usedNames) '_')

def pickFreshName (base : String) (usedNames : List String) : String :=
  if !usedNames.contains base then
    base
  else
    base ++ "_" ++ freshSuffix usedNames

private theorem length_lt_usedNamesTotalLength_of_mem
    {usedNames : List String}
    {queryName : String}
    (hmem : queryName ∈ usedNames) :
    queryName.length < usedNamesTotalLength usedNames := by
  have hfold :
      ∀ (acc : Nat) (names : List String),
        List.foldl (fun total name => total + name.length) acc names =
          acc + List.foldl (fun total name => total + name.length) 0 names := by
    intro acc names
    induction names generalizing acc with
    | nil =>
        simp [List.foldl]
    | cons head tail ih =>
        calc
          List.foldl (fun total name => total + name.length) (acc + String.length head) tail
            = acc + (String.length head + List.foldl (fun total name => total + name.length) 0 tail) := by
                simpa [Nat.add_assoc] using ih (acc := acc + String.length head)
          _ = acc + List.foldl (fun total name => total + name.length) (String.length head) tail := by
                rw [ih (acc := String.length head)]
          _ = acc + List.foldl (fun total name => total + name.length) 0 (head :: tail) := by
                simp [List.foldl]
  unfold usedNamesTotalLength
  induction usedNames with
  | nil =>
      cases hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      ·
        have hsum :
            List.foldl (fun acc name => acc + name.length) 0 (queryName :: tail) =
              String.length queryName + List.foldl (fun acc name => acc + name.length) 0 tail := by
          simpa using hfold (String.length queryName) tail
        have hle : String.length queryName ≤
            String.length queryName + List.foldl (fun acc name => acc + name.length) 0 tail := by
          exact Nat.le_add_right _ _
        rw [hsum]
        omega
      ·
        have ih' := ih hmem
        have hsum :
            List.foldl (fun acc name => acc + name.length) 0 (head :: tail) =
              String.length head + List.foldl (fun acc name => acc + name.length) 0 tail := by
          simpa using hfold (String.length head) tail
        rw [hsum]
        omega

theorem pickFreshName_not_mem_usedNames
    (base : String)
    (usedNames : List String) :
    pickFreshName base usedNames ∉ usedNames := by
  unfold pickFreshName
  by_cases hbase : base ∈ usedNames
  · intro hmem
    simp [hbase] at hmem
    have hlenUsed : (base ++ "_" ++ freshSuffix usedNames).length < freshSuffixLen usedNames := by
      simpa [freshSuffixLen] using
        (length_lt_usedNamesTotalLength_of_mem
          (usedNames := usedNames)
          (queryName := base ++ "_" ++ freshSuffix usedNames)
          hmem)
    have hlenFresh : freshSuffixLen usedNames ≤ (base ++ "_" ++ freshSuffix usedNames).length := by
      simp [freshSuffix, freshSuffixLen, usedNamesTotalLength]
    omega
  · simp [hbase]

end Compiler.CompilationModel
