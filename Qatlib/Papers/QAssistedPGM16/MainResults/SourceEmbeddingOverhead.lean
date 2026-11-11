/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QAssistedPGM16 — embedding overhead is quadratic (c003)

Fixed source: arXiv:1609.02542, complexity paragraph on p.6 and Table I on p.7.

The paper argues: a fully connected model on `N` logical variables has
`N(N-1)/2 + N` parameters, i.e. `O(N²)`.  Embedding it into a sparse Chimera
graph uses `O(N²)` physical qubits, but the number of parameters stays `O(N²)`:
each DW2X qubit has degree at most six, so the number of extra couplings is at
most `3M` for `M` physical qubits, plus `M` local fields, i.e. `4M`.  Table I
reports that the resulting physical/logical parameter ratio is about 3.

`physicalParamsBound M 6 = 4M` is the degree-six Chimera parameter budget.  The
existence of a minor embedding with `M ≤ C N²` physical qubits is a graph
theory fact (Chimera minor embedding) that the paper cites but does not prove;
we take it as the explicit hypothesis `hM` and prove the parameter-count
consequences.  The numerical Table I checks are fully proved.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QAssistedPGM16.MainResults

/-- Number of parameters of a fully connected Ising model on `N` logical
variables: `N(N−1)/2` couplings plus `N` fields (p.6). -/
def logicalParams (N : ℕ) : ℚ := (N : ℚ) * ((N : ℚ) - 1) / 2 + N

/-- Parameter budget of an `M`-qubit hardware graph of maximum degree `d`:
at most `dM/2` couplings plus `M` fields (p.6-7; Chimera has `d = 6`). -/
def physicalParamsBound (M d : ℕ) : ℚ := (d : ℚ) * M / 2 + M

/-- Chimera has maximum degree six, so the physical parameter budget is `4M`. -/
theorem physicalParamsBound_six (M : ℕ) : physicalParamsBound M 6 = 4 * M := by
  unfold physicalParamsBound
  push_cast
  ring

/-- Main quantitative content of c003 (p.6): if a fully connected `N`-variable
model is embedded in `M` physical qubits with `M ≤ C N²` (the `O(N²)`
embedding overhead), then both the physical parameter budget and the logical
parameter count are `O(N²)`; in particular the physical budget is at most
`4 C N²`. -/
theorem embedding_overhead_quadratic (N M C : ℕ) (hN : 1 ≤ N) (hM : M ≤ C * N ^ 2) :
    physicalParamsBound M 6 = 4 * (M : ℚ) ∧
    physicalParamsBound M 6 ≤ 4 * (C : ℚ) * (N : ℚ) ^ 2 ∧
    logicalParams N ≤ (N : ℚ) ^ 2 := by
  have hNq : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have hMq : (M : ℚ) ≤ (C : ℚ) * (N : ℚ) ^ 2 := by exact_mod_cast hM
  refine ⟨?_, ?_, ?_⟩
  · exact physicalParamsBound_six M
  · rw [physicalParamsBound_six]
    nlinarith
  · unfold logicalParams
    nlinarith

/-- Table I (p.7): the three reported embeddings have the stated logical and
physical parameter counts, satisfy the degree-six budget `4M`, and their
physical/logical parameter ratios all lie between 2 and 4 (the paper rounds
this to "about 3"). -/
theorem tableI_parameters :
    logicalParams 15 = 120 ∧ logicalParams 42 = 903 ∧ logicalParams 46 = 1081 ∧
    (252 : ℚ) ≤ physicalParamsBound 76 6 ∧
    (2644 : ℚ) ≤ physicalParamsBound 739 6 ∧
    (3389 : ℚ) ≤ physicalParamsBound 940 6 ∧
    (2 : ℚ) ≤ 252 / logicalParams 15 ∧ (252 / logicalParams 15) ≤ 4 ∧
    (2 : ℚ) ≤ 2644 / logicalParams 42 ∧ (2644 / logicalParams 42) ≤ 4 ∧
    (2 : ℚ) ≤ 3389 / logicalParams 46 ∧ (3389 / logicalParams 46) ≤ 4 := by
  norm_num [logicalParams, physicalParamsBound]

end Qatlib.Papers.QAssistedPGM16.MainResults
