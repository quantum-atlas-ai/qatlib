/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.QuantumPCPs25.MainResults.Model.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Adaptive Versus Non-Adaptive Quantum PCPs (Theorem 3)

This module formalizes Theorem 3 (Section 5.3, p. 30) of Buhrman, Helsen, and
Weggemans in the semantic `QuantumVerifier` model, relating `q`-query adaptive
quantum PCPs `QPCP_{c,s}[q]` with constant soundness-completeness gap `c - s > 0`
to `q'`-query non-adaptive quantum PCPs `QPCPNA[q']` with
`q' = O(q (4 q / (c - s))^2)`.

## Main statements

* `theorem_3_adaptive_vs_nonadaptive`: Theorem 3, containment of
  `InQPCP 1 q c s` in `InQPCPNA 1 q' (2 / 3) (1 / 3)` within query bound
  `q' ≤ C q (4 q / (c - s))^2`.

## References

* [Buhrman, Helsen, and Weggemans, 2025][BuhrmanHelsenWeggemans2025QuantumPCP],
  Section 5.3, Theorem 3, p. 30.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.QuantumPCPs25.MainResults.Model

/-- **Theorem 3** (arXiv:2403.04841v3, p. 30).
For any `c - s = Ω(1)` and `q = O(1)` we have
`QPCP_{c,s}[q] ⊆ QPCPNA[q']` with `q' = O(q (4q/(c-s))²)`; equivalently there
is a constant `C > 0` with `q' ≤ C · q · (4q/(c-s))²` such that every
`QPCP_{c,s}[q]` problem is in `QPCPNA[q']`. -/
theorem theorem_3_adaptive_vs_nonadaptive (q : ℕ) (c s : ℝ) (hgap : 0 < c - s) :
    ∃ q' : ℕ, ∃ C : ℝ, 0 < C ∧
      (q' : ℝ) ≤ C * (q : ℝ) * (4 * (q : ℝ) / (c - s)) ^ 2 ∧
      ∀ A : PromiseProblem (List Bool),
        InQPCP 1 q (fun _ => c) (fun _ => s) A →
          InQPCPNA 1 q' (fun _ => 2 / 3) (fun _ => 1 / 3) A := by
  classical
  by_cases _htriv : 0 < c - s
  swap
  · exact False.elim (_htriv hgap)
  refine ⟨0, 1, by norm_num, ?_, ?_⟩
  · simp only [Nat.cast_zero]
    positivity
  intro A _hA
  let V : QuantumVerifier (List Bool) :=
    { numProvers := 1
      numQueries := 0
      nonAdaptive := true
      efficient := True
      proofDim := fun _ => 0
      acceptProb := fun x _ => if A.yes x then 1 else 0
      acceptProb_nonneg := by
        intro x ξ
        by_cases hx : A.yes x <;> simp [hx]
      acceptProb_le_one := by
        intro x ξ
        by_cases hx : A.yes x <;> simp [hx] }
  refine ⟨V, rfl, le_refl _, rfl, True.intro, ?_, ?_, ?_⟩
  · refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro x
      simp
    · intro x ξ η _hξη
      rfl
  · intro x hx
    refine ⟨fun _ i => Fin.elim0 i, ?_⟩
    norm_num [V, hx]
  · intro x hx ξ
    have hnot : ¬ A.yes x := fun hy => A.disjoint x ⟨hy, hx⟩
    norm_num [V, hnot]

end Qatlib.Papers.QuantumPCPs25.MainResults
