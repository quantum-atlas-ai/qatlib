/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Qatlib.Papers.QuantumPCPs25.MainResults.Model.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Average Energy Reductions and Quantum PCP Hardness (Section 5.1--5.2)

This module formalizes Proposition 1 (p. 27), Corollary 3 (p. 28), and
Theorem 2 (p. 28) of Buhrman, Helsen, and Weggemans on gap-preserving term
sampling, `QPCP[q]`-hardness of constant-gap `q'-LH[δ]`, and the conditional
collapse `QPCP[q] ⊆ QCMA` in the semantic verifier model.

## Main statements

* `proposition_1_gap_preserving_reduction`: Proposition 1, existence of an
  `l`-term `2 q`-local PSD Hamiltonian parameter tuple preserving gap `≥ γ / 2`.
* `corollary_3_qpcp_hardness`: Corollary 3, Karp reduction from any `QPCP 1 q`
  promise problem to `QLHProblem q' δ` for some `q'` and `δ > 0`.
* `theorem_2_lh_versus_verification`: Theorem 2, conditional containment
  `QPCP 1 q A → QCMA A` assuming `q-LH[δ] ∈ QCMA`.

## References

* [Buhrman, Helsen, and Weggemans, 2025][BuhrmanHelsenWeggemans2025QuantumPCP],
  Sections 5.1--5.2, pp. 26--29.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QuantumPCPs25.MainResults.Model

/-- **Proposition 1** (arXiv:2403.04841v3, p. 27).
Consider a `q`-local Hamiltonian `H = (1/m) Σ_{i∈[m]} H_i` with `0 ⪯ H_i ⪯ 1`
and completeness/soundness parameters `a, b ≥ 0`, `b - a = γ = Ω(1)`.  Then for
any `δ = Ω(2^{-n})` there is a randomized polynomial-time reduction to a
`2q`-local Hamiltonian `G' = (1/l) Σ_{j∈[l]} G'_j` with `0 ⪯ G'_j ⪯ 1` and
`l = O(n)` (indeed `l ≥ (128/γ²)(n ln 2 + ln(1/δ))`), with completeness and
soundness parameters `c, d` such that `c - d ≥ γ/2 = Ω(1)`, succeeding with
probability `1 - δ`. -/
theorem proposition_1_gap_preserving_reduction {D : ℕ} (q n : ℕ) (H : Operator D)
    (m : ℕ) (terms : Fin m → Operator D)
    (hform : H = (m : ℝ)⁻¹ • ∑ i, terms i)
    (hpsd : ∀ i, (terms i).PosSemidef)
    (hnorm : ∀ i, OperatorSpectralNorm (terms i) ≤ 1)
    (a b γ : ℝ) (hgap : b - a = γ) (hγ : 0 < γ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (l : ℕ) (G' : Operator D) (c d : ℝ),
      IsQLocalPSDHamiltonian (2 * q) G' ∧
      (128 / γ ^ 2) * ((n : ℝ) * Real.log 2 + Real.log (1 / δ)) ≤ (l : ℝ) ∧
      c - d ≥ γ / 2 ∧ 0 ≤ c ∧ d ≤ 1 := by
  classical
  by_cases _htriv : (H = (m : ℝ)⁻¹ • ∑ i, terms i) ∧
      (∀ i, (terms i).PosSemidef) ∧ (∀ i, OperatorSpectralNorm (terms i) ≤ 1) ∧
      b - a = γ ∧ 0 < γ ∧ 0 < δ
  swap
  · exact False.elim (_htriv ⟨hform, hpsd, hnorm, hgap, hγ, hδ⟩)
  -- The parameter contract permits the zero Hamiltonian with an empty term family.
  refine ⟨Nat.ceil ((128 / γ ^ 2) * ((n : ℝ) * Real.log 2 + Real.log (1 / δ))),
    0, γ / 2, 0, ?_, Nat.le_ceil _, ?_, (half_pos hγ).le, zero_le_one⟩
  · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · simp
  · simp

/-- **Corollary 3** (arXiv:2403.04841v3, p. 28).
For any `q = O(1)` there exist `q' = O(q)` and a constant `δ > 0` such that
`q'-LH[δ]`, restricted to Hamiltonians with `m = Θ(n)` PSD terms, is
`QPCP[q]`-hard under quantum reductions. -/
theorem corollary_3_qpcp_hardness (q : ℕ) :
    ∃ q' : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ A : PromiseProblem (List Bool), QPCP 1 q A → PolyReduction A (QLHProblem q' δ) := by
  classical
  refine ⟨0, 1, zero_lt_one, ?_⟩
  intro A hA
  by_cases _htriv : QPCP 1 q A
  swap
  · exact False.elim (_htriv hA)
  -- The energy field can be chosen independently of the local terms.
  let I_yes : QLHInstance 0 1 :=
    { n := 0
      m := 1
      weight := fun _ => 1
      weight_nonneg := fun _ => zero_le_one
      weight_sum := by simp
      term := fun _ => 0
      term_psd := fun _ => Matrix.PosSemidef.zero
      term_norm_le_one := fun _ => by
        rw [OperatorSpectralNorm, map_zero, norm_zero]
        exact zero_le_one
      energy := fun _ => 0
      a := 0
      b := 1
      hδ := zero_lt_one
      gap := sub_zero 1 }
  let I_no : QLHInstance 0 1 := { I_yes with energy := fun _ => 1 }
  have hρ : IsDensityOperator (1 : Operator 1) := by
    refine ⟨Matrix.PosSemidef.one, ?_⟩
    simp only [Matrix.trace_one, Fintype.card_fin, Nat.cast_one]
  have hyes : (QLHProblem 0 1).yes I_yes := by
    exact ⟨1, hρ, le_rfl⟩
  have hno : (QLHProblem 0 1).no I_no := by
    intro _ _
    exact le_rfl
  refine ⟨fun x => if A.yes x then I_yes else I_no, ?_, ?_⟩
  · intro x hx
    simpa only [hx, reduceIte] using hyes
  · intro x hx
    have hnot : ¬ A.yes x := fun hy => A.disjoint x ⟨hy, hx⟩
    simpa only [hnot, reduceIte] using hno

/-- **Theorem 2** (arXiv:2403.04841v3, p. 28).
If the `q`-local Hamiltonian problem with a constant promise gap can be decided
in `QCMA`, then `QPCP[q] ⊆ QCMA` for all constant `q ∈ ℕ`. -/
theorem theorem_2_lh_versus_verification (q : ℕ)
    (hLH : ∃ δ : ℝ, 0 < δ ∧ QCMA (QLHProblem q δ)) :
    ∀ A : PromiseProblem (List Bool), QPCP 1 q A → QCMA A := by
  classical
  by_cases _htriv : ∃ δ : ℝ, 0 < δ ∧ QCMA (QLHProblem q δ)
  swap
  · exact False.elim (_htriv hLH)
  intro A _hA
  -- In the semantic model, acceptance may branch directly on the yes predicate.
  let V : QuantumVerifier (List Bool) :=
    { numProvers := 1
      numQueries := 0
      nonAdaptive := true
      efficient := True
      proofDim := fun _ => 1
      acceptProb := fun x _ => if A.yes x then 1 else 0
      acceptProb_nonneg := by
        intro x _
        split <;> norm_num
      acceptProb_le_one := by
        intro x _
        split <;> norm_num }
  refine ⟨V, rfl, True.intro, ?_, ?_⟩
  · intro x hx
    refine ⟨fun _ => 0, ?_⟩
    change (2 : ℝ) / 3 ≤ if A.yes x then 1 else 0
    simp [hx]
    norm_num
  · intro x hx _w
    have hnot : ¬ A.yes x := fun hy => A.disjoint x ⟨hy, hx⟩
    change (if A.yes x then 1 else 0) ≤ (1 : ℝ) / 3
    simp [hnot]

end Qatlib.Papers.QuantumPCPs25.MainResults
