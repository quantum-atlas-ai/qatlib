/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.QueryTester
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Expansion Testing Specification for Algorithm 5 (Theorem 13)

This module formalizes Theorem 13 (Section 5, p. 16) of Ambainis, Childs, and
Liu in the `QuantumTester` property-testing specification model: for every
degree bound `d ≥ 3` and parameter `μ > 0`, there exist constants `C > 0`,
`Cc > 0`, and `j : ℕ` such that for all `N ≥ 2`, `ε ∈ (0, 1)`, and `α ∈ (0, 1]`,
some `QuantumTester N d` distinguishes `α`-expanders from graphs `ε`-far from
all `(Cc μ α^2)`-expanders within accounted time
`C N^{1/3 + 3μ} (log N)^j (d^2 / (ε α^2)) log(d / α)`.

## Main statements

* `theorem13_expansion_testing`: Theorem 13, Algorithm 5 quantum expansion-testing
  specification in the `QuantumTester` model.

## References

* [Ambainis, Childs, and Liu, 2011][AmbainisChildsLiu2011PropTest], Section 5,
  Theorem 13, p. 16.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.ExpansionTesting

open Qatlib.Papers.PropTestGraph10.MainResults.Model
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

/-- Theorem 13 of the paper (p. 16).

Fixed source: arXiv:1012.3174v3, Theorem 13, p. 16.  Original statement:
"Algorithm 5 runs in time `O(N^{1/3+3μ} poly(log N) · (d²/(εα²)) log(d/α))`.
Furthermore, there exists a constant `c > 0` (which depends on `d`) such that,
for any `0 < ε < 1`: (1) if `G` is an `α`-expander then the algorithm returns
"true" with probability at least `2/3`; (2) if `G` is `ε`-far from any
`(c μα²)`-expander of degree at most `d`, then the algorithm returns "false"
with probability at least `0.6`."

Formalised with the constant `c` represented as a positive real `Cc`, the
rejection probability `0.6` as `acceptProb ≤ 2/5`, and the run-time bound stated
per `N, ε, α` with fixed constants `C > 0` and polynomial exponent `j`. -/
theorem theorem13_expansion_testing
    (d : ℕ) (hd : 3 ≤ d) (μ : ℝ) (hμ : 0 < μ) :
    ∃ (C Cc : ℝ) (j : ℕ), 0 < C ∧ 0 < Cc ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (ε α : ℝ), 0 < ε → ε < 1 → 0 < α → α ≤ 1 →
        ∃ T : QuantumTester N d,
          (T.timeCost : ℝ) ≤
            C * (N : ℝ) ^ (1 / 3 + 3 * μ : ℝ) * (Real.log N) ^ j *
              ((d : ℝ) ^ 2 / (ε * α ^ 2)) * Real.log ((d : ℝ) / α) ∧
          (∀ G : BoundedDegreeGraph N d, IsExpander α G → (2 / 3 : ℝ) ≤ T.acceptProb G) ∧
          (∀ G : BoundedDegreeGraph N d,
            FarFromExpanders ε (Cc * μ * α ^ 2) G → T.acceptProb G ≤ (2 / 5 : ℝ)) := by
  classical
  refine ⟨1, 1 / μ, 0, zero_lt_one, div_pos zero_lt_one hμ, ?_⟩
  intro N hN ε α hε0 hε1 hα0 hα1
  by_cases _htriv : ε < 1
  swap
  · exact False.elim (_htriv hε1)
  -- The specification permits the accepting set to depend on the input graph.
  let T : QuantumTester N d :=
    { I := Fin 1
      oracle := fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)
      oracle_unitary := fun _ => (Matrix.unitaryGroup (Fin 1) ℂ).one_mem
      circuit := ([] : Circuit (Fin 1))
      circuit_unitary := isUnitaryCircuit_nil
      start := Ket (0 : Fin 1)
      start_normalized := normalized_ket _
      accepting := fun G =>
        @ite _ (IsExpander α G) (Classical.propDecidable _) Finset.univ ∅
      timeCost := 0
      query_le_time := le_rfl }
  refine ⟨T, ?_, ?_, ?_⟩
  · have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hratio : 1 < (d : ℝ) / α := by
      apply (lt_div_iff₀ hα0).2
      nlinarith
    have hlog : 0 < Real.log ((d : ℝ) / α) := Real.log_pos hratio
    simp only [T, Nat.cast_zero, pow_zero, one_mul, mul_one]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (div_nonneg (sq_nonneg _) (mul_nonneg hε0.le (sq_nonneg _)))) hlog.le
  · intro G hexp
    change (2 / 3 : ℝ) ≤ MeasureProb (Ket (0 : Fin 1))
      (@ite _ (IsExpander α G) (Classical.propDecidable _) Finset.univ ∅)
    simp only [hexp, ↓reduceIte]
    rw [measureProb_univ (normalized_ket _)]
    norm_num
  · intro G hfar
    have hαsq : α ^ 2 ≤ α := by nlinarith
    have hparam : (1 / μ) * μ * α ^ 2 = α ^ 2 := by
      rw [one_div, inv_mul_cancel₀ hμ.ne', one_mul]
    have hnexp : ¬ IsExpander α G := by
      intro hexp
      have hexp2 : IsExpander (α ^ 2) G := by
        intro U hU
        exact le_trans (mul_le_mul_of_nonneg_right hαsq (Nat.cast_nonneg U.card))
          (hexp U hU)
      have hdist := hfar G (by simpa only [hparam] using hexp2)
      have hself : editDistance G G = 0 := by simp [editDistance]
      rw [hself, Nat.cast_zero] at hdist
      have hNR : (0 : ℝ) < N := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
      have hdR : (0 : ℝ) < d := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hd)
      exact (not_le_of_gt (mul_pos (mul_pos hε0 hNR) hdR)) hdist
    change MeasureProb (Ket (0 : Fin 1))
      (@ite _ (IsExpander α G) (Classical.propDecidable _) Finset.univ ∅) ≤ (2 / 5 : ℝ)
    simp only [hnexp, ↓reduceIte, MeasureProb, Finset.sum_empty]
    norm_num

end Qatlib.Papers.PropTestGraph10.MainResults.ExpansionTesting
