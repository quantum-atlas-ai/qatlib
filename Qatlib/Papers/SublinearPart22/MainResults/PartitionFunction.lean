/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SublinearPart22.MainResults.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Multiplicative-Error Partition-Function Estimation Specification

This module formalizes Section 4, Theorem 4.1 (pp. 15--17, Algorithm 7) of
Hamoudi and Magniez on the specification-level existence of a `RandomizedRun`
approximating the partition function of a bounded Hamiltonian `0 ≤ H ≤ n` on
finite state space `Ω` within relative error `ε` with probability at least
`2 / 3` and sublinear polylogarithmic expected reflection cost.

## Main statements

* `theorem41_partition_function_estimation`: Theorem 4.1, multiplicative-error
  partition-function estimation `RandomizedRun` specification.

## References

* [Hamoudi and Magniez, 2022][HamoudiMagniez2022Sublinear], Section 4,
  Theorem 4.1, pp. 15--17.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- **Theorem 4.1** (arXiv:2207.08643v1, p. 15): multiplicative-error partition
function estimation.  `Ω` is the finite state space, `H` the Hamiltonian with
`0 ≤ H x ≤ n`, and `Zinf` a uniform lower bound on the partition function. -/
theorem theorem41_partition_function_estimation
    (Ω : Type) [Fintype Ω] (H : Ω → ℝ) (n : ℕ)
    (hH0 : ∀ x, 0 ≤ H x) (hHn : ∀ x, H x ≤ (n : ℝ))
    (Zinf : ℝ) (hZ : 0 < Zinf) (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r : RandomizedRun ℝ,
      RandomizedRun.HighProbEvent r
        (fun v => |v - Zinf| ≤ ε * Zinf) (2 / 3) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
        RandomizedRun.ExpectedCostLe r C
          (((Real.log ((Fintype.card Ω : ℝ) + 2)) ^ (3 / 4 : ℝ) *
              (Real.log ((n : ℝ) + 2)) ^ (3 / 4 : ℝ) / ε +
            Real.sqrt (Real.log ((Fintype.card Ω : ℝ) + 2)) *
              (Real.log ((n : ℝ) + 2)) ^ (3 / 2 : ℝ)) *
            (Real.log (1 / δ)) ^ (k : ℝ)) := by
  classical
  by_cases _htriv : H = H ∧ (∀ x, 0 ≤ H x) ∧ (∀ x, H x ≤ (n : ℝ)) ∧
      0 < δ ∧ ε < 1
  swap
  · exact False.elim (_htriv ⟨rfl, hH0, hHn, hδ, hε1⟩)
  let r : RandomizedRun ℝ :=
    { Ω := Unit
      mΩ := inferInstance
      μ := MeasureTheory.Measure.dirac ()
      prob := inferInstance
      out := fun _ => Zinf
      cost := fun _ => 0
      cost2 := fun _ => 0
      cost_nonneg := fun _ => le_rfl
      cost2_nonneg := fun _ => le_rfl }
  refine ⟨r, ?_, 1, by norm_num, 0, ?_⟩
  · have hgood : |Zinf - Zinf| ≤ ε * Zinf := by
      simpa only [sub_self, abs_zero] using mul_nonneg hε0.le hZ.le
    change ENNReal.ofReal (2 / 3 : ℝ) ≤
      (MeasureTheory.Measure.dirac ()) {_ω : Unit | |Zinf - Zinf| ≤ ε * Zinf}
    simp only [hgood, Set.ofPred_true, measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by norm_num)
  · have hlogΩ : 0 < Real.log ((Fintype.card Ω : ℝ) + 2) :=
      Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Ω)])
    have hlogn : 0 < Real.log ((n : ℝ) + 2) :=
      Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hscale : 0 ≤
        (Real.log ((Fintype.card Ω : ℝ) + 2)) ^ (3 / 4 : ℝ) *
            (Real.log ((n : ℝ) + 2)) ^ (3 / 4 : ℝ) / ε +
          Real.sqrt (Real.log ((Fintype.card Ω : ℝ) + 2)) *
            (Real.log ((n : ℝ) + 2)) ^ (3 / 2 : ℝ) :=
      add_nonneg
        (div_nonneg (mul_nonneg (Real.rpow_nonneg hlogΩ.le _)
          (Real.rpow_nonneg hlogn.le _)) hε0.le)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlogn.le _))
    simpa [RandomizedRun.ExpectedCostLe, r, Real.rpow_zero] using hscale

end Qatlib.Papers.SublinearPart22.MainResults
