/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Coherent unitary square-root chains

This module packages the existence of successive unitary square roots with a quantitative
approach to identity. `UnitarySqrtChainSpec` requires each term to square to its predecessor and
bounds its distance from identity by `π / 2^j`, supplying the square-root data used in
multi-controlled synthesis [BarencoEtAl1995].

## Main statements

* `unitary_sqrt_chain_spec`: every unitary matrix on a nonempty finite index type possesses such
  a chain.

## References

* [Barenco et al., 1995, Section 7][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


namespace Qatlib.Concepts.CircuitImpl.SqrtApprox

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Every unitary matrix on a nonempty finite index type possesses a sequence starting at that
matrix, with each term unitary, each successor squaring to its predecessor, and distance
from identity at most `π / 2^j`. -/
def UnitarySqrtChainSpec : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (U : Matrix I I ℂ), U ∈ Matrix.unitaryGroup I ℂ →
    ∃ Vseq : ℕ → Matrix I I ℂ,
      Vseq 0 = U ∧
      (∀ j, Vseq j ∈ Matrix.unitaryGroup I ℂ) ∧
      (∀ j, Vseq (j + 1) * Vseq (j + 1) = Vseq j) ∧
      (∀ j, ‖(Vseq j - 1 : Matrix I I ℂ)‖ ≤ Real.pi / (2 ^ j : ℝ))

/-- Every unitary matrix on a nonempty finite index type possesses the coherent square-root
chain specified by `UnitarySqrtChainSpec`. -/
theorem unitary_sqrt_chain_spec : UnitarySqrtChainSpec := by
  intro I _ _ _ U hU
  letI : CStarAlgebra (Matrix I I ℂ) := {}
  letI : ContinuousFunctionalCalculus ℂ (Matrix I I ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have hu : U ∈ unitary (Matrix I I ℂ) := hU
  have hn : IsStarNormal U := isStarNormal_of_mem_unitary hu
  let f (j : ℕ) (z : ℂ) := Complex.exp (((z.arg / 2 ^ j : ℝ) : ℂ) * Complex.I)
  have hf (j : ℕ) : ContinuousOn (f j) (spectrum ℂ U) := U.finite_spectrum.continuousOn _
  refine ⟨fun j => cfc (f j) U, ?_, ?_, ?_, ?_⟩
  · calc
      cfc (f 0) U = cfc (id : ℂ → ℂ) U := by
        apply cfc_congr
        intro z hz
        have hnorm : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary hu hz
        simpa only [f, pow_zero, div_one, hnorm, Complex.ofReal_one, one_mul] using!
          Complex.norm_mul_exp_arg_mul_I z
      _ = U := cfc_id ℂ U hn
  · intro j
    apply (cfc_unitary_iff (f j) U hn (hf j)).mpr
    intro z _
    have hnorm : ‖f j z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    calc
      star (f j z) * f j z = (Complex.normSq (f j z) : ℂ) :=
        (Complex.normSq_eq_conj_mul_self (z := f j z)).symm
      _ = 1 := by rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
  · intro j
    rw [← cfc_mul (f (j + 1)) (f (j + 1)) U (hf _) (hf _)]
    apply cfc_congr
    intro z _
    dsimp only [f]
    rw [← Complex.exp_add]
    congr 1
    have hp : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    rw [pow_succ]
    field_simp
    ring
  · intro j
    rw [← cfc_const_one ℂ U hn, ← cfc_sub (f j) (fun _ : ℂ => 1) U (hf j)
      continuousOn_const]
    apply norm_cfc_le (by positivity)
    intro z _
    calc
      ‖f j z - 1‖ ≤ ‖z.arg / (2 ^ j : ℝ)‖ := by
        simpa only [f, mul_comm] using!
          (Real.norm_exp_I_mul_ofReal_sub_one_le (x := z.arg / (2 ^ j : ℝ)))
      _ = |z.arg| / (2 ^ j : ℝ) := by
        rw [Real.norm_eq_abs, abs_div,
          abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j)]
      _ ≤ _ := div_le_div_of_nonneg_right (Complex.abs_arg_le_pi z) (by positivity)

end Qatlib.Concepts.CircuitImpl.SqrtApprox
