/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.TwirlingCounterexample
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.HspRecovery.Reduction.OracleTwirling

/-!
# A two-point counterexample for twirling recovery

This module proves `TwirlingCounterexample` using the constant matrix `sourcePlusDensity` on the
two-element group. The matrix is positive, has trace one, and is fixed by right twirling, yet
differs from the trivial-subgroup coset density.

The same input satisfies the projector conditions for both the trivial and full subgroups,
ruling out the uniform conversion asserted in the counterexample specification. See
[Watrous2018] for the mathematical background.

## Main statements

* `sourceTwirlingCounterexample`: establish the counterexample using the two-point density.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
open scoped ComplexOrder

namespace Qatlib.Concepts.HspRecovery.RecordExtract
open Matrix

/-- The two-point group consists of the multiplicative images of zero and one in `ZMod 2`. -/
private theorem twoPoint_univ : (Finset.univ : Finset SourceTwoPointGroup) =
    {Multiplicative.ofAdd (0 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)} := by
  ext x
  fin_cases x <;> decide

/-- The identity of the two-point group differs from the multiplicative image of one in `ZMod
2`. -/
private theorem twoPoint_ne : (1 : SourceTwoPointGroup) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by
  decide

/-- The multiplicative image of zero in `ZMod 2` is the group identity. -/
private theorem twoPoint_zero : Multiplicative.ofAdd (0 : ZMod 2) = (1 : SourceTwoPointGroup) := rfl

/-- The nonidentity element of the two-point group squares to the identity. -/
private theorem twoPoint_square : Multiplicative.ofAdd (1 : ZMod 2) *
    Multiplicative.ofAdd (1 : ZMod 2) = (1 : SourceTwoPointGroup) := by decide

/-- The constant two-point plus density is positive semidefinite. -/
private theorem plus_psd : sourcePlusDensity.PosSemidef := by
  have hp := (Matrix.posSemidef_vecMulVec_self_star
    (fun _ : SourceTwoPointGroup => (1 : ℂ))).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert hp using 1
  ext p q
  norm_num [sourcePlusDensity, Matrix.vecMulVec, Matrix.smul_apply]

/-- The two-point plus density has trace one. -/
private theorem plus_trace : sourcePlusDensity.trace = 1 := by
  simp [Matrix.trace, sourcePlusDensity]

/-- The fixed-space projector for the trivial subgroup of the two-point group is the identity
matrix. -/
private theorem bot_projector : sourceFixedProjector SourceTwoPointGroup ⊥ = 1 := by
  have hd : (↑(default : (⊥ : Subgroup SourceTwoPointGroup)) : SourceTwoPointGroup) = 1 :=
    Subgroup.mem_bot.mp (default : (⊥ : Subgroup SourceTwoPointGroup)).property
  ext p q
  simp [sourceFixedProjector, permMatrix, Matrix.one_apply, hd]

/-- The fixed-space projector for the full two-point group is the plus density. -/
private theorem top_projector : sourceFixedProjector SourceTwoPointGroup ⊤ = sourcePlusDensity := by
  classical
  letI : DecidableEq SourceTwoPointGroup := Classical.decEq _
  ext p q
  simp only [sourceFixedProjector, Matrix.smul_apply, Matrix.sum_apply, permMatrix,
    Matrix.of_apply, sourcePlusDensity]
  rw [Finset.sum_eq_single (⟨p * q⁻¹, by simp⟩ : (⊤ : Subgroup SourceTwoPointGroup))]
  · norm_num [mul_assoc]
  · intro h _ hne
    have hp : p ≠ h.val * q := by
      intro he
      apply hne
      apply Subtype.ext
      rw [he, mul_assoc, mul_inv_cancel, mul_one]
    simp [hp]
  · simp

/-- The two-point plus density is idempotent. -/
private theorem plus_square : sourcePlusDensity * sourcePlusDensity = sourcePlusDensity := by
  ext p q
  norm_num [Matrix.mul_apply, sourcePlusDensity, twoPoint_univ, twoPoint_ne]

/-- Right twirling fixes the two-point plus density. -/
private theorem plus_twirl : sourceRightTwirl SourceTwoPointGroup sourcePlusDensity =
    sourcePlusDensity := by
  classical
  letI : DecidableEq SourceTwoPointGroup := Classical.decEq _
  have hleft (g : SourceTwoPointGroup) :
      permMatrix (fun a => a * g) * sourcePlusDensity = sourcePlusDensity := by
    ext p q
    simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply, sourcePlusDensity]
    rw [Finset.sum_eq_single (p * g⁻¹)]
    · simp [mul_assoc]
    · intro k _ hk
      have hne : p ≠ k * g := by
        intro he
        apply hk
        rw [he, mul_assoc, mul_inv_cancel, mul_one]
      simp [hne]
    · simp
  have hright (g : SourceTwoPointGroup) :
      sourcePlusDensity * (permMatrix (fun a => a * g)).conjTranspose = sourcePlusDensity := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permMatrix, Matrix.of_apply,
      sourcePlusDensity]
    rw [Finset.sum_eq_single (q * g⁻¹)]
    · simp [mul_assoc]
    · intro k _ hk
      have hne : q ≠ k * g := by
        intro he
        apply hk
        rw [he, mul_assoc, mul_inv_cancel, mul_one]
      simp [hne]
    · simp
  simp only [sourceRightTwirl, hleft, hright, Finset.sum_const, Finset.card_univ]
  ext p q
  norm_num [Matrix.smul_apply, sourcePlusDensity, two_mul, Matrix.add_apply]

/-- The two-point plus density differs from the coset density of the trivial subgroup. -/
private theorem plus_ne_bot : sourcePlusDensity ≠ sourceCosetDensity SourceTwoPointGroup ⊥ := by
  intro h
  have he := congrFun (congrFun h (1 : SourceTwoPointGroup))
    (Multiplicative.ofAdd (1 : ZMod 2))
  norm_num [sourcePlusDensity, sourceCosetDensity, Subgroup.mem_bot] at he

/-- The coset density for the full two-point group equals the plus density. -/
private theorem top_density : sourceCosetDensity SourceTwoPointGroup ⊤ = sourcePlusDensity := by
  ext p q
  norm_num [sourceCosetDensity, sourcePlusDensity]

/-- The two-point plus density establishes `TwirlingCounterexample`: it is fixed by twirling and
satisfies the stated projector conditions without determining the subgroup coset density. -/
theorem sourceTwirlingCounterexample : TwirlingCounterexample := by
  have hb : sourceFixedProjector SourceTwoPointGroup ⊥ * sourcePlusDensity *
      sourceFixedProjector SourceTwoPointGroup ⊥ = sourcePlusDensity := by
    rw [bot_projector, Matrix.one_mul, Matrix.mul_one]
  have ht : sourceFixedProjector SourceTwoPointGroup ⊤ * sourcePlusDensity *
      sourceFixedProjector SourceTwoPointGroup ⊤ = sourcePlusDensity := by
    rw [top_projector, plus_square, plus_square]
  refine ⟨plus_psd, plus_trace, hb, plus_twirl, plus_ne_bot, ?_⟩
  rintro ⟨convert, hconvert⟩
  have hbot := hconvert ⊥ sourcePlusDensity plus_psd plus_trace hb
  have htop := hconvert ⊤ sourcePlusDensity plus_psd plus_trace ht
  apply plus_ne_bot
  exact top_density.symm.trans (htop.symm.trans hbot)

end Qatlib.Concepts.HspRecovery.RecordExtract
