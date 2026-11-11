/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardDefinitions
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberBridge
import Qatlib.Concepts.CoherentSim.ResetDiscard.Theorem13CorrectedHami

/-!
# Raw reset-and-discard identities and obstructions

This module identifies `ResetDiscardStep` with conjugation by the workspace corner and exhibits
its scale-dependent loss. `resetDiscardSegmentation_zero_obstruction` and
`resetDiscardSegmentation_one_step_obstruction` refute the proposed raw segmentation property,
clarifying the role of amplification in [BerryEtAl2015Taylor].

## Main statements

* `resetDiscardStep_encoding_scalar`: The scale factor in a raw encoded step.
* `resetDiscardSegmentation_one_step_obstruction`: Failure of the raw-step segmentation
  property.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

set_option autoImplicit false
namespace Qatlib.Concepts.CoherentSim.ResetDiscard
open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator

/-- Tensoring a system operator with the ancillary basis-state outer product equals its fiber
embedding. -/
theorem ancillaSystemOp_ket_eq_fiberEmbed {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (j₀ : J) (ρ : Matrix I I ℂ) :
    AncillaSystemOp (vecOuter (Qatlib.Foundations.PureStateMath.Ket j₀)) ρ=FiberEmbed j₀ ρ := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases ha : a=j₀ <;> by_cases hb : b=j₀ <;>
    simp [AncillaSystemOp, vecOuter, Qatlib.Foundations.PureStateMath.Ket, fiberEmbed_apply,
        ha, hb]

/-- Taking the reduced operator of a fiber embedding recovers the original system operator. -/
theorem reducedState_fiberEmbed {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (j₀ : J) (ρ : Matrix I I ℂ) :
    ReducedState (FiberEmbed j₀ ρ)=ρ := by
  ext i j
  simp [ReducedState, fiberEmbed_apply]

/-- A raw reset-and-discard step equals conjugation by the selected block corner of the
workspace. -/
theorem resetDiscardStep_eq_corner {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (W : Matrix (J × I) (J × I) ℂ)
    (j₀ : J) (ρ : Matrix I I ℂ) :
    ResetDiscardStep W j₀ ρ=BlockCorner W j₀*ρ*(BlockCorner W j₀)ᴴ := by
  let F := encodingFiber (I := I) j₀
  let P := FiberProjector (I := I) j₀
  have hp : Pᴴ=P := (isOrthogonalProjector_fiberProjector (I := I) j₀).2
  have hPF : P*W*F=F*BlockCorner W j₀ := by
    ext ⟨a,i⟩ j
    rw [fiberProjector_mul]
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.of_apply]
    dsimp [F]
    simp only [encodingFiber_apply]
    by_cases ha : a=j₀
    · subst a
      simp [BlockCorner, Prod.mk.injEq, ite_and]
    · simp [ha, BlockCorner]
  rw [ResetDiscardStep, ancillaSystemOp_ket_eq_fiberEmbed,
    ← encodingFiber_mul_mul_conjTranspose]
  have he : P*(W*(F*ρ*Fᴴ)*Wᴴ)*P=(P*W*F)*ρ*(P*W*F)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hp]
    simp only [Matrix.mul_assoc]
  change ReducedState (P*(W*(F*ρ*Fᴴ)*Wᴴ)*P)=_
  rw [he, hPF]
  rw [Matrix.conjTranspose_mul]
  have he' : (F*BlockCorner W j₀)*ρ*((BlockCorner W j₀)ᴴ*Fᴴ)=
      F*(BlockCorner W j₀*ρ*(BlockCorner W j₀)ᴴ)*Fᴴ := by simp only [Matrix.mul_assoc]
  rw [he', encodingFiber_mul_mul_conjTranspose, reducedState_fiberEmbed]

/-- For a scale-`s` block encoding of `X`, the raw step equals `s⁻²` times conjugation by `X`. -/
theorem resetDiscardStep_encoding_scalar {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (W : Matrix (J × I) (J × I) ℂ)
    (j₀ : J) (X : Matrix I I ℂ) (s : ℝ) (hW : IsBlockEncoding W j₀ X s)
    (ρ : Matrix I I ℂ) :
    ResetDiscardStep W j₀ ρ=((s⁻¹^2 : ℝ) : ℂ) • (X*ρ*Xᴴ) := by
  rw [resetDiscardStep_eq_corner, hW.2.2, Matrix.conjTranspose_smul]
  simp only [RCLike.star_def, Complex.conj_ofReal]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← Complex.ofReal_mul, ← pow_two]

/-- For every real scale at least one, the one-dimensional identity has a block encoding with a
Boolean ancillary register. -/
theorem scaled_identity_encoding_exists (s : ℝ) (hs : 1 ≤ s) :
    ∃ W : Matrix (Bool × Unit) (Bool × Unit) ℂ,
      IsBlockEncoding W false (1 : Matrix Unit Unit ℂ) s := by
  have hspos : 0 < s := by linarith
  have hi : s⁻¹ ≤ 1 := (inv_le_one₀ hspos).mpr (by linarith)
  have hi2 : s⁻¹^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (inv_nonneg.mpr hspos.le) hi 2
  let v : QState Bool := fun b => if b then (Real.sqrt (1-s⁻¹^2) : ℂ) else (s⁻¹ : ℂ)
  have hv : ∑ b : Bool, ‖v b‖^2=1 := by
    rw [Fintype.sum_bool]
    simp only [v, if_pos rfl, if_neg Bool.false_ne_true,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1-s⁻¹^2)]
    rw [abs_of_pos hspos]
    ring
  obtain ⟨A,hA,hcol⟩ := Qatlib.Concepts.CoherentSim.ResetDiscard.existsUnitaryColumn false v hv
  refine ⟨TensorGate A (1 : Matrix Unit Unit ℂ), tensorGate_unitary hA (Submonoid.one_mem _),
      hspos, ?_⟩
  ext i j
  simp [BlockCorner, TensorGate, hcol, v]

/-- The proposed raw reset-and-discard segmentation property is false in universe zero. -/
theorem resetDiscardSegmentation_zero_obstruction : ¬ResetDiscardSegmentation.{0,0} := by
  intro h
  have hU : (-1 : Matrix Unit Unit ℂ) ∈ Matrix.unitaryGroup Unit ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simp
  have hW : IsBlockEncoding (-1 : Matrix (Unit × Unit) (Unit × Unit) ℂ)
      () (-1 : Matrix Unit Unit ℂ) 1 := by
    refine ⟨?_, by norm_num, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      simp
    · ext i j
      simp [BlockCorner]
  have hρ : (1 : Matrix Unit Unit ℂ).PosSemidef := Matrix.PosSemidef.one
  have htrace : Matrix.trace (1 : Matrix Unit Unit ℂ)=1 := by simp [Matrix.trace]
  have hh := h (Unit) (Unit) (-1) () (-1) (-1) 1 0 1 0 hW hU
    (by simp) (by norm_num) (by norm_num) (by norm_num) 1 hρ htrace
  simp only [Function.iterate_zero, id_eq, pow_zero,
    Matrix.conjTranspose_neg, Matrix.conjTranspose_one, Matrix.mul_neg,
    Matrix.mul_one, Nat.cast_zero] at hh
  norm_num at hh
  have hz : Matrix.traceNorm (2 : Matrix Unit Unit ℂ)=0 :=
    le_antisymm hh (Matrix.traceNorm_nonneg _)
  have he := (Matrix.traceNorm_zero_iff _).mp hz
  have hv := congrArg (fun A : Matrix Unit Unit ℂ => A () ()) he
  norm_num [Matrix.ofNat_apply] at hv

/-- The proposed raw reset-and-discard segmentation property also fails in a one-step instance
in universe zero. -/
theorem resetDiscardSegmentation_one_step_obstruction : ¬ResetDiscardSegmentation.{0,0} := by
  intro h
  obtain ⟨W,hW⟩ := scaled_identity_encoding_exists 2 (by norm_num)
  have hU : (1 : Matrix Unit Unit ℂ) ∈ Matrix.unitaryGroup Unit ℂ := Submonoid.one_mem _
  have hh := h Bool Unit W false 1 1 2 0 0 1 hW hU
    (by simp) (by norm_num) (by norm_num) (by norm_num)
    (1 : Matrix Unit Unit ℂ) Matrix.PosSemidef.one (by simp [Matrix.trace])
  simp only [Function.iterate_one, pow_one,
    Matrix.conjTranspose_one, Matrix.mul_one] at hh
  rw [resetDiscardStep_encoding_scalar W false 1 2 hW 1] at hh
  simp only [Matrix.conjTranspose_one, Matrix.mul_one] at hh
  norm_num at hh
  have hz := le_antisymm hh (Matrix.traceNorm_nonneg _)
  have he := (Matrix.traceNorm_zero_iff _).mp hz
  have hv := congrArg (fun A : Matrix Unit Unit ℂ => A () ()) he
  norm_num [Matrix.smul_apply, Matrix.one_apply] at hv

end Qatlib.Concepts.CoherentSim.ResetDiscard
