/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Qubitization walks and invariant planes

`QubitizationWalk` is a product of a fiber reflection and its unitary conjugate. For a Hermitian
block encoding, `qubitization_invariant_subspace` constructs an orthonormal invariant plane from
an interior eigenvalue, and `qubitization_amplifies_fiber` computes the projected walk action.
See [LowChuang2019] for background.

## Main statements

* `qubitization_invariant_subspace`: A normalized eigenvector of the Hermitian encoded matrix
  with `|x| < 1` yields an orthonormal invariant plane on which the walk has diagonal
  coefficient `2 * x^2 - 1` and off-diagonal coefficients `±2 * x * y`, where `y > 0` and `x^2 +
  y^2 = 1`. See [LowChuang2019].
* `qubitization_amplifies_fiber`: For an eigenvector of the Hermitian encoded matrix with
  eigenvalue `x`, projecting one walk step from its distinguished fiber multiplies the embedded
  vector by `2 * x^2 - 1`.

## References

* [Low and Chuang, 2019][LowChuang2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.AmplitudeCore.InvFreePhase

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- Complex conjugation fixes a real scalar embedded in `ℂ`. -/
theorem starRingEnd_ofReal (r : ℝ) : (starRingEnd ℂ) ((r : ℂ)) = ((r : ℂ)) := by simp

/-- Scaling the first argument of `Inner` conjugates the scalar. -/
theorem inner_smul_left (c : ℂ) (ψ φ : QState I) :
    Inner (c • ψ) φ = (starRingEnd ℂ) c * Inner ψ φ := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Scaling the second argument of `Inner` multiplies the inner product by that scalar. -/
theorem inner_smul_right (c : ℂ) (ψ φ : QState I) :
    Inner ψ (c • φ) = c * Inner ψ φ := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- The state inner product distributes over subtraction in its first argument. -/
theorem inner_sub_left (ψ φ χ : QState I) :
    Inner (ψ - φ) χ = Inner ψ χ - Inner φ χ := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply, smul_eq_mul, map_sub]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- The state inner product distributes over subtraction in its second argument. -/
theorem inner_sub_right (ψ φ χ : QState I) :
    Inner ψ (φ - χ) = Inner ψ φ - Inner ψ χ := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Moving a matrix action from the first argument of the state inner product to the second
replaces it by its conjugate transpose. -/
theorem inner_mulVec_left (M : Matrix I I ℂ) (ψ φ : QState I) :
    Inner (M *ᵥ ψ) φ = Inner ψ (Mᴴ *ᵥ φ) := by
  have hL : ∀ i, (starRingEnd ℂ) ((M *ᵥ ψ) i) * φ i
      = ∑ j, (starRingEnd ℂ) (M i j) * ((starRingEnd ℂ) (ψ j)) * φ i := by
    intro i
    rw [show (M *ᵥ ψ) i = ∑ j, M i j * ψ j from by simp [Matrix.mulVec, dotProduct]]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by rw [map_mul]
  have hR : ∀ j, (starRingEnd ℂ) (ψ j) * ((Mᴴ *ᵥ φ) j)
      = ∑ i, (starRingEnd ℂ) (ψ j) * ((starRingEnd ℂ) (M i j) * φ i) := by
    intro j
    rw [show (Mᴴ *ᵥ φ) j = ∑ i, (starRingEnd ℂ) (M i j) * φ i from by
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, RCLike.star_def]]
    rw [Finset.mul_sum]
  rw [inner_apply, inner_apply]
  refine (Finset.sum_congr rfl fun i _ => hL i).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (Finset.sum_congr rfl fun i _ => by ring).trans (hR j).symm

/-- The fiber projector can be moved between the two arguments of the state inner product. -/
theorem inner_fiberProjector_left (j₀ : J) (χ φ : QState (J × I)) :
    Inner (FiberProjector j₀ *ᵥ χ) φ = Inner χ (FiberProjector j₀ *ᵥ φ) := by
  rw [inner_mulVec_left, fiberProjector_hermitian]

/-- The walk matrix `FiberReflection j₀ * V * FiberReflection j₀ * Vᴴ`. -/
noncomputable def QubitizationWalk (V : Matrix (J × I) (J × I) ℂ) (j₀ : J) :
    Matrix (J × I) (J × I) ℂ :=
  FiberReflection j₀ * V * FiberReflection j₀ * Vᴴ

/-- The qubitization walk is unitary whenever `V` is unitary. -/
theorem qubitizationWalk_unitary {V : Matrix (J × I) (J × I) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (J × I) ℂ) (j₀ : J) :
    QubitizationWalk V j₀ ∈ Matrix.unitaryGroup (J × I) ℂ := by
  have hVct : Vᴴ ∈ Matrix.unitaryGroup (J × I) ℂ := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hV
    rw [Matrix.star_eq_conjTranspose] at h
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact h
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ (fiberReflection_unitary j₀) hV)
      (fiberReflection_unitary j₀)) hVct

/-- The action of the qubitization walk expands into the four successive matrix actions defining
it. -/
theorem qubitizationWalk_mulVec (V : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (χ : QState (J × I)) :
    QubitizationWalk V j₀ *ᵥ χ
      = FiberReflection j₀ *ᵥ (V *ᵥ (FiberReflection j₀ *ᵥ (Vᴴ *ᵥ χ))) := by
  rw [QubitizationWalk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- A normalized eigenvector of the Hermitian encoded matrix with `|x| < 1` yields an
orthonormal invariant plane on which the walk has diagonal coefficient `2 * x^2 - 1` and
off-diagonal coefficients `±2 * x * y`, where `y > 0` and `x^2 + y^2 = 1`. See
[LowChuang2019]. -/
theorem qubitization_invariant_subspace
    (V : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (hV : IsBlockEncoding V j₀ A 1) (hA : Aᴴ = A)
    (ψ : QState I) (hψ : Normalized ψ)
    (x : ℝ) (hx : A *ᵥ ψ = ((x : ℝ) : ℂ) • ψ) (hx1 : |x| < 1) :
    ∃ (ψ₀ ψ₁ : QState (J × I)) (y : ℝ),
      Normalized ψ₀ ∧ Normalized ψ₁ ∧ Inner ψ₀ ψ₁ = 0 ∧
      QubitizationWalk V j₀ *ᵥ ψ₀
        = (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₀ - (((2 * x * y : ℝ)) : ℂ) • ψ₁ ∧
      QubitizationWalk V j₀ *ᵥ ψ₁
        = (((2 * x * y : ℝ)) : ℂ) • ψ₀ + (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₁ ∧
      0 < y ∧ x ^ 2 + y ^ 2 = 1 := by
  have hx2lt : x ^ 2 < 1 := by nlinarith [abs_lt.mp hx1]
  set y : ℝ := Real.sqrt (1 - x ^ 2) with hydef
  have hy : 0 < y := Real.sqrt_pos.mpr (by nlinarith [hx2lt])
  have hy2 : y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith [hx2lt])
  have hy2c : (y : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by
    exact_mod_cast hy2
  have hyneq : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  set ψ₀ : QState (J × I) := TensorState (Ket j₀) ψ with hψ₀def
  set φ : QState (J × I) := V *ᵥ ψ₀ - ((x : ℝ) : ℂ) • ψ₀ with hφdef
  set φ' : QState (J × I) := Vᴴ *ᵥ ψ₀ - ((x : ℝ) : ℂ) • ψ₀ with hφ'def
  set ψ₁ : QState (J × I) := (((y : ℝ) : ℂ))⁻¹ • φ with hψ₁def

  have hψ₀ : Normalized ψ₀ := normalized_tensorState (normalized_ket j₀) hψ
  have hPfix : FiberProjector j₀ *ᵥ ψ₀ = ψ₀ := fiberProjector_mulVec_tensorState_ket j₀ ψ
  have hcorn : BlockCorner V j₀ = A := by simpa using hV.2.2
  have hPVP : FiberProjector j₀ * (V * FiberProjector j₀) = FiberEmbed j₀ A := by
    rw [fiberProjector_mul_mul_corner, hcorn]
  have hPVctP : FiberProjector j₀ * (Vᴴ * FiberProjector j₀) = FiberEmbed j₀ A := by
    have h1 : (FiberProjector j₀ * (V * FiberProjector j₀))ᴴ
        = FiberProjector j₀ * (Vᴴ * FiberProjector j₀) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, fiberProjector_hermitian,
        Matrix.mul_assoc]
    rw [← h1, hPVP, fiberEmbed_conjTranspose, hA]
  have hPVψ₀ : FiberProjector j₀ *ᵥ (V *ᵥ ψ₀) = ((x : ℝ) : ℂ) • ψ₀ := by
    conv_lhs => rw [← hPfix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
    rw [hPVP, fiberEmbed_mulVec_tensorState_ket, hx, tensorState_smul_ket_right]
  have hPVctψ₀ : FiberProjector j₀ *ᵥ (Vᴴ *ᵥ ψ₀) = ((x : ℝ) : ℂ) • ψ₀ := by
    conv_lhs => rw [← hPfix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
    rw [hPVctP, fiberEmbed_mulVec_tensorState_ket, hx, tensorState_smul_ket_right]

  have h00 : Inner ψ₀ ψ₀ = 1 := inner_self_eq_one hψ₀
  have h0V : Inner ψ₀ (V *ᵥ ψ₀) = ((x : ℝ) : ℂ) := by
    calc Inner ψ₀ (V *ᵥ ψ₀) = Inner (FiberProjector j₀ *ᵥ ψ₀) (V *ᵥ ψ₀) := by rw [hPfix]
      _ = Inner ψ₀ (FiberProjector j₀ *ᵥ (V *ᵥ ψ₀)) := inner_fiberProjector_left _ _ _
      _ = Inner ψ₀ (((x : ℝ) : ℂ) • ψ₀) := by rw [hPVψ₀]
      _ = ((x : ℝ) : ℂ) * Inner ψ₀ ψ₀ := inner_smul_right _ _ _
      _ = ((x : ℝ) : ℂ) := by rw [h00, mul_one]
  have hV0 : Inner (V *ᵥ ψ₀) ψ₀ = ((x : ℝ) : ℂ) := by
    calc Inner (V *ᵥ ψ₀) ψ₀ = Inner (V *ᵥ ψ₀) (FiberProjector j₀ *ᵥ ψ₀) := by rw [hPfix]
      _ = Inner (FiberProjector j₀ *ᵥ (V *ᵥ ψ₀)) ψ₀ := (inner_fiberProjector_left _ _ _).symm
      _ = Inner (((x : ℝ) : ℂ) • ψ₀) ψ₀ := by rw [hPVψ₀]
      _ = (starRingEnd ℂ) (((x : ℝ) : ℂ)) * Inner ψ₀ ψ₀ := inner_smul_left _ _ _
      _ = ((x : ℝ) : ℂ) := by rw [starRingEnd_ofReal, h00, mul_one]
  have hφφ : Inner φ φ = ((1 - x ^ 2 : ℝ) : ℂ) := by
    have hVV : Inner (V *ᵥ ψ₀) (V *ᵥ ψ₀) = 1 :=
      (inner_applyGate hV.1 ψ₀ ψ₀).trans h00
    rw [hφdef, inner_sub_left, inner_sub_right, inner_sub_right, hVV,
      inner_smul_right, hV0, inner_smul_left, h0V, inner_smul_left, inner_smul_right,
      h00, starRingEnd_ofReal]
    push_cast
    ring

  have horth : Inner ψ₀ ψ₁ = 0 := by
    rw [hψ₁def, inner_smul_right, hφdef, inner_sub_right, h0V, inner_smul_right, h00]
    simp
  have hψ₁norm : Normalized ψ₁ := by
    rw [normalized_iff_inner_self, hψ₁def, inner_smul_left, ← Complex.ofReal_inv,
      starRingEnd_ofReal, inner_smul_right, hφφ]
    push_cast
    rw [show (1 : ℂ) - (x : ℂ) ^ 2 = (y : ℂ) ^ 2 from hy2c.symm]
    field_simp

  have hVψ₀ : V *ᵥ ψ₀ = ((x : ℝ) : ℂ) • ψ₀ + φ := by
    rw [hφdef]
    exact (add_sub_cancel _ _).symm
  have hVctψ₀ : Vᴴ *ᵥ ψ₀ = ((x : ℝ) : ℂ) • ψ₀ + φ' := by
    rw [hφ'def]
    exact (add_sub_cancel _ _).symm
  have hφeq : φ = ((y : ℝ) : ℂ) • ψ₁ := by
    rw [hψ₁def, smul_smul, mul_inv_cancel₀ hyneq, one_smul]
  have hVψ₀₁ : V *ᵥ ψ₀ = ((x : ℝ) : ℂ) • ψ₀ + ((y : ℝ) : ℂ) • ψ₁ := by
    rw [hVψ₀, hφeq]
  have hVVct : ∀ χ : QState (J × I), V *ᵥ (Vᴴ *ᵥ χ) = χ := fun χ => by
    have h1 : V * Vᴴ = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff).mp hV.1
      rwa [Matrix.star_eq_conjTranspose] at h
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hVctV : ∀ χ : QState (J × I), Vᴴ *ᵥ (V *ᵥ χ) = χ := fun χ => by
    have h1 : Vᴴ * V = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff').mp hV.1
      rwa [Matrix.star_eq_conjTranspose] at h
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

  have hPφ : FiberProjector j₀ *ᵥ φ = 0 := by
    rw [hφdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hPVψ₀, hPfix, sub_self]
  have hPφ' : FiberProjector j₀ *ᵥ φ' = 0 := by
    rw [hφ'def, Matrix.mulVec_sub, Matrix.mulVec_smul, hPVctψ₀, hPfix, sub_self]
  have hRψ₀ : FiberReflection j₀ *ᵥ ψ₀ = ψ₀ := by
    rw [fiberReflection_mulVec, hPfix]
    module
  have hRφ : FiberReflection j₀ *ᵥ φ = -φ := by
    rw [fiberReflection_mulVec, hPφ, smul_zero, zero_sub]
  have hRφ' : FiberReflection j₀ *ᵥ φ' = -φ' := by
    rw [fiberReflection_mulVec, hPφ', smul_zero, zero_sub]
  have hRVψ₀ : FiberReflection j₀ *ᵥ (V *ᵥ ψ₀)
      = (2 : ℂ) • (((x : ℝ) : ℂ) • ψ₀) - V *ᵥ ψ₀ := by
    rw [fiberReflection_mulVec, hPVψ₀]

  have hA1 : FiberReflection j₀ *ᵥ (Vᴴ *ᵥ ψ₀)
      = (2 : ℂ) • (((x : ℝ) : ℂ) • ψ₀) - Vᴴ *ᵥ ψ₀ := by
    rw [hVctψ₀, Matrix.mulVec_add, Matrix.mulVec_smul, hRψ₀, hRφ', hφ'def]
    module
  have hA2 : V *ᵥ (FiberReflection j₀ *ᵥ (Vᴴ *ᵥ ψ₀))
      = (2 : ℂ) • (((x : ℝ) : ℂ) • (V *ᵥ ψ₀)) - ψ₀ := by
    rw [hA1, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hVVct]
  have walk0 : QubitizationWalk V j₀ *ᵥ ψ₀
      = (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₀ - (((2 * x * y : ℝ)) : ℂ) • ψ₁ := by
    rw [qubitizationWalk_mulVec, hA2, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hRVψ₀, hRψ₀, hVψ₀₁]
    rw [show (((2 * x ^ 2 - 1 : ℝ)) : ℂ) = 2 * (x : ℂ) ^ 2 - 1 from by push_cast; ring,
      show (((2 * x * y : ℝ)) : ℂ) = 2 * (x : ℂ) * (y : ℂ) from by push_cast; ring]
    module

  have hVφ' : V *ᵥ φ' = ψ₀ - ((x : ℝ) : ℂ) • (V *ᵥ ψ₀) := by
    rw [hφ'def, Matrix.mulVec_sub, Matrix.mulVec_smul, hVVct]
  have hC1 : Vᴴ *ᵥ ψ₁ = (((y : ℝ) : ℂ))⁻¹ • (ψ₀ - ((x : ℝ) : ℂ) • (Vᴴ *ᵥ ψ₀)) := by
    rw [hψ₁def, Matrix.mulVec_smul, hφdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hVctV]
  have hC2 : FiberReflection j₀ *ᵥ (Vᴴ *ᵥ ψ₁)
      = (((y : ℝ) : ℂ))⁻¹ • ((1 - ((x : ℝ) : ℂ) ^ 2) • ψ₀ + ((x : ℝ) : ℂ) • φ') := by
    rw [hC1, Matrix.mulVec_smul]
    refine congrArg _ ?_
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hRψ₀, hA1, hVctψ₀]
    module
  have hC3 : V *ᵥ (FiberReflection j₀ *ᵥ (Vᴴ *ᵥ ψ₁))
      = (((y : ℝ) : ℂ))⁻¹ • ((1 - 2 * ((x : ℝ) : ℂ) ^ 2) • (V *ᵥ ψ₀) + ((x : ℝ) : ℂ) • ψ₀) := by
    rw [hC2, Matrix.mulVec_smul]
    refine congrArg _ ?_
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hVφ']
    module
  have walk1 : QubitizationWalk V j₀ *ᵥ ψ₁
      = (((2 * x * y : ℝ)) : ℂ) • ψ₀ + (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₁ := by
    rw [qubitizationWalk_mulVec, hC3, Matrix.mulVec_smul, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hRVψ₀, hRψ₀, hVψ₀₁]
    rw [show (((y : ℝ) : ℂ))⁻¹ • ((1 - 2 * ((x : ℝ) : ℂ) ^ 2) •
          ((2 : ℂ) • (((x : ℝ) : ℂ) • ψ₀) - (((x : ℝ) : ℂ) • ψ₀ + ((y : ℝ) : ℂ) • ψ₁))
          + ((x : ℝ) : ℂ) • ψ₀)
        = (((2 * x * y : ℝ)) : ℂ) • ψ₀ + (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₁ from by
      rw [show (1 - 2 * ((x : ℝ) : ℂ) ^ 2) •
            ((2 : ℂ) • (((x : ℝ) : ℂ) • ψ₀) - (((x : ℝ) : ℂ) • ψ₀ + ((y : ℝ) : ℂ) • ψ₁))
            + ((x : ℝ) : ℂ) • ψ₀
          = (2 * ((x : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ 2) • ψ₀
            + ((2 * ((x : ℝ) : ℂ) ^ 2 - 1) * ((y : ℝ) : ℂ)) • ψ₁ from by
        rw [hy2c]
        module]
      rw [smul_add, smul_smul, smul_smul]
      rw [show (((y : ℝ) : ℂ))⁻¹ * (2 * ((x : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ 2)
          = (((2 * x * y : ℝ)) : ℂ) from by push_cast; field_simp]
      rw [show (((y : ℝ) : ℂ))⁻¹ * ((2 * ((x : ℝ) : ℂ) ^ 2 - 1) * ((y : ℝ) : ℂ))
          = (((2 * x ^ 2 - 1 : ℝ)) : ℂ) from by push_cast; field_simp]]

  exact ⟨ψ₀, ψ₁, y, hψ₀, hψ₁norm, horth, walk0, walk1, hy, by rw [hy2]; ring⟩

/-- For an eigenvector of the Hermitian encoded matrix with eigenvalue `x`, projecting one walk
step from its distinguished fiber multiplies the embedded vector by `2 * x^2 - 1`. -/
theorem qubitization_amplifies_fiber
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (V : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (hV : IsBlockEncoding V j₀ A 1) (hA : Aᴴ = A)
    (ψ : QState I) (x : ℝ) (hx : A *ᵥ ψ = ((x : ℝ) : ℂ) • ψ) :
    FiberProjector j₀ *ᵥ (QubitizationWalk V j₀ *ᵥ TensorState (Ket j₀) ψ)
      = (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • TensorState (Ket j₀) ψ := by
  have hcorn : BlockCorner V j₀ = A := by simpa using hV.2.2
  have hPVP : FiberProjector j₀ * (V * FiberProjector j₀) = FiberEmbed j₀ A := by
    rw [fiberProjector_mul_mul_corner, hcorn]
  have hPVctP : FiberProjector j₀ * (Vᴴ * FiberProjector j₀) = FiberEmbed j₀ A := by
    have h1 : (FiberProjector j₀ * (V * FiberProjector j₀))ᴴ
        = FiberProjector j₀ * (Vᴴ * FiberProjector j₀) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, fiberProjector_hermitian,
        Matrix.mul_assoc]
    rw [← h1, hPVP, fiberEmbed_conjTranspose, hA]
  have hPfix : FiberProjector j₀ *ᵥ TensorState (Ket j₀) ψ = TensorState (Ket j₀) ψ :=
    fiberProjector_mulVec_tensorState_ket j₀ ψ
  have hPVψ₀ : FiberProjector j₀ *ᵥ (V *ᵥ TensorState (Ket j₀) ψ)
      = ((x : ℝ) : ℂ) • TensorState (Ket j₀) ψ := by
    conv_lhs => rw [← hPfix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
    rw [hPVP, fiberEmbed_mulVec_tensorState_ket, hx, tensorState_smul_ket_right]
  have hPVctψ₀ : FiberProjector j₀ *ᵥ (Vᴴ *ᵥ TensorState (Ket j₀) ψ)
      = ((x : ℝ) : ℂ) • TensorState (Ket j₀) ψ := by
    conv_lhs => rw [← hPfix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
    rw [hPVctP, fiberEmbed_mulVec_tensorState_ket, hx, tensorState_smul_ket_right]
  have hVVct : ∀ χ : QState (J × I), V *ᵥ (Vᴴ *ᵥ χ) = χ := fun χ => by
    have h1 : V * Vᴴ = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff).mp hV.1
      rwa [Matrix.star_eq_conjTranspose] at h
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hPR : ∀ χ : QState (J × I), FiberProjector j₀ *ᵥ (FiberReflection j₀ *ᵥ χ)
      = FiberProjector j₀ *ᵥ χ := fun χ => by
    rw [Matrix.mulVec_mulVec, fiberProjector_mul_fiberReflection]
  rw [qubitizationWalk_mulVec, hPR, fiberReflection_mulVec, hPVctψ₀]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hVVct, hPVψ₀, hPfix]
  rw [show (((2 * x ^ 2 - 1 : ℝ)) : ℂ) = 2 * ((x : ℝ) : ℂ) ^ 2 - 1 from by
    push_cast; ring]
  module

end Qatlib.Concepts.AmplitudeCore.InvFreePhase
