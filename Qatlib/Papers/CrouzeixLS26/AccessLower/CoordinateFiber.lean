/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.Execution.WorkspaceCP

/-!
# Coordinate frames for a fixed auxiliary-register sector

`encodingFiber j₀` embeds a data basis into the `j₀` sector. Its isometry and
compression laws do not depend on independent ancilla lifts, circuit syntax,
or error estimates. `jointEncodingFiber` is the same frame on a product label.
The public declaration names remain unchanged when imported through
`AncillaErrorLaws`.
-/

set_option autoImplicit false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.ReferenceError.RefTraceError
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.Coordinate

open Matrix


variable {J K I : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I]

/-! ## Indicator sums over a fiber -/

/-- A left indicator collapses a finite sum to the fiber point. -/
theorem sum_fiber_mul_left {X : Type*} [Fintype X] [DecidableEq X] (p₀ : X) (F : X → ℂ) :
    ∑ p, (if p = p₀ then (1 : ℂ) else 0) * F p = F p₀ := by
  rw [Finset.sum_eq_single p₀]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- A right indicator collapses a finite sum to the fiber point. -/
theorem sum_fiber_mul_right {X : Type*} [Fintype X] [DecidableEq X] (p₀ : X) (F : X → ℂ) :
    ∑ p, F p * (if p = p₀ then (1 : ℂ) else 0) = F p₀ := by
  rw [Finset.sum_eq_single p₀]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-! ## The coordinate fibers -/

/-- The encoding fiber on a single auxiliary register `J` over data `I`: the column
selecting data basis `i` inside the `j₀`-labeled sector. -/
def encodingFiber (j₀ : J) : Matrix (J × I) I ℂ :=
  Matrix.of fun x i => if x.1 = j₀ ∧ x.2 = i then 1 else 0

/-- Pointwise form of the single-register fiber. -/
theorem encodingFiber_apply (j₀ : J) (x : J × I) (i : I) :
    encodingFiber j₀ x i = if x = (j₀, i) then 1 else 0 := by
  obtain ⟨a, b⟩ := x
  by_cases h1 : a = j₀ <;> by_cases h2 : b = i <;> simp [encodingFiber, h1, h2]

/-- Pointwise form of the fiber's adjoint. -/
theorem encodingFiber_conjTranspose (j₀ : J) (i : I) (x : J × I) :
    (encodingFiber j₀)ᴴ i x = if x = (j₀, i) then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, encodingFiber_apply]
  by_cases hx : x = (j₀, i) <;> simp [hx]

/-- The two-ancilla fiber on the joint workspace `(J × K) × I`. -/
def jointEncodingFiber (j₀ : J) (k₀ : K) : Matrix ((J × K) × I) I ℂ :=
  encodingFiber (j₀, k₀)

/-- The single-register fiber is an isometry. -/
theorem encodingFiber_isIsometry (j₀ : J) : IsIsometry (encodingFiber (I := I) j₀) := by
  unfold IsIsometry
  ext i k
  by_cases hik : i = k
  · subst k
    calc ((encodingFiber j₀)ᴴ * encodingFiber j₀ : Matrix I I ℂ) i i
        = ∑ p, (encodingFiber j₀)ᴴ i p * encodingFiber j₀ p i := Matrix.mul_apply
      _ = ∑ p, (if p = (j₀, i) then (1 : ℂ) else 0) * (if p = (j₀, i) then 1 else 0) := by
          simp only [encodingFiber_conjTranspose, encodingFiber_apply]
      _ = ∑ p, (if p = (j₀, i) then (1 : ℂ) else 0) * 1 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hp : p = (j₀, i) <;> simp [hp]
      _ = 1 := by simp
      _ = (1 : Matrix I I ℂ) i i := by rw [Matrix.one_apply_eq]
  · have hterm : ∀ p : J × I, (encodingFiber j₀)ᴴ i p * encodingFiber j₀ p k = 0 := by
      intro p
      rw [encodingFiber_conjTranspose, encodingFiber_apply]
      by_cases hp : p = (j₀, i)
      · rw [ite_eq_left hp, one_mul]
        refine ite_eq_right ?_
        intro h
        exact hik (congrArg Prod.snd (hp.symm.trans h))
      · rw [ite_eq_right hp, zero_mul]
    calc ((encodingFiber j₀)ᴴ * encodingFiber j₀ : Matrix I I ℂ) i k
        = ∑ p, (encodingFiber j₀)ᴴ i p * encodingFiber j₀ p k := Matrix.mul_apply
      _ = 0 := Finset.sum_eq_zero fun p _ => hterm p
      _ = (1 : Matrix I I ℂ) i k := by rw [Matrix.one_apply_ne hik]

/-- The two-ancilla fiber is an isometry. -/
theorem jointEncodingFiber_isIsometry (j₀ : J) (k₀ : K) :
    IsIsometry (jointEncodingFiber (I := I) j₀ k₀) :=
  encodingFiber_isIsometry (I := I) (j₀, k₀)

/-- The corner of any operator compressed between single-register fibers. -/
theorem compress_encodingFiber_eq (j₀ : J) (M : Matrix (J × I) (J × I) ℂ) (i₁ i₂ : I) :
    compress (encodingFiber j₀) M (encodingFiber j₀) i₁ i₂ = M (j₀, i₁) (j₀, i₂) := by
  have h1 : ∀ x : J × I,
      ∑ w : J × I, (encodingFiber j₀)ᴴ i₁ w * M w x = M (j₀, i₁) x := by
    intro x
    simp only [encodingFiber_conjTranspose]
    exact sum_fiber_mul_left (j₀, i₁) (fun w => M w x)
  calc compress (encodingFiber j₀) M (encodingFiber j₀) i₁ i₂
      = ∑ x : J × I,
          (∑ w : J × I, (encodingFiber j₀)ᴴ i₁ w * M w x) * encodingFiber j₀ x i₂ := by
        rw [compress]
        simp only [Matrix.mul_apply]
    _ = ∑ x : J × I, M (j₀, i₁) x * encodingFiber j₀ x i₂ :=
          Finset.sum_congr rfl fun x _ => by rw [h1 x]
    _ = ∑ x : J × I, M (j₀, i₁) x * (if x = (j₀, i₂) then (1 : ℂ) else 0) := by
        simp only [encodingFiber_apply]
    _ = M (j₀, i₁) (j₀, i₂) := sum_fiber_mul_right (j₀, i₂) (fun x => M (j₀, i₁) x)

open scoped Matrix.Norms.L2Operator

/-- An isometry acts norm-preservingly on wrapped vectors. -/
theorem isometry_mulVec_norm {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O]
    [DecidableEq O]
    {L : Matrix H O ℂ} (hL : IsIsometry L) (v : QState O) :
    ‖toEuclidean_fromVec (L *ᵥ v)‖ = ‖toEuclidean_fromVec v‖ := by
  have hkey : Inner (L *ᵥ v) (L *ᵥ v) = Inner v v := by
    show (star (L *ᵥ v) ⬝ᵥ (L *ᵥ v)) = star v ⬝ᵥ v
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hL,
      Matrix.one_mulVec]
  have h1 : ‖toEuclidean_fromVec (L *ᵥ v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_sq_eq_re_inner, norm_toEuclidean_sq_eq_re_inner, hkey]
  rw [← Real.sqrt_sq (norm_nonneg (toEuclidean_fromVec (L *ᵥ v))),
    ← Real.sqrt_sq (norm_nonneg (toEuclidean_fromVec v)), h1]

/-- An isometry between rectangular frames is an L2 contraction. -/
theorem isometry_norm_le {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O]
    [DecidableEq O] {L : Matrix H O ℂ} (hL : IsIsometry L) : ‖L‖ ≤ 1 := by
  refine l2_opNorm_le_of_mulVec_le zero_le_one L fun v => ?_
  rw [one_mul]
  exact (isometry_mulVec_norm hL v).le

set_option maxHeartbeats 1000000 in
/-- A unitary compressed between isometric frames is an L2 contraction. -/
theorem l2_norm_compress_le_one {H I O : Type*} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] [Fintype O] [DecidableEq O] {L : Matrix H O ℂ} {U : Matrix H H ℂ}
    {R : Matrix H I ℂ} (hL : IsIsometry L) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hR : IsIsometry R) : ‖compress L U R‖ ≤ 1 := by
  have h1 : ‖compress L U R‖ ≤ ‖Lᴴ‖ * (‖U‖ * ‖R‖) := by
    have hstep1 : ‖Lᴴ * (U * R)‖ ≤ ‖Lᴴ‖ * ‖U * R‖ := Matrix.l2_opNorm_mul Lᴴ (U * R)
    have hstep2 : ‖U * R‖ ≤ ‖U‖ * ‖R‖ := Matrix.l2_opNorm_mul U R
    have hassoc : compress L U R = Lᴴ * U * R := rfl
    rw [hassoc]
    calc ‖Lᴴ * U * R‖ = ‖Lᴴ * (U * R)‖ := by rw [Matrix.mul_assoc]
      _ ≤ ‖Lᴴ‖ * ‖U * R‖ := hstep1
      _ ≤ ‖Lᴴ‖ * (‖U‖ * ‖R‖) := mul_le_mul_of_nonneg_left hstep2 (norm_nonneg _)
  have hL1 : ‖Lᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact isometry_norm_le hL
  have hR1 : ‖R‖ ≤ 1 := isometry_norm_le hR
  have hU1 : ‖U‖ ≤ 1 := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hU
  refine h1.trans ?_
  have hprod : ‖Lᴴ‖ * (‖U‖ * ‖R‖) ≤ 1 * (1 * 1) :=
    mul_le_mul hL1 (mul_le_mul hU1 hR1 (norm_nonneg R) zero_le_one)
      (mul_nonneg (norm_nonneg U) (norm_nonneg R)) zero_le_one
  norm_num at hprod
  exact hprod


end Qatlib.Papers.CrouzeixLS26.AccessLower.Coordinate
