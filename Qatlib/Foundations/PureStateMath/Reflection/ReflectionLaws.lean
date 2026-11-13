/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Foundations.PureStateMath.Reflection.Basic

/-!
# Reflections associated with orthogonal projectors

This module defines `ReflectionAbout P = 2 * P - 1` and proves its involution, adjoint, and
unitarity laws for orthogonal projectors. It constructs `outerProduct ψ` and proves that a
normalized state gives an orthogonal projector and hence a unitary reflection, providing the
linear algebra used in amplitude amplification [BrassardEtAl2002].

## Main statements

* `reflectionAbout_unitary`: orthogonal projectors give unitary reflections.
* `applyGate_reflectionAbout_of_fixed`: projected vectors are fixed.
* `outerProduct_reflection_unitary`: normalized states give unitary reflections.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.Reflection

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The matrix `2 * P - 1`, which reflects about the range when `P` is an orthogonal projector. -/
noncomputable def ReflectionAbout (P : Matrix I I ℂ) : Matrix I I ℂ := (2 : ℂ) • P - 1

/-- The reflection associated with an orthogonal projector squares to the identity. -/
theorem reflectionAbout_mul_self {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) :
    ReflectionAbout P * ReflectionAbout P = 1 := by
  have hid : P * P = P := hP.1
  simp only [ReflectionAbout, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hid]
  module

/-- The reflection associated with an orthogonal projector equals its conjugate transpose. -/
theorem reflectionAbout_conjTranspose {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) :
    (ReflectionAbout P)ᴴ = ReflectionAbout P := by
  have hstar : Pᴴ = P := hP.2
  simp [ReflectionAbout, hstar]

/-- The reflection associated with an orthogonal projector is unitary. -/
theorem reflectionAbout_unitary {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) :
    ReflectionAbout P ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    reflectionAbout_conjTranspose hP]
  exact reflectionAbout_mul_self hP

/-- Applying `ReflectionAbout P` gives twice the projected vector minus the original vector. -/
theorem applyGate_reflectionAbout (P : Matrix I I ℂ) (ψ : QState I) :
    ApplyGate (ReflectionAbout P) ψ = (2 : ℂ) • ApplyGate P ψ - ψ := by
  simp [ReflectionAbout, ApplyGate, Matrix.sub_mulVec, Matrix.smul_mulVec]

/-- The reflection fixes any vector fixed by `P`. -/
theorem applyGate_reflectionAbout_of_fixed {P : Matrix I I ℂ} {ψ : QState I}
    (h : ApplyGate P ψ = ψ) : ApplyGate (ReflectionAbout P) ψ = ψ := by
  rw [applyGate_reflectionAbout, h]
  module

/-- The reflection negates any vector annihilated by `P`. -/
theorem applyGate_reflectionAbout_of_zero {P : Matrix I I ℂ} {ψ : QState I}
    (h : ApplyGate P ψ = 0) : ApplyGate (ReflectionAbout P) ψ = -ψ := by
  rw [applyGate_reflectionAbout, h, smul_zero, zero_sub]

/-- Diffusion is the reflection associated with the averaging matrix. -/
theorem diffusion_eq_reflectionAbout :
    Diffusion I = ReflectionAbout (AverageProjection I) := rfl

/-- The matrix `|ψ⟩⟨ψ|` with entries formed from an amplitude and a conjugated amplitude. -/
noncomputable def outerProduct (ψ : QState I) : Matrix I I ℂ :=
  Matrix.of fun i j => ψ i * (starRingEnd ℂ) (ψ j)

omit [Fintype I] [DecidableEq I] in

/-- The `(i, j)` entry of `outerProduct ψ` is `ψ i` times the complex conjugate of `ψ j`. -/
theorem outerProduct_apply (ψ : QState I) (i j : I) :
    outerProduct ψ i j = ψ i * (starRingEnd ℂ) (ψ j) := rfl

omit [DecidableEq I] in

/-- The outer product of `ψ` sends `φ` to `Inner ψ φ` times `ψ`. -/
theorem outerProduct_mulVec (ψ φ : QState I) :
    outerProduct ψ *ᵥ φ = (Inner ψ φ) • ψ := by
  funext i
  have h : (∑ j, ψ i * (starRingEnd ℂ) (ψ j) * φ j)
      = (∑ j, (starRingEnd ℂ) (ψ j) * φ j) * ψ i := by
    rw [Finset.sum_mul Finset.univ (fun j => (starRingEnd ℂ) (ψ j) * φ j) (ψ i)]
    exact Finset.sum_congr rfl fun j _ => by ring
  simpa using! h

/-- A normalized state has inner product one with itself. -/
theorem inner_self_eq_one {ψ : QState I} (hψ : Normalized ψ) : Inner ψ ψ = 1 := by
  rw [normalized_iff_inner_self] at hψ
  exact hψ

/-- The outer product of a normalized state is an orthogonal projector. -/
theorem isOrthogonalProjector_outerProduct {ψ : QState I} (hψ : Normalized ψ) :
    IsOrthogonalProjector (outerProduct ψ) := by
  constructor
  · show outerProduct ψ * outerProduct ψ = outerProduct ψ
    ext i j
    simp only [outerProduct, Matrix.mul_apply, Matrix.of_apply]
    have hterm : ∀ k : I,
        ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
          = ((starRingEnd ℂ) (ψ k) * ψ k) * (ψ i * (starRingEnd ℂ) (ψ j)) :=
      fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k, ((starRingEnd ℂ) (ψ k) * ψ k) * (ψ i * (starRingEnd ℂ) (ψ j)))
        = (∑ k, (starRingEnd ℂ) (ψ k) * ψ k) * (ψ i * (starRingEnd ℂ) (ψ j)) from
      (Finset.sum_mul Finset.univ (fun k => (starRingEnd ℂ) (ψ k) * ψ k)
        (ψ i * (starRingEnd ℂ) (ψ j))).symm]
    rw [show (∑ k, (starRingEnd ℂ) (ψ k) * ψ k) = Inner ψ ψ from rfl,
      inner_self_eq_one hψ, one_mul]
  · show star (outerProduct ψ) = outerProduct ψ
    ext i j
    simp only [outerProduct, Matrix.star_apply, Matrix.of_apply, RCLike.star_def,
      map_mul]
    rw [show (starRingEnd ℂ) ((starRingEnd ℂ) (ψ i)) = ψ i from star_star _]
    ring

/-- Reflection about the outer product of a normalized state is unitary. -/
theorem outerProduct_reflection_unitary {ψ : QState I} (hψ : Normalized ψ) :
    ReflectionAbout (outerProduct ψ) ∈ Matrix.unitaryGroup I ℂ :=
  reflectionAbout_unitary (isOrthogonalProjector_outerProduct hψ)

end Qatlib.Foundations.PureStateMath.Reflection

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]
namespace Qatlib.Foundations.PureStateMath.Reflection

/-- Matrix-vector multiplication by `ReflectionAbout P` gives twice `P *ᵥ χ` minus `χ`. -/
theorem reflectionAbout_mulVec {K : Type*} [Fintype K] [DecidableEq K]
    (P : Matrix K K ℂ) (χ : QState K) :
    ReflectionAbout P *ᵥ χ = (2 : ℂ) • (P *ᵥ χ) - χ := by
  rw [ReflectionAbout, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
end Qatlib.Foundations.PureStateMath.Reflection
