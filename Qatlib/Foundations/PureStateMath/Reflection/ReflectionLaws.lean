/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Foundations.PureStateMath.Reflection.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.Reflection

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def ReflectionAbout (P : Matrix I I ℂ) : Matrix I I ℂ := (2 : ℂ) • P - 1

theorem reflectionAbout_mul_self {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) :
    ReflectionAbout P * ReflectionAbout P = 1 := by
  have hid : P * P = P := hP.1
  simp only [ReflectionAbout, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hid]
  module

theorem reflectionAbout_conjTranspose {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) :
    (ReflectionAbout P)ᴴ = ReflectionAbout P := by
  have hstar : Pᴴ = P := hP.2
  simp [ReflectionAbout, hstar]

theorem reflectionAbout_unitary {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) :
    ReflectionAbout P ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    reflectionAbout_conjTranspose hP]
  exact reflectionAbout_mul_self hP

theorem applyGate_reflectionAbout (P : Matrix I I ℂ) (ψ : QState I) :
    ApplyGate (ReflectionAbout P) ψ = (2 : ℂ) • ApplyGate P ψ - ψ := by
  simp [ReflectionAbout, ApplyGate, Matrix.sub_mulVec, Matrix.smul_mulVec]

theorem applyGate_reflectionAbout_of_fixed {P : Matrix I I ℂ} {ψ : QState I}
    (h : ApplyGate P ψ = ψ) : ApplyGate (ReflectionAbout P) ψ = ψ := by
  rw [applyGate_reflectionAbout, h]
  module

theorem applyGate_reflectionAbout_of_zero {P : Matrix I I ℂ} {ψ : QState I}
    (h : ApplyGate P ψ = 0) : ApplyGate (ReflectionAbout P) ψ = -ψ := by
  rw [applyGate_reflectionAbout, h, smul_zero, zero_sub]

theorem diffusion_eq_reflectionAbout :
    Diffusion I = ReflectionAbout (AverageProjection I) := rfl

noncomputable def outerProduct (ψ : QState I) : Matrix I I ℂ :=
  Matrix.of fun i j => ψ i * (starRingEnd ℂ) (ψ j)

theorem outerProduct_apply (ψ : QState I) (i j : I) :
    outerProduct ψ i j = ψ i * (starRingEnd ℂ) (ψ j) := rfl

theorem outerProduct_mulVec (ψ φ : QState I) :
    outerProduct ψ *ᵥ φ = (Inner ψ φ) • ψ := by
  funext i
  have h : (∑ j, ψ i * (starRingEnd ℂ) (ψ j) * φ j)
      = (∑ j, (starRingEnd ℂ) (ψ j) * φ j) * ψ i := by
    rw [Finset.sum_mul Finset.univ (fun j => (starRingEnd ℂ) (ψ j) * φ j) (ψ i)]
    exact Finset.sum_congr rfl fun j _ => by ring
  simpa using! h

theorem inner_self_eq_one {ψ : QState I} (hψ : Normalized ψ) : Inner ψ ψ = 1 := by
  rw [normalized_iff_inner_self] at hψ
  exact hψ

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

theorem outerProduct_reflection_unitary {ψ : QState I} (hψ : Normalized ψ) :
    ReflectionAbout (outerProduct ψ) ∈ Matrix.unitaryGroup I ℂ :=
  reflectionAbout_unitary (isOrthogonalProjector_outerProduct hψ)

end Qatlib.Foundations.PureStateMath.Reflection

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]
namespace Qatlib.Foundations.PureStateMath.Reflection

theorem reflectionAbout_mulVec {K : Type*} [Fintype K] [DecidableEq K]
    (P : Matrix K K ℂ) (χ : QState K) :
    ReflectionAbout P *ᵥ χ = (2 : ℂ) • (P *ᵥ χ) - χ := by
  rw [ReflectionAbout, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
end Qatlib.Foundations.PureStateMath.Reflection
