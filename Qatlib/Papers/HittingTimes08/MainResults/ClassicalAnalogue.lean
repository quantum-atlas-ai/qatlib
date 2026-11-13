/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.Comparison
import Qatlib.Concepts.WalkSearch.TwoLevelLower

/-!
# Classical kernels associated with walk amplitudes

The structure `WalkStructure` packages a probability weight and compatible real walk amplitudes.
This module constructs the squared-amplitude kernel and proves its stochasticity, stationarity,
and reversibility criterion, following the classical analogue in [MagniezEtAl2008].

## Main statements

* `lemma_3_17`: collects the kernel and reversibility properties.
* `theorem_3_18`: transfers an assumed quantile equality to a square-root relation for the
  squared law.

## References

* [Magniez et al., 2008][MagniezEtAl2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

open Qatlib.Concepts.WalkSearch.TwoLevelLower

/-- A probability weight, two families of unit real amplitude vectors, and a joint amplitude
array compatible with both families through square-root weighting. -/
structure WalkStructure (X : Type*) [Fintype X] where

  π : X → ℝ

  φ : X → X → ℝ

  ψ : X → X → ℝ

  w : X → X → ℝ
  π_nonneg : ∀ x, 0 ≤ π x
  π_sum : ∑ x, π x = 1

  φ_unit : ∀ x, ∑ y, (φ x y) ^ 2 = 1

  ψ_unit : ∀ y, ∑ x, (ψ y x) ^ 2 = 1

  w_φ : ∀ x y, w x y = Real.sqrt (π x) * φ x y

  w_ψ : ∀ x y, w x y = Real.sqrt (π y) * ψ y x

namespace WalkStructure

variable {X : Type*} [Fintype X]

/-- The classical kernel obtained by squaring the forward amplitudes `φ x y`. -/
def classicalKernel (D : WalkStructure X) : X → X → ℝ := fun x y => (D.φ x y) ^ 2

/-- The condition that the joint amplitude array `w` is symmetric under swapping its arguments. -/
def swapFixed (D : WalkStructure X) : Prop := ∀ x y, D.w x y = D.w y x

/-- The weighted kernel entry `π x * classicalKernel x y` equals `w x y ^ 2`. -/
theorem pi_mul_kernel (D : WalkStructure X) (x y : X) :
    D.π x * D.classicalKernel x y = D.w x y ^ 2 := by
  rw [classicalKernel, D.w_φ x y, mul_pow, Real.sq_sqrt (D.π_nonneg x)]

/-- The squared-amplitude kernel is a transition matrix, as in Lemma 3.17 of [MagniezEtAl2008]. -/
theorem isTransitionMatrix (D : WalkStructure X) :
    IsTransitionMatrix D.classicalKernel := by
  refine ⟨fun x y => sq_nonneg (D.φ x y), fun x => D.φ_unit x⟩

/-- The probability weight `π` is stationary for the squared-amplitude kernel. -/
theorem isStationary (D : WalkStructure X) :
    IsStationary D.classicalKernel D.π := by
  refine ⟨D.π_nonneg, D.π_sum, fun y => ?_⟩
  calc ∑ x, D.π x * D.classicalKernel x y
      = ∑ x, D.w x y ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact D.pi_mul_kernel x y
    _ = ∑ x, (Real.sqrt (D.π y) * D.ψ y x) ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [D.w_ψ x y]
    _ = ∑ x, D.π y * (D.ψ y x) ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [mul_pow, Real.sq_sqrt (D.π_nonneg y)]
    _ = D.π y * (∑ x, (D.ψ y x) ^ 2) := by rw [Finset.mul_sum]
    _ = D.π y := by rw [D.ψ_unit y, mul_one]

/-- The squared-amplitude kernel is reversible with respect to `π` exactly when `w x y ^ 2 = w y
x ^ 2` for every pair of states. -/
theorem reversible_iff (D : WalkStructure X) :
    IsReversible D.classicalKernel D.π ↔ ∀ x y, D.w x y ^ 2 = D.w y x ^ 2 := by
  constructor
  · intro h x y
    have hxy := h x y
    rw [← D.pi_mul_kernel x y, ← D.pi_mul_kernel y x]
    exact hxy
  · intro h x y
    rw [D.pi_mul_kernel x y, D.pi_mul_kernel y x]
    exact h x y

/-- Symmetry of the joint amplitudes implies reversibility of the squared-amplitude kernel with
respect to `π`. -/
theorem isReversible_of_swapFixed (D : WalkStructure X) (h : D.swapFixed) :
    IsReversible D.classicalKernel D.π := by
  rw [D.reversible_iff]
  intro x y
  rw [h x y]

/-- Collects the transition, stationarity, and squared-amplitude reversibility properties,
including reversibility under `swapFixed`. These are the classical-kernel properties
associated with [Magniez et al., Lemma 3.17][MagniezEtAl2008]. -/
theorem lemma_3_17 (D : WalkStructure X) :
    IsTransitionMatrix D.classicalKernel ∧ IsStationary D.classicalKernel D.π ∧
      (IsReversible D.classicalKernel D.π ↔ ∀ x y, D.w x y ^ 2 = D.w y x ^ 2) ∧
        (D.swapFixed → IsReversible D.classicalKernel D.π) :=
  ⟨D.isTransitionMatrix, D.isStationary, D.reversible_iff, D.isReversible_of_swapFixed⟩

end WalkStructure

/-- Given equal `ε`-quantiles of `Q` and `QP` and `ε ≥ 0`, returns that equality together with
`Q.quantile ε = sqrt (QP.sqLaw.quantile ε)`. This is the quantile consequence used for
Theorem 3.18 in [MagniezEtAl2008]. -/
theorem theorem_3_18 {J : Type*} [Fintype J] (Q QP : HittingLaw J) {ε : ℝ}
    (hε : 0 ≤ ε) (hspectrum : Q.quantile ε = QP.quantile ε) :
    Q.quantile ε = QP.quantile ε ∧
      Q.quantile ε = Real.sqrt (QP.sqLaw.quantile ε) := by
  refine ⟨hspectrum, ?_⟩
  rw [hspectrum]
  exact QP.theorem_3_15_second hε

end Qatlib.Papers.HittingTimes08.MainResults
