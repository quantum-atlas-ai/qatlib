/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Minus-branch classification readout

Defines the minus-branch weight and real overlap for two amplitude vectors. For normalized
inputs, the branch weight determines the sign of the overlap; scalar variance estimates bound
the associated sampling expression. See [RebentrostMohseniLloyd2014].

## Main statements

* `minusBranchWeight_formula`: expresses the branch weight through the overlap.
* `swapTest_classification`: relates the threshold at one half to the overlap sign.

## References

* [Rebentrost et al., 2014][RebentrostMohseniLloyd2014]
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QuantumSVM13.MinusReadout

variable {n : ℕ}

/-- The squared norm of the coordinatewise half-difference of two real amplitude vectors. -/
noncomputable def minusBranchWeight (ψ φ : Fin n → ℝ) : ℝ :=
  ∑ i, ((ψ i - φ i) / 2) ^ 2

/-- The real inner product `∑ i, ψ i * φ i` of two amplitude vectors. -/
noncomputable def overlap (ψ φ : Fin n → ℝ) : ℝ := ∑ i, ψ i * φ i

/-- For normalized real vectors, the minus-branch weight is `(1 - overlap ψ φ) / 2`
[RebentrostMohseniLloyd2014]. -/
theorem minusBranchWeight_formula (ψ φ : Fin n → ℝ)
    (hψ : (∑ i, (ψ i) ^ 2) = 1) (hφ : (∑ i, (φ i) ^ 2) = 1) :
    minusBranchWeight ψ φ = (1 - overlap ψ φ) / 2 := by
  have hpt : ∀ i : Fin n, ((ψ i - φ i) / 2) ^ 2
      = ((ψ i) ^ 2 - 2 * (ψ i * φ i) + (φ i) ^ 2) / 4 := by
    intro i
    ring
  unfold minusBranchWeight overlap
  simp_rw [hpt]
  simp_rw [← Finset.sum_div]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hψ, hφ, ← Finset.mul_sum]
  ring

/-- For normalized real inputs, the minus-branch weight is below one half exactly when the
overlap is positive, and above one half exactly when the overlap is negative
[RebentrostMohseniLloyd2014]. -/
theorem swapTest_classification (ψ φ : Fin n → ℝ)
    (hψ : (∑ i, (ψ i) ^ 2) = 1) (hφ : (∑ i, (φ i) ^ 2) = 1) :
    (minusBranchWeight ψ φ < 1 / 2 ↔ 0 < overlap ψ φ) ∧
      (1 / 2 < minusBranchWeight ψ φ ↔ overlap ψ φ < 0) := by
  have hP := minusBranchWeight_formula ψ φ hψ hφ
  constructor
  · rw [hP]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  · rw [hP]
    constructor
    · intro h
      linarith
    · intro h
      linarith

/-- For a probability parameter `P`, the Bernoulli variance expression `P * (1 - P)` is at most
one quarter [RebentrostMohseniLloyd2014]. -/
theorem swapTest_sampling_variance (P : ℝ) (_hP0 : 0 ≤ P) (_hP1 : P ≤ 1) :
    P * (1 - P) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (P - 1 / 2)]

/-- For `P ∈ [0,1]` and positive precision `ε`, the variance divided by `ε ^ 2` is at most `1 /
(4 * ε ^ 2)` [RebentrostMohseniLloyd2014]. -/
theorem swapTest_repetitions (P ε : ℝ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hε : 0 < ε) :
    P * (1 - P) / ε ^ 2 ≤ 1 / (4 * ε ^ 2) := by
  have hvar := swapTest_sampling_variance P hP0 hP1
  have hε2 : 0 < ε ^ 2 := by positivity
  calc P * (1 - P) / ε ^ 2 ≤ (1 / 4) / ε ^ 2 :=
        div_le_div_of_nonneg_right hvar hε2.le
    _ = 1 / (4 * ε ^ 2) := by ring

end Qatlib.Papers.QuantumSVM13.MinusReadout
