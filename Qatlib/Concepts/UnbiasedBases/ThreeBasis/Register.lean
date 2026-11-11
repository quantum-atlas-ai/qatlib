/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite quantum registers and basis probabilities

This module models an `n`-qubit register as the Euclidean space `QReg n` indexed by binary
strings. It defines computational basis states and squared-amplitude weights `prob`, with the
finite-dimensional Born normalization identities of [NielsenChuang2010].

## Main statements

* `normSq_eq_sum_prob`: squared norm equals the sum of squared-amplitude weights.
* `sum_prob_eq_one`: unit vectors give probabilities summing to one.
* `prob_basisState`: a basis state yields its own label with weight one.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

section

open scoped ComplexConjugate

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

/-- The complex Euclidean space indexed by length-`n` binary strings, representing an `n`-qubit
register. -/
abbrev QReg (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate vector with amplitude one at `x` and zero elsewhere. -/
noncomputable def basisState (x : ι) : EuclideanSpace ℂ ι := EuclideanSpace.single x 1

/-- The amplitude of `basisState x` at `y` is one if `y = x` and zero otherwise. -/
@[simp] lemma basisState_apply (x y : ι) :
    basisState x y = if y = x then 1 else 0 := by
  rw [basisState, PiLp.single_apply]

omit [DecidableEq ι] in

/-- The squared modulus of amplitude `ψ z`, giving its computational basis measurement weight. -/
noncomputable def prob (ψ : EuclideanSpace ℂ ι) (z : ι) : ℝ := ‖ψ z‖ ^ 2

omit [DecidableEq ι] in

/-- Every squared-amplitude weight is nonnegative. -/
lemma prob_nonneg (ψ : EuclideanSpace ℂ ι) (z : ι) : 0 ≤ prob ψ z := sq_nonneg _

/-- The measurement weight at `z` is the squared norm of the inner product with `basisState z`. -/
lemma prob_eq_inner_sq [Fintype ι] (ψ : EuclideanSpace ℂ ι) (z : ι) :
    prob ψ z = ‖inner ℂ (basisState z) ψ‖ ^ 2 := by
  simp only [prob, basisState, EuclideanSpace.inner_single_left, map_one, one_mul]

omit [DecidableEq ι] in

/-- For a finite index type, the squared norm of a state is the sum of its measurement weights. -/
lemma normSq_eq_sum_prob [Fintype ι] (ψ : EuclideanSpace ℂ ι) : ‖ψ‖ ^ 2 = ∑ z, prob ψ z := by
  rw [EuclideanSpace.norm_eq]
  simp only [prob]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

omit [DecidableEq ι] in

/-- For a unit vector on a finite index type, the measurement weights sum to one. -/
lemma sum_prob_eq_one [Fintype ι] {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    ∑ z, prob ψ z = 1 := by
  rw [← normSq_eq_sum_prob, hψ, one_pow]

/-- Every computational basis state on a finite index type has norm one. -/
@[simp] lemma basisState_norm [Fintype ι] (x : ι) : ‖basisState x‖ = 1 := by
  rw [basisState, PiLp.norm_single, norm_one]

/-- The measurement weight of `basisState x` is one at `x` and zero at any other label. -/
@[simp] lemma prob_basisState (x z : ι) :
    prob (basisState x) z = if z = x then 1 else 0 := by
  rw [prob, basisState_apply]
  split <;> simp

omit [DecidableEq ι] in

/-- Evaluating a finite sum of Euclidean vectors at a coordinate equals the sum of their
coordinate values. -/
lemma sum_coord {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ ι) (y : ι) :
    (∑ k ∈ s, f k) y = ∑ k ∈ s, (f k) y := by
  have h : (∑ k ∈ s, f k).ofLp = ∑ k ∈ s, (f k).ofLp :=
    map_sum (WithLp.addEquiv 2 (ι → ℂ)) f s
  calc (∑ k ∈ s, f k) y = (∑ k ∈ s, f k).ofLp y := rfl
    _ = (∑ k ∈ s, (f k).ofLp) y := by rw [h]
    _ = ∑ k ∈ s, (f k) y := by rw [Finset.sum_apply]

omit [DecidableEq ι] in

/-- The complex Euclidean inner product is the sum of conjugated first coordinates times second
coordinates. -/
lemma inner_eq_sum [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    inner ℂ x y = ∑ i, conj (x i) * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]; rfl

/-- A complex number times its conjugate is the complex embedding of its squared norm. -/
lemma mul_conj_eq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo
