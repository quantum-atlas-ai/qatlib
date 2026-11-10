/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

section

open scoped ComplexConjugate

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

abbrev QReg (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

variable {ι : Type*} [DecidableEq ι]

noncomputable def basisState (x : ι) : EuclideanSpace ℂ ι := EuclideanSpace.single x 1

@[simp] lemma basisState_apply (x y : ι) :
    basisState x y = if y = x then 1 else 0 := by
  rw [basisState, PiLp.single_apply]

omit [DecidableEq ι] in

noncomputable def prob (ψ : EuclideanSpace ℂ ι) (z : ι) : ℝ := ‖ψ z‖ ^ 2

omit [DecidableEq ι] in

lemma prob_nonneg (ψ : EuclideanSpace ℂ ι) (z : ι) : 0 ≤ prob ψ z := sq_nonneg _

lemma prob_eq_inner_sq [Fintype ι] (ψ : EuclideanSpace ℂ ι) (z : ι) :
    prob ψ z = ‖inner ℂ (basisState z) ψ‖ ^ 2 := by
  simp only [prob, basisState, EuclideanSpace.inner_single_left, map_one, one_mul]

omit [DecidableEq ι] in

lemma normSq_eq_sum_prob [Fintype ι] (ψ : EuclideanSpace ℂ ι) : ‖ψ‖ ^ 2 = ∑ z, prob ψ z := by
  rw [EuclideanSpace.norm_eq]
  simp only [prob]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

omit [DecidableEq ι] in

lemma sum_prob_eq_one [Fintype ι] {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    ∑ z, prob ψ z = 1 := by
  rw [← normSq_eq_sum_prob, hψ, one_pow]

@[simp] lemma basisState_norm [Fintype ι] (x : ι) : ‖basisState x‖ = 1 := by
  rw [basisState, PiLp.norm_single, norm_one]

@[simp] lemma prob_basisState (x z : ι) :
    prob (basisState x) z = if z = x then 1 else 0 := by
  rw [prob, basisState_apply]
  split <;> simp

omit [DecidableEq ι] in

lemma sum_coord {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ ι) (y : ι) :
    (∑ k ∈ s, f k) y = ∑ k ∈ s, (f k) y := by
  have h : (∑ k ∈ s, f k).ofLp = ∑ k ∈ s, (f k).ofLp :=
    map_sum (WithLp.addEquiv 2 (ι → ℂ)) f s
  calc (∑ k ∈ s, f k) y = (∑ k ∈ s, f k).ofLp y := rfl
    _ = (∑ k ∈ s, (f k).ofLp) y := by rw [h]
    _ = ∑ k ∈ s, (f k) y := by rw [Finset.sum_apply]

omit [DecidableEq ι] in

lemma inner_eq_sum [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    inner ℂ x y = ∑ i, conj (x i) * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]; rfl

lemma mul_conj_eq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo
