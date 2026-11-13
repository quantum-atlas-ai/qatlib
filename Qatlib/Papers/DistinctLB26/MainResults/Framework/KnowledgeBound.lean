/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.DistinctLB26.MainResults.Framework.Operators

/-!
# Knowledge Bounds and Local Alterations for k-Distinctness

This module formalizes the initial-state knowledge vanishing, register-unitary invariance,
the local-alteration double-counting inequality (Lemma 5.3), and the reduced orbit-size and
query-gain telescoping bounds from Belovs's quantum query lower bound framework for
$k$-distinctness.

## Main statements

* `prop3_19_a`: Vanishing masked knowledge when support lies outside the target family.
* `prop3_19_b`: Norm invariance of masked knowledge under support-preserving permutations.
* `lemma5_3`: Local-alteration double-counting bound relating restricted squared norms to
  global squared norms via alteration multiplicity $K'$ and family size lower bound $K$.
* `theorem6_9`: Telescoped query-gain bound $O(t^{3/2}/n)$ for element distinctness.

## References

* [Belovs, 2026][Belovs2026]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Framework

open Qatlib.Papers.DistinctLB26.MainResults.Model

variable {α ι : Type*}

/-! ## Proposition 3.19 (knowledge of the initial state and unitary invariance) -/

/-- **Proposition 3.19(a)** [Belovs2026]: if the support of every nonzero coordinate of `φ`
lies outside `L`, then the `L`-masked state norm `‖maskL L supp φ‖` vanishes. -/
theorem prop3_19_a [Fintype ι] (L : Set (Finset α)) (supp : ι → Finset α) (φ : State ι)
    (h : ∀ σ, φ σ ≠ 0 → supp σ ∉ L) : ‖maskL L supp φ‖ = 0 := by
  have hzero : maskL L supp φ = 0 := by
    apply Qatlib.Papers.DistinctLB26.MainResults.Core.State.ext
    intro σ
    by_cases hσ : φ σ = 0
    · simp [maskL_apply, hσ]
    · rw [maskL_apply, ind_of_notMem (h σ hσ), zero_mul]
      simp
  rw [hzero]
  simp

/-- **Proposition 3.19(b)** [Belovs2026]: a permutation `permOp e` that preserves support
membership in `L` leaves the `L`-masked state norm unchanged. -/
theorem prop3_19_b [Fintype ι] (L : Set (Finset α)) (supp : ι → Finset α) (e : ι ≃ ι)
    (hinv : ∀ σ, supp (e σ) ∈ L ↔ supp σ ∈ L) (φ : State ι) :
    ‖maskL L supp (permOp e φ)‖ = ‖maskL L supp φ‖ := by
  have hterm : ∀ σ : ι, ‖maskL L supp (permOp e φ) σ‖ ^ 2
      = ‖maskL L supp φ (e.symm σ)‖ ^ 2 := by
    intro σ
    have hiff : supp σ ∈ L ↔ supp (e.symm σ) ∈ L := by
      have := hinv (e.symm σ)
      simpa using this
    by_cases h1 : supp σ ∈ L
    · have h2 : supp (e.symm σ) ∈ L := hiff.mp h1
      simp [maskL_apply, permOp_apply, ind_of_mem h1, ind_of_mem h2]
    · have h2 : supp (e.symm σ) ∉ L := fun hh => h1 (hiff.mpr hh)
      simp [maskL_apply, permOp_apply, ind_of_notMem h1, ind_of_notMem h2]
  have hsq : ‖maskL L supp (permOp e φ)‖ ^ 2 = ‖maskL L supp φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact Fintype.sum_equiv e.symm _ _ hterm
  calc ‖maskL L supp (permOp e φ)‖
      = Real.sqrt (‖maskL L supp (permOp e φ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖maskL L supp φ‖ ^ 2) := by rw [hsq]
    _ = ‖maskL L supp φ‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## Lemma 5.3 (local alterations) -/

/-- **Lemma 5.3 (Local Alterations)** [Belovs2026]: if every `p ∈ Pρ` satisfies the alteration
bound `β p ^ 2 ≤ C * ∑ q ∈ N p d, β q ^ 2` across at least `K` alterations `d : Δ`, and each
`q : P` belongs to at most `K'` sets `N p d` over `(p, d) ∈ Pρ × Δ`, then
`∑ p ∈ Pρ, β p ^ 2 ≤ C * K' / K * ∑ q, β q ^ 2`. -/
theorem lemma5_3 {P Δ : Type*} [Fintype P] [Fintype Δ] [DecidableEq P]
    (N : P → Δ → Finset P) (β : P → ℝ) (Pρ : Finset P) (C K K' : ℝ)
    (_hβ : ∀ p, 0 ≤ β p) (hC : 0 ≤ C) (hK : 0 < K)
    (h54 : ∀ p ∈ Pρ, ∀ d : Δ, β p ^ 2 ≤ C * ∑ q ∈ N p d, β q ^ 2)
    (hK' : ∀ q : P, (∑ p ∈ Pρ, ∑ d : Δ, if q ∈ N p d then (1 : ℝ) else 0) ≤ K')
    (hΔ : ∀ p ∈ Pρ, K ≤ (Fintype.card Δ : ℝ)) :
    ∑ p ∈ Pρ, β p ^ 2 ≤ C * K' / K * ∑ q, β q ^ 2 := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hK, mul_comm _ K]
  calc K * ∑ p ∈ Pρ, β p ^ 2
      = ∑ p ∈ Pρ, K * β p ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ Pρ, (Fintype.card Δ : ℝ) * β p ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact mul_le_mul_of_nonneg_right (hΔ p hp) (sq_nonneg _)
    _ = ∑ p ∈ Pρ, ∑ _d : Δ, β p ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ Pρ, ∑ d : Δ, C * ∑ q ∈ N p d, β q ^ 2 := by
        refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun d _ => h54 p hp d
    _ = ∑ p ∈ Pρ, ∑ d : Δ, ∑ q : P,
          (if q ∈ N p d then (1 : ℝ) else 0) * (C * β q ^ 2) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        symm
        calc ∑ q : P, (if q ∈ N p d then (1 : ℝ) else 0) * (C * β q ^ 2)
            = ∑ q : P, if q ∈ N p d then C * β q ^ 2 else 0 := by
                refine Finset.sum_congr rfl fun q _ => ?_
                split_ifs <;> ring
          _ = ∑ q ∈ Finset.univ.filter (· ∈ N p d), C * β q ^ 2 := by
                rw [← Finset.sum_filter]
          _ = ∑ q ∈ N p d, C * β q ^ 2 := by
                refine Finset.sum_congr ?_ fun _ _ => rfl
                ext q
                simp
    _ = ∑ q : P,
          (∑ p ∈ Pρ, ∑ d : Δ, if q ∈ N p d then (1 : ℝ) else 0) * (C * β q ^ 2) := by
        trans ∑ p ∈ Pρ, ∑ q : P, ∑ d : Δ,
          (if q ∈ N p d then (1 : ℝ) else 0) * (C * β q ^ 2)
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ q : P, K' * (C * β q ^ 2) := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact mul_le_mul_of_nonneg_right (hK' q) (mul_nonneg hC (sq_nonneg _))
    _ = C * K' * ∑ q : P, β q ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## Claim 6.5 (orbit sizes) and its corollaries -/

/-- **Claim 6.5** [Belovs2026]: reduced orbit-counting step showing that if `A = C`,
`A * n ≤ c₁ * B`, and `c₂ * D ≤ C` with positive constants `c₁, c₂`, then `(c₂ / c₁) * n * D ≤ B`. -/
theorem claim6_5 (n A B C D c₁ c₂ : ℝ) (_hn : 0 < n) (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (hAB : A = C) (hA : A * n ≤ c₁ * B) (hC : c₂ * D ≤ C) :
    ∃ c : ℝ, 0 < c ∧ c * n * D ≤ B := by
  refine ⟨c₂ / c₁, div_pos h₂ h₁, ?_⟩
  have hA' : C * n ≤ c₁ * B := by rw [← hAB]; exact hA
  have h4 : c₂ * D * n ≤ c₁ * B := by nlinarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ h₁]
  nlinarith [h4]

/-- **Lemma 6.6** [Belovs2026]: root-ratio norm comparison `a ^ 2 ≤ (m₁ / m₂) * b ^ 2 →
a ≤ √(m₁ / m₂) * b` for nonnegative norms `a, b` and `0 ≤ m₁`, `0 < m₂`. -/
theorem lemma6_6 (a b m₁ m₂ : ℝ) (hm : 0 < m₂) (hm₁ : 0 ≤ m₁) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ m₁ / m₂ * b ^ 2) :
    a ≤ Real.sqrt (m₁ / m₂) * b := by
  have hr : 0 ≤ m₁ / m₂ := div_nonneg hm₁ (le_of_lt hm)
  have hsq : a ^ 2 ≤ (Real.sqrt (m₁ / m₂) * b) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hr]
    exact h
  have hb' : 0 ≤ Real.sqrt (m₁ / m₂) * b := mul_nonneg (Real.sqrt_nonneg _) hb
  have h1 := (sq_le_sq).mp hsq
  rwa [abs_of_nonneg ha, abs_of_nonneg hb'] at h1

/-- **Corollary 6.7** [Belovs2026]: combining Lemma 6.6 with the orbit-size ratio
`m₁ ≤ C * m₂ / n` yields `a ≤ √(C / n) * b`. -/
theorem cor6_7 (a b m₁ m₂ C n : ℝ) (hm₂ : 0 < m₂) (hm₁ : 0 ≤ m₁) (_hC : 0 ≤ C)
    (hn : 0 < n) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h66 : a ^ 2 ≤ m₁ / m₂ * b ^ 2) (hratio : m₁ ≤ C * m₂ / n) :
    a ≤ Real.sqrt (C / n) * b := by
  have hle : m₁ / m₂ ≤ C / n := by
    rw [div_le_div_iff₀ hm₂ hn]
    rw [le_div_iff₀ hn] at hratio
    exact hratio
  calc a ≤ Real.sqrt (m₁ / m₂) * b := lemma6_6 a b m₁ m₂ hm₂ hm₁ ha hb h66
    _ ≤ Real.sqrt (C / n) * b :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hle) hb

/-- **Lemma 6.8** [Belovs2026]: singleton-highlighting norm bound
`a ^ 2 ≤ t / (c * n) * b ^ 2 → a ≤ √(t / (c * n)) * b`. -/
theorem lemma6_8 (a b t n c : ℝ) (ht : 0 ≤ t) (hn : 0 < n) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ t / (c * n) * b ^ 2) :
    a ≤ Real.sqrt (t / (c * n)) * b :=
  lemma6_6 a b t (c * n) (mul_pos hc hn) ht ha hb h

/-- **Theorem 6.9 (Element Distinctness, Query Gain)** [Belovs2026]: telescoping the single-step
gains `g j ≤ √(1 / n) * (A j + A (j + 1))` with `A j ≤ √(t / (c * n))` over `j < t` yields
`K t ≤ 2 * t * √(t / (c * n ^ 2))`. -/
theorem theorem6_9 (A g K : ℕ → ℝ) (t : ℕ) (c n : ℝ) (hc : 0 < c) (hn : 0 < n)
    (hA : ∀ j, j ≤ t → A j ≤ Real.sqrt (t / (c * n)))
    (hg : ∀ j, g j ≤ Real.sqrt (1 / n) * (A j + A (j + 1)))
    (htel : K t ≤ ∑ j ∈ Finset.range t, g j) :
    K t ≤ 2 * (t : ℝ) * Real.sqrt (t / (c * n ^ 2)) := by
  have hstep : ∀ j ∈ Finset.range t, g j ≤ 2 * Real.sqrt (t / (c * n ^ 2)) := by
    intro j hj
    have hjs : j < t := Finset.mem_range.mp hj
    have h1 : A j ≤ Real.sqrt (t / (c * n)) := hA j (le_of_lt hjs)
    have h2 : A (j + 1) ≤ Real.sqrt (t / (c * n)) := hA (j + 1) hjs
    have hA2 : A j + A (j + 1) ≤ 2 * Real.sqrt (t / (c * n)) := by linarith
    have hg' : g j ≤ Real.sqrt (1 / n) * (2 * Real.sqrt (t / (c * n))) := by
      calc g j ≤ Real.sqrt (1 / n) * (A j + A (j + 1)) := hg j
        _ ≤ Real.sqrt (1 / n) * (2 * Real.sqrt (t / (c * n))) :=
            mul_le_mul_of_nonneg_left hA2 (Real.sqrt_nonneg _)
    have hroot : Real.sqrt (1 / n) * (2 * Real.sqrt (t / (c * n)))
        = 2 * Real.sqrt (t / (c * n ^ 2)) := by
      have harg : (1 / n) * (t / (c * n)) = t / (c * n ^ 2) := by
        field_simp
      calc Real.sqrt (1 / n) * (2 * Real.sqrt (t / (c * n)))
          = 2 * (Real.sqrt (1 / n) * Real.sqrt (t / (c * n))) := by ring
        _ = 2 * Real.sqrt ((1 / n) * (t / (c * n))) := by
            rw [Real.sqrt_mul (by positivity)]
        _ = 2 * Real.sqrt (t / (c * n ^ 2)) := by rw [harg]
    linarith [hg', hroot.le, hroot.ge]
  calc K t ≤ ∑ j ∈ Finset.range t, g j := htel
    _ ≤ ∑ _j ∈ Finset.range t, (2 * Real.sqrt (t / (c * n ^ 2))) := Finset.sum_le_sum hstep
    _ = (Finset.range t).card • (2 * Real.sqrt (t / (c * n ^ 2))) := Finset.sum_const _
    _ = (t : ℝ) * (2 * Real.sqrt (t / (c * n ^ 2))) := by
        rw [Finset.card_range, nsmul_eq_mul]
    _ = 2 * (t : ℝ) * Real.sqrt (t / (c * n ^ 2)) := by ring

/-! ## Lemma 6.14 (small `Ξ`-component of the knowledge) -/

/-- **Lemma 6.14** [Belovs2026]: `1 / (c * n)` squared-norm suppression implies
`a ≤ √(1 / (c * n)) * b`. -/
theorem lemma6_14 (a b n c : ℝ) (hn : 0 < n) (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ 1 / (c * n) * b ^ 2) :
    a ≤ Real.sqrt (1 / (c * n)) * b :=
  lemma6_6 a b 1 (c * n) (mul_pos hc hn) zero_le_one ha hb h

end Qatlib.Papers.DistinctLB26.MainResults.Framework
