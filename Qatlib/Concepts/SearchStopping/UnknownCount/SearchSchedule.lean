/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchCircuit

/-!
# Capped exponential schedules for unknown-count search

Defines the search widths with growth factor `6 / 5`, capped at the square root of the
search-space size, and obtains integer ranges by taking ceilings. The schedule laws and
`search_critical_stage` show that a suitable stage reaches the randomized Grover success
threshold. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `search_exponential_schedule`: For positive `N`, the widths equal `min ((6 / 5) ^ k)
  (Real.sqrt N)`, the ceiling sizes are positive and at most twice the exponential scale, and
  sampled indices are exactly the naturals below the real width.
* `search_critical_stage`: For a nonempty proper marked set, there are a density angle and a
  positive stage after which every integer search range reaches `1 / Real.sin (2 * θ)`, with the
  stated bound on the stage's exponential scale.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Concepts.SearchStopping.UnknownCount

open scoped BigOperators

/-- The recursively defined search width, starting at one and multiplying by `6 / 5` at each
stage subject to the cap `Real.sqrt N`. -/
noncomputable def ExponentialWidth (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => min ((6/5 : ℝ) * ExponentialWidth N k) (Real.sqrt N)

/-- The natural-number ceiling of the stage width `ExponentialWidth N k`. -/
noncomputable def ExponentialSizes (N : ℕ) (k : ℕ) : ℕ :=
  Nat.ceil (ExponentialWidth N k)

/-- For positive `N`, the widths equal `min ((6 / 5) ^ k) (Real.sqrt N)`, the ceiling sizes are
positive and at most twice the exponential scale, and sampled indices are exactly the
naturals below the real width. -/
theorem search_exponential_schedule (N : ℕ) (hN : 0 < N) :
    (∀ k, ExponentialWidth N k = min ((6/5 : ℝ)^k) (Real.sqrt N)) ∧
    (∀ k, 0 < ExponentialSizes N k) ∧
    (∀ k, (ExponentialSizes N k : ℝ) ≤ 2 * (6/5 : ℝ)^k) ∧
    ∀ k j : ℕ, j < ExponentialSizes N k ↔ (j : ℝ) < ExponentialWidth N k := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hcap : 1 ≤ Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N)]
  have hclosed (k : ℕ) : ExponentialWidth N k = min ((6/5 : ℝ)^k) (Real.sqrt N) := by
    induction k with
    | zero => simp [ExponentialWidth, min_eq_left hcap]
    | succ k ih =>
      rw [ExponentialWidth, ih]
      by_cases hk : (6/5 : ℝ)^k ≤ Real.sqrt N
      · rw [min_eq_left hk, pow_succ]
        congr 1
        ring
      · have hc : Real.sqrt N ≤ (6/5 : ℝ)^k := le_of_not_ge hk
        have hc' : Real.sqrt N ≤ (6/5 : ℝ) * Real.sqrt N := by nlinarith
        have hk' : Real.sqrt N ≤ (6/5 : ℝ)^k * (6/5) := by nlinarith
        rw [min_eq_right hc, min_eq_right hc', pow_succ, min_eq_right hk']
  have hone (k : ℕ) : 1 ≤ (6/5 : ℝ)^k := one_le_pow₀ (by norm_num)
  have hwidth (k : ℕ) : 0 < ExponentialWidth N k := by
    rw [hclosed]
    exact lt_min (by positivity) (by linarith)
  refine ⟨hclosed, ?_, ?_, ?_⟩
  · intro k
    exact Nat.ceil_pos.mpr (hwidth k)
  · intro k
    have hceil := Nat.ceil_lt_add_one (hwidth k).le
    have hw : ExponentialWidth N k ≤ (6/5 : ℝ)^k := by rw [hclosed]; exact min_le_left _ _
    have ho := hone k
    change (Nat.ceil (ExponentialWidth N k) : ℝ) ≤ _
    linarith
  · intro k j
    exact Nat.lt_ceil

/-- Every real threshold `m0 ≥ 1` is crossed by a power of `6 / 5` that is at most `6 / 5` times
the threshold. -/
theorem search_first_scale_crossing (m0 : ℝ) (hm0 : 1 ≤ m0) :
    ∃ K : ℕ, m0 ≤ (6/5 : ℝ)^K ∧ (6/5 : ℝ)^K ≤ (6/5) * m0 := by
  classical
  have bernoulli (n : ℕ) : 1 + (n : ℝ)/5 ≤ (6/5 : ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
  have hex : ∃ n : ℕ, m0 ≤ (6/5 : ℝ)^n := by
    obtain ⟨n,hn⟩ := exists_nat_gt (5*m0)
    refine ⟨n, ?_⟩
    have h := bernoulli n
    linarith
  let K := Nat.find hex
  refine ⟨K, Nat.find_spec hex, ?_⟩
  by_cases hK : K = 0
  · rw [hK, pow_zero]
    linarith
  · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hK
    have hsmall : (6/5 : ℝ)^k < m0 := by
      apply lt_of_not_ge
      intro h
      have hmin := Nat.find_min' hex h
      change K ≤ k at hmin
      omega
    rw [hk, pow_succ]
    nlinarith

/-- For a nontrivial marked count and an angle in `(0, π/2)` with the prescribed density, `1 /
Real.sin (2 * θ)` lies between one and `Real.sqrt N`. -/
theorem search_integer_cap (N t : ℕ) (ht : 0 < t) (htN : t < N)
    (θ : ℝ) (hθ0 : 0 < θ) (hθp : θ < Real.pi / 2)
    (hdensity : (Real.sin θ)^2 = (t : ℝ) / N) :
    1 ≤ 1 / Real.sin (2 * θ) ∧ 1 / Real.sin (2 * θ) ≤ Real.sqrt N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hgap : (t : ℝ) + 1 ≤ N := by exact_mod_cast htN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp⟩
  have h2 : 0 < Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hd : (Real.sin θ)^2 * N = t := (eq_div_iff hNr.ne').mp hdensity
  have hc2 : (Real.cos θ)^2 * N = N - t := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hprod : (N : ℝ) ≤ 4 * t * ((N : ℝ) - t) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t-1) (by linarith : (0 : ℝ) ≤ N-t-1)]
  have hsq : (Real.sin (2*θ))^2 * (N : ℝ)^2 = 4 * t * ((N : ℝ)-t) := by
    rw [Real.sin_two_mul]
    calc
      _ = 4 * ((Real.sin θ)^2 * N) * ((Real.cos θ)^2 * N) := by ring
      _ = _ := by rw [hd, hc2]
  have hbound : 1 ≤ (Real.sin (2*θ))^2 * N := by nlinarith
  have hroot : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hroot2 := Real.sq_sqrt hNr.le
  have hmul : 1 ≤ Real.sin (2*θ) * Real.sqrt N := by
    nlinarith [sq_nonneg (Real.sin (2*θ) * Real.sqrt N - 1),
      mul_nonneg h2.le hroot, sq_nonneg (Real.sin (2*θ) * Real.sqrt N)]
  constructor
  · apply (le_div_iff₀ h2).2
    simpa using Real.sin_le_one (2*θ)
  · exact (div_le_iff₀ h2).2 (by nlinarith)

/-- For a nonempty proper marked set, there are a density angle and a positive stage after which
every integer search range reaches `1 / Real.sin (2 * θ)`, with the stated bound on the
stage's exponential scale. -/
theorem search_critical_stage {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ) ∧
      ∃ L : ℕ, 0 < L ∧ (6/5 : ℝ)^L ≤ (6/5) * (1 / Real.sin (2*θ)) ∧
        ∀ k, L ≤ k → 1 / Real.sin (2*θ) ≤ (ExponentialSizes (Fintype.card I) k : ℝ) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  obtain ⟨θ,hθ0,hθp,hdensity,h2⟩ := search_principal_angle A hA hproper
  have hscale := search_integer_cap (Fintype.card I) A.card hA hproper θ hθ0 hθp hdensity
  obtain ⟨K,hKlo,hKhi⟩ := search_first_scale_crossing (1 / Real.sin (2*θ)) hscale.1
  let L := max K 1
  have hKL : K ≤ L := le_max_left _ _
  have hL : 0 < L := lt_of_lt_of_le (by omega : 0 < 1) (le_max_right _ _)
  have hLhi : (6/5 : ℝ)^L ≤ (6/5) * (1 / Real.sin (2*θ)) := by
    by_cases hK : K = 0
    · simp only [L, hK, max_eq_right (by omega : 0 ≤ 1), pow_one]
      nlinarith [hscale.1]
    · have heq : L = K := max_eq_left (by omega)
      rw [heq]
      exact hKhi
  refine ⟨θ,hθ0,hθp,hdensity,L,hL,hLhi,?_⟩
  intro k hk
  have hone (n : ℕ) : 1 ≤ (6/5 : ℝ)^n := one_le_pow₀ (by norm_num)
  have hp : (6/5 : ℝ)^K ≤ (6/5 : ℝ)^k := by
    have heq : k = K + (k-K) := by omega
    rw [heq, pow_add]
    exact le_mul_of_one_le_right (by positivity) (hone (k-K))
  change _ ≤ (Nat.ceil (ExponentialWidth (Fintype.card I) k) : ℝ)
  apply le_trans _ (Nat.le_ceil _)
  rw [(search_exponential_schedule _ hN).1]
  exact le_min (hKlo.trans hp) hscale.2

end Qatlib.Concepts.SearchStopping.UnknownCount
