/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.MonteCarloBound

/-!
# Sample mean variance and repetition bounds

This module factors expectations under finite product weights and derives the variance of an
independent sample mean. The resulting Chebyshev bounds give sufficient repetition counts for
estimating unit interval observables in the sampling discussion of [LidarWang1999].

It also bounds repeated failure probabilities by an exponential and gives a sufficient number of
repetitions to observe an event of positive probability.

## Main statements

* `variance_sampleMean`: gives the variance reduction by a factor of the positive sample count.
* `repetition_bound`: bounds the sample mean deviation probability by a prescribed positive
  tolerance.
* `rare_event_repetitions`: bounds the probability of missing an event in every repetition.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ThermalRate98.MainResults

section Single

variable {α : Type*} [Fintype α]

/-- Finite weighted expectation commutes with a finite sum of functions. -/
theorem expect_finsetSum {ι : Type*} [Fintype ι] (p : α → ℝ) (f : ι → α → ℝ) :
    expect p (fun a => ∑ i, f i a) = ∑ i, expect p (f i) := by
  unfold expect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- Subtracting the expectation produces a function with zero weighted expectation when the
weights sum to one. -/
theorem expect_centered_zero (p X : α → ℝ) (hsum : ∑ a, p a = 1) :
    expect p (fun a => X a - expect p X) = 0 := by
  rw [expect_sub, expect_const p hsum]
  ring

end Single

section Product

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Under product weights, the expectation of a product of coordinate functions is the product
of their individual weighted expectations. See [LidarWang1999]. -/
theorem expect_prod_factor (p : α → ℝ) {n : ℕ} (f : Fin n → α → ℝ) :
    expect (prodProb p n) (fun ω => ∏ i, f i (ω i)) = ∏ i, expect p (f i) := by
  unfold expect prodProb
  trans ∑ ω : Fin n → α, ∏ i, (p (ω i) * f i (ω i))
  · apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.prod_mul_distrib]
  · exact sum_prod_factor (fun i x => p x * f i x)

/-- A finite product with a single potentially nonunit factor equals that factor. -/
theorem prod_ite_one {n : ℕ} {β : Type*} (u : Fin n → β) (g : β → ℝ) (i : Fin n) :
    (∏ k, (if k = i then g (u k) else (1 : ℝ))) = g (u i) := by
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i
    (fun k => if k = i then g (u k) else (1 : ℝ)) (by simp)]
  simp

/-- A finite product with two specified distinct potentially nonunit factors equals their
product. -/
theorem prod_ite_two {n : ℕ} {β : Type*} (u : Fin n → β) (f g : β → ℝ) {i j : Fin n}
    (hij : i ≠ j) :
    (∏ k, (if k = i then f (u k) else if k = j then g (u k) else (1 : ℝ)))
      = f (u i) * g (u j) := by
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i
    (fun k => if k = i then f (u k) else if k = j then g (u k) else (1 : ℝ)) (by simp)]
  have hmemj : j ∈ Finset.univ \ ({i} : Finset (Fin n)) := by
    simp [show j ≠ i from Ne.symm hij]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmemj
    (fun k => if k = i then f (u k) else if k = j then g (u k) else (1 : ℝ))]
  have hrest : (∏ x ∈ (Finset.univ \ ({i} : Finset (Fin n))) \ {j},
      (if x = i then f (u x) else if x = j then g (u x) else (1 : ℝ))) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    have hx' : x ≠ i ∧ x ≠ j := by
      simpa only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] using hx
    simp [hx'.1, hx'.2]
  rw [hrest]
  rw [ite_eq_left rfl]
  rw [ite_eq_right (show j ≠ i from Ne.symm hij)]
  rw [ite_eq_left rfl]
  ring

/-- Under product weights whose base weights sum to one, a function of one coordinate has its
original weighted expectation. -/
theorem expect_coord (p : α → ℝ) (hsum : ∑ a, p a = 1) {n : ℕ} (g : α → ℝ)
    (i : Fin n) :
    expect (prodProb p n) (fun ω => g (ω i)) = expect p g := by
  have hprod : (fun ω : Fin n → α => g (ω i)) =
      fun ω => ∏ k, (if k = i then g (ω k) else (1 : ℝ)) := by
    funext ω
    exact (prod_ite_one (fun k => ω k) g i).symm
  rw [hprod]
  have hfac : expect (prodProb p n)
      (fun ω => ∏ k, (if k = i then g (ω k) else (1 : ℝ)))
      = ∏ k, expect p (fun a => if k = i then g a else (1 : ℝ)) :=
    expect_prod_factor (p := p) (n := n) (f := fun k a => if k = i then g a else (1 : ℝ))
  rw [hfac]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i
    (fun k => expect p (fun a => if k = i then g a else (1 : ℝ))) (by simp)]
  have hself : expect p (fun a => if i = i then g a else (1 : ℝ)) = expect p g := by
    simp
  have hother : ∀ k ∈ Finset.univ \ ({i} : Finset (Fin n)),
      expect p (fun a => if k = i then g a else (1 : ℝ)) = 1 := by
    intro k hk
    have hki : k ≠ i := by
      simpa using hk
    simp [hki, expect_const p hsum]
  rw [hself, Finset.prod_eq_one hother, mul_one]

/-- Functions of two distinct coordinates have a factored expectation under product weights
whose base weights sum to one. -/
theorem expect_pair (p : α → ℝ) (hsum : ∑ a, p a = 1) {n : ℕ} (f g : α → ℝ)
    {i j : Fin n} (hij : i ≠ j) :
    expect (prodProb p n) (fun ω => f (ω i) * g (ω j)) = expect p f * expect p g := by
  have hprod : (fun ω : Fin n → α => f (ω i) * g (ω j)) =
      fun ω => ∏ k, (if k = i then f (ω k) else if k = j then g (ω k) else (1 : ℝ)) := by
    funext ω
    exact (prod_ite_two (fun k => ω k) f g hij).symm
  rw [hprod]
  have hfac : expect (prodProb p n)
      (fun ω => ∏ k, (if k = i then f (ω k) else if k = j then g (ω k) else (1 : ℝ)))
      = ∏ k, expect p (fun a => if k = i then f a else if k = j then g a else (1 : ℝ)) :=
    expect_prod_factor (p := p) (n := n)
      (f := fun k a => if k = i then f a else if k = j then g a else (1 : ℝ))
  rw [hfac]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i
    (fun k => expect p (fun a => if k = i then f a else if k = j then g a else (1 : ℝ)))
    (by simp)]
  have hself : expect p (fun a => if i = i then f a else if i = j then g a else (1 : ℝ))
      = expect p f := by
    simp
  have hmemj : j ∈ Finset.univ \ ({i} : Finset (Fin n)) := by
    simp [show j ≠ i from Ne.symm hij]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmemj
    (fun k => expect p (fun a => if k = i then f a else if k = j then g a else (1 : ℝ)))]
  have hselfj : expect p (fun a => if j = i then f a else if j = j then g a else (1 : ℝ))
      = expect p g := by
    simp [show j ≠ i from Ne.symm hij]
  have hrest : ∀ k ∈ (Finset.univ \ ({i} : Finset (Fin n))) \ {j},
      expect p (fun a => if k = i then f a else if k = j then g a else (1 : ℝ)) = 1 := by
    intro k hk
    have hk' : k ≠ i ∧ k ≠ j := by
      simpa only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] using hk
    simp [hk'.1, hk'.2, expect_const p hsum]
  rw [hself, hselfj, Finset.prod_eq_one hrest]
  ring

omit [DecidableEq α] in

/-- The expectation of a product of finite sums expands into the double sum of expectations of
pairwise products. -/
theorem expect_sum_mul_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (p : α → ℝ)
    (f : ι → α → ℝ) (g : κ → α → ℝ) :
    expect p (fun a => (∑ i, f i a) * (∑ j, g j a))
      = ∑ i, ∑ j, expect p (fun a => f i a * g j a) := by
  unfold expect
  have h : ∀ a : α, p a * ((∑ i, f i a) * (∑ j, g j a))
      = ∑ i, ∑ j, p a * (f i a * g j a) := by
    intro a
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc ∑ a, p a * ((∑ i, f i a) * (∑ j, g j a))
      = ∑ a, ∑ i, ∑ j, p a * (f i a * g j a) :=
        Finset.sum_congr rfl (fun a _ => h a)
    _ = ∑ i, ∑ j, ∑ a, p a * (f i a * g j a) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, expect p (fun a => f i a * g j a) := rfl

/-- For a positive number `n` of independent samples from a finite probability distribution, the
sample mean variance equals the original variance divided by `n`. See [LidarWang1999]. -/
theorem variance_sampleMean (p X : α → ℝ) (hp : IsProb p) {n : ℕ} (hn : 0 < n) :
    variance (prodProb p n) (sampleMean X n) = (n : ℝ)⁻¹ * variance p X := by
  classical
  have hsum : ∑ a, p a = 1 := hp.2
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hninv : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero hn'

  have hY0 : expect p (fun a => X a - expect p X) = 0 := expect_centered_zero p X hsum

  have hpt : ∀ ω : Fin n → α,
      sampleMean X n ω - expect (prodProb p n) (sampleMean X n)
        = (n : ℝ)⁻¹ * ∑ i, (X (ω i) - expect p X) := by
    intro ω
    have hmean : expect (prodProb p n) (sampleMean X n) = expect p X :=
      sampleMean_expect p X hp hn
    rw [hmean]
    unfold sampleMean
    have hsumμ : (∑ _i : Fin n, expect p X) = (n : ℝ) * expect p X := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_sub_distrib, hsumμ, mul_sub, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]

  have hvar : variance (prodProb p n) (sampleMean X n)
      = (n : ℝ)⁻¹ ^ 2 *
          expect (prodProb p n) (fun ω => (∑ i, (X (ω i) - expect p X)) ^ 2) := by
    unfold variance
    have h1 : ∀ ω : Fin n → α,
        prodProb p n ω *
            (sampleMean X n ω - expect (prodProb p n) (sampleMean X n)) ^ 2
          = (n : ℝ)⁻¹ ^ 2 *
              (prodProb p n ω * (∑ i, (X (ω i) - expect p X)) ^ 2) := by
      intro ω
      rw [hpt ω]
      ring
    rw [Finset.sum_congr rfl (fun ω _ => h1 ω), ← Finset.mul_sum]
    rfl

  have hsq : expect (prodProb p n) (fun ω => (∑ i, (X (ω i) - expect p X)) ^ 2)
      = ∑ i : Fin n, ∑ j : Fin n,
          expect (prodProb p n) (fun ω => (X (ω i) - expect p X) * (X (ω j) - expect p X)) := by
    have h := expect_sum_mul_sum (p := prodProb p n)
      (f := fun i ω => X (ω i) - expect p X)
      (g := fun j ω => X (ω j) - expect p X)
    simpa [pow_two] using h

  have hinner : ∀ i : Fin n,
      (∑ j : Fin n,
          expect (prodProb p n) (fun ω => (X (ω i) - expect p X) * (X (ω j) - expect p X)))
        = variance p X := by
    intro i
    rw [Finset.sum_eq_single i]
    · have hdiag := expect_coord p hsum (fun a => (X a - expect p X) ^ 2) i
      simpa [pow_two, variance] using! hdiag
    · intro j _ hji
      rw [expect_pair p hsum (fun a => X a - expect p X) (fun a => X a - expect p X)
        (Ne.symm hji), hY0]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hsq2 : expect (prodProb p n) (fun ω => (∑ i, (X (ω i) - expect p X)) ^ 2)
      = (n : ℝ) * variance p X := by
    rw [hsq]
    calc ∑ i : Fin n, ∑ j : Fin n,
          expect (prodProb p n) (fun ω => (X (ω i) - expect p X) * (X (ω j) - expect p X))
        = ∑ _i : Fin n, variance p X := Finset.sum_congr rfl (fun i _ => hinner i)
      _ = (n : ℝ) * variance p X := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hvar, hsq2]
  field_simp

/-- The probability that the sample mean deviates from its expectation by at least positive `ε`
is at most the original variance divided by `n * ε²`, for positive `n`. -/
theorem chebyshev_sampleMean (p X : α → ℝ) (hp : IsProb p) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ ω ∈ Finset.univ.filter (fun ω =>
        ε ≤ |sampleMean X n ω - expect (prodProb p n) (sampleMean X n)|),
        prodProb p n ω) ≤ variance p X / ((n : ℝ) * ε ^ 2) := by
  have hcheb := chebyshev_finite (prodProb p n) (sampleMean X n)
    (prodProb_isProb p hp n).1 hε
  rw [variance_sampleMean p X hp hn] at hcheb
  refine le_trans hcheb (le_of_eq ?_)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hε' : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε.ne'
  field_simp

/-- For observations in the unit interval, at least `1 / (4 * ε² * δ)` independent samples make
the probability of a deviation of at least `ε` no greater than `δ`, for positive `ε` and
`δ`. See [LidarWang1999]. -/
theorem repetition_bound (p X : α → ℝ) (hp : IsProb p) (hX0 : ∀ a, 0 ≤ X a)
    (hX1 : ∀ a, X a ≤ 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {n : ℕ}
    (hn : (1 : ℝ) / (4 * ε ^ 2 * δ) ≤ (n : ℝ)) :
    (∑ ω ∈ Finset.univ.filter (fun ω =>
        ε ≤ |sampleMean X n ω - expect (prodProb p n) (sampleMean X n)|),
        prodProb p n ω) ≤ δ := by
  have hpos : (0 : ℝ) < 4 * ε ^ 2 * δ := by positivity
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · exfalso
      have hgt : (0 : ℝ) < 1 / (4 * ε ^ 2 * δ) := div_pos one_pos hpos
      have hle : (1 : ℝ) / (4 * ε ^ 2 * δ) ≤ 0 := by simpa [h0] using hn
      linarith
    · exact h
  have hcheb := chebyshev_sampleMean p X hp hnpos hε
  refine le_trans hcheb ?_
  have hvar := variance_le_quarter p X hp.1 hp.2 hX0 hX1
  have hle : variance p X / ((n : ℝ) * ε ^ 2) ≤ (1 / 4) / ((n : ℝ) * ε ^ 2) := by
    apply div_le_div_of_nonneg_right hvar
    positivity
  refine le_trans hle ?_
  have h4 : (1 : ℝ) ≤ 4 * (n : ℝ) * ε ^ 2 * δ := by
    have h := mul_le_mul_of_nonneg_right hn hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at h
    calc (1 : ℝ) ≤ (n : ℝ) * (4 * ε ^ 2 * δ) := h
      _ = 4 * (n : ℝ) * ε ^ 2 * δ := by ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * ε ^ 2)]
  nlinarith [h4]

/-- For `p` in the unit interval, the repeated failure factor `(1 - p)^n` is at most `exp (-n *
p)`. -/
theorem one_sub_pow_le_exp (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ Real.exp (-(n : ℝ) * p) := by
  have h0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p ≤ Real.exp (-p) := by
    have h := Real.add_one_le_exp (-p)
    linarith
  calc (1 - p) ^ n ≤ (Real.exp (-p)) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp ((n : ℝ) * (-p)) := (Real.exp_nat_mul (-p) n).symm
    _ = Real.exp (-(n : ℝ) * p) := by
        congr 1
        ring

/-- For `0 < p ≤ 1` and positive `δ`, at least `log (1 / δ) / p` repetitions ensure that `(1 -
p)^n ≤ δ`. See [LidarWang1999]. -/
theorem rare_event_repetitions (p δ : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    {n : ℕ} (hn : Real.log (1 / δ) / p ≤ (n : ℝ)) :
    (1 - p) ^ n ≤ δ := by
  refine le_trans (one_sub_pow_le_exp p hp0.le hp1 n) ?_
  have hnp : Real.log (1 / δ) ≤ (n : ℝ) * p := by
    have := mul_le_mul_of_nonneg_right hn hp0.le
    rwa [div_mul_cancel₀ _ hp0.ne'] at this
  have hlog : Real.log (1 / δ) = -Real.log δ := by
    rw [one_div, Real.log_inv]
  rw [hlog] at hnp
  have hexp : Real.exp (-(n : ℝ) * p) ≤ Real.exp (Real.log δ) := by
    apply Real.exp_le_exp.2
    linarith
  rwa [Real.exp_log hδ] at hexp

end Product

end Qatlib.Papers.ThermalRate98.MainResults
