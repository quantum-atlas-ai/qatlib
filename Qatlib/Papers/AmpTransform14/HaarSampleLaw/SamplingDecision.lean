/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Qatlib.Papers.AmpTransform14.ScalarHaar

@[expose] public section

/-!
# A finite decision bound for the Haar sample size

Chapter 5 of [Cornwell2014], printed pp. 115-117, compares a classical sample test counting sites
of success probability `M/N` against one counting sites of success probability `1 - M/N`. Their
means straddle `1/2` and they share the variance `M/N * (1 - M/N)`; the printed sample size
`36 * M * (1 - M/N) / (1 - 2 * M/N)^2` is where the two normal three-sigma intervals meet, which
is the algebraic identity `Qatlib.Papers.AmpTransform14.ScalarHaar.sampleSize_threeSigma_intersection`.

This module replaces the Gaussian step by an exact finite statement over the independent
Bernoulli law on `n` sites. The empirical proportion is the sample average of a bounded
indicator, so `FinDist.chebyshev_avg` bounds the misidentification probability of the
proportional rule (declare the balanced case when the observed proportion reaches `1/2`) by
`16 * p * (1 - p) / (n * (1 - 2p)^2)`; at `n = Nat.floor (sampleSize M N)` this is at most
`8 / (9 * N)`, below `1/2` for every feasible size. The classical-versus-quantum cost comparison
of the chapter, the printed `M > N^(1/3)` threshold, and the tightness of the printed sample size
are not proved here.

## Main statements

* `bernoulliLaw`: the Bernoulli law on one bit with success probability `p`.
* `expect_bitIndicator`, `variance_bitIndicator`: mean `p` and variance `p * (1 - p)` of the
  success indicator.
* `empirical_tail_le`: the Chebyshev bound for the deviation of the sample proportion.
* `empirical_upper_le`, `empirical_lower_le`: the two one-sided misidentification bounds.
* `sampleSize_lower`, `sampling_tail_bound`: the printed sample size is at least eighteen, and the
  Chebyshev bound there is at most `8 / (9 * N)`.
* `haar_sampling_decision`: at the printed sample size the proportional rule misidentifies the
  constant or the balanced case with probability at most `8 / (9 * N) < 1/2`.

## References

* [Cornwell, 2014][Cornwell2014], Chapter 5, printed pp. 115-117,
  [arXiv:1406.0190](https://arxiv.org/abs/1406.0190)
-/

set_option autoImplicit false

namespace Qatlib.Papers.AmpTransform14.HaarSampleLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.AmpTransform14.ScalarHaar

open scoped Classical BigOperators

attribute [local instance] Classical.propDecidable

/-- The Bernoulli law on a single bit whose success probability is `p`. -/
def bernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinDist Bool where
  prob b := if b then p else 1 - p
  nonneg b := by
    cases b with
    | true => simpa using hp0
    | false => simpa using sub_nonneg.mpr hp1
  sum_one := by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    ring

/-- The indicator of the success event on a single bit. -/
def bitIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- The success probability `M/N` is nonnegative. -/
theorem ratio_nonneg (M N : ℕ) : 0 ≤ (M : ℝ) / N :=
  div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg N)

/-- The success probability `M/N` is at most one when `M <= N`. -/
theorem ratio_le_one {M N : ℕ} (hMN : M ≤ N) (hN : 0 < N) : (M : ℝ) / N ≤ 1 := by
  rw [div_le_one (by exact_mod_cast hN)]
  exact_mod_cast hMN

/-- The half-density comparison `2 * M < N` in the reals. -/
theorem two_mul_cast_lt {M N : ℕ} (hMN : 2 * M < N) : (2 : ℝ) * (M : ℝ) < (N : ℝ) := by
  have h : ((2 * M : ℕ) : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hMN
  push_cast at h
  linarith

/-- The success indicator has expectation `p` under the Bernoulli law. -/
theorem expect_bitIndicator {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw p hp0 hp1).expect bitIndicator = p := by
  rw [FinDist.expect, Fintype.sum_bool]
  simp only [bernoulliLaw, bitIndicator, Bool.false_eq_true, ite_false, ite_true]
  ring

/-- The success indicator has variance `p * (1 - p)` under the Bernoulli law. -/
theorem variance_bitIndicator {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw p hp0 hp1).variance bitIndicator = p * (1 - p) := by
  rw [FinDist.variance, expect_bitIndicator hp0 hp1, FinDist.expect, Fintype.sum_bool]
  simp only [bernoulliLaw, bitIndicator, Bool.false_eq_true, ite_false, ite_true]
  ring

/-- Event monotonicity for finite independent sample records. -/
theorem probEvent_mono {X : Type*} [Fintype X] {L : ℕ} (p : FinDist X)
    {E E' : (Fin L → X) → Prop} (h : ∀ ω, E ω → E' ω) :
    p.probEvent E ≤ p.probEvent E' := by
  unfold FinDist.probEvent
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩
  · intro ω _ _
    exact Finset.prod_nonneg (fun i _ => p.nonneg _)

/-- Chebyshev bound for the deviation of the sample proportion from the success probability. -/
theorem empirical_tail_le {n : ℕ} (hn : 0 < n) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 < ε) :
    (bernoulliLaw p hp0 hp1).probEvent
        (fun ω : Fin n → Bool => ε < |FinDist.avg bitIndicator ω - p|) ≤
      p * (1 - p) / ((n : ℝ) * ε ^ 2) := by
  have h := FinDist.chebyshev_avg (bernoulliLaw p hp0 hp1) bitIndicator hn ε hε
  rw [expect_bitIndicator hp0 hp1, variance_bitIndicator hp0 hp1] at h
  exact h

/-- If `p < 1/2`, the probability that the observed proportion reaches `1/2` is at most
`16 * p * (1 - p) / (n * (1 - 2p)^2)`. -/
theorem empirical_upper_le {n : ℕ} (hn : 0 < n) {p : ℝ} (hp0 : 0 < p) (hp2 : p < 1 / 2) :
    (bernoulliLaw p hp0.le (by linarith : p ≤ 1)).probEvent
        (fun ω : Fin n → Bool => 1 / 2 ≤ FinDist.avg bitIndicator ω) ≤
      16 * p * (1 - p) / ((n : ℝ) * (1 - 2 * p) ^ 2) := by
  have hε : 0 < (1 - 2 * p) / 4 := by linarith
  have hbound := empirical_tail_le hn hp0.le (by linarith : p ≤ 1) hε
  have hmono : (bernoulliLaw p hp0.le (by linarith : p ≤ 1)).probEvent
        (fun ω : Fin n → Bool => 1 / 2 ≤ FinDist.avg bitIndicator ω) ≤
      (bernoulliLaw p hp0.le (by linarith : p ≤ 1)).probEvent
        (fun ω : Fin n → Bool => (1 - 2 * p) / 4 < |FinDist.avg bitIndicator ω - p|) := by
    refine probEvent_mono _ ?_
    intro ω hω
    have hpos : 0 < FinDist.avg bitIndicator ω - p := by linarith
    rw [abs_of_pos hpos]
    linarith
  refine hmono.trans (hbound.trans (le_of_eq ?_))
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsq : 1 - 2 * p ≠ 0 := by linarith
  field_simp
  ring

/-- If `1/2 < q <= 1`, the probability that the observed proportion stays below `1/2` is at most
`16 * q * (1 - q) / (n * (2q - 1)^2)`. -/
theorem empirical_lower_le {n : ℕ} (hn : 0 < n) {q : ℝ} (hq : 1 / 2 < q) (hq1 : q ≤ 1) :
    (bernoulliLaw q (by linarith : (0:ℝ) ≤ q) hq1).probEvent
        (fun ω : Fin n → Bool => FinDist.avg bitIndicator ω < 1 / 2) ≤
      16 * q * (1 - q) / ((n : ℝ) * (2 * q - 1) ^ 2) := by
  have hε : 0 < (q - 1 / 2) / 2 := by linarith
  have hbound := empirical_tail_le hn (by linarith : (0:ℝ) ≤ q) hq1 hε
  have hmono : (bernoulliLaw q (by linarith : (0:ℝ) ≤ q) hq1).probEvent
        (fun ω : Fin n → Bool => FinDist.avg bitIndicator ω < 1 / 2) ≤
      (bernoulliLaw q (by linarith : (0:ℝ) ≤ q) hq1).probEvent
        (fun ω : Fin n → Bool => (q - 1 / 2) / 2 < |FinDist.avg bitIndicator ω - q|) := by
    refine probEvent_mono _ ?_
    intro ω hω
    have hneg : FinDist.avg bitIndicator ω - q < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  refine hmono.trans (hbound.trans (le_of_eq ?_))
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsq : 2 * q - 1 ≠ 0 := by linarith
  have hshape : q - 1 / 2 = (2 * q - 1) / 2 := by ring
  rw [hshape]
  field_simp
  ring

/-- The density gap `1 - 2 * M / N` that the printed sample size divides by. -/
noncomputable def gap (M N : ℕ) : ℝ := 1 - 2 * (M : ℝ) / N

/-- The printed sample size written with the density gap. -/
theorem sampleSize_eq (M N : ℕ) :
    sampleSize (M : ℝ) (N : ℝ) = 36 * (M : ℝ) * (1 - (M : ℝ) / N) / (gap M N) ^ 2 := rfl

/-- The density gap is `1 - 2 * (M/N)`, with the scalar product pulled inside the quotient. -/
theorem gap_eq (M N : ℕ) : gap M N = 1 - 2 * ((M : ℝ) / N) := by
  have h : 2 * (M : ℝ) / N = 2 * ((M : ℝ) / N) := by rw [mul_div_assoc]
  unfold gap
  rw [h]

/-- The density gap is positive under positive half density. -/
theorem gap_pos (M N : ℕ) (hMN : 2 * M < N) : 0 < gap M N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm : (M : ℝ) / N < 1 / 2 := by
    rw [div_lt_iff₀ hNR]
    linarith [two_mul_cast_lt hMN]
  rw [gap_eq]
  linarith

/-- The density gap is at most one. -/
theorem gap_le_one (M N : ℕ) : gap M N ≤ 1 := by
  have h : 0 ≤ (M : ℝ) / N := ratio_nonneg M N
  rw [gap_eq]
  linarith

/-- The printed sample size is at least eighteen. -/
theorem sampleSize_lower (M N : ℕ) (hM : 0 < M) (hMN : 2 * M < N) :
    18 ≤ sampleSize (M : ℝ) (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMR1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp1 : (M : ℝ) / N < 1 / 2 := by
    rw [div_lt_iff₀ hNR]
    linarith [two_mul_cast_lt hMN]
  have hp0 : 0 < (M : ℝ) / N := div_pos hMR hNR
  have h1 : (1 / 2 : ℝ) ≤ 1 - (M : ℝ) / N := by linarith
  have hgap := gap_pos M N hMN
  have hgap1 : gap M N ≤ 1 := gap_le_one M N
  have hgapsq : (gap M N) ^ 2 ≤ 1 := by nlinarith
  have hprod : (1 : ℝ) * (1 / 2) ≤ (M : ℝ) * (1 - (M : ℝ) / N) :=
    mul_le_mul hMR1 h1 (by norm_num) (by linarith)
  have hnum : 18 * (gap M N) ^ 2 ≤ 36 * (M : ℝ) * (1 - (M : ℝ) / N) := by nlinarith
  rw [sampleSize_eq]
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < (gap M N) ^ 2)).mpr (by linarith)

/-- At the printed sample size, the Chebyshev bound for the proportional rule is at most
`8 / (9 * N)`. -/
theorem sampling_tail_bound (M N n : ℕ) (hM : 0 < M) (hMN : 2 * M < N)
    (hn : sampleSize (M : ℝ) (N : ℝ) / 2 ≤ (n : ℝ)) :
    16 * ((M : ℝ) / N) * (1 - (M : ℝ) / N)
        / ((n : ℝ) * (gap M N) ^ 2) ≤ 8 / (9 * (N : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp1 : (M : ℝ) / N < 1 / 2 := by
    rw [div_lt_iff₀ hNR]
    linarith [two_mul_cast_lt hMN]
  have hp0 : 0 < (M : ℝ) / N := div_pos hMR hNR
  have h1m : 0 ≤ 1 - (M : ℝ) / N := by linarith
  have hgap := gap_pos M N hMN
  have hsq : 0 < (gap M N) ^ 2 := by positivity
  have hs : 0 < sampleSize (M : ℝ) (N : ℝ) := sampleSize_pos hMR (two_mul_cast_lt hMN)
  have hA : 0 ≤ 16 * ((M : ℝ) / N) * (1 - (M : ℝ) / N) :=
    mul_nonneg (mul_nonneg (by norm_num) hp0.le) h1m
  have hstep : 16 * ((M : ℝ) / N) * (1 - (M : ℝ) / N) / ((n : ℝ) * (gap M N) ^ 2) ≤
      16 * ((M : ℝ) / N) * (1 - (M : ℝ) / N)
        / ((sampleSize (M : ℝ) (N : ℝ) / 2) * (gap M N) ^ 2) := by
    refine div_le_div_of_nonneg_left hA (by positivity) ?_
    exact mul_le_mul_of_nonneg_right hn (le_of_lt hsq)
  refine hstep.trans (le_of_eq ?_)
  rw [show (sampleSize (M : ℝ) (N : ℝ) / 2) * (gap M N) ^ 2
      = (36 * (M : ℝ) * (1 - (M : ℝ) / N)) / 2 by
    rw [show gap M N ^ 2 = (1 - 2 * ((M : ℝ) / N)) ^ 2 from congrArg (· ^ 2) (gap_eq M N),
      show (sampleSize (M : ℝ) (N : ℝ) / 2) * (1 - 2 * ((M : ℝ) / N)) ^ 2
        = (sampleSize (M : ℝ) (N : ℝ) * (1 - 2 * ((M : ℝ) / N)) ^ 2) / 2 by ring]
    have hspec := sampleSize_spec hMR (two_mul_cast_lt hMN)
    have hspec' : sampleSize (M : ℝ) (N : ℝ) * (1 - 2 * ((M : ℝ) / N)) ^ 2
        = 36 * (M : ℝ) * (1 - (M : ℝ) / N) := by
      have h2 : 2 * (M : ℝ) / N = 2 * ((M : ℝ) / N) := by rw [mul_div_assoc]
      rw [← h2]
      exact hspec
    rw [hspec']]
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMR
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have h1mne : 1 - (M : ℝ) / N ≠ 0 := by
    have hlt : (M : ℝ) / N < 1 := by linarith
    linarith
  have hNM : (N : ℝ) - (M : ℝ) ≠ 0 := by
    have hlt : (M : ℝ) < N := by
      linarith [two_mul_cast_lt hMN, hMR]
    linarith
  field_simp
  ring

/-- The constant-case misidentification probability at sample size `n`: the proportional rule
declares the balanced case when the observed proportion reaches `1/2`. -/
noncomputable def constantCaseMisident (M N n : ℕ) (hMN : M ≤ N) (hN : 0 < N) : ℝ :=
  (bernoulliLaw ((M : ℝ) / N) (ratio_nonneg M N) (ratio_le_one hMN hN)).probEvent
    (L := n) (fun ω : Fin n → Bool => 1 / 2 ≤ FinDist.avg bitIndicator ω)

/-- The balanced-case misidentification probability at sample size `n`: the proportional rule
declares the constant case when the observed proportion stays below `1/2`. -/
noncomputable def balancedCaseMisident (M N n : ℕ) (hMN : M ≤ N) (hN : 0 < N) : ℝ :=
  (bernoulliLaw (1 - (M : ℝ) / N) (by linarith [ratio_le_one hMN hN])
      (by linarith [ratio_nonneg M N])).probEvent
    (L := n) (fun ω : Fin n → Bool => FinDist.avg bitIndicator ω < 1 / 2)

/-- At the printed sample size the proportional rule misidentifies the constant case (success
probability `M/N`) or the balanced case (success probability `1 - M/N`) with probability at most
`8 / (9 * N)`, which is below `1/2` for every feasible size. -/
theorem haar_sampling_decision (M N : ℕ) (hM : 0 < M) (hMN : 2 * M < N) :
    ∃ eps : ℝ,
      0 ≤ eps ∧ eps < 1 / 2 ∧
        constantCaseMisident M N (Nat.floor (sampleSize (M : ℝ) (N : ℝ)))
            (by omega) (by omega) ≤ eps ∧
        balancedCaseMisident M N (Nat.floor (sampleSize (M : ℝ) (N : ℝ)))
            (by omega) (by omega) ≤ eps := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpos : 0 < (M : ℝ) / N := div_pos (by exact_mod_cast hM) hNR
  have hhalf : (M : ℝ) / N < 1 / 2 := by
    rw [div_lt_iff₀ hNR]
    linarith [two_mul_cast_lt hMN]
  have hs : 18 ≤ sampleSize (M : ℝ) (N : ℝ) := sampleSize_lower M N hM hMN
  have hnpos : 0 < Nat.floor (sampleSize (M : ℝ) (N : ℝ)) := by
    have h : (1 : ℝ) ≤ sampleSize (M : ℝ) (N : ℝ) := by linarith
    exact Nat.le_floor (by exact_mod_cast h)
  have hnhalf : sampleSize (M : ℝ) (N : ℝ) / 2 ≤
      (Nat.floor (sampleSize (M : ℝ) (N : ℝ)) : ℝ) := by
    have hlt := Nat.lt_floor_add_one (sampleSize (M : ℝ) (N : ℝ))
    linarith
  have hN3 : (3 : ℝ) ≤ N := by
    have h3 : 3 ≤ N := by omega
    exact_mod_cast h3
  have hgap : (1 - 2 * ((M : ℝ) / N)) ^ 2 = (gap M N) ^ 2 := by
    unfold gap
    ring
  refine ⟨8 / (9 * (N : ℝ)), by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity : (0:ℝ) < 9 * (N:ℝ))]
    nlinarith
  · refine (empirical_upper_le hnpos hpos hhalf).trans ?_
    rw [hgap]
    exact sampling_tail_bound M N _ hM hMN hnhalf
  · have hq : 1 / 2 < 1 - (M : ℝ) / N := by linarith
    have hq1 : 1 - (M : ℝ) / N ≤ 1 := by linarith
    have hnum : 16 * (1 - (M : ℝ) / N) * (1 - (1 - (M : ℝ) / N))
        = 16 * ((M : ℝ) / N) * (1 - (M : ℝ) / N) := by ring
    have hden : (Nat.floor (sampleSize (M : ℝ) (N : ℝ)) : ℝ)
          * (2 * (1 - (M : ℝ) / N) - 1) ^ 2
        = (Nat.floor (sampleSize (M : ℝ) (N : ℝ)) : ℝ) * (gap M N) ^ 2 := by
      have h2 : 2 * (1 - (M : ℝ) / N) - 1 = 1 - 2 * ((M : ℝ) / N) := by ring
      rw [h2, hgap]
    refine (empirical_lower_le hnpos hq hq1).trans ?_
    rw [hnum, hden]
    exact sampling_tail_bound M N _ hM hMN hnhalf

end Qatlib.Papers.AmpTransform14.HaarSampleLaw
