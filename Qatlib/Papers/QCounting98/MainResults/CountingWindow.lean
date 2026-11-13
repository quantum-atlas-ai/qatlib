/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Corollary2FixedBudgetQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem5ApproximateCountingQuan

/-!
# Approximate-counting windows

`levelSet` packages a Boolean predicate as a finite marked set. The approximate-counting law and
fixed-budget specialization are combined with an explicit precision threshold that makes the
counting error less than one half. The mathematical context is [BrassardHoyerTapp1998Counting].

## Main statements

* `source_theorem5_approximate_counting`: For positive `N`, at most `N/2` marked indices, and `P
  ≥ 4`, the amplitude-estimation law places probability at least `8/π²` in the strict Theorem 5
  counting window [BrassardHoyerTapp1998Counting].
* `source_theorem5_half_window`: Under the stated positive-count and precision hypotheses, the
  counting estimate lies strictly within one half of the true count with probability at least
  `8/π²` [BrassardHoyerTapp1998Counting].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open scoped BigOperators

/-- The finite set of indices at which a Boolean predicate is true. -/
def levelSet {N : ℕ} (F : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun i => F i = true)

/-- For positive `N`, at most `N/2` marked indices, and `P ≥ 4`, the amplitude-estimation law
places probability at least `8/π²` in the strict Theorem 5 counting window
[BrassardHoyerTapp1998Counting]. -/
theorem source_theorem5_approximate_counting (N P : ℕ) (F : Fin N → Bool)
    (hN : 0 < N) (ht : (levelSet F).card ≤ N / 2) (hP : 4 ≤ P) :
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
          |(N : ℝ) * aeEstimate P z - ((levelSet F).card : ℝ)| <
            2 * Real.pi / (P : ℝ) * Real.sqrt (((levelSet F).card : ℝ) * (N : ℝ)) +
              Real.pi ^ 2 / (P : ℝ) ^ 2 * (N : ℝ)),
        (aeLaw P (QFTMatrix N) ⟨0, hN⟩ (levelSet F) (qftMatrix_unitary hN)
          (le_trans (by norm_num) hP)).prob z :=
  theorem5ApproximateCounting N P (levelSet F) hN ht hP

/-- When `P = c√N` with `c > 0` and `P ≥ 4`, the counted circuit uses `P - 1` queries and the
stated simplified counting window has probability at least `8/π²`
[BrassardHoyerTapp1998Counting]. -/
theorem source_corollary2_fixed_budget (N P : ℕ) (F : Fin N → Bool) (c : ℝ)
    (hN : 0 < N) (ht : (levelSet F).card ≤ N / 2) (hc : 0 < c)
    (hPc : (P : ℝ) = c * Real.sqrt (N : ℝ)) (hP : 4 ≤ P) :
    QueryCount (countedAECircuit P (QFTMatrix N) ⟨0, hN⟩) = P - 1 ∧
      8 / Real.pi ^ 2 ≤
        ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
            |(N : ℝ) * aeEstimate P z - ((levelSet F).card : ℝ)| <
              2 * Real.pi / c * Real.sqrt ((levelSet F).card : ℝ) + Real.pi ^ 2 / c ^ 2),
          (aeLaw P (QFTMatrix N) ⟨0, hN⟩ (levelSet F) (qftMatrix_unitary hN)
            (le_trans (by norm_num) hP)).prob z :=
  corollary2FixedBudget N P (levelSet F) c hN ht hc hPc hP

/-- For `0 < t ≤ N`, precision greater than `π(2 + √6)√(tN)` makes the stated counting error
bound strictly less than one half. -/
theorem source_counting_window_lt_half (N t P : ℕ) (ht : 0 < t) (htN : t ≤ N)
    (hP : Real.pi * (2 + Real.sqrt 6) * Real.sqrt ((t : ℝ) * (N : ℝ)) < (P : ℝ)) :
    2 * Real.pi / (P : ℝ) * Real.sqrt ((t : ℝ) * (N : ℝ)) +
        Real.pi ^ 2 / (P : ℝ) ^ 2 * (N : ℝ) < 1 / 2 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hNR : (0 : ℝ) < N := lt_of_lt_of_le htR (by exact_mod_cast htN)
  set x : ℝ := Real.sqrt ((t : ℝ) * (N : ℝ)) with hxdef
  set s : ℝ := Real.sqrt 6 with hsdef
  have hx : 0 < x := by
    rw [hxdef]; exact Real.sqrt_pos.2 (mul_pos htR hNR)
  have hxsq : x ^ 2 = (t : ℝ) * (N : ℝ) := by
    rw [hxdef]; exact Real.sq_sqrt (le_of_lt (mul_pos htR hNR))
  have hs6 : s ^ 2 = 6 := by rw [hsdef]; exact Real.sq_sqrt (by norm_num)
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 (by norm_num)
  have hbase : 0 < Real.pi * (2 + s) * x :=
    mul_pos (mul_pos Real.pi_pos (by linarith)) hx
  have hPR : 0 < (P : ℝ) := lt_trans hbase hP
  have hfirst : 2 * Real.pi / (P : ℝ) * x < s - 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hPR]
    nlinarith [hP, hs6, hx, Real.pi_pos, hspos]
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hP2 : Real.pi ^ 2 * (2 + s) ^ 2 * ((t : ℝ) * (N : ℝ)) < (P : ℝ) ^ 2 := by
    have hsq : (Real.pi * (2 + s) * x) ^ 2 =
        Real.pi ^ 2 * (2 + s) ^ 2 * ((t : ℝ) * (N : ℝ)) := by
      rw [mul_pow, mul_pow, hxsq]
    nlinarith [hP, hbase]
  have hsecond : Real.pi ^ 2 / (P : ℝ) ^ 2 * (N : ℝ) ≤ 1 / (2 + s) ^ 2 := by
    have hden : 0 < (2 + s) ^ 2 := by positivity
    have hmono : Real.pi ^ 2 * (2 + s) ^ 2 * (N : ℝ) ≤
        Real.pi ^ 2 * (2 + s) ^ 2 * ((t : ℝ) * (N : ℝ)) := by
      have hnn : 0 ≤ Real.pi ^ 2 * (2 + s) ^ 2 * (N : ℝ) := by positivity
      nlinarith [ht1, hNR, hden, hnn]
    have htarget : Real.pi ^ 2 * (N : ℝ) * (2 + s) ^ 2 ≤ (P : ℝ) ^ 2 := by
      nlinarith [hmono, hP2]
    rw [div_mul_eq_mul_div, le_div_iff₀ hden, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < (P : ℝ) ^ 2)]
    nlinarith [htarget]
  have hkey : s - 2 + 1 / (2 + s) ^ 2 = 1 / 2 := by
    have hsq : (2 + s) ^ 2 = 10 + 4 * s := by rw [add_sq, hs6]; ring
    have hne : (10 + 4 * s) ≠ 0 := by nlinarith
    rw [hsq]
    field_simp
    nlinarith [hs6]
  linarith [hfirst, hsecond, hkey]

/-- Under the stated positive-count and precision hypotheses, the counting estimate lies
strictly within one half of the true count with probability at least `8/π²`
[BrassardHoyerTapp1998Counting]. -/
theorem source_theorem5_half_window (N P : ℕ) (F : Fin N → Bool)
    (hN : 0 < N) (ht : (levelSet F).card ≤ N / 2) (hP : 4 ≤ P)
    (htpos : 0 < (levelSet F).card)
    (hbig : Real.pi * (2 + Real.sqrt 6) *
        Real.sqrt (((levelSet F).card : ℝ) * (N : ℝ)) < (P : ℝ)) :
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
          |(N : ℝ) * aeEstimate P z - ((levelSet F).card : ℝ)| < 1 / 2),
        (aeLaw P (QFTMatrix N) ⟨0, hN⟩ (levelSet F) (qftMatrix_unitary hN)
          (le_trans (by norm_num) hP)).prob z := by
  have hle : (levelSet F).card ≤ N := by
    have hsub : levelSet F ⊆ Finset.univ := Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    simpa using hcard
  have hw := source_counting_window_lt_half N (levelSet F).card P htpos hle hbig
  refine (source_theorem5_approximate_counting N P F hN ht hP).trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact lt_trans hz hw
  · intro z _ _; exact (aeLaw _ _ _ _ _ _).nonneg z

end Qatlib.Papers.QCounting98.MainResults
