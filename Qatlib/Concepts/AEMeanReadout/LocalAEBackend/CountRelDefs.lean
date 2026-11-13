/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem13K2WindowQuan
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Adaptive relative quantum counting

This module defines relative-counting readouts and their probability and cost guarantees,
following the counting analysis of [BrassardHoyerTapp1998Counting]. The final grid
`countRelFinalGrid` depends on the observed stopping scale, and `countRelOutput` rounds a
Fourier-prepared amplitude estimate to an integer.

The zero-prefix estimates control the selected scale, while `countRel_joint_success` combines
prefix and final-stage probabilities. Expected cost bounds average over all prefix records for a
nonempty marked set.

## Main statements

* `countRelFinalGood_of_precision`: conditional success probability at least `31/32`.
* `countRel_zero_branch`: deterministic output zero for an empty marked set.
* `countRel_joint_success`: overall relative-counting success probability at least `3/4`.
* `countRel_expected_cost`: explicit upper and lower expected cost bounds.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
namespace CountRelNext

/-- The counting error radius `2πk√(t(N-t))/M + π²k²N/M²` for grid size `M` and window parameter
`k`. -/
noncomputable def countRelWindow (M k : ℕ) (N : ℕ) (t : ℝ) : ℝ :=
  2 * Real.pi * (k : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ) +
    Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) / (M : ℝ) ^ 2

/-- The final relative-counting grid size `⌈340π²c·2^s⌉` at stopping scale `s`. -/
noncomputable def countRelFinalGrid (c : ℝ) (s : ℕ) : ℕ :=
  Nat.ceil (340 * Real.pi ^ 2 * c * (2 ^ s : ℝ))

/-- The Fourier-prepared amplitude-estimation distribution at the final grid determined by the
prefix record `ω`. -/
noncomputable def countRelFinalLaw {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (c : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ countRelFinalGrid c (basicApproxCountStop N ω)) :
    FinDist (Fin (countRelFinalGrid c (basicApproxCountStop N ω))) :=
  aeLaw (countRelFinalGrid c (basicApproxCountStop N ω)) (QFTMatrix N) ⟨0, hN⟩ S
    (qftMatrix_unitary hN) hω

/-- The integer count obtained by applying `⌊x + 1/2⌋` to the final amplitude estimate scaled by
`N`. -/
noncomputable def countRelOutput {N : ℕ} (c : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (y : Fin (countRelFinalGrid c (basicApproxCountStop N ω))) : ℤ :=
  ⌊(N : ℝ) * aeEstimate (countRelFinalGrid c (basicApproxCountStop N ω)) y + 1 / 2⌋

/-- The event that the rounded final count has absolute error strictly less than `S.card / c`. -/
noncomputable def countRelGood {N : ℕ} (_hN : 0 < N) (S : Finset (Fin N)) (c : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (y : Fin (countRelFinalGrid c (basicApproxCountStop N ω))) : Prop :=
  |((countRelOutput c ω y : ℤ) : ℝ) - (S.card : ℝ)| < (S.card : ℝ) / c

/-- The probability, under `countRelFinalLaw`, that the final rounded count satisfies
`countRelGood`. -/
noncomputable def countRelFinalGood {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (c : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ countRelFinalGrid c (basicApproxCountStop N ω)) : ℝ :=
  ∑ y ∈ Finset.univ.filter (countRelGood hN S c ω),
    (countRelFinalLaw hN S c ω hω).prob y

/-- The final relative-counting grid has at least two points whenever `c ≥ 1`. -/
theorem countRel_grid_two {c : ℝ} (hc : 1 ≤ c) (s : ℕ) : 2 ≤ countRelFinalGrid c s := by
  have hpi2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hD : (1 : ℝ) < 340 * Real.pi ^ 2 := by nlinarith
  have hE : (1 : ℝ) ≤ c * (2 : ℝ) ^ s := by
    have h1 : (1 : ℝ) ≤ c := hc
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
    nlinarith
  have hval : (1 : ℝ) < 340 * Real.pi ^ 2 * c * (2 ^ s : ℝ) := by
    have hmul : 1 * (c * (2 : ℝ) ^ s) < 340 * Real.pi ^ 2 * (c * (2 : ℝ) ^ s) :=
      mul_lt_mul_of_pos_right hD (by positivity)
    rw [← mul_assoc] at hmul
    linarith
  have hceil : 1 < countRelFinalGrid c s := by
    rw [countRelFinalGrid]
    exact (Nat.lt_ceil (n := 1)
      (a := 340 * Real.pi ^ 2 * c * (2 ^ s : ℝ))).2 (by simpa using! hval)
  omega

/-- The stated lower bounds on the grid and stopping scale make the `k = 17` counting window at
most `17 * (t / c) / 64` for `0 < t ≤ N` and `c ≥ 1`. -/
theorem countRel_window_le {N : ℕ} {c t : ℝ} {s : ℕ} {M : ℕ}
    (hN : 0 < N) (ht0 : 0 < t) (htN : t ≤ (N : ℝ)) (hc : 1 ≤ c)
    (hM : 340 * Real.pi ^ 2 * c * (2 ^ s : ℝ) ≤ (M : ℝ))
    (hs : (2 : ℝ) ^ s ≥ (2 / (5 * Real.pi)) * Real.sqrt ((N : ℝ) / t)) :
    countRelWindow M 17 N t ≤ 17 * (t / c) / 64 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have htN0 : 0 ≤ t := ht0.le
  have hcpos : 0 < c := by linarith
  have hgap : 0 ≤ (N : ℝ) - t := by linarith
  have hK : (0 : ℝ) < 136 * Real.pi * c := by positivity
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have hpi2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
    have hD : (1 : ℝ) < 340 * Real.pi ^ 2 := by nlinarith
    have hE : (1 : ℝ) ≤ c * (2 : ℝ) ^ s := by
      have h1 : (1 : ℝ) ≤ c := hc
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
      nlinarith
    have hmul : 1 * (c * (2 : ℝ) ^ s) < 340 * Real.pi ^ 2 * (c * (2 : ℝ) ^ s) :=
      mul_lt_mul_of_pos_right hD (by positivity)
    have hc0 : (0 : ℝ) < c := by linarith
    have h1 : (0 : ℝ) < 340 * Real.pi ^ 2 * c * (2 ^ s : ℝ) := by
      have hmul : (0 : ℝ) < 340 * Real.pi ^ 2 * (c * (2 ^ s : ℝ)) := by
        exact mul_pos (by positivity) (by positivity)
      simpa [mul_assoc] using! hmul
    linarith

  have hMlow : 136 * Real.pi * c * Real.sqrt ((N : ℝ) / t) ≤ (M : ℝ) := by
    calc 136 * Real.pi * c * Real.sqrt ((N : ℝ) / t)
        = 340 * Real.pi ^ 2 * c *
            ((2 / (5 * Real.pi)) * Real.sqrt ((N : ℝ) / t)) := by field_simp; ring
      _ ≤ 340 * Real.pi ^ 2 * c * (2 : ℝ) ^ s := by
            exact mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 340 * Real.pi ^ 2 * c)
      _ ≤ (M : ℝ) := hM

  have hscale : Real.sqrt (t * (N : ℝ)) = t * Real.sqrt ((N : ℝ) / t) := by
    have hq : (0 : ℝ) < (N : ℝ) / t := div_pos hNr ht0
    have hnonneg1 : 0 ≤ Real.sqrt (t * (N : ℝ)) := Real.sqrt_nonneg _
    have hnonneg2 : 0 ≤ t * Real.sqrt ((N : ℝ) / t) := mul_nonneg ht0.le (Real.sqrt_nonneg _)
    have hsq1 : Real.sqrt (t * (N : ℝ)) ^ 2 = t * (N : ℝ) :=
      Real.sq_sqrt (mul_nonneg ht0.le hNr.le)
    have hsq2 : (t * Real.sqrt ((N : ℝ) / t)) ^ 2 = t * (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hq.le]
      field_simp
    nlinarith [sq_nonneg (Real.sqrt (t * (N : ℝ)) - t * Real.sqrt ((N : ℝ) / t))]

  have hfirst : 2 * Real.pi * 17 * Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ) ≤ t / (4 * c) := by
    apply (div_le_iff₀ hMpos).mpr
    have hprod : 0 ≤ t * ((N : ℝ) - t) := mul_nonneg htN0 hgap
    have hnum : (0 : ℝ) ≤ 2 * Real.pi * 17 * Real.sqrt (t * ((N : ℝ) - t)) := by positivity
    have hsqrtD : Real.sqrt (t * ((N : ℝ) - t)) ≤ Real.sqrt (t * (N : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hnum2 : 2 * Real.pi * 17 * Real.sqrt (t * ((N : ℝ) - t))
        ≤ 2 * Real.pi * 17 * Real.sqrt (t * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrtD (by positivity : 0 ≤ 2 * Real.pi * 17)
    have hsqrtbound : Real.sqrt ((N : ℝ) / t) ≤ (M : ℝ) / (136 * Real.pi * c) := by
      apply (le_div_iff₀ hK).mpr
      simpa [mul_comm] using! hMlow
    calc 2 * Real.pi * 17 * Real.sqrt (t * ((N : ℝ) - t))
        ≤ 2 * Real.pi * 17 * Real.sqrt (t * (N : ℝ)) := hnum2
      _ = 34 * Real.pi * (t * Real.sqrt ((N : ℝ) / t)) := by rw [hscale]; ring
      _ ≤ 34 * Real.pi * (t * ((M : ℝ) / (136 * Real.pi * c))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsqrtbound (by positivity : 0 ≤ t))
              (by positivity : 0 ≤ 34 * Real.pi)
      _ = (t / (4 * c)) * (M : ℝ) := by
            have hc0 : (0 : ℝ) < c := hcpos
            have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
            field_simp
            ring

  have hsecond : Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 ≤ t / (64 * c ^ 2) := by
    have hsq : (136 * Real.pi * c * Real.sqrt ((N : ℝ) / t)) ^ 2 ≤ (M : ℝ) ^ 2 := by
      have hnonneg : (0 : ℝ) ≤ 136 * Real.pi * c * Real.sqrt ((N : ℝ) / t) := by positivity
      nlinarith [sq_nonneg ((M : ℝ) - 136 * Real.pi * c * Real.sqrt ((N : ℝ) / t))]
    have hKsq : (0 : ℝ) < (136 * Real.pi * c * Real.sqrt ((N : ℝ) / t)) ^ 2 := by positivity
    have hrecip : 1 / (M : ℝ) ^ 2
        ≤ 1 / (136 * Real.pi * c * Real.sqrt ((N : ℝ) / t)) ^ 2 :=
      one_div_le_one_div_of_le hKsq hsq
    have hnum : (0 : ℝ) ≤ Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) := by positivity
    calc Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) / (M : ℝ) ^ 2
        = Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) * (1 / (M : ℝ) ^ 2) := by field_simp
      _ ≤ Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) *
          (1 / (136 * Real.pi * c * Real.sqrt ((N : ℝ) / t)) ^ 2) :=
          mul_le_mul_of_nonneg_left hrecip hnum
      _ = t / (64 * c ^ 2) := by
            have hsq2 : (136 * Real.pi * c * Real.sqrt ((N : ℝ) / t)) ^ 2
                = (136 * Real.pi * c) ^ 2 * ((N : ℝ) / t) := by
              rw [mul_pow, mul_pow, Real.sq_sqrt (div_pos hNr ht0).le]
            rw [hsq2, div_eq_mul_inv]
            have hc0 : (0 : ℝ) < c := hcpos
            have hN0 : (0 : ℝ) < N := hNr
            have ht0p : (0 : ℝ) < t := ht0
            have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
            have hcne : c ≠ 0 := ne_of_gt hc0
            have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hN0
            have htne : t ≠ 0 := ne_of_gt ht0p
            field_simp
            ring

  unfold countRelWindow
  have hband : t / (4 * c) + t / (64 * c ^ 2) ≤ 17 * (t / c) / 64 := by
    have hc0 : (0 : ℝ) < c := hcpos
    have h1 : t / (4 * c) = (t / c) / 4 := by field_simp
    have h2 : t / (64 * c ^ 2) = (t / c) / (64 * c) := by field_simp
    have h3 : (t / c) / (64 * c) ≤ (t / c) / 64 := by
      have hnonneg : (0 : ℝ) ≤ (t / c) / 64 := by positivity
      have hmul : (t / c) / 64 ≤ (t / c) / 64 * c := by
        simpa [mul_comm, mul_left_comm] using! mul_le_mul_of_nonneg_right hc hnonneg
      have heq : (t / c) / (64 * c) = ((t / c) / 64) / c := by ring
      rw [heq]
      exact (div_le_iff₀ (by linarith : (0 : ℝ) < c)).2 hmul
    rw [h1, h2]
    linarith
  linarith

/-- Rounding a real value within `17 * (m / c) / 64` of a positive integer `m` gives error
strictly less than `m / c` when `c ≥ 1`. -/
theorem countRel_round_lt {m : ℕ} {c x : ℝ} (hm : 0 < m) (hc : 1 ≤ c)
    (hx : |x - (m : ℝ)| ≤ 17 * ((m : ℝ) / c) / 64) :
    |((⌊x + 1 / 2⌋ : ℤ) : ℝ) - (m : ℝ)| < (m : ℝ) / c := by
  have htpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hcpos : (0 : ℝ) < c := by linarith
  have hdpos : (0 : ℝ) < (m : ℝ) / c := div_pos htpos hcpos
  by_cases hsmall : 17 * ((m : ℝ) / c) / 64 < 1 / 2
  · have hx' := abs_le.mp hx
    have hle : (m : ℝ) ≤ x + 1 / 2 := by linarith
    have hlt : x + 1 / 2 < (m : ℝ) + 1 := by linarith
    have heq : ⌊x + 1 / 2⌋ = (m : ℤ) := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    rw [heq]
    simp
    exact hdpos
  · have hbig : (1 / 2 : ℝ) ≤ 17 * ((m : ℝ) / c) / 64 := by linarith
    have hmul : (32 : ℝ) ≤ 17 * ((m : ℝ) / c) := by
      have h := mul_le_mul_of_nonneg_right hbig (by norm_num : (0 : ℝ) ≤ 64)
      linarith
    have hstrict : (17 : ℝ) * ((m : ℝ) / c) < 47 * ((m : ℝ) / c) := by
      have hnonneg : (0 : ℝ) ≤ 30 * ((m : ℝ) / c) := by positivity
      linarith
    have hkey : (32 : ℝ) < 47 * ((m : ℝ) / c) := by linarith
    have hbound : 1 / 2 + 17 * ((m : ℝ) / c) / 64 < (m : ℝ) / c := by
      have hnonneg : (0 : ℝ) ≤ 17 * ((m : ℝ) / c) := by positivity
      nlinarith
    have hfloor_le : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
    have hfloor_gt : x + 1 / 2 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hr : |((⌊x + 1 / 2⌋ : ℤ) : ℝ) - x| ≤ 1 / 2 := by
      apply abs_le.mpr
      constructor <;> linarith
    have hstep : |((⌊x + 1 / 2⌋ : ℤ) : ℝ) - (m : ℝ)|
        ≤ |((⌊x + 1 / 2⌋ : ℤ) : ℝ) - x| + |x - (m : ℝ)| :=
      abs_sub_le _ _ _
    linarith

/-- The stated lower bound on the observed stopping scale makes the final `k = 17` counting
window at most `17 * (S.card / c) / 64`. -/
theorem countRel_window_at_grid {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card)
    (c : ℝ) (hc : 1 ≤ c)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hscale : (2 / (5 * Real.pi)) * Real.sqrt ((N : ℝ) / (S.card : ℝ))
      ≤ (2 : ℝ) ^ basicApproxCountStop N ω) :
    countRelWindow (countRelFinalGrid c (basicApproxCountStop N ω)) 17 N (S.card : ℝ)
      ≤ 17 * ((S.card : ℝ) / c) / 64 := by
  have hcard : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS
  have htN : (S.card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show S.card ≤ N by simpa using! S.card_le_univ)
  have hM : 340 * Real.pi ^ 2 * c * (2 ^ basicApproxCountStop N ω : ℝ)
      ≤ (countRelFinalGrid c (basicApproxCountStop N ω) : ℝ) := by
    rw [countRelFinalGrid]
    exact Nat.le_ceil _
  exact countRel_window_le hN hcard htN hc hM hscale

/-- For a nonempty marked set and `c ≥ 1`, the stated final-window bound gives relative-counting
success probability at least `31/32`. -/
theorem countRelFinalGood_of_precision {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card)
    (c : ℝ) (hc : 1 ≤ c)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ countRelFinalGrid c (basicApproxCountStop N ω))
    (hwin : countRelWindow (countRelFinalGrid c (basicApproxCountStop N ω)) 17 N (S.card : ℝ)
      ≤ 17 * ((S.card : ℝ) / c) / 64) :
    31 / 32 ≤ countRelFinalGood hN S c ω hω := by
  let M := countRelFinalGrid c (basicApproxCountStop N ω)
  have hM2 : 2 ≤ M := hω
  have hcard : (0 : ℕ) < S.card := hS
  have hk := bhmt_counting_k2_window N M S hN hM2 17 (by norm_num)
  have hsub : Finset.univ.filter (fun z : Fin M =>
      |(N : ℝ) * aeEstimate M z - (S.card : ℝ)| ≤
        2 * Real.pi * 17 * Real.sqrt ((S.card : ℝ) * ((N : ℝ) - S.card)) / (M : ℝ) +
          Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) / (M : ℝ) ^ 2)
      ⊆ Finset.univ.filter (countRelGood hN S c ω) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    unfold countRelGood
    have hhz := hz
    rcases abs_le.mp hhz with ⟨hl, hu⟩
    have hwin' : countRelWindow M 17 N (S.card : ℝ)
        ≤ 17 * ((S.card : ℝ) / c) / 64 := hwin
    have hround := countRel_round_lt (m := S.card) hcard hc
      (by
        have hle : |(N : ℝ) * aeEstimate M z - (S.card : ℝ)|
            ≤ countRelWindow M 17 N (S.card : ℝ) := by
          have hx : |(N : ℝ) * aeEstimate M z - (S.card : ℝ)|
              ≤ 2 * Real.pi * 17 * Real.sqrt ((S.card : ℝ) * ((N : ℝ) - S.card)) / (M : ℝ) +
                Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := hz
          have heq : countRelWindow M 17 N (S.card : ℝ)
              = 2 * Real.pi * 17 * Real.sqrt ((S.card : ℝ) * ((N : ℝ) - S.card)) / (M : ℝ) +
                Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := rfl
          rw [heq]
          exact hx
        exact hle.trans hwin')
    rw [countRelOutput]
    exact hround
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun y _ _ => (countRelFinalLaw hN S c ω hω).nonneg y)
  have hk' : 1 - 1 / (2 * ((17 : ℝ) - 1)) ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |(N : ℝ) * aeEstimate M z - (S.card : ℝ)| ≤
          2 * Real.pi * 17 * Real.sqrt ((S.card : ℝ) * ((N : ℝ) - S.card)) / (M : ℝ) +
            Real.pi ^ 2 * 17 ^ 2 * (N : ℝ) / (M : ℝ) ^ 2),
        (countRelFinalLaw hN S c ω hω).prob z := by
    have heq : (aeLaw M (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hM2) = countRelFinalLaw hN S c ω hω := by
      rfl
    rw [← heq]
    exact hk
  have hconst : (31 / 32 : ℝ) = 1 - 1 / (2 * ((17 : ℝ) - 1)) := by norm_num
  exact hconst.le.trans (hk'.trans hmass)

/-- When the marked set is empty and `c ≥ 1`, the final law assigns probability one to label
zero, whose rounded output is zero. -/
theorem countRel_zero_branch {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = 0)
    (c : ℝ) (_hc : 1 ≤ c)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ countRelFinalGrid c (basicApproxCountStop N ω)) :
    (countRelFinalLaw hN S c ω hω).prob ⟨0, by omega⟩ = 1 ∧
      countRelOutput c ω ⟨0, by omega⟩ = 0 := by
  let M := countRelFinalGrid c (basicApproxCountStop N ω)
  have hM2 : 2 ≤ M := hω
  have ha : MeasureProb (preparedAAState (QFTMatrix N) ⟨0, hN⟩) S = 0 := by
    rw [prepared_qft_mark_mass, hS, Nat.cast_zero, zero_div]
  have hp := (prepared_ae_bhmt_error_and_endpoints M hM2 (QFTMatrix N) ⟨0, hN⟩ S
    (qftMatrix_unitary hN)).2.1 ha
  have hp' : (aeLaw M (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hM2).prob ⟨0, by omega⟩ = 1 := by
    have heq : aeLaw M (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hM2
        = countRelFinalLaw hN S c ω hω := rfl
    rw [heq]
    exact hp
  refine ⟨hp', ?_⟩
  rw [countRelOutput]
  norm_num [aeEstimate]

/-- The predicate that all prefix observations with index less than `n` are zero. -/
noncomputable def countRelPrefixZero (N : ℕ) (n : ℕ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) : Prop :=
  ∀ l : Fin (basicApproxCountLoopCap N), l.val < n → basicApproxCountObserved N ω l = 0

/-- A zero prefix of length `n` forces the stopping index to be at least `n + 1`, provided that
stage is within the loop cap [BrassardHoyerTapp1998Counting]. -/
theorem countRelStop_of_prefix {N n : ℕ} (hn : n + 1 ≤ basicApproxCountLoopCap N)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hz : countRelPrefixZero N n ω) : n + 1 ≤ basicApproxCountStop N ω :=
  basicApproxCountStop_of_prefix hn ω hz

/-- If `2^n * θ ≤ 1/5` and the stated angle and loop-cap hypotheses hold, zero prefixes of
length `n` have total weight at least `7/8` [BrassardHoyerTapp1998Counting]. -/
theorem countRel_prefix_zero_mass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : (S.card : ℝ) / N = Real.sin θ ^ 2)
    (n : ℕ) (hn : n ≤ basicApproxCountLoopCap N)
    (hsmall : (2 : ℝ) ^ n * θ ≤ 1 / 5) :
    (7 / 8 : ℝ) ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      if countRelPrefixZero N n ω then basicApproxCountPrefixWeight hN S ω else 0 := by
  have h := basicApproxCount_prefix_zero_lower hN S θ hθ0 hθ1 ha n hn hsmall
  exact h

/-- A zero prefix followed by the stated dyadic angle crossing forces the stopping scale to be
at least `(2 / (5π)) * √(N / S.card)` [BrassardHoyerTapp1998Counting]. -/
theorem countRel_exit_scale {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card)
    (θ : ℝ) (hθ0 : 0 < θ)
    (hangle : θ * Real.sqrt (N : ℝ) ≤ Real.pi / 2 * Real.sqrt (S.card : ℝ))
    (n : ℕ) (hn : n + 1 ≤ basicApproxCountLoopCap N)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hz : countRelPrefixZero N n ω)
    (hcross : (1 / 5 : ℝ) < (2 : ℝ) ^ (n + 1) * θ) :
    (2 / (5 * Real.pi)) * Real.sqrt ((N : ℝ) / (S.card : ℝ))
      ≤ (2 : ℝ) ^ basicApproxCountStop N ω := by
  generalize hP : (2 : ℝ) ^ basicApproxCountStop N ω = P
  have hstop : n + 1 ≤ basicApproxCountStop N ω := countRelStop_of_prefix hn ω hz
  have hp : (2 : ℝ) ^ (n + 1) ≤ P := by
    have hh : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ basicApproxCountStop N ω :=
      pow_le_pow_right₀ (by norm_num) hstop
    exact hh.trans_eq hP
  have hstopθ : (1 / 5 : ℝ) ≤ P * θ :=
    hcross.le.trans (mul_le_mul_of_nonneg_right hp hθ0.le)
  have hP0 : (0 : ℝ) ≤ P := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ basicApproxCountStop N ω := one_le_pow₀ (by norm_num)
    rw [hP] at h1
    exact le_trans (by norm_num) h1
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsqrtt : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hS)
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hmul : P * θ * Real.sqrt (N : ℝ) ≤ P * (Real.pi / 2) * Real.sqrt (S.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hangle hP0
    simpa [mul_assoc, mul_comm, mul_left_comm] using! h
  have hlow : (1 / 5 : ℝ) * Real.sqrt (N : ℝ) ≤ P * θ * Real.sqrt (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hstopθ (Real.sqrt_nonneg (N : ℝ))
    simpa [mul_assoc, mul_comm, mul_left_comm] using! h
  have h1 : (1 / 5 : ℝ) * Real.sqrt (N : ℝ) ≤ P * (Real.pi / 2) * Real.sqrt (S.card : ℝ) :=
    hlow.trans hmul
  have h2 : Real.sqrt (N : ℝ) ≤ P * Real.sqrt (S.card : ℝ) * (5 * Real.pi / 2) := by
    have h := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 5)
    calc
      Real.sqrt (N : ℝ) = 5 * (1 / 5 * Real.sqrt (N : ℝ)) := by ring
      _ ≤ 5 * (P * (Real.pi / 2) * Real.sqrt (S.card : ℝ)) := h
      _ = P * Real.sqrt (S.card : ℝ) * (5 * Real.pi / 2) := by ring
  have h3 : (2 / (5 * Real.pi)) * Real.sqrt (N : ℝ) ≤ P * Real.sqrt (S.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 / (5 * Real.pi))
    calc
      (2 / (5 * Real.pi)) * Real.sqrt (N : ℝ)
          = (2 / (5 * Real.pi)) * Real.sqrt (N : ℝ) := rfl
      _ ≤ (2 / (5 * Real.pi)) * (P * Real.sqrt (S.card : ℝ) * (5 * Real.pi / 2)) := h
      _ = P * Real.sqrt (S.card : ℝ) := by field_simp
  have hsqrtdiv : Real.sqrt ((N : ℝ) / (S.card : ℝ))
      = Real.sqrt (N : ℝ) / Real.sqrt (S.card : ℝ) :=
    Real.sqrt_div (by positivity) (S.card : ℝ)
  rw [hsqrtdiv, mul_div_assoc']
  exact (div_le_iff₀ hsqrtt).2 h3

/-- For a nonempty marked set and `c ≥ 1`, averaging final relative-counting success over prefix
records gives probability at least `3/4` [Brassard et al., Corollary
3][BrassardHoyerTapp1998Counting]. -/
theorem countRel_joint_success {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card)
    (c : ℝ) (hc : 1 ≤ c) :
    (3 / 4 : ℝ) ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω *
        countRelFinalGood hN S c ω (countRel_grid_two hc (basicApproxCountStop N ω)) := by
  obtain ⟨θ, hθ0, hθ1, ha, hroot, hangle⟩ := basicApproxCount_angle hN S hS
  obtain ⟨n, hn, hcross, hnsmall⟩ := basicApproxCount_threshold N hN θ hθ0 hroot
  have hmass : (7 / 8 : ℝ) ≤
      ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        if countRelPrefixZero N n ω then basicApproxCountPrefixWeight hN S ω else 0 := by
    rcases hnsmall with hn0 | hnsmall
    · rw [hn0]
      have hz (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
          countRelPrefixZero N 0 ω := by intro l hl; omega
      simp only [ite_eq_left (hz _), basicApproxCountPrefixWeight_sum]
      norm_num
    · have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hθsmall : θ ≤ 1 / 5 := by nlinarith
      have hstrict : θ < Real.pi / 2 := by linarith [Real.pi_gt_three]
      exact countRel_prefix_zero_mass hN S θ hθ0 hstrict ha n (by omega) hnsmall
  have hp0 (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
      0 ≤ basicApproxCountPrefixWeight hN S ω :=
    Finset.prod_nonneg (fun l _ => (basicApproxCountLoopLaw hN S l).nonneg (ω l))
  have hpoint (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
      (if countRelPrefixZero N n ω then basicApproxCountPrefixWeight hN S ω else 0) * (31 / 32) ≤
        basicApproxCountPrefixWeight hN S ω *
          countRelFinalGood hN S c ω (countRel_grid_two hc (basicApproxCountStop N ω)) := by
    by_cases hz : countRelPrefixZero N n ω
    · rw [ite_eq_left hz]
      have hscale := countRel_exit_scale hN S hS θ hθ0 hangle n hn ω hz hcross
      have hwin := countRel_window_at_grid hN S hS c hc ω hscale
      exact mul_le_mul_of_nonneg_left
        (countRelFinalGood_of_precision hN S hS c hc ω (countRel_grid_two hc _) hwin) (hp0 ω)
    · rw [ite_eq_right hz, zero_mul]
      exact mul_nonneg (hp0 ω) (Finset.sum_nonneg
        (fun y _ => (countRelFinalLaw hN S c ω (countRel_grid_two hc _)).nonneg y))
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hpoint ω)
  rw [← Finset.sum_mul] at hsum
  have hmass' := mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ (31 / 32 : ℝ))
  have hconst : (3 / 4 : ℝ) ≤ 7 / 8 * (31 / 32) := by norm_num
  exact hconst.trans (hmass'.trans hsum)

/-- For positive `c`, the relative-counting final grid equals `basicApproxCountFinalM` with
accuracy parameter `1 / (17 * c)`. -/
theorem countRelFinalGrid_eq (c : ℝ) (hc : 0 < c) (s : ℕ) :
    countRelFinalGrid c s = basicApproxCountFinalM (1 / (17 * c)) s := by
  unfold countRelFinalGrid basicApproxCountFinalM
  congr 1
  field_simp
  ring

/-- The basic approximate-counting total cost evaluated with accuracy parameter `1 / (17 * c)`. -/
noncomputable def countRelTotalCost (N : ℕ) (c : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) : ℕ :=
  basicApproxCountTotalCost N (1 / (17 * c)) ω

/-- For a nonempty marked set and `c ≥ 1`, the expected total cost lies between
`(119π/2)c√(N/S.card)` and `34000c√(N/S.card)` [Brassard et al., Corollary
3][BrassardHoyerTapp1998Counting]. -/
theorem countRel_expected_cost {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card)
    (c : ℝ) (hc : 1 ≤ c) :
    (119 * Real.pi / 2) * c * Real.sqrt ((N : ℝ) / (S.card : ℝ))
        ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((countRelTotalCost N c ω : ℕ) : ℝ) ∧
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((countRelTotalCost N c ω : ℕ) : ℝ))
        ≤ 34000 * c * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hε : 0 < 1 / (17 * c) := by positivity
  have hε1 : 1 / (17 * c) ≤ 1 := by
    have h17 : 1 ≤ 17 * c := by nlinarith
    have hpos : 0 < 17 * c := by positivity
    exact (div_le_iff₀ hpos).2 (by linarith)
  have h := bhmt_basic_approx_count_expected_cost N S hN (1 / (17 * c)) hε hε1
  have hpos := h.2 hS
  have hεinv : (1 : ℝ) / (1 / (17 * c)) = 17 * c := by field_simp
  constructor
  · have hlo := hpos.1
    rw [hεinv] at hlo
    calc
      (119 * Real.pi / 2) * c * Real.sqrt ((N : ℝ) / (S.card : ℝ))
          = 7 * Real.pi / 2 * (17 * c) * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := by ring
      _ ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((basicApproxCountTotalCost N (1 / (17 * c)) ω : ℕ) : ℝ) := hlo
      _ = ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω * ((countRelTotalCost N c ω : ℕ) : ℝ) := by
        simp [countRelTotalCost]
  · have hup := hpos.2
    rw [hεinv] at hup
    calc
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω * ((countRelTotalCost N c ω : ℕ) : ℝ))
        = ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((basicApproxCountTotalCost N (1 / (17 * c)) ω : ℕ) : ℝ) := by
        simp [countRelTotalCost]
      _ ≤ 2000 * (17 * c) * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := hup
      _ ≤ 34000 * c * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := by
        have hconst : 2000 * (17 * c) = 34000 * c := by ring
        rw [hconst]

/-- For a nonempty marked set and `c ≥ 1`, the expected total cost is at most `34000 * (c +
log(log(N + 2))) * √(N/S.card)` [BrassardHoyerTapp1998Counting]. -/
theorem countRel_expected_cost_source_form {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hS : 0 < S.card) (c : ℝ) (hc : 1 ≤ c) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((countRelTotalCost N c ω : ℕ) : ℝ))
        ≤ 34000 * (c + Real.log (Real.log ((N : ℕ) + 2)))
          * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := by
  have hlog : 0 ≤ Real.log (Real.log ((N : ℕ) + 2)) := by
    have hN1 : (1 : ℕ) ≤ N := by omega
    have hbig : (0 : ℝ) < ((N : ℕ) + 2 : ℝ) := by
      have : (0 : ℕ) < N + 2 := by omega
      exact_mod_cast this
    have hthree : (3 : ℝ) ≤ ((N : ℕ) + 2 : ℝ) := by
      have : (3 : ℕ) ≤ N + 2 := by omega
      exact_mod_cast this
    have hlogpos : (0 : ℝ) < Real.log ((N : ℕ) + 2) :=
      Real.log_pos (by linarith)
    have hone : (1 : ℝ) ≤ Real.log ((N : ℕ) + 2) := by
      have hexp : Real.exp 1 ≤ ((N : ℕ) + 2 : ℝ) := by
        linarith [Real.exp_one_lt_three]
      exact (Real.le_log_iff_exp_le hbig).2 hexp
    have hone' : Real.exp 0 ≤ Real.log ((N : ℕ) + 2) := by simpa using! hone
    exact (Real.le_log_iff_exp_le hlogpos).2 hone'
  have hcost := (countRel_expected_cost hN S hS c hc).2
  calc
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((countRelTotalCost N c ω : ℕ) : ℝ))
        ≤ 34000 * c * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := hcost
    _ ≤ 34000 * (c + Real.log (Real.log ((N : ℕ) + 2)))
          * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity :
        (0 : ℝ) ≤ 34000 * Real.sqrt ((N : ℝ) / (S.card : ℝ)))
      nlinarith

end CountRelNext
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
