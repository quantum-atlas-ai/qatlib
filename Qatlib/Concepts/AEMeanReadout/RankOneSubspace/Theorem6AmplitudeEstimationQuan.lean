/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem6AmplitudeEstimationStat

/-!
# Amplitude-estimation error bound

`theorem6AmplitudeEstimation` establishes the probability bound for the numerical output
`aeEstimate` under `aeLaw` for a unitary prepared state. The stated error depends on the square
root of the initial marked probability and on the precision parameter. For background, see
[BrassardHoyerTapp1998Counting].

## Main statements

* `theorem6AmplitudeEstimation`: For unitary preparation and `P ≥ 4`, the law `aeLaw` gives mass
  at least `8 / π²` to estimates with error strictly below `2π * sqrt a / P + π² / P²`, where
  `a` is the prepared marked probability. See [BrassardHoyerTapp1998Counting].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

/-- The success constant `8 / π²` is at most one. -/
private theorem estimation_success_constant : 8/Real.pi^2 ≤ (1 : ℝ) := by
  apply (div_le_one (sq_pos_of_pos Real.pi_pos)).2
  nlinarith [Real.pi_gt_three]

/-- For unitary preparation and `P ≥ 4`, the law `aeLaw` gives mass at least `8 / π²` to
estimates with error strictly below `2π * sqrt a / P + π² / P²`, where `a` is the prepared
marked probability. See [BrassardHoyerTapp1998Counting]. -/
theorem theorem6AmplitudeEstimation : Theorem6AmplitudeEstimation := by
  intro I _ _ P A j S hA hP
  have hP2 : 2 ≤ P := by omega
  have hp : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  let a := MeasureProb (preparedAAState A j) S
  let p := aeLaw P A j S hA hP2
  have ha0 : 0 ≤ a := measureProb_nonneg _ _
  have ha1 : a ≤ 1 := measureProb_le_one (normalized_applyGate hA (normalized_ket j)) S
  by_cases ha : a = 0
  · have hz := (prepared_ae_bhmt_error_and_endpoints P hP2 A j S hA).2.1 ha
    let z : Fin P := ⟨0, by omega⟩
    have hmem : z ∈ Finset.univ.filter (fun z : Fin P =>
        |aeEstimate P z-a| < 2*Real.pi/(P : ℝ)*Real.sqrt a+Real.pi^2/(P : ℝ)^2) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [z, aeEstimate, ha, Nat.cast_zero, mul_zero, zero_div, Real.sin_zero,
        zero_pow (by decide : 2 ≠ 0), sub_zero, abs_zero, Real.sqrt_zero, zero_add]
      positivity
    calc
      _ ≤ 1 := estimation_success_constant
      _ = p.prob z := hz.symm
      _ ≤ _ := Finset.single_le_sum (fun y _ => p.nonneg y) hmem
  · have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    have hsq : Real.sqrt (a*(1-a)) < Real.sqrt a :=
      Real.sqrt_lt_sqrt (mul_nonneg ha0 (sub_nonneg.mpr ha1))
        (by nlinarith [sq_pos_of_pos haPos])
    apply (prepared_ae_bhmt_error_and_endpoints P hP2 A j S hA).1.trans
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      calc
        _ ≤ _ := hz
        _ = 2*Real.pi/(P : ℝ)*Real.sqrt (a*(1-a))+Real.pi^2/(P : ℝ)^2 := by ring
        _ < _ := by
          have hh := mul_lt_mul_of_pos_left hsq
            (show (0 : ℝ) < 2*Real.pi/(P : ℝ) by positivity)
          change 2*Real.pi/(P : ℝ)*Real.sqrt (a*(1-a))+Real.pi^2/(P : ℝ)^2 <
            2*Real.pi/(P : ℝ)*Real.sqrt a+Real.pi^2/(P : ℝ)^2
          linarith
    · intro z _ _
      exact p.nonneg z

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
