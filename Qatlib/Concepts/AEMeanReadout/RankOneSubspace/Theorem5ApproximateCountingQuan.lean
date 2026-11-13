/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem5ApproximateCountingStat

/-!
# Approximate counting from amplitude estimation

`theorem5ApproximateCounting` proves a probability lower bound for counting marked elements
using `aeLaw` with Fourier preparation. The module also checks that the success constant `8 /
π²` is at most one. For background, see [BrassardHoyerTapp1998Counting].

## Main statements

* `theorem5ApproximateCounting`: For positive `N`, marked size at most `N / 2`, and `P ≥ 4`, the
  amplitude-estimation law assigns mass at least `8 / π²` to estimates with count error strictly
  below `2π * sqrt (|S| * N) / P + π² * N / P²`. See [BrassardHoyerTapp1998Counting].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

/-- The success constant `8 / π²` is at most one. -/
private theorem counting_success_constant : 8/Real.pi^2 ≤ (1 : ℝ) := by
  apply (div_le_one (sq_pos_of_pos Real.pi_pos)).2
  nlinarith [Real.pi_gt_three]

/-- For positive `N`, marked size at most `N / 2`, and `P ≥ 4`, the amplitude-estimation law
assigns mass at least `8 / π²` to estimates with count error strictly below `2π * sqrt (|S|
* N) / P + π² * N / P²`. See [BrassardHoyerTapp1998Counting]. -/
theorem theorem5ApproximateCounting : Theorem5ApproximateCounting := by
  intro N P S hN _hS hP
  have hP2 : 2 ≤ P := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  let p := aeLaw P (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hP2
  by_cases ht : S.card = 0
  · have ha : MeasureProb (preparedAAState (QFTMatrix N) ⟨0, hN⟩) S = 0 := by
      rw [prepared_qft_mark_mass, ht]
      simp
    have hz := (prepared_ae_bhmt_error_and_endpoints P hP2 (QFTMatrix N)
      (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN)).2.1 ha
    let z : Fin P := ⟨0, by omega⟩
    have hmem : z ∈ Finset.univ.filter (fun z : Fin P =>
        |(N : ℝ)*aeEstimate P z-(S.card : ℝ)| <
          2*Real.pi/(P : ℝ)*Real.sqrt ((S.card : ℝ)*N)+Real.pi^2/(P : ℝ)^2*N) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [z, aeEstimate, ht, Nat.cast_zero, mul_zero, zero_div, Real.sin_zero,
        zero_pow (by decide : 2 ≠ 0), sub_zero, abs_zero]
      positivity
    calc
      _ ≤ 1 := counting_success_constant
      _ = p.prob z := hz.symm
      _ ≤ _ := Finset.single_le_sum (fun y _ => p.nonneg y) hmem
  · have ht0 : (0 : ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
    have htN : (S.card : ℝ) ≤ N := by
      have hh := Finset.card_le_card (Finset.subset_univ S)
      exact_mod_cast (by simpa only [Finset.card_univ, Fintype.card_fin] using hh)
    have hsq : Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card)) <
        Real.sqrt ((S.card : ℝ)*N) := Real.sqrt_lt_sqrt (mul_nonneg (le_of_lt ht0)
          (sub_nonneg.mpr htN)) (by nlinarith [sq_pos_of_pos ht0])
    apply (amplitude_counting_actual_consumer N P hN hP2 S).trans
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      calc
        _ ≤ _ := hz
        _ = 2*Real.pi/(P : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))+
            Real.pi^2/(P : ℝ)^2*N := by ring
        _ < _ := by
          have hh := mul_lt_mul_of_pos_left hsq
            (show (0 : ℝ) < 2*Real.pi/(P : ℝ) by positivity)
          linarith
    · intro z _ _
      exact p.nonneg z

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
