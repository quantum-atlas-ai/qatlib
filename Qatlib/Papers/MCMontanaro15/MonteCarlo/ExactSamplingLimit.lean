/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroThm8ExactSamplingSubgoalMont
public import Qatlib.Papers.MCMontanaro15.MonteCarlo.MonteCarloDefs

@[expose] public section

/-!
# Theorem 8 at infinite final inverse temperature

The locked exact-sampling subgoal (`montanaroTheorem8ExactSamplingSubgoal`) proves a relative
error `ε` for the partition function at the *finite* final schedule point `β_ℓ`. Theorem 8 of
[Montanaro2015] is stated at `β = ∞`, where the partition function becomes the number of
ground states `partitionFnLimit`.

The tail estimate of the locked library
(`partitionFn_sub_partitionFnLimit_le`) bounds `partitionFn H β_ℓ - partitionFnLimit H` by
`|Ω| * exp (-β_ℓ)`. Substituting that tail into the failure event costs one extra copy of the
relative accuracy, so the tolerance found here is `3 * ε` rather than `ε`; the failure
probability stays at `1/4`.

## Main statements

* `theorem8_limit_target_failure_le_quarter`: the estimator relative to the finite-`β` partition
  function is also within `3 * ε` (relative) of `partitionFnLimit H` except with probability at
  most `1/4`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo

open Matrix
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib.Papers.MCMontanaro15.MonteCarlo.StageBMONTECARLO
open scoped BigOperators

/-- A pointwise implication between sample events preserves the ordering of their
probabilities. -/
private theorem probEvent_le_of_imp {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) {E F : (Fin L → X) → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) : p.probEvent E ≤ p.probEvent F := by
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent,
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun ω hω => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩)
    (fun ω _ _ => Finset.prod_nonneg fun _ _ => p.nonneg _)

/-- The zero-energy partition limit is nonnegative. -/
private theorem partitionFnLimit_nonneg {Ω : Type} [Fintype Ω] (H : Ω → ℕ) :
    0 ≤ partitionFnLimit H := by
  unfold partitionFnLimit
  exact Finset.sum_nonneg fun x _ => by split <;> norm_num

/-- Under the exact-sampling hypotheses of the locked Theorem 8 subgoal, together with the tail
assumption `|Ω| * exp (-β_ℓ) ≤ ε * partitionFnLimit H`, the cardinality-scaled product of factor
medians is within relative error `3 * ε` of `partitionFnLimit H` except with probability at most
`1/4`. This carries [Montanaro2015], Theorem 8 from the finite final inverse temperature to the
ground-state limit. -/
theorem theorem8_limit_target_failure_le_quarter
    (Ω : Type) [Fintype Ω] [DecidableEq Ω] (H : Ω → ℕ) (ℓ : ℕ)
    (β : Fin (ℓ + 1) → ℝ) (As : Fin ℓ → Matrix Ω Ω ℂ) (js : Fin ℓ → Ω)
    (B ε : ℝ) (N k r : ℕ)
    (hℓ : 0 < ℓ) (hβ0 : β 0 = 0)
    (hmono : ∀ i : Fin ℓ, 0 ≤ β i.castSucc ∧ β i.castSucc ≤ β i.succ)
    (hAs : ∀ i : Fin ℓ, As i ∈ Matrix.unitaryGroup Ω ℂ)
    (hB : 1 ≤ B) (hε : 0 < ε) (hε1 : ε < 1)
    (hN : 32 * B ≤ (N : ℝ)) (hk : 4 ≤ k)
    (hacc : 3 * Real.sqrt (B + 1) * (1 / 2 : ℝ) ^ k ≤ ε / (2 * (ℓ : ℝ)))
    (hr : (143 / 144 : ℝ) ^ r ≤ 1 / (4 * (ℓ : ℝ)))
    (hZ : ∀ i : Fin (ℓ + 1), 0 < partitionFn H (β i))
    (hBorn : ∀ i : Fin ℓ, ∀ x : Ω,
      BornProb (ApplyGate (As i) (Ket (js i))) x
        = Real.exp (-(β i.castSucc * (H x : ℝ))) / partitionFn H (β i.castSucc))
    (hCheb : ∀ i : Fin ℓ, partitionFn H (2 * β i.succ - β i.castSucc)
        * partitionFn H (β i.castSucc) ≤ B * partitionFn H (β i.succ) ^ 2)
    (hTail : (Fintype.card Ω : ℝ) * Real.exp (-(β (Fin.last ℓ))) ≤ ε * partitionFnLimit H) :
    (independentSampleLaw (fun i : Fin ℓ => theorem6FactorLaw (As i) (js i)
        (fun x => Real.exp (-((β i.succ - β i.castSucc) * (H x : ℝ)))) B N k r (hAs i)
        (fun _ => (Real.exp_pos _).le))).probEvent
      (fun ξ : Fin 1 → (Fin ℓ → (Fin (2 * r + 1) → ((Fin N → Ω) × LayerRecord k))) =>
        3 * ε * partitionFnLimit H
          < |(Fintype.card Ω : ℝ)
              * ∏ i, theorem6FactorMedian (fun x =>
                  Real.exp (-((β i.succ - β i.castSucc) * (H x : ℝ)))) B N k r (ξ 0 i)
            - partitionFnLimit H|)
      ≤ 1 / 4 := by
  classical
  have hmonoR : ∀ (n : ℕ) (h : n ≤ ℓ), β 0 ≤ β ⟨n, Nat.lt_succ_of_le h⟩ := by
    intro n
    induction n with
    | zero =>
      intro h
      exact le_of_eq (congrArg β (Fin.ext rfl))
    | succ m ih =>
      intro h
      have hm : m ≤ ℓ := by omega
      have hstep := (hmono ⟨m, by omega⟩).2
      exact le_trans (ih hm) hstep
  have hβlast : (0 : ℝ) ≤ β (Fin.last ℓ) := by
    have := hmonoR ℓ le_rfl
    rw [hβ0] at this
    simpa [Fin.last] using this
  have hP := partitionFn_sub_partitionFnLimit_le H (β (Fin.last ℓ)) hβlast
  have hL0 : 0 ≤ partitionFnLimit H := partitionFnLimit_nonneg H
  have htail : partitionFn H (β (Fin.last ℓ)) - partitionFnLimit H
      ≤ ε * partitionFnLimit H := le_trans hP.2 hTail
  have hmain := montanaroTheorem8ExactSamplingSubgoal Ω H ℓ β As js B ε N k r
    hℓ hβ0 hmono hAs hB hε hε1 hN hk hacc hr hZ hBorn hCheb
  simp only [] at hmain
  set P : ℝ := partitionFn H (β (Fin.last ℓ)) with hPdef
  set L : ℝ := partitionFnLimit H with hLdef
  set est : (Fin 1 → (Fin ℓ → (Fin (2 * r + 1) → ((Fin N → Ω) × LayerRecord k)))) → ℝ :=
    fun ξ => (Fintype.card Ω : ℝ)
      * ∏ i, theorem6FactorMedian (fun x =>
          Real.exp (-((β i.succ - β i.castSucc) * (H x : ℝ)))) B N k r (ξ 0 i) with hest
  have hmain' : (independentSampleLaw (fun i : Fin ℓ => theorem6FactorLaw (As i) (js i)
        (fun x => Real.exp (-((β i.succ - β i.castSucc) * (H x : ℝ)))) B N k r (hAs i)
        (fun _ => (Real.exp_pos _).le))).probEvent
      (fun ξ => ε * P < |est ξ - P|) ≤ 1 / 4 := hmain
  refine le_trans (probEvent_le_of_imp _ (fun ξ hξ => ?_)) hmain'
  by_contra hle
  have hPL0 : (0 : ℝ) ≤ P - L := hP.1
  have hPLeps : P - L ≤ ε * L := htail
  have hle' : |est ξ - P| ≤ ε * P := le_of_not_gt hle
  have hshift : |est ξ - L| ≤ ε * P + (P - L) := by
    have h1 : est ξ - L = (est ξ - P) + (P - L) := by ring
    rw [h1]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_of_nonneg hPL0]
    linarith
  have hbound : ε * P + (P - L) ≤ 3 * ε * L := by
    have hPle : P ≤ L + ε * L := by linarith
    have hmul : ε * P ≤ ε * (L + ε * L) := mul_le_mul_of_nonneg_left hPle hε.le
    have hsq : ε * (ε * L) ≤ ε * L := by
      have h1 : ε * ε ≤ ε := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 hL0]
    linarith
  linarith

end Qatlib.Papers.MCMontanaro15.MonteCarlo
