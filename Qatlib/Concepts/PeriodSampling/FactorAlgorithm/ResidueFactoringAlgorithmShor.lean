/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueFactoringAlgorithmStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueAttemptSuccessShor
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPreprocessingShor

/-!
# Amplified residue factoring algorithm

Combines preprocessing with repeated residue-based attempts to establish
`residueFactoringAlgorithm`. Counting gcd-success residues separately from units bounds the
single-attempt expression by one and yields the amplified success guarantee in the probability
model associated with [Shor1997].

## Main statements

* `residue_gcd_units_count_le`: Bounds the combined number of gcd-success residues and units.
* `residueFactoringAlgorithm`: Establishes amplified success and factor soundness.

## References

* [Shor, 1997][Shor1997]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

/-- A lower bound `c` on a single-trial event probability yields lower bound `1 - (1 - c) ^ R`
on success in `R` independent trials. -/
private theorem residue_fresh_success_bound {A : Type*} [Fintype A] [DecidableEq A]
    (p : FinDist A) (P : A → Prop) [DecidablePred P] (R : ℕ) (c : ℝ)
    (hc : c ≤ p.probEvent (L := 1) (fun ω => P (ω 0))) :
    1 - (1 - c) ^ R ≤ p.probEvent (fun ω : Fin R → A => ∃ j, P (ω j)) := by
  let bad : ℝ := ∑ a ∈ Finset.univ.filter (fun a => ¬ P a), p.prob a
  have hpart : (∑ a ∈ Finset.univ.filter P, p.prob a) + bad = 1 := by
    dsimp [bad]
    rw [Finset.sum_filter_add_sum_filter_not, p.sum_one]
  rw [singleEvent_mass] at hc
  have hb : bad ≤ 1 - c := by linarith
  have hbn : 0 ≤ bad := Finset.sum_nonneg fun a _ => p.nonneg a
  have hrecords : p.probEvent (fun ω : Fin R → A => ∃ j, P (ω j)) +
      p.probEvent (fun ω : Fin R → A => ∀ j, ¬ P (ω j)) = 1 := by
    simp only [FinDist.probEvent]
    have h := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin R → A)))
      (p := fun ω => ∃ j, P (ω j)) (f := p.probOf)
    simpa only [not_exists, p.sum_probOf R] using! h
  have hind : ∀ ω : Fin R → A,
      (∏ j, if ¬ P (ω j) then (1 : ℝ) else 0) =
        if ∀ j, ¬ P (ω j) then 1 else 0 := by
    intro ω
    by_cases h : ∀ j, ¬ P (ω j)
    · simp [h]
    · rw [if_neg h]
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  have hbad : p.probEvent (fun ω : Fin R → A => ∀ j, ¬ P (ω j)) = bad ^ R := by
    have h := p.expect_prod (fun _ : Fin R => fun a => if ¬ P a then (1 : ℝ) else 0)
    simpa only [hind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, FinDist.probEvent, bad] using! h
  have hpow : bad ^ R ≤ (1 - c) ^ R := by gcongr
  rw [hbad] at hrecords
  linarith

/-- The number of residues producing a proper gcd factor plus the number of units is at most
`N`. -/
theorem residue_gcd_units_count_le (N : ℕ) [NeZero N] :
    residueGcdProperCount N + Fintype.card (ZMod N)ˣ ≤ N := by
  have hsub : (Finset.univ.filter fun y : ZMod N =>
      1 < Nat.gcd y.val N ∧ Nat.gcd y.val N < N) ⊆
      (Finset.univ.filter fun y : ZMod N => ¬ Nat.Coprime y.val N) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro hc
    have he := hc.gcd_eq_one
    omega
  have hle := Finset.card_le_card hsub
  have hpart := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun y : ZMod N => Nat.Coprime y.val N)
  rw [residue_coprime_card, Finset.card_univ, ZMod.card N] at hpart
  dsimp [residueGcdProperCount]
  omega

/-- For `N ≥ 3` and sampler capacity at least `N`, the residue-attempt bound is at most one. -/
private theorem residue_attempt_bound_le_one (N k : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hk : N ≤ 2^k) : shorResidueAttemptBound N k ≤ 1 := by
  have hs : 1 ≤ N.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
  have hz : (2 : ℝ)^(-(N.primeFactors.card-1 : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hzn : 0 ≤ (2 : ℝ)^(-(N.primeFactors.card-1 : ℤ)) := by positivity
  have hpn : 0 < Real.pi^2 := by positivity
  have hrn : 0 ≤ (8 : ℝ)/Real.pi^2 := by positivity
  have hr : (8 : ℝ)/Real.pi^2 ≤ 2 := by
    rw [div_le_iff₀ hpn]
    nlinarith [Real.pi_gt_three]
  have hC : ((8/Real.pi^2 : ℝ)^2/4) ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    nlinarith
  have hquant : (Fintype.card (ZMod N)ˣ : ℝ)*
      (1-(2 : ℝ)^(-(N.primeFactors.card-1 : ℤ)))*((8/Real.pi^2)^2/4) ≤
      (Fintype.card (ZMod N)ˣ : ℝ) := by
    calc
      _ ≤ (Fintype.card (ZMod N)ˣ : ℝ)*1*1 := by gcongr; linarith
      _ = _ := by ring
  have htotal : (residueGcdProperCount N : ℝ)+(Fintype.card (ZMod N)ˣ : ℝ) ≤ 2^k := by
    exact_mod_cast (residue_gcd_units_count_le N).trans hk
  unfold shorResidueAttemptBound
  apply (div_le_one (by positivity)).2
  linarith only [hquant, htotal]

/-- Establishes preprocessing soundness, amplified residue-attempt success, and soundness of
both classical and unit-based factor outputs in the model associated with [Shor1997]. -/
theorem residueFactoringAlgorithm : ResidueFactoringAlgorithm := by
  intro N R k M _ hM hk hN hcomposite hsize
  refine ⟨fun d h => factoringPreprocessing.1 N d hN h, ?_,
    residue_classical_factor_sound N, attemptFactor_sound N M⟩
  unfold shorResidueProgramSuccessProb
  cases hpre : shorPreprocess N with
  | factor d =>
    have hc := residue_attempt_bound_le_one N k hN hk
    have hn : 0 ≤ (1-shorResidueAttemptBound N k)^R := pow_nonneg (by linarith) R
    linarith
  | residue =>
    have hcert := factoringPreprocessing.2 N hN hpre
    have hs := hcert.2.resolve_left hcomposite
    have h := residueAttemptSuccess N M k hM hk hN hcert.1 hs hsize
    have he : (residueAttemptLaw N M k hM hk).probEvent (residueAttemptRepSuccess N M k R) =
        (residueAttemptLaw N M k hM hk).probEvent
          (fun ω : Fin R → residueAttemptOutcome N M k => ∃ j, residueAttemptSuccessEvent N M k (ω j)) := by
      unfold FinDist.probEvent
      apply Finset.sum_congr
      · ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, residueAttemptRepSuccess]
      · intro ω _
        rfl
    change (residueAttemptLaw N M k hM hk).probEvent (residueAttemptRepSuccess N M k R) ≥ _
    rw [he]
    exact residue_fresh_success_bound (residueAttemptLaw N M k hM hk)
      (residueAttemptSuccessEvent N M k) R (shorResidueAttemptBound N k) h.1

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
