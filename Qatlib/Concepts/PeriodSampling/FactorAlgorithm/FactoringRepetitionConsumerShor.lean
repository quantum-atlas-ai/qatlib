/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringRepetitionConsumerStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.SampledAttemptSuccessShor
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

private theorem fresh_success_bound {A : Type*} [Fintype A] [DecidableEq A]
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

theorem factoringRepetitionConsumer : FactoringRepetitionConsumer := by
  intro N M k R _ hM hk hN hodd hs hsize
  have h := sampledAttemptSuccess N M k hM hk hN hodd hs hsize
  refine ⟨?_, h.2⟩
  have he : (attemptLaw N M k hM hk).probEvent (attemptRepSuccess N M k R) =
      (attemptLaw N M k hM hk).probEvent
        (fun ω : Fin R → Reg k ⊕ (ZMod N)ˣ × Fin M × Fin M =>
          ∃ j, attemptSuccess N M k (ω j)) := by
    unfold FinDist.probEvent
    apply Finset.sum_congr
    · ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, attemptRepSuccess]
    · intro ω _
      rfl
  rw [he]
  exact fresh_success_bound (attemptLaw N M k hM hk) (attemptSuccess N M k)
    R (shorAttemptBound N k) h.1

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
