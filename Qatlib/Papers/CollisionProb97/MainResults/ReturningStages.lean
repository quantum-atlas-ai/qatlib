/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralUnboundedExecution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped ENNReal
namespace Qatlib.Papers.CollisionProb97.MainResults.ReturningStages
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

theorem finite_expected_time_never_zero {S O : Type} (next : S → PMF (O ⊕ S))
    (cfg : O ⊕ S) (h : generalUnboundedTime next cfg < ⊤) :
    generalNeverMass next cfg = 0 :=
  (general_unbounded_actual_expected_time S O next cfg).2.1 h

theorem adaptive_two_stage_bound {S T : Type} (p : CostedLaw S)
    (step : S → CostedLaw T) (a b : ℝ≥0∞)
    (hp : expectedCost p ≤ a) (hs : ∀ s, expectedCost (step s) ≤ b) :
    expectedCost (CostedLaw.bind p step) ≤ a+b := by
  rw [expectedCost_bind]
  refine add_le_add hp ?_
  calc
    expectation p (fun x => expectedCost (step x.1)) ≤ expectation p (fun _ => b) :=
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_le_of_forall
        (fun x => hs x.1)
    _ = b := expectation_const p b

noncomputable def stageSequence {S : Type} (step : ℕ → S → CostedLaw S)
    (initial : S) : ℕ → CostedLaw S
  | 0 => CostedLaw.ret initial
  | n+1 => CostedLaw.bind (stageSequence step initial n) (step n)

theorem fixed_stage_expected_bound {S : Type} (step : ℕ → S → CostedLaw S)
    (initial : S) (c : ℝ≥0∞) (hs : ∀ i s, expectedCost (step i s) ≤ c) (n : ℕ) :
    expectedCost (stageSequence step initial n) ≤ (n : ℝ≥0∞)*c := by
  induction n with
  | zero => simp [stageSequence]
  | succ n ih =>
    calc
      expectedCost (stageSequence step initial (n+1)) ≤ (n:ℝ≥0∞)*c+c :=
        adaptive_two_stage_bound (stageSequence step initial n) (step n) _ _ ih (hs n)
      _ = ((n+1:ℕ):ℝ≥0∞)*c := by simp [Nat.cast_add, add_mul]

theorem option_tsum_split {α : Type} (F : Option α → ℝ≥0∞) :
    ∑' z, F z = (∑' a, F (some a)) + F none := by
  have hs := (ENNReal.summable
    (f := fun x : α ⊕ PUnit => F ((Equiv.optionEquivSumPUnit α).symm x))).hasSum
  rw [tsum_sum_type'] at hs
  have h := ((Equiv.hasSum_iff (Equiv.optionEquivSumPUnit α).symm).mp hs).tsum_eq
  simpa using h

noncomputable def returnLaw {S O : Type} [Nonempty O]
    (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) : CostedLaw O :=
  (generalUnboundedLaw next cfg).map (fun z => z.getD (Classical.choice inferInstance, 0))

theorem returnLaw_apply {S O : Type} [Nonempty O]
    (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (hNever : generalNeverMass next cfg = 0) (o : O) (k : ℕ) :
    returnLaw next cfg (o,k) = haltJoint next cfg o k := by
  classical
  rw [returnLaw, PMF.map_apply, option_tsum_split]
  simp only [generalUnboundedLaw_apply, generalUnboundedMass, hNever,
    ite_self, add_zero, Option.getD_some]
  have hp : ∀ p : O × ℕ, (if (o,k) = p then haltJoint next cfg p.1 p.2 else 0)
      = if p = (o,k) then haltJoint next cfg p.1 p.2 else 0 := by
    intro p
    simp only [eq_comm]
  rw [tsum_congr hp, tsum_ite_eq]

theorem returnLaw_nonzero_some {S O : Type} [Nonempty O]
    (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (hNever : generalNeverMass next cfg = 0) (o : O) (k : ℕ)
    (h : returnLaw next cfg (o,k) ≠ 0) :
    generalUnboundedLaw next cfg (some (o,k)) ≠ 0 := by
  simpa only [returnLaw_apply next cfg hNever o k,
    generalUnboundedLaw_apply, generalUnboundedMass_some] using h

theorem returnLaw_expectedCost {S O : Type} [Nonempty O]
    (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S)
    (hNever : generalNeverMass next cfg = 0) :
    expectedCost (returnLaw next cfg) = generalUnboundedTime next cfg := by
  rw [(general_unbounded_actual_expected_time S O next cfg).1, hNever, mul_zero, add_zero]
  unfold expectedCost expectation
  rw [tsum_prod_type']
  exact tsum_congr fun o => tsum_congr fun k => by
    rw [returnLaw_apply next cfg hNever o k, mul_comm]

noncomputable def relabelSupported {α β : Type} (p : CostedLaw α)
    (f : ∀ z ∈ p.support, β) : CostedLaw β :=
  p.bindOnSupport fun z hz => PMF.pure (f z hz, z.2)

theorem relabelSupported_expectedCost {α β : Type} (p : CostedLaw α)
    (f : ∀ z ∈ p.support, β) : expectedCost (relabelSupported p f) = expectedCost p := by
  classical
  unfold relabelSupported expectedCost expectation
  simp only [PMF.bindOnSupport_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro z
  by_cases hz : p z = 0
  · simp [hz]
  · simp only [dif_neg hz, PMF.pure_apply, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, tsum_ite_eq]

theorem relabelSupported_support {α β : Type} (p : CostedLaw α)
    (f : ∀ z ∈ p.support, β) (b : β) (c : ℕ)
    (h : relabelSupported p f (b,c) ≠ 0) :
    ∃ (z : α × ℕ) (hz : z ∈ p.support), b = f z hz ∧ c = z.2 := by
  change (b,c) ∈ (p.bindOnSupport fun z hz => PMF.pure (f z hz, z.2)).support at h
  obtain ⟨z, hz, hb⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp h
  have he : (b,c) = (f z hz, z.2) := (PMF.mem_support_pure_iff _ _).mp hb
  exact ⟨z, hz, congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem expectation_const_on_support {α : Type} (p : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ a, p a ≠ 0 → f a = c) : expectation p f = c := by
  calc
    expectation p f = expectation p (fun _ => c) := by
      unfold expectation
      apply tsum_congr
      intro a
      by_cases ha : p a = 0
      · simp [ha]
      · rw [h a ha]
    _ = c := expectation_const p c

theorem expectation_lower_on_support {α : Type} (p : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ a, p a ≠ 0 → c ≤ f a) : c ≤ expectation p f := by
  rw [← expectation_const p c]
  unfold expectation
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul' le_rfl (h a ha)

theorem bind_support {α β : Type} (p : CostedLaw α) (f : α → CostedLaw β)
    (b : β) (c : ℕ) (h : CostedLaw.bind p f (b,c) ≠ 0) :
    ∃ (a : α) (i j : ℕ), p (a,i) ≠ 0 ∧ f a (b,j) ≠ 0 ∧ c = i+j := by
  change (b,c) ∈ (PMF.bind p fun z => CostedLaw.charge z.2 (f z.1)).support at h
  obtain ⟨z, hz, hc⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
  obtain ⟨w, hw, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  rcases z with ⟨a,i⟩
  rcases w with ⟨b',j⟩
  have hb : b' = b := congrArg Prod.fst he
  subst b'
  exact ⟨a,i,j,hz,hw,(congrArg Prod.snd he).symm⟩

theorem stageSequence_invariant {S : Type} (step : ℕ → S → CostedLaw S) (initial : S)
    (P : ℕ → S → Prop) (h0 : P 0 initial)
    (hs : ∀ n s t c, P n s → step n s (t,c) ≠ 0 → P (n+1) t)
    (n : ℕ) (t : S) (c : ℕ) (h : stageSequence step initial n (t,c) ≠ 0) : P n t := by
  induction n generalizing t c with
  | zero =>
    change (t,c) ∈ (PMF.pure (initial,0)).support at h
    have he : (t,c) = (initial,0) := (PMF.mem_support_pure_iff _ _).mp h
    cases he
    exact h0
  | succ n ih =>
    obtain ⟨s,i,j,hp,hq,_⟩ := bind_support (stageSequence step initial n) (step n) t c h
    exact hs n s t j (ih s i hp) hq

end Qatlib.Papers.CollisionProb97.MainResults.ReturningStages
