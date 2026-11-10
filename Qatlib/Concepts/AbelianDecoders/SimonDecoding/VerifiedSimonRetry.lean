/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AbelianDecoders.SimonDecoding.SimonDecoderConsumers
import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralUnboundedExecution
import Mathlib.Analysis.SpecificLimits.Basic
set_option warningAsError false
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher
set_option autoImplicit false
open scoped ENNReal Classical
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.AbelianDecoders.SimonDecoding

def simonVerifyCandidate {n : ℕ} {R : Type} [DecidableEq R]
    (f : BooleanVec n → R) : Option (Reg n) → Option (Reg n)
  | none => none
  | some t => if f (regBooleanEquiv n t) = f 0 then some t else none

noncomputable def simonVerifiedTrial {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) : PMF (Option (Reg n)) :=
  PMF.map (simonVerifyCandidate f) (simonDecodedRun f (n+1)).1

noncomputable def simonVerifiedRetryKernel {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) : Unit → PMF (Reg n ⊕ Unit) :=
  fun _ => PMF.map (fun x => match x with
    | none => Sum.inr ()
    | some t => Sum.inl t) (simonVerifiedTrial f)

abbrev SimonRetryRecord (n : ℕ) := Fin (n+1) → AddChar (BooleanVec n) ℂ

def simonBlockOpsBound (n : ℕ) : ℕ := 10*((n+1)*n^2+n^3+(n+1)*n+n^2+n+1)

noncomputable def simonVerifiedHistory {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) :
    ℕ → PMF (Option (Reg n) × List (SimonRetryRecord n))
  | 0 => PMF.pure (none,[])
  | T+1 => PMF.bind (hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv (n+1))
      (fun xs =>
        let out := simonVerifyCandidate f (decodeSimonSecret (simonRecordBits xs))
        match out with
        | some t => PMF.pure (some t,[xs])
        | none => PMF.map (fun h => (h.1,xs::h.2)) (simonVerifiedHistory f T))

noncomputable def simonClassicalTraceCost {n : ℕ} (xs : List (SimonRetryRecord n)) : ℕ :=
  (xs.map (fun z => (decodeSimonWithCost (simonRecordBits z)).2)).sum

noncomputable def simonClassicalExpectedLimit {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) : ℝ≥0∞ :=
  ⨆ T, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (PMF.map (fun h => (h.1,simonClassicalTraceCost h.2)) (simonVerifiedHistory f T))

theorem simon_verified_candidate_supported_sound :
 ∀ (n m : ℕ) (R : Type) [DecidableEq R]
    (f : BooleanVec n → R) (s : Reg n) (rows : Fin m → Reg n),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    (∀ i, booleanDot (regBooleanEquiv n (rows i)) (regBooleanEquiv n s) = 0) →
    ∀ t, simonVerifyCandidate f (decodeSimonSecret rows) = some t → t = s := by
  intro n m R _ f s rows hf hs t ht
  cases hd : decodeSimonSecret rows with
  | none => simp [hd, simonVerifyCandidate] at ht
  | some a =>
    simp only [hd, simonVerifyCandidate] at ht
    split_ifs at ht with hv
    · have hat : a = t := Option.some.inj ht
      subst a
      apply (regBooleanEquiv n).injective
      rcases (hf (regBooleanEquiv n t) 0).mp hv with hz | he
      · have hc := (boolean_gaussian_simon_decode_iff rows t).mp hd
        rw [hz, booleanSimonSubgroup_zero] at hc
        have hm : regBooleanEquiv n s ∈ booleanSampleCandidate (fun i => regBooleanEquiv n (rows i)) :=
          (mem_booleanSampleCandidate _ _).mpr hs
        rw [hc] at hm
        have hs0 : regBooleanEquiv n s = 0 := hm
        exact hz.trans hs0.symm
      · simpa only [zero_add] using he

theorem simon_actual_record_supported {n m : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (s : Reg n)
    (hf : BooleanSimonPromise f (regBooleanEquiv n s))
    (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hx : hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv m xs ≠ 0) :
    ∀ i, booleanDot (regBooleanEquiv n (simonRecordBits xs i)) (regBooleanEquiv n s) = 0 := by
  have h := hiddenSubgroupFreshSamples_boolean_supported_of_ne_zero f
    (booleanSimonSubgroup (regBooleanEquiv n s))
    ((booleanSimonPromise_iff_hidesSubgroup f _).mp hf) (booleanCharacterEquiv n).toEquiv xs hx
  intro i
  have hi := (mem_booleanOrthogonal _ _).mp (h i)
    ⟨regBooleanEquiv n s, self_mem_booleanSimonSubgroup _⟩
  simpa only [simonRecordBits, Equiv.apply_symm_apply] using hi

end Qatlib.Concepts.AbelianDecoders.SimonDecoding

namespace Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

theorem simon_verified_actual_trial_success_and_soundness :
 ∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (s : Reg n),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    (1/2 : ℝ≥0∞) ≤ simonVerifiedTrial f (some s) ∧
    (∀ t, t ≠ s → simonVerifiedTrial f (some t) = 0) ∧
    simonVerifiedTrial f none ≤ 1/2 := by
  classical
  intro n R _ _ _ f s hf
  have hvf : f (regBooleanEquiv n s) = f 0 := (hf _ 0).mpr (Or.inr (by simp))
  have hv : simonVerifyCandidate f (some s) = some s := by
    simp only [simonVerifyCandidate]
    rw [if_pos ((hf _ 0).mpr (Or.inr (by simp)))]
  have hgood : (1/2 : ℝ≥0∞) ≤ simonVerifiedTrial f (some s) := by
    have hb := (simon_gaussian_accessible_budget f s 1 hf).1
    norm_num only [pow_one, show (1 : ℝ) - 1/2 = 1/2 by norm_num] at hb
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hb
    apply hb.trans
    rw [simonVerifiedTrial, PMF.map_apply]
    have hle := ENNReal.le_tsum (f := fun a => if some s = simonVerifyCandidate f a then
      (simonDecodedRun f (n+1)).1 a else 0) (some s)
    simpa [hvf, simonVerifyCandidate] using hle
  have hbad : ∀ t, t ≠ s → simonVerifiedTrial f (some t) = 0 := by
    intro t ht
    by_contra hp
    have hm : some t ∈ (simonVerifiedTrial f).support := (PMF.mem_support_iff _ _).mpr hp
    obtain ⟨a, ha, hat⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    change a ∈ (PMF.map (fun xs => decodeSimonSecret (simonRecordBits xs))
      (hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv (n+1))).support at ha
    obtain ⟨xs, hx, hxa⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
    have hs := simon_verified_candidate_supported_sound n (n+1) R f s (simonRecordBits xs) hf
      (simon_actual_record_supported f s hf xs ((PMF.mem_support_iff _ _).mp hx)) t
      (by rw [hxa]; exact hat)
    exact ht hs
  have htotal : simonVerifiedTrial f none + simonVerifiedTrial f (some s) = 1 := by
    have h := (simonVerifiedTrial f).tsum_coe
    rw [tsum_fintype, Fintype.sum_option] at h
    have he : (∑ t : Reg n, simonVerifiedTrial f (some t)) = simonVerifiedTrial f (some s) := by
      exact Finset.sum_eq_single s (fun t _ ht => hbad t ht) (by simp)
    rwa [he] at h
  refine ⟨hgood, hbad, ?_⟩
  have hle : simonVerifiedTrial f none + (1/2 : ℝ≥0∞) ≤ 1 := by
    calc
      _ ≤ simonVerifiedTrial f none + simonVerifiedTrial f (some s) := add_le_add_right hgood _
      _ = 1 := htotal
  have hh : (1/2 : ℝ≥0∞) + 1/2 = 1 := by simpa using ENNReal.inv_two_add_inv_two
  exact ENNReal.le_of_add_le_add_right (by simp : (1/2 : ℝ≥0∞) ≠ ⊤)
    (hle.trans_eq hh.symm)

theorem simon_verified_actual_oracle_and_decoder_ledgers :
 ∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (x : BooleanVec n),
    Run (AddOracle f) ([.query] : Circuit (BooleanVec n × R)) (Qatlib.Foundations.PureStateMath.Ket (x,0)) = Qatlib.Foundations.PureStateMath.Ket (x,f x) ∧
    (simonDecodedRun f (n+1)).2 = (n+1,2*(n+1),n+1) ∧
    (∀ rows : Fin (n+1) → Reg n,
      (decodeSimonWithCost rows).2 ≤
        10*((n+1)*n^2+n^3+(n+1)*n+n^2+n+1)) := by
  intro n R _ _ _ f x
  refine ⟨?_, (simon_actual_preparation_and_quantum_cost f (n+1)).2.2.2.2, ?_⟩
  · simpa only [run_query, run_nil, zero_add] using applyGate_addOracle_ket f x (0 : R)
  · intro rows
    exact (boolean_gaussian_actual_operation_bound rows).2.1

theorem simon_verified_runFor_succ {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (K : ℕ) :
    runFor (simonVerifiedRetryKernel f) (K+1) (Sum.inr ()) =
    PMF.bind (simonVerifiedTrial f) (fun out => match out with
      | none => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor (simonVerifiedRetryKernel f) K (Sum.inr ()))
      | some t => PMF.pure (Sum.inl t,1)) := by
  simp only [runFor, tick, simonVerifiedRetryKernel, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.bind_map,
    Function.comp_def]
  congr 1
  funext out
  cases out with
  | none => rfl
  | some t => simp only [runFor_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]

theorem simon_verified_pending {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (K : ℕ) :
    generalPendingMass (simonVerifiedRetryKernel f) (Sum.inr ()) K =
      (simonVerifiedTrial f none)^K := by
  induction K with
  | zero => simp [generalPendingMass, runFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event]
  | succ K ih =>
    unfold generalPendingMass
    rw [simon_verified_runFor_succ]
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype,
        Fintype.sum_option]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    simp only [Sum.inl_ne_inr, exists_false, if_false, mul_zero, Finset.sum_const_zero, add_zero]
    rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor (simonVerifiedRetryKernel f) K (Sum.inr ())) =
      PMF.map (fun z => (z.1,1+z.2)) (runFor (simonVerifiedRetryKernel f) K (Sum.inr ())) from rfl,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    change simonVerifiedTrial f none * generalPendingMass (simonVerifiedRetryKernel f)
        (Sum.inr ()) K = _
    rw [ih, pow_succ, mul_comm]

theorem simon_verified_halt_point_succ {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (K j : ℕ) (t : Reg n) :
    runFor (simonVerifiedRetryKernel f) (K+1) (Sum.inr ()) (Sum.inl t,j+1) =
      simonVerifiedTrial f none * runFor (simonVerifiedRetryKernel f) K (Sum.inr ()) (Sum.inl t,j) +
      (if j = 0 then simonVerifiedTrial f (some t) else 0) := by
  rw [simon_verified_runFor_succ, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  rw [GeneralExecution.charge_point_mass, if_pos (by omega)]
  simp only [Nat.add_sub_cancel]
  have he : (∑ a : Reg n, simonVerifiedTrial f (some a) * PMF.pure ((Sum.inl a : Reg n ⊕ Unit),1) (Sum.inl t,j+1)) =
      if j = 0 then simonVerifiedTrial f (some t) else 0 := by
    by_cases hj : j = 0
    · subst j
      simp only [Nat.zero_add, PMF.pure_apply, Prod.mk.injEq, Sum.inl.injEq, and_true,
        mul_ite, mul_one, mul_zero]
      simp
    · have hn : j+1 ≠ 1 := by omega
      simp [PMF.pure_apply, hj]
  rw [he]

theorem simon_verified_actual_geometric_joint_law :
 ∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (K : ℕ) (t : Reg n),
    generalPendingMass (simonVerifiedRetryKernel f) (Sum.inr ()) K =
      (simonVerifiedTrial f none)^K ∧
    haltJoint (simonVerifiedRetryKernel f) (Sum.inr ()) t (K+1) =
      (simonVerifiedTrial f none)^K*simonVerifiedTrial f (some t) := by
  intro n R _ _ _ f K t
  refine ⟨simon_verified_pending f K, ?_⟩
  induction K with
  | zero =>
    rw [haltJoint, simon_verified_halt_point_succ]
    simp [runFor_zero, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
  | succ K ih =>
    change runFor (simonVerifiedRetryKernel f) ((K+1)+1) (Sum.inr ()) (Sum.inl t,(K+1)+1) = _
    rw [simon_verified_halt_point_succ, if_neg (by omega), add_zero]
    change simonVerifiedTrial f none * haltJoint (simonVerifiedRetryKernel f) (Sum.inr ()) t
        (K+1) = _
    rw [ih, pow_succ]
    ac_rfl

theorem simon_verified_unbounded_expected_queries_and_cutoff :
 ∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (s : Reg n),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    generalNeverMass (simonVerifiedRetryKernel f) (Sum.inr ()) = 0 ∧
    generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) ≤ 2 ∧
    (∑' K : ℕ, haltJoint (simonVerifiedRetryKernel f) (Sum.inr ()) s K) = 1 ∧
    ((n+3 : ℕ) : ℝ≥0∞)*generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) ≤
      (2*(n+3) : ℕ) ∧
    (∀ K, generalPendingMass (simonVerifiedRetryKernel f) (Sum.inr ()) K ≤ (1/2 : ℝ≥0∞)^K) := by
  classical
  intro n R _ _ _ f s hf
  have htrial := simon_verified_actual_trial_success_and_soundness n R f s hf
  have htail : ∀ K, generalPendingMass (simonVerifiedRetryKernel f) (Sum.inr ()) K ≤ (1/2 : ℝ≥0∞)^K := by
    intro K
    rw [simon_verified_pending]
    exact pow_le_pow_left₀ (by positivity) htrial.2.2 K
  have htime : generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) ≤ 2 := by
    calc
      _ ≤ ∑' K : ℕ, (1/2 : ℝ≥0∞)^K := ENNReal.tsum_le_tsum htail
      _ = 2 := by rw [ENNReal.tsum_geometric]; norm_num [ENNReal.one_sub_inv_two]
  have hnever := (general_unbounded_actual_expected_time Unit (Reg n)
    (simonVerifiedRetryKernel f) (Sum.inr ())).2.1 (htime.trans_lt (by simp))
  have hbad : ∀ t, t ≠ s → (∑' K, haltJoint (simonVerifiedRetryKernel f) (Sum.inr ()) t K) = 0 := by
    intro t ht
    apply ENNReal.tsum_eq_zero.mpr
    intro K
    cases K with
    | zero => exact GeneralExecution.runFor_point_halt_zero _ 0 () t
    | succ K => rw [(simon_verified_actual_geometric_joint_law n R f K t).2, htrial.2.1 t ht, mul_zero]
  have htotal := general_haltJoint_tsum_add_never (simonVerifiedRetryKernel f) (Sum.inr ())
  rw [hnever, add_zero, tsum_eq_single s (fun t ht => hbad t ht)] at htotal
  refine ⟨hnever, htime, htotal, ?_, htail⟩
  calc
    _ ≤ ((n+3 : ℕ) : ℝ≥0∞)*2 := mul_le_mul_right htime _
    _ = _ := by push_cast; rw [mul_comm]

def simonVerificationInput {n : ℕ} (candidate : Option (Reg n)) : BooleanVec n :=
  match candidate with
  | none => 0
  | some t => regBooleanEquiv n t

theorem simon_verified_two_basis_queries {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (candidate : Option (Reg n)) :
    Run (AddOracle f) ([.query] : Circuit (BooleanVec n × R)) (Qatlib.Foundations.PureStateMath.Ket (0,0)) = Qatlib.Foundations.PureStateMath.Ket (0,f 0) ∧
    Run (AddOracle f) ([.query] : Circuit (BooleanVec n × R))
      (Qatlib.Foundations.PureStateMath.Ket (simonVerificationInput candidate,0)) =
      Qatlib.Foundations.PureStateMath.Ket (simonVerificationInput candidate,f (simonVerificationInput candidate)) := by
  exact ⟨(simon_verified_actual_oracle_and_decoder_ledgers n R f 0).1,
    (simon_verified_actual_oracle_and_decoder_ledgers n R f (simonVerificationInput candidate)).1⟩

theorem simon_verified_complete_block_ledger {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) :
    let q := QueryCount ([.query] : Circuit (BooleanVec n × R))
    let g := GateCount ([.query] : Circuit (BooleanVec n × R))
    ((simonDecodedRun f (n+1)).2.1 + 2*q,
      (simonDecodedRun f (n+1)).2.2.1 + 2*g,
      (simonDecodedRun f (n+1)).2.2.2 + 2) = (n+3,2*(n+1),n+3) := by
  rw [(simon_actual_preparation_and_quantum_cost f (n+1)).2.2.2.2]
  rfl

def simonHistoryObserve {n : ℕ} (h : Option (Reg n) × List (SimonRetryRecord n)) :
    (Reg n ⊕ Unit) × ℕ :=
  ((match h.1 with | none => Sum.inr () | some t => Sum.inl t), h.2.length)

theorem simon_verified_history_coupling {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (T : ℕ) :
    PMF.map simonHistoryObserve (simonVerifiedHistory f T) =
      runFor (simonVerifiedRetryKernel f) T (Sum.inr ()) := by
  induction T with
  | zero => simp [simonVerifiedHistory, simonHistoryObserve, runFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map]
  | succ T ih =>
    rw [simonVerifiedHistory, PMF.map_bind, simon_verified_runFor_succ]
    simp only [simonVerifiedTrial, simonDecodedRun, PMF.map_comp, PMF.bind_map, Function.comp_def]
    congr 1
    funext xs
    cases he : simonVerifyCandidate f (decodeSimonSecret (simonRecordBits xs)) with
    | some t => simp [PMF.pure_map, simonHistoryObserve]
    | none =>
      rw [← ih]
      simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.map_comp,
          Function.comp_def]
      congr 1
      funext h
      simp only [simonHistoryObserve, List.length_cons, Nat.add_comm]

theorem simon_verified_history_length {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (T : ℕ) :
    ∀ h, simonVerifiedHistory f T h ≠ 0 → h.2.length ≤ T := by
  induction T with
  | zero =>
    intro h hh
    have he : h = (none,[]) := (PMF.mem_support_pure_iff _ _).mp ((PMF.mem_support_iff _ _).mpr hh)
    simp [he]
  | succ T ih =>
    intro h hh
    have hs : h ∈ (simonVerifiedHistory f (T+1)).support := (PMF.mem_support_iff _ _).mpr hh
    obtain ⟨xs, _, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    cases he : simonVerifyCandidate f (decodeSimonSecret (simonRecordBits xs)) with
    | some t =>
      simp only [he] at hx
      have hEq := (PMF.mem_support_pure_iff _ _).mp hx
      simp [hEq]
    | none =>
      simp only [he] at hx
      obtain ⟨h0, hh0, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      have hb := ih h0 ((PMF.mem_support_iff _ _).mp hh0)
      simpa only [List.length_cons] using Nat.succ_le_succ hb

theorem simon_classical_trace_bound {n : ℕ} (xs : List (SimonRetryRecord n)) :
    simonClassicalTraceCost xs ≤ simonBlockOpsBound n * xs.length := by
  induction xs with
  | nil => simp [simonClassicalTraceCost]
  | cons xs rest ih =>
    have hx := (boolean_gaussian_actual_operation_bound (simonRecordBits xs)).2.1
    change (decodeSimonWithCost (simonRecordBits xs)).2 + simonClassicalTraceCost rest ≤ _
    calc
      _ ≤ simonBlockOpsBound n + simonBlockOpsBound n * rest.length := Nat.add_le_add hx ih
      _ = _ := by simp only [List.length_cons]; ring

theorem simon_verified_receipt_trace_coupling_and_classical_expected_work :
∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (s : Reg n),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    (∀ T : ℕ,
      PMF.map (fun h => ((match h.1 with | none => Sum.inr () | some t => Sum.inl t),h.2.length))
        (simonVerifiedHistory f T) =
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor (simonVerifiedRetryKernel f) T (Sum.inr ()) ∧
      (∀ h, simonVerifiedHistory f T h ≠ 0 →
        h.2.length ≤ T ∧ simonClassicalTraceCost h.2 ≤ simonBlockOpsBound n*h.2.length) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (PMF.map (fun h => (h.1,simonClassicalTraceCost h.2))
        (simonVerifiedHistory f T)) ≤ (2*simonBlockOpsBound n : ℕ)) ∧
    simonClassicalExpectedLimit f ≤ (2*simonBlockOpsBound n : ℕ) := by
  classical
  intro n R _ _ _ f s hf
  have htime := (simon_verified_unbounded_expected_queries_and_cutoff n R f s hf).2.1
  have hcost : ∀ T, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (PMF.map (fun h => (h.1,simonClassicalTraceCost h.2))
      (simonVerifiedHistory f T)) ≤ (2*simonBlockOpsBound n : ℕ) := by
    intro T
    have hround : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T) (fun h => (h.2.length : ℝ≥0∞)) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) := by
      rw [← simon_verified_history_coupling,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      rfl
    have hfinite : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor (simonVerifiedRetryKernel f) T (Sum.inr ())) ≤ 2 := by
      rw [(general_unbounded_actual_expected_time Unit (Reg n) (simonVerifiedRetryKernel f) (Sum.inr ())).2.2 T]
      exact (ENNReal.sum_le_tsum (Finset.range T)).trans htime
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    calc
      _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
          (fun h => (simonBlockOpsBound n : ℝ≥0∞)*(h.2.length : ℝ≥0∞)) := by
        apply ENNReal.tsum_le_tsum
        intro h
        apply mul_le_mul_right
        change (simonClassicalTraceCost h.2 : ℝ≥0∞) ≤
            (simonBlockOpsBound n : ℝ≥0∞)*(h.2.length : ℝ≥0∞)
        rw [← Nat.cast_mul]
        exact_mod_cast simon_classical_trace_bound h.2
      _ = (simonBlockOpsBound n : ℝ≥0∞)*Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
          (fun h => (h.2.length : ℝ≥0∞)) := by
        unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro h
        (try dsimp only)
        ac_rfl
      _ ≤ (simonBlockOpsBound n : ℝ≥0∞)*2 := mul_le_mul_right (hround ▸ hfinite) _
      _ = _ := by push_cast; rw [mul_comm]
  refine ⟨fun T => ⟨simon_verified_history_coupling f T,
    fun h hh => ⟨simon_verified_history_length f T h hh, simon_classical_trace_bound h.2⟩, hcost T⟩, ?_⟩
  exact iSup_le hcost

end Qatlib.Concepts.AbelianDecoders.SimonDecoding
