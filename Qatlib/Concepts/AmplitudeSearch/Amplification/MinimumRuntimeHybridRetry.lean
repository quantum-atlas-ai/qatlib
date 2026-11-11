/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainder
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumRuntimeDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainder
import Qatlib.Concepts.AmplitudeSearch.Amplification.SortedTable
import Mathlib.Data.List.GetD
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumRuntimeNativeAttempt

/-!
# Hybrid BBHT retries and their cost limits

This module verifies hybrid implementations of repeated BBHT search [BoyerEtAl1998] used in
quantum minimum finding [DurrHoyer1996]. It proves legality of preparation and reset circuits,
exact success and exhaustion recurrences, and instrument formulas for the same operational
semantics.

The cost analysis tracks queries, gates, measurements, and random-bit reads. Append identities
and monotonicity give limits as the schedule grows; for a fixed positive-width schedule,
increasing the sampler cap yields explicit limits for costs, statuses, and homogeneous terminal
quantum payoffs.

## Main statements

* `hybridRetrySuccess_cons`: gives the exact one-stage success recurrence.
* `hybridRetryMoment_charge_cons`: separates sampler, attempt, reset, and continuation charges.
* `hybridRetry_status_partition`: partitions total mass into success, exhaustion, and timeout.
* `hybridRetry_quantum_cap_limit`: identifies the sampler-cap limit for homogeneous terminal
  payoffs.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.UniformTape

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CappedFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false

open Qatlib
open scoped ENNReal

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount Matrix
open Classical
open scoped ComplexOrder

/-- Adding a constant to the successful-depth payoff adds that constant times the total
successful-path mass to `codeSuccess`. -/
theorem codeSuccess_add_const {m : ℕ} (p : CoinCode (SamplerRecord m))
    (F : Fin m → ℝ) (a : ℝ) :
    codeSuccess p (fun j => F j + a) = codeSuccess p F + a * codeSuccess p (fun _ => 1) := by
  unfold codeSuccess
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rcases h : (p.paths.get c).1.1 with x | x
  · rcases x with ⟨j,b,d⟩
    ring
  · ring

/-- For positive depth width `m`, the prepared BBHT instrument's expected gate count is the
sampler-return mass times `((m + 1) / 2 + (n + 2))`. -/
theorem preparedBBHTInstrument_expected_gates (n : ℕ) {m : ℕ} (hm : 0 < m)
    (cap : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (preparedBBHTInstrument n m cap A) (preparedInput n) z *
      ((((preparedBBHTProgram n m).compile cap).record
        (encodeGate (BitOracleOn (fun i => decide (i ∈ A)))) z).gates : ℝ)) =
    (1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) *
      (((m : ℝ) + 1) / 2 + (n + 2)) := by
  rw [preparedBBHTInstrument_gates_paths, codeSuccess_add_const]
  have hq := bbhtInstrument_expected_queries (Nat.two_pow_pos n) hm cap A
  rw [bbhtInstrument_queries_paths] at hq
  rw [hq, uniformDepth_success hm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- A finite-code bit-flip gate maps a basis ket to the ket with its designated bit negated. -/
theorem finiteCode_x_ket {n : ℕ} (w : Fin n) (x : Reg n) :
    ApplyGate (finiteCodeMatrix n (.x w.val)) (Ket x) = Ket (flipAt x w) := by
  rw [finiteCodeMatrix, dif_pos w.isLt, applyGate_wireGate_ket]
  cases hx : x w <;> simp [PauliX, permMatrix, flipAt, hx]

/-- Running the masked bit-flip word on a basis ket yields the ket of `flipRegister`. -/
theorem maskWord_run_ket {n : ℕ} (ws : List (Fin n)) (mask x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (maskWord ws mask)) (Ket x) =
      Ket (flipRegister ws mask x) := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
      cases hm : mask w
      · simpa only [maskWord, List.flatMap_cons, hm, Bool.false_eq_true, ↓reduceIte,
          List.nil_append, flipRegister] using! ih x
      · simp only [maskWord, List.flatMap_cons, hm, ↓reduceIte, List.singleton_append]
        change Run _ (.gate (finiteCodeMatrix n (.x w.val)) ::
          finiteCodeCircuit n (maskWord ws mask)) (Ket x) = _
        rw [Run, finiteCode_x_ket, ih]
        simp [flipRegister, hm]

/-- For a duplicate-free wire list, `flipRegister` XORs a bit with its mask exactly when the
wire belongs to the list. -/
theorem flipRegister_apply {n : ℕ} (ws : List (Fin n)) (hws : ws.Nodup)
    (mask x : Reg n) (i : Fin n) :
    flipRegister ws mask x i = if i ∈ ws then (x i ^^ mask i) else x i := by
  induction ws generalizing x with
  | nil => simp [flipRegister]
  | cons w ws ih =>
      obtain ⟨hw,hws⟩ := List.nodup_cons.mp hws
      rw [flipRegister, ih hws]
      by_cases hiw : i = w
      · subst i
        have hi : w ∉ ws := hw
        cases hm : mask w <;> simp [flipAt, hi]
      · cases hm : mask w <;> by_cases hi : i ∈ ws <;>
          simp [flipAt, hi, hiw]

/-- The reset word associated with a register maps that register's basis ket to the all-zero
basis ket. -/
theorem basisResetWord_run (n : ℕ) (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (basisResetWord n x)) (Ket x) =
      Ket (ZeroStr n) := by
  rw [basisResetWord, maskWord_run_ket]
  congr 1
  ext i
  rw [flipRegister_apply _ (List.nodup_finRange n)]
  simp [ZeroStr]

/-- A masked bit-flip word has length at most the length of its supplied wire list. -/
theorem maskWord_length_le {n : ℕ} (ws : List (Fin n)) (mask : Reg n) :
    (maskWord ws mask).length ≤ ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [maskWord] at ih
      cases hm : mask w <;> simp only [maskWord, List.flatMap_cons, hm,
      Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append,
      List.length_cons] <;> omega

/-- Every masked bit-flip word passes the finite-word legality test. -/
theorem maskWord_legal {n : ℕ} (ws : List (Fin n)) (mask : Reg n) :
    finiteWordLegal n (maskWord ws mask) = true := by
  induction ws with
  | nil => rfl
  | cons w ws ih => cases hm : mask w <;>
      simp [maskWord, hm, finiteWordLegal, finiteCodeLegal, w.isLt] at *

/-- The reset word for an `n`-bit register uses at most `n` gates. -/
theorem basisResetWord_length_le (n : ℕ) (x : Reg n) : (basisResetWord n x).length ≤ n := by
  simpa only [basisResetWord, List.length_finRange] using! maskWord_length_le (List.finRange n) x

/-- Every basis-reset word passes the finite-word legality test at its register width. -/
theorem basisResetWord_legal (n : ℕ) (x : Reg n) :
    finiteWordLegal n (basisResetWord n x) = true := maskWord_legal _ _

/-- A basis-reset circuit uses no queries, has one gate per reset-word entry, and uses at most
`n + 1` gates. -/
theorem basisResetCircuit_counts (n : ℕ) (x : Fin (2 ^ n * 2)) :
    QueryCount (basisResetCircuit n x) = 0 ∧
    GateCount (basisResetCircuit n x) = (basisResetWord (n + 1) ((prepLayout n).symm x)).length ∧
    GateCount (basisResetCircuit n x) ≤ n + 1 := by
  have h := relabelCircuit_legality_resources (prepLayout n)
    (finiteCodeCircuit (n + 1) (basisResetWord (n + 1) ((prepLayout n).symm x)))
  have hc := finiteCodeCircuit_counts (n + 1) (basisResetWord (n + 1) ((prepLayout n).symm x))
  exact ⟨h.2.1.trans hc.1, h.2.2.1.trans hc.2,
    (h.2.2.1.trans hc.2).le.trans (basisResetWord_length_le _ _)⟩

/-- Every encoded basis-reset circuit is a unitary circuit. -/
theorem basisResetCircuit_legal (n : ℕ) (x : Fin (2 ^ n * 2)) :
    IsUnitaryCircuit (basisResetCircuit n x) :=
  (relabelCircuit_legality_resources _ _).1.mpr
    ((finite_gate_description_rejection_unitarity_and_counts _ _).2 (basisResetWord_legal _ _)).1

/-- For any oracle, the reset circuit associated with a basis index maps its ket to the zero
preparation ket. -/
theorem basisResetCircuit_run (n : ℕ) (x : Fin (2 ^ n * 2)) (O : Operator (2 ^ n * 2)) :
    Run O (basisResetCircuit n x) (Ket x) = Ket (prepZero n) := by
  have h := (run_relabelCircuit_readout (prepLayout n)
    (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      (finiteCodeCircuit (n + 1) (basisResetWord (n + 1) ((prepLayout n).symm x)))
        (Ket ((prepLayout n).symm x)) ∅).1
  rw [Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one, relabel_ket, Equiv.apply_symm_apply,
    basisResetWord_run, relabel_ket] at h
  exact (run_eq_of_queryCount_eq_zero O 1 _ (basisResetCircuit_counts n x).1 _).trans h

/-- Resetting a measured basis state and then preparing it yields the encoded uniform index
state with a minus ancilla. -/
theorem basisResetCircuit_prepare (n : ℕ) (x : Fin (2 ^ n * 2)) (O : Operator (2 ^ n * 2)) :
    Run O (basisResetCircuit n x ++ prepPowCircuit n) (Ket x) =
      encodeState (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.WithMinus (Uniform (Fin (2 ^ n)))) := by
  rw [Qatlib.Foundations.QueryWordCore.Circuit.run_append, basisResetCircuit_run, prepZero,
      prepPowCircuit_run]

/-- Reset followed by preparation uses no queries and at most `2 * n + 3` gates. -/
theorem basisResetCircuit_prepare_counts (n : ℕ) (x : Fin (2 ^ n * 2)) :
    QueryCount (basisResetCircuit n x ++ prepPowCircuit n) = 0 ∧
    GateCount (basisResetCircuit n x ++ prepPowCircuit n) ≤ 2 * n + 3 := by
  rw [queryCount_append, gateCount_append, (basisResetCircuit_counts n x).1,
    (prepPowCircuit_counts n).1, (prepPowCircuit_counts n).2]
  exact ⟨rfl, by have h := (basisResetCircuit_counts n x).2.2; omega⟩

/-- The full-basis measurement followed by basis reset is a well-formed observed circuit. -/
theorem measuredBasisReset_legal (n : ℕ) : observedWellFormed (measuredBasisReset n) :=
  fun x => prependCircuit_legal _ (basisResetCircuit_legal n x) _ trivial

/-- Circuit execution commutes with complex scalar multiplication of the input state. -/
theorem circuit_run_smul {D : ℕ} (O : Operator D) (C : Circuit (Fin D)) (c : ℂ)
    (ψ : QState (Fin D)) : Run O C (c • ψ) = c • Run O C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih => cases s <;> simp only [Run,ApplyGate,Matrix.mulVec_smul,ih]

/-- The traces of measured basis reset are exactly the list of `measuredResetTrace` values over
all basis outcomes. -/
theorem measuredBasisReset_traces (n : ℕ) (O : Operator (2 ^ n * 2))
    (ψ : QState (Fin (2 ^ n * 2))) :
    observedTraces O (measuredBasisReset n) ψ = List.ofFn (measuredResetTrace n ψ) := by
  unfold measuredBasisReset
  simp only [observedTraces,prependCircuit_traces,id_eq,collapse_singleton,
    circuit_run_smul,basisResetCircuit_run,List.map_singleton]
  have h (x : Fin (2 ^ n * 2)) :
      addCircuitCounts (basisResetCircuit n x)
        ⟨ψ x • Ket (prepZero n),true,0,0,0,[]⟩ =
      ⟨ψ x • Ket (prepZero n),true,0,(basisResetWord (n+1) ((prepLayout n).symm x)).length,0,[]⟩ := by
    simp only [addCircuitCounts,(basisResetCircuit_counts n x).1,(basisResetCircuit_counts n x).2.1,
      Nat.zero_add]
  simp only [h]
  change (List.ofFn (fun x => [measuredResetTrace n ψ x])).flatten = _
  change (List.ofFn ((fun z => [z]) ∘ measuredResetTrace n ψ)).flatten = _
  rw [← List.map_ofFn]
  exact List.flatMap_singleton' _

/-- The hybrid checked-readout program is legal. -/
theorem hybridCheckedReadout_legal (N : ℕ) : (hybridCheckedReadout N).Legal :=
  fun x => ⟨(checkedReadout_legal N x).1,fun _ => trivial⟩

/-- The hybrid checked attempt is legal for a positive number of indices. -/
theorem hybridCheckedAttempt_legal {N : ℕ} (hN : 0 < N) (j : ℕ) : (hybridCheckedAttempt N j).Legal :=
  HybridProgram.prependCircuit_legal _ (encodeCircuit_legal _
    (Qatlib.Concepts.SearchStopping.KnownCount.isUnitaryCircuit_groverCircuit (by simpa using! hN) j).lift) _ (hybridCheckedReadout_legal N)

/-- Every explicitly prepared hybrid checked attempt is legal. -/
theorem hybridPreparedAttempt_legal (n j : ℕ) : (hybridPreparedAttempt n j).Legal :=
  HybridProgram.prependCircuit_legal _ (prepPowCircuit_legal n) _
    (hybridCheckedAttempt_legal (Nat.two_pow_pos n) j)

/-- The hybrid retry program is legal for any finite width schedule and sampler cap. -/
theorem hybridRetry_legal (n cap : ℕ) (sizes : List ℕ) : (hybridRetry n cap sizes).Legal := by
  induction sizes with
  | nil => trivial
  | cons m ms ih =>
      apply HybridProgram.ofCoins_legal
      intro a
      cases ha : a.1 with
      | inr cfg => trivial
      | inl cfg =>
          apply HybridProgram.bind_legal _ (hybridPreparedAttempt_legal n cfg.1.val)
          intro z
          split_ifs
          · trivial
          · apply HybridProgram.prependCircuit_legal _ (basisResetCircuit_legal n _)
            exact HybridProgram.bind_legal _ ih _ (fun _ => trivial)

/-- Forgetting the index returned by hybrid checked readout gives the hybrid embedding of the
observed checked-readout circuit. -/
theorem hybridCheckedReadout_forget (N : ℕ) :
    (hybridCheckedReadout N).bind (fun z => .ret z.2) = HybridProgram.ofObserved (checkedReadout N) := rfl

/-- Binding a continuation after a prepended circuit equals prepending that circuit to the bound
hybrid program. -/
theorem hybrid_bind_prepend {D : ℕ} {A B : Type} (C : Circuit (Fin D)) (p : HybridProgram D A)
    (k : A → HybridProgram D B) :
    (HybridProgram.prependCircuit C p).bind k = HybridProgram.prependCircuit C (p.bind k) := by
  induction C with
  | nil => rfl
  | cons s C ih => simpa only [HybridProgram.prependCircuit,HybridProgram.bind] using! congrArg (HybridProgram.step s) ih

/-- Embedding an observed program with a prepended circuit equals prepending the circuit to its
hybrid embedding. -/
theorem hybrid_ofObserved_prepend {D : ℕ} (C : Circuit (Fin D)) (p : ObservedCircuit (Fin D)) :
    HybridProgram.ofObserved (prependCircuit C p) =
      HybridProgram.prependCircuit C (HybridProgram.ofObserved p) := by
  induction C with
  | nil => rfl
  | cons s C ih => simpa only [prependCircuit,HybridProgram.prependCircuit,HybridProgram.ofObserved]
      using! congrArg (HybridProgram.step s) ih

/-- Forgetting the returned index of a prepared hybrid attempt gives the hybrid embedding of the
prepared observed attempt. -/
theorem hybridPreparedAttempt_forget (n j : ℕ) :
    (hybridPreparedAttempt n j).bind (fun z => .ret z.2) =
      HybridProgram.ofObserved (preparedAttempt n j) := by
  simp only [hybridPreparedAttempt,hybridCheckedAttempt,hybrid_bind_prepend,
    hybridCheckedReadout_forget,preparedAttempt,checkedAttempt,hybrid_ofObserved_prepend]

/-- The encoded membership oracle used by the retry program is unitary. -/
theorem retryOracle_unitary {n : ℕ} (A : Finset (Fin (2 ^ n))) :
    retryOracle A ∈ Matrix.unitaryGroup (Fin (2 ^ n * 2)) ℂ :=
  encodeGate_unitary (bitOracleOn_unitary _)

/-- A continuation after measured basis reset evaluates as its value on the zero preparation ket
multiplied by the input branch mass. -/
theorem measuredBasisReset_eval_cont {B : Type} (n : ℕ) (O : Operator (2 ^ n * 2))
    (p : HybridProgram (2 ^ n * 2) B) (f : B → ℝ) (ψ : QState (Fin (2 ^ n * 2))) :
    (HybridProgram.ofObserved (measuredBasisReset n)).eval O ψ
      (fun _ φ => p.eval O φ (fun b χ => branchMass χ * f b)) =
      branchMass ψ * p.eval O (Ket (prepZero n)) (fun b χ => branchMass χ * f b) := by
  rw [HybridProgram.eval_ofObserved,measuredBasisReset_traces]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,measuredResetTrace,
    HybridProgram.eval_mass_smul]
  rw [← Finset.sum_mul]
  rfl

/-- The success value of a prepared hybrid attempt is the sum of its checked output masses over
all indices. -/
theorem hybridPreparedAttempt_success_eval (n j : ℕ) (A : Finset (Fin (2 ^ n))) :
    (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
      (fun z φ => branchMass φ * (if z.2 then 1 else 0)) =
      ∑ i : Fin (2 ^ n), CheckedOutputMass A j i := by
  have h := congrArg (fun p : HybridProgram (2 ^ n * 2) Bool => p.eval (retryOracle A)
    (Ket (prepZero n)) (fun b φ => branchMass φ * (if b then 1 else 0)))
      (hybridPreparedAttempt_forget n j)
  (try dsimp only at h)
  rw [HybridProgram.eval_bind,HybridProgram.eval_ofObserved] at h
  exact h.trans (preparedAttempt_success_sum n j A)

/-- A prepared attempt with payoff one on success and constant `r` on failure evaluates to
checked success mass plus failure mass times `r`. -/
theorem hybridPreparedAttempt_cont (n j : ℕ) (A : Finset (Fin (2 ^ n))) (r : ℝ) :
    (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
      (fun z φ => branchMass φ * (if z.2 then 1 else r)) =
      (∑ i : Fin (2 ^ n), CheckedOutputMass A j i) +
        (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j i) * r := by
  have hpay : (fun z : Fin (2 ^ n) × Bool => fun φ : QState (Fin (2 ^ n * 2)) =>
      branchMass φ * (if z.2 then 1 else r)) =
      (fun z φ => r * branchMass φ + (1-r) * (branchMass φ * (if z.2 then 1 else 0))) := by
    funext z φ
    cases z.2 <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring
  have hk : branchMass (Ket (prepZero n)) = 1 := measureProb_univ (normalized_ket _)
  rw [hpay,HybridProgram.eval_add,HybridProgram.eval_mul,HybridProgram.eval_mul,
    HybridProgram.eval_mass _ (retryOracle_unitary A) _ (hybridPreparedAttempt_legal n j),
    hk,hybridPreparedAttempt_success_eval]
  ring

/-- The false-bit checked leaf is the original basis amplitude on the same index with false
ancilla when the oracle is false, and is zero otherwise. -/
theorem checkedLeafState_false_basis {N : ℕ} (f : Fin N → Bool)
    (ψ : QState (Fin (N * 2))) (x : Fin (N * 2)) :
    checkedLeafState f ψ x 0 =
      (if f ((indexBitEquiv N).symm x).1 then 0 else ψ x) •
        Ket (indexBitEquiv N (((indexBitEquiv N).symm x).1,false)) := by
  unfold checkedLeafState
  cases hf : f ((indexBitEquiv N).symm x).1 <;> norm_num [boolEquivFin2]

/-- Resetting a failed checked-readout branch before a continuation replaces its state by the
zero preparation ket, with the original branch mass factored out. -/
theorem hybridReadout_reset_cont {B : Type} (n : ℕ) (A : Finset (Fin (2 ^ n)))
    (p : HybridProgram (2 ^ n * 2) B) (f : B → ℝ) (ψ : QState (Fin (2 ^ n * 2))) :
    (hybridCheckedReadout (2 ^ n)).eval (retryOracle A) ψ
      (fun z φ => if z.2 then branchMass φ else
        p.eval (retryOracle A)
          (Run (retryOracle A) (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))) φ)
          (fun b χ => branchMass χ * f b)) =
    (hybridCheckedReadout (2 ^ n)).eval (retryOracle A) ψ
      (fun z φ => branchMass φ * (if z.2 then 1 else
        p.eval (retryOracle A) (Ket (prepZero n)) (fun b χ => branchMass χ * f b))) := by
  simp only [hybridCheckedReadout,HybridProgram.eval,retryOracle,id_eq,
    query_reset_collapsed,collapse_encoded_bit]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro b _
  fin_cases b
  · norm_num
    cases hf : decide (((indexBitEquiv (2 ^ n)).symm x).1 ∈ A)
    · norm_num [boolEquivFin2]
      rw [circuit_run_smul,basisResetCircuit_run,HybridProgram.eval_mass_smul]
      rw [branchMass,measureProb_smul,measureProb_univ (normalized_ket _),mul_one]
    · norm_num [boolEquivFin2]
      have hz : Run (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
          (basisResetCircuit n (indexBitEquiv (2 ^ n) (((indexBitEquiv (2 ^ n)).symm x).1,false))) 0 = 0 := by
        have h := circuit_run_smul (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
          (basisResetCircuit n (indexBitEquiv (2 ^ n) (((indexBitEquiv (2 ^ n)).symm x).1,false))) 0
            (Ket (prepZero n))
        simpa using! h
      rw [hz]
      have he := p.eval_mass_smul (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
        (Ket (prepZero n)) f 0
      simpa [branchMass,MeasureProb,BornProb] using! he
  · norm_num

/-- A prepared attempt followed by reset and continuation on failure evaluates to checked
success mass plus failure mass times the continuation value from the zero preparation ket. -/
theorem hybridPreparedAttempt_reset_cont {B : Type} (n j : ℕ) (A : Finset (Fin (2 ^ n)))
    (p : HybridProgram (2 ^ n * 2) B) (f : B → ℝ) :
    (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
      (fun z φ => if z.2 then branchMass φ else p.eval (retryOracle A)
        (Run (retryOracle A) (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))) φ)
        (fun b χ => branchMass χ * f b)) =
      (∑ i : Fin (2 ^ n), CheckedOutputMass A j i) +
        (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j i) *
          p.eval (retryOracle A) (Ket (prepZero n)) (fun b χ => branchMass χ * f b) := by
  calc
    _ = (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
        (fun z φ => branchMass φ * (if z.2 then 1 else
          p.eval (retryOracle A) (Ket (prepZero n)) (fun b χ => branchMass χ * f b))) := by
      simp only [hybridPreparedAttempt,hybridCheckedAttempt,HybridProgram.eval_prepend]
      exact hybridReadout_reset_cont n A p f _
    _ = _ := hybridPreparedAttempt_cont n j A _

/-- An empty hybrid retry schedule has success value zero. -/
theorem hybridRetrySuccess_nil (n cap : ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetrySuccess n cap [] A = 0 := by
  simp [hybridRetrySuccess,hybridRetry,HybridProgram.eval,foundUtility]

/-- Prepending a retry width expresses success as a sampler-path-weighted sum of immediate
checked success and failure-weighted continuation success. -/
theorem hybridRetrySuccess_cons_paths (n cap m : ℕ) (ms : List ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetrySuccess n cap (m :: ms) A =
      codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
        (fun j => (∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) +
          (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) * hybridRetrySuccess n cap ms A) := by
  rw [hybridRetrySuccess,hybridRetry,HybridProgram.eval_ofCoins]
  unfold codeSuccess
  conv_lhs => rw [← List.ofFn_get (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths]
  rw [List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [Function.comp_apply]
  generalize (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.get c = z
  cases hz : z.1.1 with
  | inr cfg => simp only [HybridProgram.eval,foundUtility,mul_zero]
  | inl cfg =>
      rw [HybridProgram.eval_bind]
      have hc : (fun x : Fin (2 ^ n) × Bool => fun φ =>
          HybridProgram.eval (retryOracle A)
            (if x.2 then HybridProgram.ret ⟨RetryStatus.found x.1,[depthDraw z.1]⟩ else
              HybridProgram.prependCircuit
                (basisResetCircuit n (indexBitEquiv (2 ^ n) (x.1,false)))
                ((hybridRetry n cap ms).bind (fun r =>
                  HybridProgram.ret {r with draws := depthDraw z.1 :: r.draws}))) φ
            (fun r χ => branchMass χ * foundUtility r)) =
          (fun x φ => if x.2 then branchMass φ else (hybridRetry n cap ms).eval (retryOracle A)
            (Run (retryOracle A) (basisResetCircuit n (indexBitEquiv (2 ^ n) (x.1,false))) φ)
            (fun r χ => branchMass χ * foundUtility r)) := by
        funext x φ
        cases x.2 <;> simp only [Bool.false_eq_true,↓reduceIte,HybridProgram.eval_prepend,
          HybridProgram.eval_bind,HybridProgram.eval,foundUtility,mul_one]
      rw [hc,hybridPreparedAttempt_reset_cont]
      rfl

/-- For a positive first width, retry success is sampler-return mass times the sum of checked
success and checked failure times the remaining schedule's success. -/
theorem hybridRetrySuccess_cons (n cap : ℕ) {m : ℕ} (hm : 0 < m)
    (ms : List ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetrySuccess n cap (m :: ms) A =
      (1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) *
        (CheckedSuccess A m + (1 - CheckedSuccess A m) * hybridRetrySuccess n cap ms A) := by
  rw [hybridRetrySuccess_cons_paths,uniformDepth_success hm]
  unfold CheckedSuccess
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [sub_mul,one_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
/-- The quantum instrument of the legal hybrid retry program under its unitary membership
oracle. -/
noncomputable def hybridRetryInstrument (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) :=
  (hybridRetry n cap sizes).instrument (retryOracle A) (retryOracle_unitary A)
    (hybridRetry_legal n cap sizes)

/-- Summing the instrument probabilities weighted by the found-status indicator gives
`hybridRetrySuccess`. -/
theorem hybridRetryInstrument_success (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (hybridRetryInstrument n cap sizes A) (preparedInput n) z *
      foundUtility ((hybridRetry n cap sizes).leaf (retryOracle A) z).value) =
      hybridRetrySuccess n cap sizes A :=
  HybridProgram.eval_instrument _ (retryOracle_unitary A) _ (hybridRetry_legal n cap sizes) _ _

/-- A zero sampler cap gives zero hybrid retry success for any schedule. -/
theorem hybridRetrySuccess_cap_zero (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetrySuccess n 0 sizes A = 0 := by
  cases sizes with
  | nil => exact hybridRetrySuccess_nil n 0 A
  | cons m ms => simp [hybridRetrySuccess,hybridRetry,weightedSampler,countedLoop,
      HybridProgram.ofCoins,HybridProgram.eval,foundUtility]

/-- For positive divisor `b`, the ceiling-division bound `ceilDivNat a b ≤ k` is equivalent to
`a ≤ k * b`. -/
theorem ceilDivNat_le {a b k : ℕ} (hb : 0 < b) : ceilDivNat a b ≤ k ↔ a ≤ k * b := by
  cases a with
  | zero => simp [ceilDivNat]
  | succ a => simp only [ceilDivNat,Nat.add_one_ne_zero,↓reduceIte,Nat.add_sub_cancel,
      Nat.add_one_le_iff,Nat.div_lt_iff_lt_mul hb]

/-- The bound `ceilSqrtNat N ≤ k` is equivalent to `N ≤ k ^ 2`. -/
theorem ceilSqrtNat_le (N k : ℕ) : ceilSqrtNat N ≤ k ↔ N ≤ k ^ 2 := by
  cases N with
  | zero => simp [ceilSqrtNat]
  | succ N => simp only [ceilSqrtNat,Nat.add_one_ne_zero,↓reduceIte,Nat.add_sub_cancel,
      Nat.add_one_le_iff,Nat.sqrt_lt']

/-- For a positive divisor, `ceilDivNat` equals the natural ceiling of the corresponding real
quotient. -/
theorem ceilDivNat_eq {a b : ℕ} (hb : 0 < b) : ceilDivNat a b = Nat.ceil ((a : ℝ) / b) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [ceilDivNat_le hb,Nat.ceil_le,div_le_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)]
  exact_mod_cast Iff.rfl

/-- The computable integer square-root ceiling equals the natural ceiling of the real square
root. -/
theorem ceilSqrtNat_eq (N : ℕ) : ceilSqrtNat N = Nat.ceil (Real.sqrt N) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [ceilSqrtNat_le,Nat.ceil_le,Real.sqrt_le_iff]
  simp only [Nat.cast_nonneg,true_and]
  exact_mod_cast Iff.rfl

/-- For a positive table size, the effective integer BBHT width agrees with `ExponentialSizes`. -/
theorem effectiveBBHTSize_eq {N : ℕ} (hN : 0 < N) (k : ℕ) :
    effectiveBBHTSize N k = ExponentialSizes N k := by
  have hmin (r s : ℝ) : Nat.ceil (min r s) = min (Nat.ceil r) (Nat.ceil s) := by
    by_cases h : r ≤ s
    · rw [min_eq_left h,min_eq_left (Nat.ceil_mono h)]
    · rw [min_eq_right (le_of_not_ge h),min_eq_right (Nat.ceil_mono (le_of_not_ge h))]
  rw [effectiveBBHTSize,if_neg hN.ne',ExponentialSizes,(search_exponential_schedule N hN).1 k,
    hmin,ceilDivNat_eq (Nat.pow_pos (by decide : 0 < 5)),ceilSqrtNat_eq]
  norm_num only [Nat.cast_pow,Nat.cast_ofNat]
  rw [div_pow]

/-- The exponential width for a zero-sized table vanishes at every positive stage. -/
theorem exponentialWidth_zero (k : ℕ) : ExponentialWidth 0 (k + 1) = 0 := by
  induction k with
  | zero => norm_num [ExponentialWidth]
  | succ k ih => rw [ExponentialWidth,ih]; norm_num

/-- The effective integer BBHT schedule agrees with `ExponentialSizes` at every table size and
stage. -/
theorem effectiveBBHTSize_eq_all (N k : ℕ) : effectiveBBHTSize N k = ExponentialSizes N k := by
  cases N with
  | zero => cases k with
      | zero => norm_num [effectiveBBHTSize,ExponentialSizes,ExponentialWidth]
      | succ k => simp [effectiveBBHTSize,ExponentialSizes,exponentialWidth_zero]
  | succ N => exact effectiveBBHTSize_eq (Nat.succ_pos N) k

/-- A prefix of the effective BBHT schedule has length equal to its requested number of rounds. -/
theorem effectiveBBHTPrefix_length (N start rounds : ℕ) :
    (effectiveBBHTPrefix N start rounds).length = rounds := by
  induction rounds generalizing start with
  | zero => rfl
  | succ r ih => simp only [effectiveBBHTPrefix,List.length_cons,ih]

/-- The effective BBHT prefix is the list of `ExponentialSizes` values at the consecutive stages
starting at `start`. -/
theorem effectiveBBHTPrefix_source (N start rounds : ℕ) :
    effectiveBBHTPrefix N start rounds =
      List.ofFn (fun k : Fin rounds => ExponentialSizes N (start + k.val)) := by
  induction rounds generalizing start with
  | zero => rfl
  | succ r ih =>
      rw [effectiveBBHTPrefix,List.ofFn_succ,effectiveBBHTSize_eq_all,ih]
      simp only [Fin.val_zero,Nat.add_zero,List.cons.injEq,true_and]
      apply congrArg List.ofFn
      funext i
      congr 1
      simp only [Fin.val_succ]
      omega

/-- A prefix with `r + s` rounds splits into its first `r` rounds and the next `s` rounds
starting at `start + r`. -/
theorem effectiveBBHTPrefix_append (N start r s : ℕ) :
    effectiveBBHTPrefix N start (r + s) =
      effectiveBBHTPrefix N start r ++ effectiveBBHTPrefix N (start + r) s := by
  induction r generalizing start with
  | zero => simp [effectiveBBHTPrefix]
  | succ r ih =>
      simp only [Nat.succ_add,effectiveBBHTPrefix,List.cons_append,ih]
      congr 2

/-- Every effective BBHT width is positive when the table size is positive. -/
theorem effectiveBBHTSize_pos {N : ℕ} (hN : 0 < N) (k : ℕ) : 0 < effectiveBBHTSize N k := by
  rw [effectiveBBHTSize_eq hN]
  exact (search_exponential_schedule N hN).2.1 k

/-- Every finite growing-schedule hybrid retry program is legal. -/
theorem growingRetry_legal (n cap start rounds : ℕ) : (growingRetry n cap start rounds).Legal :=
  hybridRetry_legal _ _ _

/-- The growing retry program equals hybrid retry on the corresponding consecutive
`ExponentialSizes` widths. -/
theorem growingRetry_source (n cap start rounds : ℕ) :
    growingRetry n cap start rounds = hybridRetry n cap
      (List.ofFn (fun k : Fin rounds => ExponentialSizes (2 ^ n) (start + k.val))) := by
  rw [growingRetry,effectiveBBHTPrefix_source]
/-- The quantum instrument of the growing-schedule retry program under its unitary membership
oracle. -/
noncomputable def growingRetryInstrument (n cap start rounds : ℕ) (A : Finset (Fin (2 ^ n))) :=
  (growingRetry n cap start rounds).instrument (retryOracle A) (retryOracle_unitary A)
    (growingRetry_legal n cap start rounds)

/-- The found-status probability computed from the growing retry instrument equals
`growingRetrySuccess`. -/
theorem growingRetryInstrument_success (n cap start rounds : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (growingRetryInstrument n cap start rounds A) (preparedInput n) z *
      foundUtility ((growingRetry n cap start rounds).leaf (retryOracle A) z).value) =
      growingRetrySuccess n cap start rounds A :=
  hybridRetryInstrument_success n cap _ A

/-- Success for one additional growing-schedule round equals the current sampler-return mass
times immediate checked success plus checked failure times success from the next stage. -/
theorem growingRetrySuccess_succ (n cap start rounds : ℕ) (A : Finset (Fin (2 ^ n))) :
    growingRetrySuccess n cap start (rounds + 1) A =
      (1 - (rationalRejectMass (fun _ : Fin (ExponentialSizes (2 ^ n) start) => 1)
        (Nat.clog 2 (ExponentialSizes (2 ^ n) start)) ^ cap).toReal) *
      (CheckedSuccess A (ExponentialSizes (2 ^ n) start) +
        (1 - CheckedSuccess A (ExponentialSizes (2 ^ n) start)) *
          growingRetrySuccess n cap (start + 1) rounds A) := by
  rw [growingRetrySuccess,effectiveBBHTPrefix,
    hybridRetrySuccess_cons n cap (effectiveBBHTSize_pos (Nat.two_pow_pos n) start)]
  rw [effectiveBBHTSize_eq_all]
  rfl

/-- Every leaf of hybrid checked readout uses exactly one oracle query. -/
theorem hybridCheckedReadout_queries (N : ℕ) (O : Operator (N * 2))
    (t : HybridLeaf (N * 2) (Fin N × Bool)) (ht : t ∈ (hybridCheckedReadout N).leaves O) :
    t.queries = 1 := by
  obtain ⟨ls,hls,ht⟩ := List.mem_flatten.mp ht
  obtain ⟨x,rfl⟩ := List.mem_ofFn.mp hls
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  obtain ⟨ls,hls,hw⟩ := List.mem_flatten.mp hw
  obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hls
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
  simp only [HybridProgram.leaves,List.mem_singleton] at hz
  subst z
  rfl

/-- Every leaf of a depth-`j` prepared hybrid attempt uses exactly `j + 1` oracle queries. -/
theorem hybridPreparedAttempt_queries (n j : ℕ) (O : Operator (2 ^ n * 2))
    (t : HybridLeaf (2 ^ n * 2) (Fin (2 ^ n) × Bool))
    (ht : t ∈ (hybridPreparedAttempt n j).leaves O) : t.queries = j + 1 := by
  obtain ⟨u,hu,hp⟩ := HybridProgram.prependCircuit_queries O (prepPowCircuit n)
    (hybridCheckedAttempt (2 ^ n) j) t ht
  obtain ⟨v,hv,hs⟩ := HybridProgram.prependCircuit_queries O
    (encodeCircuit (LiftCircuit (SearchCircuit (Fin (2 ^ n)) j))) (hybridCheckedReadout (2 ^ n)) u hu
  rw [hp,hs,hybridCheckedReadout_queries _ O v hv,(prepPowCircuit_counts n).1]
  rw [(encodeCircuit_counts _).1]
  have hc := (search_checked_attempt (by simp)
    (∅ : Finset (Fin (2 ^ n))) j).1
  change QueryCount (LiftCircuit (SearchCircuit (Fin (2 ^ n)) j)) + 1 = j + 1 at hc
  omega

/-- Every leaf of a hybrid retry program uses at most the sum of the supplied search widths in
oracle queries. -/
theorem hybridRetry_queries_le (n cap : ℕ) (sizes : List ℕ) (O : Operator (2 ^ n * 2))
    (t : HybridLeaf (2 ^ n * 2) (RetryReport (2 ^ n)))
    (ht : t ∈ (hybridRetry n cap sizes).leaves O) : t.queries ≤ sizes.sum := by
  induction sizes generalizing t with
  | nil => simp only [hybridRetry,HybridProgram.leaves,List.mem_singleton] at ht; subst t; rfl
  | cons m ms ih =>
      apply HybridProgram.ofCoins_queries_le O _ _ (m + ms.sum) ?_ t ht
      intro a v hv
      cases ha : a.1 with
      | inr cfg =>
          simp only [ha] at hv
          simp only [HybridProgram.leaves,List.mem_singleton] at hv
          subst v
          exact Nat.zero_le _
      | inl cfg =>
          rcases cfg with ⟨j,b,c⟩
          simp only [ha] at hv
          apply HybridProgram.bind_queries_le O
              (hybridPreparedAttempt n j.val) _ m ms.sum ?_ ?_ v hv
          · intro u hu
            rw [hybridPreparedAttempt_queries _ _ O u hu]
            exact j.isLt
          · intro z w hw
            split_ifs at hw
            · simp only [HybridProgram.leaves,List.mem_singleton] at hw
              subst w
              exact Nat.zero_le _
            · obtain ⟨u,hu,hq⟩ := HybridProgram.prependCircuit_queries O
                (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))) _ w hw
              rw [hq,(basisResetCircuit_counts n _).1,Nat.add_zero]
              apply HybridProgram.bind_queries_le O (hybridRetry n cap ms) _ ms.sum 0 ?_ ?_ u hu
              · exact fun u hu => ih u hu
              · intro r s hs
                simp only [HybridProgram.leaves,List.mem_singleton] at hs
                subst s
                rfl

/-- For a positive table size, each effective BBHT width is at most the integer square-root
ceiling. -/
theorem effectiveBBHTSize_le_cap {N : ℕ} (hN : 0 < N) (k : ℕ) :
    effectiveBBHTSize N k ≤ ceilSqrtNat N := by
  rw [effectiveBBHTSize,if_neg hN.ne']
  exact min_le_right _ _

/-- For a positive table size, the sum of a schedule prefix is at most its round count times the
integer square-root ceiling. -/
theorem effectiveBBHTPrefix_sum_le {N : ℕ} (hN : 0 < N) (start rounds : ℕ) :
    (effectiveBBHTPrefix N start rounds).sum ≤ rounds * ceilSqrtNat N := by
  induction rounds generalizing start with
  | zero => simp [effectiveBBHTPrefix]
  | succ r ih =>
      simp only [effectiveBBHTPrefix,List.sum_cons,Nat.succ_mul]
      exact Nat.add_le_add (effectiveBBHTSize_le_cap hN start) (ih (start + 1)) |>.trans_eq
        (Nat.add_comm _ _)

/-- Every growing-retry leaf uses at most the sum of its effective BBHT schedule widths in
oracle queries. -/
theorem growingRetry_queries_le (n cap start rounds : ℕ) (O : Operator (2 ^ n * 2))
    (t : HybridLeaf (2 ^ n * 2) (RetryReport (2 ^ n)))
    (ht : t ∈ (growingRetry n cap start rounds).leaves O) :
    t.queries ≤ (effectiveBBHTPrefix (2 ^ n) start rounds).sum :=
  hybridRetry_queries_le n cap _ O t ht

/-- The query count of any indexed growing-retry leaf is bounded by the sum of its effective
BBHT prefix. -/
theorem growingRetry_leaf_queries_le (n cap start rounds : ℕ) (O : Operator (2 ^ n * 2))
    (z : Fin (growingRetry n cap start rounds).leafCount) :
    ((growingRetry n cap start rounds).leaf O z).queries ≤
      (effectiveBBHTPrefix (2 ^ n) start rounds).sum := by
  apply growingRetry_queries_le
  rw [← (growingRetry n cap start rounds).leaf_ofFn O]
  exact List.mem_ofFn.mpr ⟨z,rfl⟩

/-- Every indexed growing-retry leaf uses at most `rounds * ceilSqrtNat (2 ^ n)` queries. -/
theorem growingRetry_leaf_queries_cap (n cap start rounds : ℕ) (O : Operator (2 ^ n * 2))
    (z : Fin (growingRetry n cap start rounds).leafCount) :
    ((growingRetry n cap start rounds).leaf O z).queries ≤ rounds * ceilSqrtNat (2 ^ n) :=
  (growingRetry_leaf_queries_le n cap start rounds O z).trans
    (effectiveBBHTPrefix_sum_le (Nat.two_pow_pos n) start rounds)

/-- The expected query count of the growing retry instrument is bounded by the sum of its
effective BBHT prefix. -/
theorem growingRetry_expected_queries_le (n cap start rounds : ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (growingRetryInstrument n cap start rounds A) (preparedInput n) z *
      (((growingRetry n cap start rounds).leaf (retryOracle A) z).queries : ℝ)) ≤
      (effectiveBBHTPrefix (2 ^ n) start rounds).sum := by
  calc
    _ ≤ ∑ z, instrumentProb (growingRetryInstrument n cap start rounds A) (preparedInput n) z *
        ((effectiveBBHTPrefix (2 ^ n) start rounds).sum : ℝ) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast growingRetry_leaf_queries_le n cap start rounds (retryOracle A) z
      · exact instrumentProb_nonneg _ (preparedInput_density n).1 z
    _ = _ := by
      rw [← Finset.sum_mul,sum_instrumentProb_isDensityOperator _ (preparedInput_density n),one_mul]

/-- Every hybrid checked-readout leaf has one query, one gate, two measurements, and zero
random-bit reads. -/
theorem hybridCheckedReadout_counts (N : ℕ) (O : Operator (N * 2))
    (t : HybridLeaf (N * 2) (Fin N × Bool)) (ht : t ∈ (hybridCheckedReadout N).leaves O) :
    t.counts = ⟨1,1,2,0⟩ := by
  obtain ⟨ls,hls,ht⟩ := List.mem_flatten.mp ht
  obtain ⟨x,rfl⟩ := List.mem_ofFn.mp hls
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  obtain ⟨ls,hls,hw⟩ := List.mem_flatten.mp hw
  obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hls
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
  simp only [HybridProgram.leaves,List.mem_singleton] at hz
  subst z
  rfl

/-- Every depth-`j` prepared hybrid attempt leaf has `j + 1` queries, `j + 1 + (n + 2)` gates,
two measurements, and zero random-bit reads. -/
theorem hybridPreparedAttempt_counts (n j : ℕ) (O : Operator (2 ^ n * 2))
    (t : HybridLeaf (2 ^ n * 2) (Fin (2 ^ n) × Bool))
    (ht : t ∈ (hybridPreparedAttempt n j).leaves O) : t.counts = ⟨j+1,j+1+(n+2),2,0⟩ := by
  obtain ⟨u,hu,hp⟩ := HybridProgram.prependCircuit_counts O (prepPowCircuit n)
    (hybridCheckedAttempt (2 ^ n) j) t ht
  obtain ⟨v,hv,hs⟩ := HybridProgram.prependCircuit_counts O
    (encodeCircuit (LiftCircuit (SearchCircuit (Fin (2 ^ n)) j))) (hybridCheckedReadout (2 ^ n)) u hu
  rw [hp,hs,hybridCheckedReadout_counts _ O v hv,(prepPowCircuit_counts n).1,
    (prepPowCircuit_counts n).2,(encodeCircuit_counts _).1,(encodeCircuit_counts _).2,
    queryCount_liftCircuit,gateCount_liftCircuit,Qatlib.Concepts.SearchStopping.KnownCount.queryCount_groverCircuit]
  simp [HybridCounts.plus,SearchCircuit,Qatlib.Concepts.SearchStopping.KnownCount.GroverCircuit,gateCount_repeatCircuit,
    Qatlib.Concepts.SearchStopping.KnownCount.GroverStep,GateCount,Nat.add_comm]

/-- Counted evaluation of a prepared attempt adds its fixed query, gate, and measurement counts
to the initial counters before evaluating the terminal payoff. -/
theorem hybridPreparedAttempt_evalCounts (n j : ℕ) (O : Operator (2 ^ n * 2))
    (ψ : QState (Fin (2 ^ n * 2))) (c : HybridCounts)
    (F : (Fin (2 ^ n) × Bool) → QState (Fin (2 ^ n * 2)) → HybridCounts → ℝ) :
    (hybridPreparedAttempt n j).evalCounts O ψ c F =
      (hybridPreparedAttempt n j).eval O ψ (fun a φ => F a φ (c.plus ⟨j+1,j+1+(n+2),2,0⟩)) :=
  HybridProgram.evalCounts_fixed O _ ψ c _ (hybridPreparedAttempt_counts n j O) F

/-- For a payoff homogeneous of degree two under complex scaling, a failed readout branch
followed by reset contributes its branch mass times the payoff at the zero preparation ket. -/
theorem hybridReadout_reset_homogeneous (n : ℕ) (A : Finset (Fin (2 ^ n)))
    (E : Fin (2 ^ n) → QState (Fin (2 ^ n * 2)) → ℝ)
    (hE : ∀ i (z : ℂ) φ, E i (z • φ) = ‖z‖ ^ 2 * E i φ) (ψ : QState (Fin (2 ^ n * 2))) :
    (hybridCheckedReadout (2 ^ n)).eval (retryOracle A) ψ
      (fun z φ => if z.2 then 0 else
        E z.1
          (Run (retryOracle A) (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))) φ)) =
    (hybridCheckedReadout (2 ^ n)).eval (retryOracle A) ψ
      (fun z φ => branchMass φ * (if z.2 then 0 else E z.1 (Ket (prepZero n)))) := by
  simp only [hybridCheckedReadout,HybridProgram.eval,retryOracle,id_eq,
    query_reset_collapsed,collapse_encoded_bit]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro b _
  fin_cases b
  · norm_num
    cases hf : decide (((indexBitEquiv (2 ^ n)).symm x).1 ∈ A)
    · norm_num [boolEquivFin2]
      rw [circuit_run_smul,basisResetCircuit_run,hE]
      rw [branchMass,measureProb_smul,measureProb_univ (normalized_ket _),mul_one]
    · norm_num [boolEquivFin2]
      have hz : Run (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
          (basisResetCircuit n (indexBitEquiv (2 ^ n) (((indexBitEquiv (2 ^ n)).symm x).1,false))) 0 = 0 := by
        have h := circuit_run_smul (encodeGate (BitOracleOn (fun i => decide (i ∈ A))))
          (basisResetCircuit n (indexBitEquiv (2 ^ n) (((indexBitEquiv (2 ^ n)).symm x).1,false))) 0
            (Ket (prepZero n))
        simpa using! h
      rw [hz]
      have he := hE (((indexBitEquiv (2 ^ n)).symm x).1) 0 (Ket (prepZero n))
      simpa [branchMass,MeasureProb,BornProb] using! he
  · norm_num

/-- A basis-reset circuit preserves branch mass for every input state. -/
theorem basisReset_mass (n : ℕ) (A : Finset (Fin (2 ^ n))) (i : Fin (2 ^ n))
    (ψ : QState (Fin (2 ^ n * 2))) :
    branchMass (Run (retryOracle A) (basisResetCircuit n (indexBitEquiv (2 ^ n) (i,false))) ψ) =
      branchMass ψ := by
  have h := HybridProgram.eval_mass (retryOracle A) (retryOracle_unitary A)
    (HybridProgram.prependCircuit (basisResetCircuit n (indexBitEquiv (2 ^ n) (i,false)))
      (.ret ())) (HybridProgram.prependCircuit_legal _ (basisResetCircuit_legal n _) _ trivial) ψ
  simpa only [HybridProgram.eval_prepend,HybridProgram.eval] using! h

/-- A prepared attempt with constant success payoff `a` and failure payoff `b` evaluates to `a`
times checked success mass plus `b` times checked failure mass. -/
theorem hybridPreparedAttempt_value_cont (n j : ℕ) (A : Finset (Fin (2 ^ n))) (a b : ℝ) :
    (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
      (fun z φ => branchMass φ * (if z.2 then a else b)) =
      a * (∑ i : Fin (2 ^ n), CheckedOutputMass A j i) +
        b * (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j i) := by
  have hpay : (fun z : Fin (2 ^ n) × Bool => fun φ : QState (Fin (2 ^ n * 2)) =>
      branchMass φ * (if z.2 then a else b)) =
      (fun z φ => b * branchMass φ + (a-b) * (branchMass φ * (if z.2 then 1 else 0))) := by
    funext z φ
    cases z.2 <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring
  rw [hpay,HybridProgram.eval_add,HybridProgram.eval_mul,HybridProgram.eval_mul,
    HybridProgram.eval_mass _ (retryOracle_unitary A) _ (hybridPreparedAttempt_legal n j),
    show branchMass (Ket (prepZero n)) = 1 from measureProb_univ (normalized_ket _),
    hybridPreparedAttempt_success_eval]
  ring

/-- For a payoff homogeneous of degree two under complex scaling, the reset-on-failure
contribution of a prepared attempt is its failure mass times the payoff at the zero
preparation ket. -/
theorem hybridPreparedAttempt_reset_homogeneous (n j : ℕ) (A : Finset (Fin (2 ^ n)))
    (E : QState (Fin (2 ^ n * 2)) → ℝ)
    (hE : ∀ (z : ℂ) φ, E (z • φ) = ‖z‖ ^ 2 * E φ) :
    (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
      (fun z φ => if z.2 then 0 else E
        (Run (retryOracle A) (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))) φ)) =
      (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j i) * E (Ket (prepZero n)) := by
  calc
    _ = (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
        (fun z φ => branchMass φ * (if z.2 then 0 else E (Ket (prepZero n)))) := by
      simp only [hybridPreparedAttempt,hybridCheckedAttempt,HybridProgram.eval_prepend]
      exact hybridReadout_reset_homogeneous n A (fun _ => E) (fun _ => hE) _
    _ = _ := by rw [hybridPreparedAttempt_value_cont]; ring

/-- For a legal continuation and an additive counter statistic, a prepared attempt's counted
evaluation splits into the initial statistic, fixed attempt statistic, reset moment, and
failure-weighted continuation moment. -/
theorem hybridPreparedAttempt_statistic_cont {B : Type} (n j : ℕ) (A : Finset (Fin (2 ^ n)))
    (p : HybridProgram (2 ^ n * 2) B) (hp : p.Legal) (c : HybridCounts)
    (f : HybridCounts → ℝ) (hf : ∀ a b, f (a.plus b) = f a + f b) :
    (hybridPreparedAttempt n j).evalCounts (retryOracle A) (Ket (prepZero n)) c
      (fun z φ d => if z.2 then branchMass φ * f d else
        (HybridProgram.prependCircuit (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))) p).evalCounts
          (retryOracle A) φ d (fun _ χ e => branchMass χ * f e)) =
    f c + f ⟨j+1,j+1+(n+2),2,0⟩ + hybridResetMoment n j A f +
      (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j i) *
        p.evalCounts (retryOracle A) (Ket (prepZero n)) HybridCounts.zero (fun _ φ d => branchMass φ * f d) := by
  rw [hybridPreparedAttempt_evalCounts]
  have hpay : (fun z : Fin (2 ^ n) × Bool => fun φ : QState (Fin (2 ^ n * 2)) =>
      if z.2 then branchMass φ * f (c.plus ⟨j+1,j+1+(n+2),2,0⟩) else
        (HybridProgram.prependCircuit (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))) p).evalCounts
          (retryOracle A) φ (c.plus ⟨j+1,j+1+(n+2),2,0⟩) (fun _ χ e => branchMass χ * f e)) =
    (fun z φ => branchMass φ * (f c + f ⟨j+1,j+1+(n+2),2,0⟩) +
      branchMass φ * (if z.2 then 0 else f ⟨0,GateCount (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))),0,0⟩) +
      (if z.2 then 0 else p.evalCounts (retryOracle A)
        (Run (retryOracle A) (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))) φ)
        HybridCounts.zero (fun _ χ e => branchMass χ * f e))) := by
    funext z φ
    cases z.2 with
    | false =>
        simp only [Bool.false_eq_true,↓reduceIte,HybridProgram.evalCounts_prepend,(basisResetCircuit_counts n _).1]
        rw [HybridProgram.evalCounts_statistic_start _ (retryOracle_unitary A) p hp _ _ f hf,
          basisReset_mass]
        simp only [hf]
        ring
    | true => simp only [↓reduceIte,hf]; ring
  rw [hpay,HybridProgram.eval_add,HybridProgram.eval_add]
  have hconst : (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
      (fun _ φ => branchMass φ * (f c + f ⟨j+1,j+1+(n+2),2,0⟩)) = f c + f ⟨j+1,j+1+(n+2),2,0⟩ := by
    have h :=
        HybridProgram.eval_mass _ (retryOracle_unitary A) _ (hybridPreparedAttempt_legal n j)
        (Ket (prepZero n))
    simp_rw [mul_comm (branchMass _)]
    rw [HybridProgram.eval_mul,h,show branchMass (Ket (prepZero n)) = 1 from measureProb_univ (normalized_ket _),mul_one]
  rw [hconst,hybridPreparedAttempt_reset_homogeneous n j A
    (fun φ => p.evalCounts (retryOracle A) φ HybridCounts.zero (fun _ χ d => branchMass χ * f d))
    (fun z φ => p.evalCounts_mass_smul (retryOracle A) φ HybridCounts.zero (fun _ d => f d) z)]
  rfl

/-- An empty retry schedule has zero counter moment whenever the statistic vanishes at zero
counters. -/
theorem hybridRetryMoment_nil (n cap : ℕ) (A : Finset (Fin (2 ^ n)))
    (f : HybridCounts → ℝ) (hf : f HybridCounts.zero = 0) :
    hybridRetryMoment n cap [] A f = 0 := by
  simp only [hybridRetryMoment,hybridRetry,HybridProgram.evalCounts,hf,mul_zero]

/-- For an additive counter statistic, the retry moment expands over sampler paths into
random-bit costs, successful-depth attempt costs, reset moments, and failure-weighted
continuation moments. -/
theorem hybridRetryMoment_cons_paths (n cap m : ℕ) (ms : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : HybridCounts → ℝ) (hf : ∀ a b, f (a.plus b) = f a + f b) :
    hybridRetryMoment n cap (m :: ms) A f =
    ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.map (fun z =>
      CoinCode.wordWeight z.2 * (f ⟨0,0,0,z.2.length⟩ + match z.1.1 with
        | .inr _ => 0
        | .inl (j,_,_) => f ⟨j.val+1,j.val+1+(n+2),2,0⟩ + hybridResetMoment n j.val A f +
            (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) * hybridRetryMoment n cap ms A f))).sum := by
  rw [hybridRetryMoment,hybridRetry,HybridProgram.evalCounts_ofCoins]
  apply congrArg List.sum
  apply List.map_congr_left
  intro z _
  congr 1
  rw [HybridCounts.zero_plus]
  cases hz : z.1.1 with
  | inr cfg =>
      simp only [HybridProgram.evalCounts,show branchMass (Ket (prepZero n)) = 1 from
        measureProb_univ (normalized_ket _),one_mul,add_zero]
  | inl cfg =>
      rw [HybridProgram.evalCounts_bind]
      have hc : (fun x : Fin (2 ^ n) × Bool => fun φ d =>
          HybridProgram.evalCounts (retryOracle A)
            (if x.2 then HybridProgram.ret ⟨RetryStatus.found x.1,[depthDraw z.1]⟩ else
              HybridProgram.prependCircuit
                (basisResetCircuit n (indexBitEquiv (2 ^ n) (x.1,false)))
                ((hybridRetry n cap ms).bind (fun r =>
                  HybridProgram.ret {r with draws := depthDraw z.1 :: r.draws}))) φ d
            (fun _ χ e => branchMass χ * f e)) =
          (fun x φ d => if x.2 then branchMass φ * f d else
            (HybridProgram.prependCircuit (basisResetCircuit n (indexBitEquiv (2 ^ n) (x.1,false)))
              (hybridRetry n cap ms)).evalCounts (retryOracle A) φ d (fun _ χ e => branchMass χ * f e)) := by
        funext x φ d
        cases x.2 <;> simp only [Bool.false_eq_true,↓reduceIte,HybridProgram.evalCounts_prepend,
          HybridProgram.evalCounts_bind,HybridProgram.evalCounts]
      rw [hc,hybridPreparedAttempt_statistic_cont n cfg.1.val A _ (hybridRetry_legal n cap ms) _ f hf]
      dsimp only [hybridRetryMoment]
      ring

/-- The instrument-weighted mean of a retry leaf's counter statistic equals `hybridRetryMoment`. -/
theorem hybridRetryInstrument_moment (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : HybridCounts → ℝ) :
    (∑ z, instrumentProb (hybridRetryInstrument n cap sizes A) (preparedInput n) z *
      f ((hybridRetry n cap sizes).leaf (retryOracle A) z).counts) = hybridRetryMoment n cap sizes A f :=
  HybridProgram.evalCounts_instrument _ (retryOracle_unitary A) _ (hybridRetry_legal n cap sizes) _ (fun _ => f)

/-- A checked-readout payoff depending only on the returned index and Boolean is the
Born-weighted sum over full-basis outcomes, with the Boolean fixed by the oracle. -/
theorem hybridCheckedReadout_value_eval {N : ℕ} (f : Fin N → Bool)
    (ψ : QState (Fin (N * 2))) (h : Fin N × Bool → ℝ) :
    (hybridCheckedReadout N).eval (encodeGate (BitOracleOn f)) ψ (fun z φ => branchMass φ * h z) =
      ∑ x : Fin (N * 2), BornProb ψ x * h (((indexBitEquiv N).symm x).1,f ((indexBitEquiv N).symm x).1) := by
  simp only [hybridCheckedReadout,HybridProgram.eval,id_eq,query_reset_collapsed,collapse_encoded_bit]
  apply Finset.sum_congr rfl
  intro x _
  have hm (z : ℂ) (y : Fin (N * 2)) : branchMass (z • Ket y) = ‖z‖ ^ 2 := by
    rw [branchMass,measureProb_smul,measureProb_univ (normalized_ket _),mul_one]
  have hz : branchMass (0 : QState (Fin (N * 2))) = 0 := by simp [branchMass,MeasureProb,BornProb]
  cases hf : f ((indexBitEquiv N).symm x).1 <;>
    norm_num [Fin.sum_univ_two,boolEquivFin2,hm,hz,BornProb,show ((0 : Fin 2) == 1) = false from rfl]

/-- A prepared attempt's output payoff is the Born-weighted sum over search indices paired with
their marked-set membership bits. -/
theorem hybridPreparedAttempt_value_eval (n j : ℕ) (A : Finset (Fin (2 ^ n)))
    (h : Fin (2 ^ n) × Bool → ℝ) :
    (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n)) (fun z φ => branchMass φ * h z) =
      ∑ i : Fin (2 ^ n), BornProb (SearchState A j) i * h (i,decide (i ∈ A)) := by
  simp only [hybridPreparedAttempt,hybridCheckedAttempt,HybridProgram.eval_prepend]
  rw [prepZero,prepPowCircuit_run]
  simp only [retryOracle,encodeCircuit_run]
  change (hybridCheckedReadout (2 ^ n)).eval (retryOracle A)
      (encodeState (CheckedSearchState A j)) _ = _
  dsimp only [retryOracle]
  rw [hybridCheckedReadout_value_eval]
  rw [← (indexBitEquiv (2 ^ n)).sum_comp (fun x => BornProb (encodeState (CheckedSearchState A j)) x *
      h (((indexBitEquiv (2 ^ n)).symm x).1,decide (((indexBitEquiv (2 ^ n)).symm x).1 ∈ A))),
    Fintype.sum_prod_type]
  have hb (i : Fin (2 ^ n)) (a : Bool) :
      BornProb (encodeState (CheckedSearchState A j)) (indexBitEquiv (2 ^ n) (i,a)) =
        BornProb (CheckedSearchState A j) (i,a) := by simp [BornProb,encodeState]
  simp only [Equiv.symm_apply_apply,hb,← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hm := (search_bit_oracle_compile_phase (fun i => decide (i ∈ A))
    (SearchCircuit (Fin (2 ^ n)) j) (Uniform (Fin (2 ^ n)))).2.2 {i}
  simpa only [CheckedSearchState,SearchState,Qatlib.Concepts.SearchStopping.KnownCount.GroverState,SetOracle,
    MeasureProb,Finset.sum_product,Finset.sum_singleton] using! hm

/-- The reset moment is the Born-weighted sum of reset-counter payoffs over unmarked search
outputs. -/
theorem hybridResetMoment_value (n j : ℕ) (A : Finset (Fin (2 ^ n))) (f : HybridCounts → ℝ) :
    hybridResetMoment n j A f =
      ∑ i : Fin (2 ^ n), BornProb (SearchState A j) i *
        (if i ∈ A then 0 else f ⟨0,GateCount (basisResetCircuit n (indexBitEquiv (2 ^ n) (i,false))),0,0⟩) := by
  rw [hybridResetMoment,hybridPreparedAttempt_value_eval]
  simp only [decide_eq_true_eq]

/-- The growing retry instrument's counter-statistic mean equals the hybrid retry moment for its
effective BBHT prefix. -/
theorem growingRetryInstrument_moment (n cap start rounds : ℕ) (A : Finset (Fin (2 ^ n)))
    (f : HybridCounts → ℝ) :
    (∑ z, instrumentProb (growingRetryInstrument n cap start rounds A) (preparedInput n) z *
      f ((growingRetry n cap start rounds).leaf (retryOracle A) z).counts) =
      hybridRetryMoment n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A f :=
  HybridProgram.evalCounts_instrument _ (retryOracle_unitary A) _ (growingRetry_legal n cap start rounds) _ (fun _ => f)

/-- For an additive counter statistic, the first retry stage's moment separates into sampler
read cost and a successful-depth weighted sum of attempt, reset, and continuation costs. -/
theorem hybridRetryMoment_cons_split (n cap m : ℕ) (ms : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : HybridCounts → ℝ) (hf : ∀ a b, f (a.plus b) = f a + f b) :
    hybridRetryMoment n cap (m :: ms) A f =
      ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.map (fun z =>
        CoinCode.wordWeight z.2 * f ⟨0,0,0,z.2.length⟩)).sum +
      codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
        (fun j => f ⟨j.val+1,j.val+1+(n+2),2,0⟩ + hybridResetMoment n j.val A f +
          (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) * hybridRetryMoment n cap ms A f) := by
  rw [hybridRetryMoment_cons_paths n cap m ms A f hf]
  simp only [mul_add,List.sum_map_add]
  congr 1
  unfold codeSuccess
  conv_lhs => rw [← List.ofFn_get (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths]
  rw [List.map_ofFn,List.sum_ofFn]
  rfl

/-- Only the gate price contributes to the reset charge moment, which equals that price times
the reset-gate moment. -/
theorem hybridResetMoment_charge (n j : ℕ) (A : Finset (Fin (2 ^ n))) (q g m r : ℝ) :
    hybridResetMoment n j A (HybridCounts.charge q g m r) =
      g * hybridResetMoment n j A (HybridCounts.charge 0 1 0 0) := by
  simp only [hybridResetMoment_value,HybridCounts.charge,zero_mul,zero_add,add_zero,one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- The expected reset-gate count after a depth-`j` attempt is at most `n + 1` times its checked
failure mass. -/
theorem hybridResetMoment_gate_bound (n j : ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridResetMoment n j A (HybridCounts.charge 0 1 0 0) ≤
      (n+1 : ℝ) * (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j i) := by
  unfold hybridResetMoment
  calc
    _ ≤ (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
        (fun z φ => branchMass φ * (if z.2 then 0 else (n+1 : ℝ))) := by
      apply HybridProgram.eval_mono
      intro z φ
      cases z.2 with
      | false =>
          simp only [Bool.false_eq_true,↓reduceIte,HybridCounts.charge,zero_mul,zero_add,add_zero,one_mul]
          apply mul_le_mul_of_nonneg_left _ (measureProb_nonneg φ _)
          exact_mod_cast (basisResetCircuit_counts n (indexBitEquiv (2 ^ n) (z.1,false))).2.2
      | true => simp
    _ = _ := by rw [hybridPreparedAttempt_value_cont]; ring

/-- For positive width, the weighted depth sampler's mean read count equals `depthReadMean`. -/
theorem depthReadMean_eq {m : ℕ} (hm : 0 < m) (cap : ℕ) :
    (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).readMean = depthReadMean m cap :=
  CoinCode.weightedSampler_readMean _ _ _ (by simpa [weightTotal] using! hm)
    (by simpa [weightTotal] using! Nat.le_pow_clog (by norm_num : 1 < 2) m)

/-- Checked-search success is the average, over depths in `Fin m`, of the summed checked output
masses. -/
theorem checkedSuccess_fin {N : ℕ} (A : Finset (Fin N)) (m : ℕ) :
    CheckedSuccess A m = (∑ j : Fin m, ∑ i : Fin N, CheckedOutputMass A j.val i) / m := by
  unfold CheckedSuccess
  rw [← Fin.sum_univ_eq_sum_range]

/-- The sum of the real numbers `j + 1` for `j : Fin m` equals `m * (m + 1) / 2`. -/
theorem depth_sum_succ (m : ℕ) : (∑ j : Fin m, ((j.val : ℝ) + 1)) = (m : ℝ)*(m+1)/2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j : ℝ) + 1) m]
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih,Nat.cast_add,Nat.cast_one]; ring

/-- For positive depth width, the average reset-gate cost is at most `n + 1` times the
checked-search failure probability. -/
theorem meanResetGates_bound (n : ℕ) {m : ℕ} (hm : 0 < m) (A : Finset (Fin (2 ^ n))) :
    meanResetGates n m A ≤ (n+1 : ℝ) * (1 - CheckedSuccess A m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [meanResetGates,div_le_iff₀ hmR]
  calc
    _ ≤ ∑ j : Fin m, (n+1 : ℝ) * (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) :=
      Finset.sum_le_sum (fun j _ => hybridResetMoment_gate_bound n j.val A)
    _ = _ := by
      rw [checkedSuccess_fin]
      simp only [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      field_simp

/-- For a positive first width, the charged retry moment equals random-bit read cost plus
sampler-return mass times attempt cost, reset cost, and failure-weighted continuation cost. -/
theorem hybridRetryMoment_charge_cons (n cap : ℕ) {m : ℕ} (hm : 0 < m)
    (ms : List ℕ) (A : Finset (Fin (2 ^ n))) (q g t r : ℝ) :
    hybridRetryMoment n cap (m :: ms) A (HybridCounts.charge q g t r) =
      r * depthReadMean m cap + depthReturnMass m cap *
        ((q+g) * ((m : ℝ)+1)/2 + g*(n+2) + 2*t + g*meanResetGates n m A +
          (1 - CheckedSuccess A m) * hybridRetryMoment n cap ms A (HybridCounts.charge q g t r)) := by
  rw [hybridRetryMoment_cons_split n cap m ms A _ (HybridCounts.charge_plus q g t r)]
  have hreads : ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.map
      (fun z => CoinCode.wordWeight z.2 * HybridCounts.charge q g t r ⟨0,0,0,z.2.length⟩)).sum =
      r * depthReadMean m cap := by
    rw [← depthReadMean_eq hm cap,CoinCode.readMean,← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro z _
    simp only [HybridCounts.charge,Nat.cast_zero,mul_zero,zero_add]
    ring
  rw [hreads,uniformDepth_success hm]
  have hF : (fun j : Fin m => HybridCounts.charge q g t r ⟨j.val+1,j.val+1+(n+2),2,0⟩ +
      hybridResetMoment n j.val A (HybridCounts.charge q g t r) +
      (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) *
        hybridRetryMoment n cap ms A (HybridCounts.charge q g t r)) =
    (fun j => (q+g)*((j.val : ℝ)+1) + (g*(n+2)+2*t) +
      g*hybridResetMoment n j.val A (HybridCounts.charge 0 1 0 0) +
      (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) *
        hybridRetryMoment n cap ms A (HybridCounts.charge q g t r)) := by
    funext j
    rw [hybridResetMoment_charge]
    simp only [HybridCounts.charge,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_zero,mul_zero,add_zero]
    ring
  rw [hF]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [depth_sum_succ,checkedSuccess_fin]
  unfold depthReturnMass meanResetGates
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

/-- An empty retry schedule is exhausted with probability one. -/
theorem hybridRetryExhaustion_nil (n cap : ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetryExhaustion n cap [] A = 1 := by
  simp only [hybridRetryExhaustion,hybridRetry,HybridProgram.eval,exhaustedUtility,mul_one]
  exact measureProb_univ (normalized_ket _)

/-- Exhaustion after a prepended width is the sampler-path-weighted sum of checked failure mass
times the remaining schedule's exhaustion probability. -/
theorem hybridRetryExhaustion_cons_paths (n cap m : ℕ) (ms : List ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetryExhaustion n cap (m :: ms) A =
      codeSuccess (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
        (fun j => (1 - ∑ i : Fin (2 ^ n), CheckedOutputMass A j.val i) * hybridRetryExhaustion n cap ms A) := by
  rw [hybridRetryExhaustion,hybridRetry,HybridProgram.eval_ofCoins]
  unfold codeSuccess
  conv_lhs => rw [← List.ofFn_get (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths]
  rw [List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [Function.comp_apply]
  generalize (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.get c = z
  cases hz : z.1.1 with
  | inr cfg => simp only [HybridProgram.eval,exhaustedUtility,mul_zero]
  | inl cfg =>
      rw [HybridProgram.eval_bind]
      have hc : (fun x : Fin (2 ^ n) × Bool => fun φ =>
          HybridProgram.eval (retryOracle A)
            (if x.2 then HybridProgram.ret ⟨RetryStatus.found x.1,[depthDraw z.1]⟩ else
              HybridProgram.prependCircuit
                (basisResetCircuit n (indexBitEquiv (2 ^ n) (x.1,false)))
                ((hybridRetry n cap ms).bind (fun r =>
                  HybridProgram.ret {r with draws := depthDraw z.1 :: r.draws}))) φ
            (fun r χ => branchMass χ * exhaustedUtility r)) =
          (fun x φ => if x.2 then 0 else (hybridRetry n cap ms).eval (retryOracle A)
            (Run (retryOracle A) (basisResetCircuit n (indexBitEquiv (2 ^ n) (x.1,false))) φ)
            (fun r χ => branchMass χ * exhaustedUtility r)) := by
        funext x φ
        cases x.2 <;> simp only [Bool.false_eq_true,↓reduceIte,HybridProgram.eval_prepend,
          HybridProgram.eval_bind,HybridProgram.eval,exhaustedUtility,mul_zero]
      rw [hc,hybridPreparedAttempt_reset_homogeneous n cfg.1.val A
        (fun φ => (hybridRetry n cap ms).eval (retryOracle A) φ (fun r χ => branchMass χ * exhaustedUtility r))
        (fun z φ => HybridProgram.eval_mass_smul (retryOracle A) (hybridRetry n cap ms) φ exhaustedUtility z)]
      rfl

/-- For a positive first width, exhaustion probability factors into sampler-return mass,
checked-search failure probability, and remaining-schedule exhaustion probability. -/
theorem hybridRetryExhaustion_cons (n cap : ℕ) {m : ℕ} (hm : 0 < m)
    (ms : List ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetryExhaustion n cap (m :: ms) A =
      depthReturnMass m cap * (1 - CheckedSuccess A m) * hybridRetryExhaustion n cap ms A := by
  rw [hybridRetryExhaustion_cons_paths,uniformDepth_success hm,checkedSuccess_fin]
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  unfold depthReturnMass
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- For a schedule of positive widths, hybrid retry exhaustion equals the product `retryReach`. -/
theorem hybridRetryExhaustion_eq_reach (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) : hybridRetryExhaustion n cap sizes A = retryReach cap A sizes := by
  induction sizes with
  | nil => simp only [hybridRetryExhaustion_nil,retryReach,List.map_nil,List.prod_nil]
  | cons m ms ih =>
      rw [hybridRetryExhaustion_cons n cap (hs m (List.mem_cons_self))]
      rw [ih (fun k hk => hs k (List.mem_cons_of_mem m hk))]
      rfl

/-- The instrument-weighted exhausted-status indicator equals `hybridRetryExhaustion`. -/
theorem hybridRetryInstrument_exhaustion (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (hybridRetryInstrument n cap sizes A) (preparedInput n) z *
      exhaustedUtility ((hybridRetry n cap sizes).leaf (retryOracle A) z).value) =
      hybridRetryExhaustion n cap sizes A :=
  HybridProgram.eval_instrument _ (retryOracle_unitary A) _ (hybridRetry_legal n cap sizes) _ _

/-- For a positive-width initial schedule, the charged moment of concatenated schedules is the
initial moment plus its reach probability times the appended moment. -/
theorem hybridRetryMoment_append (n cap : ℕ) (sizes more : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (q g t r : ℝ) :
    hybridRetryMoment n cap (sizes ++ more) A (HybridCounts.charge q g t r) =
      hybridRetryMoment n cap sizes A (HybridCounts.charge q g t r) + retryReach cap A sizes *
        hybridRetryMoment n cap more A (HybridCounts.charge q g t r) := by
  induction sizes with
  | nil => simp [hybridRetryMoment_nil,HybridCounts.charge,HybridCounts.zero,retryReach]
  | cons m ms ih =>
      have hm : 0 < m := hs m (List.mem_cons_self)
      rw [List.cons_append,hybridRetryMoment_charge_cons n cap hm (ms ++ more),
        hybridRetryMoment_charge_cons n cap hm ms,ih (fun k hk => hs k (List.mem_cons_of_mem m hk))]
      simp only [retryReach,List.map_cons,List.prod_cons]
      ring

/-- For a positive-width initial schedule, success on concatenated schedules is initial success
plus initial reach probability times appended success. -/
theorem hybridRetrySuccess_append (n cap : ℕ) (sizes more : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) :
    hybridRetrySuccess n cap (sizes ++ more) A =
      hybridRetrySuccess n cap sizes A + retryReach cap A sizes * hybridRetrySuccess n cap more A := by
  induction sizes with
  | nil => simp [hybridRetrySuccess_nil,retryReach]
  | cons m ms ih =>
      have hm : 0 < m := hs m (List.mem_cons_self)
      rw [List.cons_append,hybridRetrySuccess_cons n cap hm (ms ++ more),
        hybridRetrySuccess_cons n cap hm ms,ih (fun k hk => hs k (List.mem_cons_of_mem m hk))]
      simp only [retryReach,List.map_cons,List.prod_cons,depthReturnMass]
      ring

/-- The hybrid retry exhaustion probability lies between zero and one. -/
theorem hybridRetryExhaustion_bounds (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) :
    0 ≤ hybridRetryExhaustion n cap sizes A ∧ hybridRetryExhaustion n cap sizes A ≤ 1 := by
  have hu (r : RetryReport (2 ^ n)) : 0 ≤ exhaustedUtility r ∧ exhaustedUtility r ≤ 1 := by
    rcases r with ⟨status,draws⟩
    cases status <;> norm_num [exhaustedUtility]
  constructor
  · exact HybridProgram.eval_nonneg _ _ _ _
      (fun r φ => mul_nonneg (measureProb_nonneg φ _) (hu r).1)
  · have h := HybridProgram.eval_mono (retryOracle A) (hybridRetry n cap sizes) (Ket (prepZero n))
        (fun r φ => branchMass φ * exhaustedUtility r) (fun _ φ => branchMass φ)
        (fun r φ => by simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hu r).2 (measureProb_nonneg φ _))
    rw [HybridProgram.eval_mass _ (retryOracle_unitary A) _ (hybridRetry_legal n cap sizes),
      show branchMass (Ket (prepZero n)) = 1 from measureProb_univ (normalized_ket _)] at h
    exact h

/-- Nonnegative query, gate, measurement, and random-bit prices give a nonnegative charged retry
moment. -/
theorem hybridRetryMoment_charge_nonneg (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (q g t r : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    0 ≤ hybridRetryMoment n cap sizes A (HybridCounts.charge q g t r) :=
  HybridProgram.evalCounts_nonneg _ _ _ _ _ (fun _ φ c =>
    mul_nonneg (measureProb_nonneg φ _) (HybridCounts.charge_nonneg q g t r hq hg ht hr c))

/-- With nonnegative operation prices and a positive-width initial schedule, appending retries
cannot decrease the charged moment. -/
theorem hybridRetryMoment_le_append (n cap : ℕ) (sizes more : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (q g t r : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    hybridRetryMoment n cap sizes A (HybridCounts.charge q g t r) ≤
      hybridRetryMoment n cap (sizes ++ more) A (HybridCounts.charge q g t r) := by
  rw [hybridRetryMoment_append n cap sizes more A hs]
  apply le_add_of_nonneg_right
  have hreach := (hybridRetryExhaustion_bounds n cap sizes A).1
  rw [hybridRetryExhaustion_eq_reach n cap sizes A hs] at hreach
  exact mul_nonneg hreach (hybridRetryMoment_charge_nonneg n cap more A q g t r hq hg ht hr)

/-- Every width in an effective BBHT prefix is positive when the table size is positive. -/
theorem effectiveBBHTPrefix_pos {N : ℕ} (hN : 0 < N) (start rounds : ℕ) :
    ∀ m ∈ effectiveBBHTPrefix N start rounds, 0 < m := by
  induction rounds generalizing start with
  | zero => simp [effectiveBBHTPrefix]
  | succ rounds ih =>
      intro m hm
      simp only [effectiveBBHTPrefix,List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact effectiveBBHTSize_pos hN start
      · exact ih (start+1) m hm

/-- With nonnegative operation prices, the growing-schedule charged moment is monotone in the
number of rounds. -/
theorem growingCharge_monotone (n cap start : ℕ) (A : Finset (Fin (2 ^ n)))
    (q g t r : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    Monotone (fun rounds => hybridRetryMoment n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A
      (HybridCounts.charge q g t r)) := by
  apply monotone_nat_of_le_succ
  intro rounds
  rw [effectiveBBHTPrefix_append (2 ^ n) start rounds 1]
  exact hybridRetryMoment_le_append n cap _ _ A (effectiveBBHTPrefix_pos (Nat.two_pow_pos n) start rounds)
    q g t r hq hg ht hr

/-- With nonnegative operation prices, the extended nonnegative charged moments tend to
`growingChargeSup` as the number of rounds tends to infinity. -/
theorem growingCharge_tendsto_sup (n cap start : ℕ) (A : Finset (Fin (2 ^ n)))
    (q g t r : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    Filter.Tendsto (fun rounds => ENNReal.ofReal (hybridRetryMoment n cap
      (effectiveBBHTPrefix (2 ^ n) start rounds) A (HybridCounts.charge q g t r)))
      Filter.atTop (nhds (growingChargeSup n cap start A q g t r)) := by
  exact tendsto_atTop_iSup
      (ENNReal.ofReal_mono.comp (growingCharge_monotone n cap start A q g t r hq hg ht hr))

/-- The instrument-weighted sampler-timeout indicator equals `hybridRetryTimeout`. -/
theorem hybridRetryInstrument_timeout (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) :
    (∑ z, instrumentProb (hybridRetryInstrument n cap sizes A) (preparedInput n) z *
      timeoutUtility ((hybridRetry n cap sizes).leaf (retryOracle A) z).value) = hybridRetryTimeout n cap sizes A :=
  HybridProgram.eval_instrument _ (retryOracle_unitary A) _ (hybridRetry_legal n cap sizes) _ _

/-- Hybrid retry success, schedule-exhaustion, and sampler-timeout probabilities sum to one. -/
theorem hybridRetry_status_partition (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetrySuccess n cap sizes A + hybridRetryExhaustion n cap sizes A + hybridRetryTimeout n cap sizes A = 1 := by
  unfold hybridRetrySuccess hybridRetryExhaustion hybridRetryTimeout
  rw [← HybridProgram.eval_add,← HybridProgram.eval_add]
  have hpay : (fun r : RetryReport (2 ^ n) => fun φ : QState (Fin (2 ^ n * 2)) =>
      (branchMass φ * foundUtility r + branchMass φ * exhaustedUtility r) + branchMass φ * timeoutUtility r) =
    (fun _ φ => branchMass φ) := by
    funext r φ
    rcases r with ⟨status,draws⟩
    cases status <;> simp [foundUtility,exhaustedUtility,timeoutUtility]
  rw [hpay,HybridProgram.eval_mass _ (retryOracle_unitary A) _ (hybridRetry_legal n cap sizes)]
  exact measureProb_univ (normalized_ket _)

/-- Exhaustion probability for concatenated positive-width schedules is the product of their
exhaustion probabilities. -/
theorem hybridRetryExhaustion_append (n cap : ℕ) (sizes more : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (hm : ∀ m ∈ more, 0 < m) :
    hybridRetryExhaustion n cap (sizes ++ more) A =
      hybridRetryExhaustion n cap sizes A * hybridRetryExhaustion n cap more A := by
  have ha : ∀ m ∈ sizes ++ more, 0 < m := by
    intro m h
    rcases List.mem_append.mp h with h | h
    · exact hs m h
    · exact hm m h
  rw [hybridRetryExhaustion_eq_reach n cap (sizes ++ more) A ha,
    hybridRetryExhaustion_eq_reach n cap sizes A hs,hybridRetryExhaustion_eq_reach n cap more A hm]
  simp only [retryReach,List.map_append,List.prod_append]

/-- The exhaustion probability of the growing retry schedule is antitone in the number of
rounds. -/
theorem growingExhaustion_antitone (n cap start : ℕ) (A : Finset (Fin (2 ^ n))) :
    Antitone (fun rounds => hybridRetryExhaustion n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A) := by
  apply antitone_nat_of_succ_le
  intro rounds
  rw [effectiveBBHTPrefix_append (2 ^ n) start rounds 1,
    hybridRetryExhaustion_append n cap _ _ A (effectiveBBHTPrefix_pos (Nat.two_pow_pos n) _ _)
      (effectiveBBHTPrefix_pos (Nat.two_pow_pos n) _ _)]
  have hp := hybridRetryExhaustion_bounds n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A
  have hm := hybridRetryExhaustion_bounds n cap (effectiveBBHTPrefix (2 ^ n) (start+rounds) 1) A
  exact mul_le_of_le_one_right hp.1 hm.2

/-- The extended nonnegative exhaustion probabilities tend to `growingExhaustionInf` as the
number of rounds tends to infinity. -/
theorem growingExhaustion_tendsto_inf (n cap start : ℕ) (A : Finset (Fin (2 ^ n))) :
    Filter.Tendsto (fun rounds => ENNReal.ofReal (hybridRetryExhaustion n cap
      (effectiveBBHTPrefix (2 ^ n) start rounds) A)) Filter.atTop (nhds (growingExhaustionInf n cap start A)) := by
  exact tendsto_atTop_iInf
      (fun _ _ h => ENNReal.ofReal_le_ofReal (growingExhaustion_antitone n cap start A h))

/-- For a terminal payoff homogeneous of degree two under complex scaling, checked readout can
replace each terminal state by its encoded basis ket and multiply by branch mass. -/
theorem hybridCheckedReadout_eval_basis {N : ℕ} (f : Fin N → Bool) (ψ : QState (Fin (N * 2)))
    (F : (Fin N × Bool) → QState (Fin (N * 2)) → ℝ)
    (hF : ∀ a (z : ℂ) φ, F a (z • φ) = ‖z‖ ^ 2 * F a φ) :
    (hybridCheckedReadout N).eval (encodeGate (BitOracleOn f)) ψ F =
      (hybridCheckedReadout N).eval (encodeGate (BitOracleOn f)) ψ
        (fun z φ => branchMass φ * F z (Ket (indexBitEquiv N z))) := by
  have hz (a : Fin N × Bool) : F a 0 = 0 := by
    have h := hF a 0 (0 : QState (Fin (N * 2)))
    simpa using! h
  have hm (z : ℂ) (x : Fin (N * 2)) : branchMass (z • Ket x) = ‖z‖ ^ 2 := by
    rw [branchMass,measureProb_smul,measureProb_univ (normalized_ket _),mul_one]
  have hzero : branchMass (0 : QState (Fin (N * 2))) = 0 := by
    simp [branchMass,MeasureProb,BornProb]
  simp only [hybridCheckedReadout,HybridProgram.eval,id_eq,query_reset_collapsed,collapse_encoded_bit]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro b _
  fin_cases b <;> cases hf : f ((indexBitEquiv N).symm x).1 <;>
    norm_num [boolEquivFin2,hz,hF,hm,hzero,show ((0 : Fin 2) == 1) = false from rfl]

/-- A homogeneous terminal payoff after a prepared attempt is the Born-weighted sum of its
values at the encoded checked-output basis kets. -/
theorem hybridPreparedAttempt_eval_basis (n j : ℕ) (A : Finset (Fin (2 ^ n)))
    (F : (Fin (2 ^ n) × Bool) → QState (Fin (2 ^ n * 2)) → ℝ)
    (hF : ∀ a (z : ℂ) φ, F a (z • φ) = ‖z‖ ^ 2 * F a φ) :
    (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n)) F =
      ∑ i : Fin (2 ^ n), BornProb (SearchState A j) i *
        F (i,decide (i ∈ A)) (Ket (indexBitEquiv (2 ^ n) (i,decide (i ∈ A)))) := by
  calc
    _ = (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
        (fun z φ => branchMass φ * F z (Ket (indexBitEquiv (2 ^ n) z))) := by
      simp only [hybridPreparedAttempt,hybridCheckedAttempt,HybridProgram.eval_prepend,retryOracle]
      exact hybridCheckedReadout_eval_basis _ _ F hF
    _ = _ := hybridPreparedAttempt_value_eval n j A (fun z => F z (Ket (indexBitEquiv (2 ^ n) z)))

/-- For a homogeneous terminal payoff, hybrid retry evaluation factors each terminal branch into
its mass and the payoff at the basis ket determined by its status. -/
theorem hybridRetry_eval_finalBasis (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (G : RetryReport (2 ^ n) → QState (Fin (2 ^ n * 2)) → ℝ)
    (hG : ∀ a (z : ℂ) φ, G a (z • φ) = ‖z‖ ^ 2 * G a φ) :
    (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n)) G =
      (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n))
        (fun r φ => branchMass φ * G r (Ket (retryFinalBasis n r.status))) := by
  induction sizes generalizing G with
  | nil =>
      simp only [hybridRetry,HybridProgram.eval,retryFinalBasis,
        show branchMass (Ket (prepZero n)) = 1 from measureProb_univ (normalized_ket _),one_mul]
  | cons m ms ih =>
      rw [hybridRetry,HybridProgram.eval_ofCoins,HybridProgram.eval_ofCoins]
      apply congrArg List.sum
      apply List.map_congr_left
      intro a _
      congr 1
      cases ha : a.1.1 with
      | inr cfg => simp only [HybridProgram.eval,retryFinalBasis,
          show branchMass (Ket (prepZero n)) = 1 from measureProb_univ (normalized_ket _),one_mul]
      | inl cfg =>
          rw [HybridProgram.eval_bind,HybridProgram.eval_bind]
          let go : Fin (2 ^ n) × Bool → HybridProgram (2 ^ n * 2) (RetryReport (2 ^ n)) := fun x =>
            if x.2 then .ret ⟨.found x.1,[depthDraw a.1]⟩ else
              HybridProgram.prependCircuit (basisResetCircuit n (indexBitEquiv (2 ^ n) (x.1,false)))
                ((hybridRetry n cap ms).bind (fun r => .ret {r with draws := depthDraw a.1 :: r.draws}))
          change (hybridPreparedAttempt n cfg.1.val).eval (retryOracle A) (Ket (prepZero n))
              (fun x φ => (go x).eval (retryOracle A) φ G) =
            (hybridPreparedAttempt n cfg.1.val).eval (retryOracle A) (Ket (prepZero n))
              (fun x φ => (go x).eval (retryOracle A) φ
                (fun r χ => branchMass χ * G r (Ket (retryFinalBasis n r.status))))
          have hpay (r : RetryReport (2 ^ n)) (z : ℂ) (φ : QState (Fin (2 ^ n * 2))) :
              branchMass (z • φ) * G r (Ket (retryFinalBasis n r.status)) =
                ‖z‖ ^ 2 * (branchMass φ * G r (Ket (retryFinalBasis n r.status))) := by
            simp only [branchMass,measureProb_smul]
            ring
          rw [hybridPreparedAttempt_eval_basis n cfg.1.val A _
              (fun x z φ => (go x).eval_smul (retryOracle A) φ G hG z),
            hybridPreparedAttempt_eval_basis n cfg.1.val A _
              (fun x z φ => (go x).eval_smul (retryOracle A) φ _ hpay z)]
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          cases hm : decide (i ∈ A) with
          | true => simp only [go,↓reduceIte,HybridProgram.eval,retryFinalBasis,
              show branchMass (Ket (indexBitEquiv (2 ^ n) (i,true))) = 1 from measureProb_univ
                  (normalized_ket _),one_mul]
          | false =>
              simp only [go,Bool.false_eq_true,↓reduceIte,HybridProgram.eval_prepend,
                basisResetCircuit_run,HybridProgram.eval_bind,HybridProgram.eval]
              exact ih (fun r φ => G {r with draws := depthDraw a.1 :: r.draws} φ)
                (fun r z φ => hG {r with draws := depthDraw a.1 :: r.draws} z φ)

/-- For positive width, the depth sampler's return mass tends to one as the sampler cap tends to
infinity. -/
theorem depthReturnMass_tendsto_one {m : ℕ} (hm : 0 < m) :
    Filter.Tendsto (depthReturnMass m) Filter.atTop (nhds 1) := by
  have hW : 0 < weightTotal (fun _ : Fin m => 1) := by simpa [weightTotal] using! hm
  have hb : weightTotal (fun _ : Fin m => 1) ≤ 2 ^ Nat.clog 2 m := by
    simpa [weightTotal] using! Nat.le_pow_clog (by norm_num : 1 < 2) m
  have he := weightedSampler_timeout_tendsto_zero (fun _ : Fin m => 1) (Nat.clog 2 m) hW hb
  simp only [weightedSampler_timeout _ _ _ hb] at he
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  simpa only [ENNReal.toReal_zero,sub_zero] using!
    (tendsto_const_nhds.sub hr : Filter.Tendsto (fun cap => 1 -
      (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal) Filter.atTop (nhds (1 - (0 : ℝ))))

/-- For positive width, the mean depth-sampling read count tends to `depthReadLimit` as the
sampler cap tends to infinity. -/
theorem depthReadMean_tendsto_limit {m : ℕ} (hm : 0 < m) :
    Filter.Tendsto (depthReadMean m) Filter.atTop (nhds (depthReadLimit m)) := by
  have hW : 0 < weightTotal (fun _ : Fin m => 1) := by simpa [weightTotal] using! hm
  have hb : weightTotal (fun _ : Fin m => 1) ≤ 2 ^ Nat.clog 2 m := by
    simpa [weightTotal] using! Nat.le_pow_clog (by norm_num : 1 < 2) m
  have he := weightedSampler_expected_reads_limit (fun _ : Fin m => 1) (Nat.clog 2 m) hW hb
  have hr := (ENNReal.tendsto_toReal he.2.ne).comp he.1
  convert! hr using 1
  funext cap
  dsimp only [Function.comp_apply]
  rw [← CoinCode.readMean_expectedCost,ENNReal.toReal_ofReal (CoinCode.readMean_nonneg _),depthReadMean_eq hm]

/-- For a fixed positive-width schedule, exhaustion probability tends to the product of
checked-search failure probabilities as the sampler cap tends to infinity. -/
theorem hybridRetryExhaustion_cap_limit (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) :
    Filter.Tendsto (fun cap => hybridRetryExhaustion n cap sizes A) Filter.atTop
      (nhds (retryCapLimitExhaustion A sizes)) := by
  induction sizes with
  | nil => simpa only [hybridRetryExhaustion_nil,retryCapLimitExhaustion,List.map_nil,List.prod_nil]
      using! (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1))
  | cons m ms ih =>
      have hm : 0 < m := hs m List.mem_cons_self
      have ht := ((depthReturnMass_tendsto_one hm).mul_const (1 - CheckedSuccess A m)).mul
        (ih (fun k hk => hs k (List.mem_cons_of_mem m hk)))
      simpa only [hybridRetryExhaustion_cons n _ hm,retryCapLimitExhaustion,List.map_cons,List.prod_cons,one_mul] using! ht

/-- For a fixed positive-width schedule, success probability tends to one minus the product of
checked-search failure probabilities as the sampler cap tends to infinity. -/
theorem hybridRetrySuccess_cap_limit (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) :
    Filter.Tendsto (fun cap => hybridRetrySuccess n cap sizes A) Filter.atTop
      (nhds (1 - retryCapLimitExhaustion A sizes)) := by
  induction sizes with
  | nil => simpa only [hybridRetrySuccess_nil,retryCapLimitExhaustion,List.map_nil,List.prod_nil,sub_self]
      using! (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  | cons m ms ih =>
      have hm : 0 < m := hs m List.mem_cons_self
      have hc :
          Filter.Tendsto (fun _ : ℕ => CheckedSuccess A m) Filter.atTop
          (nhds (CheckedSuccess A m)) := tendsto_const_nhds
      have ht := (depthReturnMass_tendsto_one hm).mul
        (hc.add ((ih (fun k hk => hs k (List.mem_cons_of_mem m hk))).const_mul (1 - CheckedSuccess A m)))
      have hlim : 1 * (CheckedSuccess A m + (1 - CheckedSuccess A m) * (1 - retryCapLimitExhaustion A ms)) =
          1 - retryCapLimitExhaustion A (m :: ms) := by
        simp only [retryCapLimitExhaustion,List.map_cons,List.prod_cons]
        ring
      rw [hlim] at ht
      simpa only [hybridRetrySuccess_cons n _ hm,depthReturnMass] using! ht

/-- For a fixed positive-width schedule, sampler-timeout probability tends to zero as the
sampler cap tends to infinity. -/
theorem hybridRetryTimeout_cap_limit (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) :
    Filter.Tendsto (fun cap => hybridRetryTimeout n cap sizes A) Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have ht := ((hc.sub (hybridRetrySuccess_cap_limit n sizes A hs)).sub
    (hybridRetryExhaustion_cap_limit n sizes A hs))
  have he (cap : ℕ) : hybridRetryTimeout n cap sizes A =
      1 - hybridRetrySuccess n cap sizes A - hybridRetryExhaustion n cap sizes A := by
    have h := hybridRetry_status_partition n cap sizes A
    linarith
  simp_rw [← he] at ht
  simpa only [sub_sub_cancel,sub_self] using! ht

/-- For a fixed positive-width schedule, the charged retry moment tends to `retryCapLimitMoment`
as the sampler cap tends to infinity. -/
theorem hybridRetryMoment_cap_limit (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (q g t r : ℝ) :
    Filter.Tendsto (fun cap => hybridRetryMoment n cap sizes A (HybridCounts.charge q g t r))
      Filter.atTop (nhds (retryCapLimitMoment n A q g t r sizes)) := by
  induction sizes with
  | nil => simpa only [hybridRetryMoment_nil n _ A (HybridCounts.charge q g t r) (by simp [HybridCounts.charge,HybridCounts.zero]),retryCapLimitMoment]
      using! (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  | cons m ms ih =>
      have hm : 0 < m := hs m List.mem_cons_self
      have hc : Filter.Tendsto (fun _ : ℕ => (q+g)*((m : ℝ)+1)/2 + g*(n+2) + 2*t + g*meanResetGates n m A)
          Filter.atTop (nhds ((q+g)*((m : ℝ)+1)/2 + g*(n+2) + 2*t + g*meanResetGates n m A)) := tendsto_const_nhds
      have ht := ((depthReadMean_tendsto_limit hm).const_mul r).add
        ((depthReturnMass_tendsto_one hm).mul (hc.add
          ((ih (fun k hk => hs k (List.mem_cons_of_mem m hk))).const_mul (1 - CheckedSuccess A m))))
      have hlim : r * depthReadLimit m + 1 *
          ((q+g)*((m : ℝ)+1)/2 + g*(n+2) + 2*t + g*meanResetGates n m A +
            (1 - CheckedSuccess A m) * retryCapLimitMoment n A q g t r ms) =
          retryCapLimitMoment n A q g t r (m :: ms) := by rw [retryCapLimitMoment]; ring
      rw [hlim] at ht
      simpa only [hybridRetryMoment_charge_cons n _ hm] using! ht

/-- For positive width, the extended nonnegative image of `depthReadLimit` equals block width
divided by one minus rejection mass. -/
theorem depthReadLimit_exact {m : ℕ} (hm : 0 < m) :
    ENNReal.ofReal (depthReadLimit m) =
      (Nat.clog 2 m : ℝ≥0∞) / (1 - rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m)) := by
  have he := weightedSampler_expected_reads_limit (fun _ : Fin m => 1) (Nat.clog 2 m)
    (by simpa [weightTotal] using! hm)
    (by simpa [weightTotal] using! Nat.le_pow_clog (by norm_num : 1 < 2) m)
  exact ENNReal.ofReal_toReal he.2.ne

/-- The depth sampler's mean random-bit read count is monotone in the sampler cap. -/
theorem depthReadMean_mono (m : ℕ) : Monotone (depthReadMean m) := by
  intro a b hab
  unfold depthReadMean
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
  intro i _ _
  exact pow_nonneg ENNReal.toReal_nonneg i

/-- The depth sampler's defined return mass lies between zero and one. -/
theorem depthReturnMass_bounds (m cap : ℕ) : 0 ≤ depthReturnMass m cap ∧ depthReturnMass m cap ≤ 1 := by
  have hb : weightTotal (fun _ : Fin m => 1) ≤ 2 ^ Nat.clog 2 m := by
    simpa [weightTotal] using! Nat.le_pow_clog (by norm_num : 1 < 2) m
  have he := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).law
    (fun z => rejectionOutcome z.1.1 = .inr ())
  rw [weightedSampler_timeout _ _ _ hb] at he
  have hr := ENNReal.toReal_mono ENNReal.one_ne_top he
  simp only [ENNReal.toReal_one] at hr
  exact ⟨sub_nonneg.mpr hr,sub_le_self _ ENNReal.toReal_nonneg⟩

/-- The depth sampler's return mass is monotone in the sampler cap. -/
theorem depthReturnMass_mono (m : ℕ) : Monotone (depthReturnMass m) := by
  have hq := (depthReturnMass_bounds m 1).1
  simp only [depthReturnMass,pow_one] at hq
  apply monotone_nat_of_le_succ
  intro cap
  simp only [depthReturnMass,ENNReal.toReal_pow,pow_succ,ENNReal.toReal_mul]
  have hb : (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m)).toReal ≤ 1 := by linarith
  have hp : 0 ≤ (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m)).toReal ^ cap :=
    pow_nonneg ENNReal.toReal_nonneg cap
  exact sub_le_sub_left (mul_le_of_le_one_right hp hb) 1

/-- The mean reset-gate cost is nonnegative. -/
theorem meanResetGates_nonneg (n m : ℕ) (A : Finset (Fin (2 ^ n))) : 0 ≤ meanResetGates n m A := by
  unfold meanResetGates
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro j _
  rw [hybridResetMoment_value]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (sq_nonneg _) _
  split_ifs
  · exact le_rfl
  · simp only [HybridCounts.charge,zero_mul,one_mul,zero_add,add_zero]
    exact Nat.cast_nonneg _

/-- For positive depth width, checked-search success on `2 ^ n` indices lies between zero and
one. -/
theorem checkedSuccess_bounds (n : ℕ) (A : Finset (Fin (2 ^ n))) {m : ℕ} (hm : 0 < m) :
    0 ≤ CheckedSuccess A m ∧ CheckedSuccess A m ≤ 1 := by
  have h := search_checked_random_attempt (by simp) A m hm
  have hf : 0 ≤ 1 - CheckedSuccess A m := by rw [← h.2.1]; exact h.2.2.1.2
  exact ⟨h.2.2.1.1,by linarith⟩

/-- For a positive-width schedule and nonnegative operation prices, the charged retry moment is
monotone in the sampler cap. -/
theorem hybridRetryMoment_cap_mono (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (q g t r : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    Monotone (fun cap => hybridRetryMoment n cap sizes A (HybridCounts.charge q g t r)) := by
  induction sizes with
  | nil =>
      intro a b _
      (try dsimp only)
      rw [hybridRetryMoment_nil n a A (HybridCounts.charge q g t r) (by simp [HybridCounts.charge,HybridCounts.zero]),
        hybridRetryMoment_nil n b A (HybridCounts.charge q g t r) (by simp [HybridCounts.charge,HybridCounts.zero])]
  | cons m ms ih =>
      intro a b hab
      (try dsimp only)
      have hm : 0 < m := hs m List.mem_cons_self
      have hms : ∀ k ∈ ms, 0 < k := fun k hk => hs k (List.mem_cons_of_mem m hk)
      rw [hybridRetryMoment_charge_cons n a hm,hybridRetryMoment_charge_cons n b hm]
      have hf : 0 ≤ 1 - CheckedSuccess A m := sub_nonneg.mpr (checkedSuccess_bounds n A hm).2
      have hlocal : 0 ≤ (q+g)*((m : ℝ)+1)/2 + g*(n+2) + 2*t + g*meanResetGates n m A := by
        have hb := meanResetGates_nonneg n m A
        positivity
      apply add_le_add (mul_le_mul_of_nonneg_left (depthReadMean_mono m hab) hr)
      apply mul_le_mul (depthReturnMass_mono m hab)
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ((ih hms) hab) hf)
      · exact add_nonneg hlocal
          (mul_nonneg hf (hybridRetryMoment_charge_nonneg n a ms A q g t r hq hg ht hr))
      · exact (depthReturnMass_bounds m b).1

/-- For a positive-width schedule and nonnegative prices, the supremum over sampler caps of the
extended charged moment equals the extended value of `retryCapLimitMoment`. -/
theorem hybridRetryMoment_cap_iSup (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (q g t r : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (⨆ (cap : ℕ), ENNReal.ofReal (hybridRetryMoment n cap sizes A (HybridCounts.charge q g t r))) =
      ENNReal.ofReal (retryCapLimitMoment n A q g t r sizes) := by
  exact tendsto_nhds_unique
    (tendsto_atTop_iSup (ENNReal.ofReal_mono.comp (hybridRetryMoment_cap_mono n sizes A hs q g t r hq hg ht hr)))
    (ENNReal.tendsto_ofReal (hybridRetryMoment_cap_limit n sizes A hs q g t r))

/-- For a positive-width schedule and nonnegative prices, the supremum over sampler caps of the
extended charged moment is finite. -/
theorem hybridRetryMoment_cap_iSup_finite (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (q g t r : ℝ) (hq : 0 ≤ q) (hg : 0 ≤ g) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (⨆ (cap : ℕ), ENNReal.ofReal (hybridRetryMoment n cap sizes A (HybridCounts.charge q g t r))) < ⊤ := by
  rw [hybridRetryMoment_cap_iSup n sizes A hs q g t r hq hg ht hr]
  exact ENNReal.ofReal_lt_top

/-- For a positive depth width, a terminal sampler payoff splits into timeout mass times its
timeout value and return mass times the uniform average of its depth payoff. -/
theorem uniformDepth_terminal {m : ℕ} (hm : 0 < m) (cap : ℕ) (F : Fin m → ℝ) (c : ℝ) :
    ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.map (fun z =>
      CoinCode.wordWeight z.2 * match z.1.1 with | .inr _ => c | .inl (j,_,_) => F j)).sum =
      (1 - depthReturnMass m cap) * c + depthReturnMass m cap * (∑ j : Fin m, F j) / m := by
  let p := weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap
  change (p.paths.map (fun z => CoinCode.wordWeight z.2 *
    match z.1.1 with | .inr _ => c | .inl (j,_,_) => F j)).sum = _
  calc
    _ = c * (∑ k : Fin p.paths.length, CoinCode.wordWeight (p.paths.get k).2) +
        codeSuccess p (fun j => F j - c) := by
      unfold codeSuccess
      conv_lhs => rw [← List.ofFn_get p.paths]
      rw [List.map_ofFn,List.sum_ofFn,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [Function.comp_apply]
      cases hcfg : (p.paths.get k).1.1 with
      | inr cfg => ring
      | inl cfg => rcases cfg with ⟨j,b,d⟩; ring
    _ = c + depthReturnMass m cap * (∑ j : Fin m, (F j - c)) / m := by
      rw [CoinCode.paths_weight_sum,mul_one,uniformDepth_success hm]
      rfl
    _ = _ := by
      simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
      ring

/-- On an empty retry schedule, the terminal-status mean is the payoff at status `exhausted`. -/
theorem hybridRetryStatusMean_nil (n cap : ℕ) (A : Finset (Fin (2 ^ n))) (f : RetryStatus (2 ^ n) → ℝ) :
    hybridRetryStatusMean n cap [] A f = f .exhausted := by
  simp only [hybridRetryStatusMean,hybridRetry,HybridProgram.eval,
    show branchMass (Ket (prepZero n)) = 1 from measureProb_univ (normalized_ket _),one_mul]

/-- The terminal-status mean expands over sampler paths into timeout payoff and the
Born-weighted found-or-continue payoff for each returned depth. -/
theorem hybridRetryStatusMean_cons_paths (n cap m : ℕ) (ms : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : RetryStatus (2 ^ n) → ℝ) :
    hybridRetryStatusMean n cap (m :: ms) A f =
    ((weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap).paths.map (fun z => CoinCode.wordWeight z.2 *
      match z.1.1 with
      | .inr _ => f .samplerTimeout
      | .inl (j,_,_) => ∑ i : Fin (2 ^ n), BornProb (SearchState A j.val) i *
          (if decide (i ∈ A) then f (.found i) else hybridRetryStatusMean n cap ms A f))).sum := by
  rw [hybridRetryStatusMean,hybridRetry,HybridProgram.eval_ofCoins]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  congr 1
  cases ha : a.1.1 with
  | inr cfg => simp only [HybridProgram.eval,
      show branchMass (Ket (prepZero n)) = 1 from measureProb_univ (normalized_ket _),one_mul]
  | inl cfg =>
      rw [HybridProgram.eval_bind]
      let go : Fin (2 ^ n) × Bool → HybridProgram (2 ^ n * 2) (RetryReport (2 ^ n)) := fun x =>
        if x.2 then .ret ⟨.found x.1,[depthDraw a.1]⟩ else
          HybridProgram.prependCircuit (basisResetCircuit n (indexBitEquiv (2 ^ n) (x.1,false)))
            ((hybridRetry n cap ms).bind (fun r => .ret {r with draws := depthDraw a.1 :: r.draws}))
      have hG (r : RetryReport (2 ^ n)) (z : ℂ) (φ : QState (Fin (2 ^ n * 2))) :
          branchMass (z • φ) * f r.status = ‖z‖ ^ 2 * (branchMass φ * f r.status) := by
        simp only [branchMass,measureProb_smul]
        ring
      change (hybridPreparedAttempt n cfg.1.val).eval (retryOracle A) (Ket (prepZero n))
        (fun x φ => (go x).eval (retryOracle A) φ (fun r χ => branchMass χ * f r.status)) = _
      rw [hybridPreparedAttempt_eval_basis n cfg.1.val A _
        (fun x z φ => (go x).eval_smul (retryOracle A) φ _ hG z)]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      cases hm : decide (i ∈ A) with
      | true => simp only [go,↓reduceIte,HybridProgram.eval,
          show branchMass (Ket (indexBitEquiv (2 ^ n) (i,true))) = 1 from measureProb_univ
              (normalized_ket _),one_mul]
      | false =>
          simp only [go,Bool.false_eq_true,↓reduceIte,HybridProgram.eval_prepend,
            basisResetCircuit_run,HybridProgram.eval_bind,HybridProgram.eval]
          rfl

/-- For a positive first width, the terminal-status mean splits into timeout payoff and a
uniform-depth average of the Born-weighted found-or-continue payoff. -/
theorem hybridRetryStatusMean_cons (n cap : ℕ) {m : ℕ} (hm : 0 < m) (ms : List ℕ)
    (A : Finset (Fin (2 ^ n))) (f : RetryStatus (2 ^ n) → ℝ) :
    hybridRetryStatusMean n cap (m :: ms) A f =
      (1 - depthReturnMass m cap) * f .samplerTimeout + depthReturnMass m cap *
        (∑ j : Fin m, ∑ i : Fin (2 ^ n), BornProb (SearchState A j.val) i *
          (if decide (i ∈ A) then f (.found i) else hybridRetryStatusMean n cap ms A f)) / m := by
  rw [hybridRetryStatusMean_cons_paths,uniformDepth_terminal hm]

/-- For a positive-width schedule, terminal-status means tend to `retryCapLimitStatusMean` as
the sampler cap tends to infinity. -/
theorem hybridRetryStatusMean_cap_limit (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (f : RetryStatus (2 ^ n) → ℝ) :
    Filter.Tendsto (fun cap => hybridRetryStatusMean n cap sizes A f) Filter.atTop
      (nhds (retryCapLimitStatusMean n A f sizes)) := by
  induction sizes with
  | nil => simpa only [hybridRetryStatusMean_nil,retryCapLimitStatusMean] using!
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => f .exhausted) Filter.atTop (nhds (f .exhausted)))
  | cons m ms ih =>
      have hm : 0 < m := hs m List.mem_cons_self
      have hms : ∀ k ∈ ms, 0 < k := fun k hk => hs k (List.mem_cons_of_mem m hk)
      have hsum : Filter.Tendsto (fun cap => ∑ j : Fin m, ∑ i : Fin (2 ^ n), BornProb (SearchState A j.val) i *
          (if decide (i ∈ A) then f (.found i) else hybridRetryStatusMean n cap ms A f)) Filter.atTop
        (nhds (∑ j : Fin m, ∑ i : Fin (2 ^ n), BornProb (SearchState A j.val) i *
          (if decide (i ∈ A) then f (.found i) else retryCapLimitStatusMean n A f ms))) := by
        apply tendsto_finsetSum
        intro j _
        apply tendsto_finsetSum
        intro i _
        cases hi : decide (i ∈ A) with
        | false => simpa only [hi,Bool.false_eq_true,↓reduceIte] using!
            ((ih hms).const_mul (BornProb (SearchState A j.val) i))
        | true => simpa only [hi,↓reduceIte] using!
            (tendsto_const_nhds : Filter.Tendsto
              (fun _ : ℕ => BornProb (SearchState A j.val) i * f (.found i)) Filter.atTop
              (nhds (BornProb (SearchState A j.val) i * f (.found i))))
      have hc : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
      have ht := (((hc.sub (depthReturnMass_tendsto_one hm)).mul_const (f .samplerTimeout))).add
        (((depthReturnMass_tendsto_one hm).mul hsum).div_const (m : ℝ))
      simpa only [hybridRetryStatusMean_cons n _ hm,sub_self,zero_mul,one_mul,zero_add,retryCapLimitStatusMean] using! ht

/-- The instrument-weighted mean of a terminal-status payoff equals `hybridRetryStatusMean`. -/
theorem hybridRetryInstrument_statusMean (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : RetryStatus (2 ^ n) → ℝ) :
    (∑ z, instrumentProb (hybridRetryInstrument n cap sizes A) (preparedInput n) z *
      f ((hybridRetry n cap sizes).leaf (retryOracle A) z).value.status) = hybridRetryStatusMean n cap sizes A f :=
  HybridProgram.eval_instrument _ (retryOracle_unitary A) _ (hybridRetry_legal n cap sizes) _ (fun r => f r.status)

/-- For a positive-width schedule, the instrument's terminal-status payoff means tend to
`retryCapLimitStatusMean` as the sampler cap tends to infinity. -/
theorem hybridRetryInstrument_status_cap_limit (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m) (f : RetryStatus (2 ^ n) → ℝ) :
    Filter.Tendsto (fun cap => ∑ z, instrumentProb (hybridRetryInstrument n cap sizes A) (preparedInput n) z *
      f ((hybridRetry n cap sizes).leaf (retryOracle A) z).value.status) Filter.atTop
      (nhds (retryCapLimitStatusMean n A f sizes)) := by
  simpa only [hybridRetryInstrument_statusMean] using!
      hybridRetryStatusMean_cap_limit n sizes A hs f

/-- For a positive-width schedule and a homogeneous status-and-state payoff, retry evaluation
tends to the limiting status recurrence evaluated at the basis ket determined by each
status. -/
theorem hybridRetry_quantum_cap_limit (n : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (hs : ∀ m ∈ sizes, 0 < m)
    (G : RetryStatus (2 ^ n) → QState (Fin (2 ^ n * 2)) → ℝ)
    (hG : ∀ a (z : ℂ) φ, G a (z • φ) = ‖z‖ ^ 2 * G a φ) :
    Filter.Tendsto (fun cap => (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n)) (fun r φ => G r.status φ))
      Filter.atTop (nhds (retryCapLimitStatusMean n A (fun status => G status (Ket (retryFinalBasis n status))) sizes)) := by
  have h :=
      hybridRetryStatusMean_cap_limit n sizes A hs
      (fun status => G status (Ket (retryFinalBasis n status)))
  convert! h using 1
  funext cap
  exact hybridRetry_eval_finalBasis n cap sizes A (fun r φ => G r.status φ)
      (fun r z φ => hG r.status z φ)

/-- A retry schedule beginning with width zero immediately returns sampler timeout with a depth
record containing no sampled depth and zero reads and comparisons. -/
theorem hybridRetry_zeroWidth (n cap : ℕ) (ms : List ℕ) :
    hybridRetry n cap (0 :: ms) = .ret ⟨.samplerTimeout,[⟨0,none,0,0,cap⟩]⟩ := by
  rw [hybridRetry,weightedSampler_empty_zeroBit]
  rfl

/-- A retry schedule beginning with width zero has sampler-timeout probability one. -/
theorem hybridRetryTimeout_zeroWidth (n cap : ℕ) (ms : List ℕ) (A : Finset (Fin (2 ^ n))) :
    hybridRetryTimeout n cap (0 :: ms) A = 1 := by
  rw [hybridRetryTimeout,hybridRetry_zeroWidth]
  simp only [HybridProgram.eval,timeoutUtility,mul_one]
  exact measureProb_univ (normalized_ket _)

/-- A retry schedule beginning with width zero has zero charged moment for every choice of
operation prices. -/
theorem hybridRetryMoment_zeroWidth (n cap : ℕ) (ms : List ℕ) (A : Finset (Fin (2 ^ n))) (q g t r : ℝ) :
    hybridRetryMoment n cap (0 :: ms) A (HybridCounts.charge q g t r) = 0 := by
  rw [hybridRetryMoment,hybridRetry_zeroWidth]
  simp [HybridProgram.evalCounts,HybridCounts.charge,HybridCounts.zero]
end Qatlib.Concepts.AmplitudeSearch.Amplification
