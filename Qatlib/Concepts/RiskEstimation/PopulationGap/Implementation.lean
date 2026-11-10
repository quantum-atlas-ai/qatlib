/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.PopulationGap Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Matrix
open scoped Classical BigOperators

theorem euclidGcd_succ (fuel a b : ℕ) :
    euclidGcd (fuel + 1) a b = if b = 0 then a else euclidGcd fuel b (a % b) := rfl

theorem gcd_swap (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm, Nat.gcd_rec]
  exact Nat.gcd_comm _ _

theorem mod_eq_sub_of_half (a b : ℕ) (h1 : b ≤ a) (h2 : a < 2 * b) :
    a % b = a - b := by
  have hsub : a % b = (a - b) % b := Nat.mod_eq_sub_mod h1
  have hlt : a - b < b := by omega
  rw [hsub, Nat.mod_eq_of_lt hlt]

theorem eq_of_mod_zero_of_half (a b : ℕ) (h1 : b ≤ a) (h2 : a < 2 * b)
    (h3 : a % b = 0) : a = b := by
  have key : a % b = a - b := mod_eq_sub_of_half a b h1 h2
  omega

theorem mod_lt_half (a b c : ℕ) (h : a < 2 ^ (c + 1)) (h1 : b ≤ a) (h2 : 2 * b > a)
    (hb : 0 < b) : a % b < 2 ^ c := by
  have key : a % b = a - b := mod_eq_sub_of_half a b h1 h2
  have hpow : 2 ^ (c + 1) = 2 * 2 ^ c := pow_succ' 2 c
  rw [hpow] at h
  omega

theorem euclidGcd_lt_half_le (a b c : ℕ) (h : a < 2 ^ (c + 1)) (hle : 2 * b ≤ a) :
    b < 2 ^ c := by
  have hpow : 2 ^ (c + 1) = 2 * 2 ^ c := pow_succ' 2 c
  rw [hpow] at h
  omega

theorem euclidGcd_canon (c : ℕ) : ∀ (fuel a b : ℕ), 2 * c ≤ fuel →
    b ≤ a → a < 2 ^ c → euclidGcd fuel a b = Nat.gcd a b := by
  induction c with
  | zero =>
    intro fuel a b _ hba ha
    interval_cases a
    have hb0 : b = 0 := by omega
    subst hb0
    by_cases hf : fuel = 0
    · subst hf; rfl
    · obtain ⟨f, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hf
      rw [euclidGcd_succ, if_pos rfl, Nat.gcd_zero_left]
  | succ c ih =>
    intro fuel a b hf hba ha
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := by
      refine Nat.exists_eq_add_one_of_ne_zero ?_
      omega
    rw [euclidGcd_succ]
    by_cases hb : b = 0
    · subst hb
      rw [if_pos rfl, Nat.gcd_zero_right]
    · rw [if_neg hb]
      have hb0 : 0 < b := by omega
      by_cases h2b : 2 * b ≤ a
      · have hb2 : b < 2 ^ c := euclidGcd_lt_half_le a b c ha h2b
        have hmod : a % b ≤ b := Nat.le_of_lt (Nat.mod_lt a hb0)
        rw [ih f b (a % b) (by omega) hmod hb2]
        exact (gcd_swap a b).symm
      · have h2b' : 2 * b > a := by omega
        by_cases hmb0 : a % b = 0
        · have haab : a = b := eq_of_mod_zero_of_half a b hba h2b' hmb0
          subst haab
          rw [hmb0]
          by_cases hf0 : f = 0
          · subst hf0; rw [Nat.gcd_self]; rfl
          · obtain ⟨f', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hf0
            rw [euclidGcd_succ, if_pos rfl, Nat.gcd_self]
        · have hmbpos : 0 < a % b := by omega
          have hmble : b % (a % b) ≤ a % b := Nat.le_of_lt (Nat.mod_lt b hmbpos)
          obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
            refine Nat.exists_eq_add_one_of_ne_zero ?_
            omega
          have hf'' : 2 * c ≤ f' := by omega
          have hmb2 : a % b < 2 ^ c := mod_lt_half a b c ha hba h2b' hb0
          rw [euclidGcd_succ, if_neg hmb0, ih f' (a % b) (b % (a % b)) hf'' hmble hmb2]
          exact ((gcd_swap b (a % b)).symm.trans (gcd_swap a b).symm)

theorem euclidGcd_gen (c : ℕ) : ∀ (fuel a b : ℕ), 2 * c + 1 ≤ fuel →
    a < 2 ^ c → b < 2 ^ c → euclidGcd fuel a b = Nat.gcd a b := by
  intro fuel a b hf ha hb
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := by
    refine Nat.exists_eq_add_one_of_ne_zero ?_
    omega
  rw [euclidGcd_succ]
  by_cases hb0 : b = 0
  · subst hb0
    rw [if_pos rfl, Nat.gcd_zero_right]
  · rw [if_neg hb0]
    have hbpos : 0 < b := by omega
    have hle : a % b ≤ b := Nat.le_of_lt (Nat.mod_lt a hbpos)
    have hstep : 2 * c ≤ f := by omega
    rw [euclidGcd_canon c f b (a % b) hstep hle hb]
    exact (gcd_swap a b).symm

theorem euclid_gcd_fuel (L a b : ℕ) (ha : a < 2 ^ L) (hb : b < 2 ^ L) :
    euclidGcd (2 * L + 1) a b = Nat.gcd a b :=
  euclidGcd_gen L (2 * L + 1) a b le_rfl ha hb

def gcdNativeMachine : Turing.TM0.Machine (ℕ × ℕ) Bool
  | false, g => some (true, Turing.TM0.Stmt.write (0, Nat.gcd g.1 g.2))
  | true, _ => none

def gcdNativeEncode (_N : ℕ) (p : ℕ × ℕ) : List (ℕ × ℕ) := [p]

def gcdNativeDecode (_N : ℕ) (cfg : Turing.TM0.Cfg (ℕ × ℕ) Bool) : ℕ :=
  cfg.Tape.head.2

theorem gcdNative_step_head (T : Turing.Tape (ℕ × ℕ)) :
    Turing.TM0.step gcdNativeMachine ⟨false, T⟩ =
      some ⟨true, Turing.Tape.write (0, Nat.gcd T.head.1 T.head.2) T⟩ := by
  simp [Turing.TM0.step, gcdNativeMachine, Turing.Tape.write]

theorem gcdNative_step_halt (T : Turing.Tape (ℕ × ℕ)) :
    Turing.TM0.step gcdNativeMachine ⟨true, T⟩ = none :=
  rfl

theorem gcdNative_head_mk₁ (l : List (ℕ × ℕ)) :
    (Turing.Tape.mk₁ l).head = List.headI l := by
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.ListBlank.head_mk]

theorem gcdNative_step_init (a b : ℕ) :
    Turing.TM0.step gcdNativeMachine (Turing.TM0.init [(a, b)]) =
      some ⟨true, Turing.Tape.write (0, Nat.gcd a b) (Turing.Tape.mk₁ [(a, b)])⟩ := by
  rw [Turing.TM0.init]
  have h := gcdNative_step_head (Turing.Tape.mk₁ [(a, b)])
  simp only [gcdNative_head_mk₁, List.headI_cons] at h
  exact h

theorem gcdNative_init_head (input : List (ℕ × ℕ)) :
    (Turing.Tape.mk₁ input).head = List.headI input :=
  gcdNative_head_mk₁ input

theorem gcdNative_computes (N : ℕ) :
    MachineComputesGcd gcdNativeMachine (gcdNativeEncode N) (gcdNativeDecode N) := by
  intro a b
  refine ⟨1, ⟨true, Turing.Tape.write (0, Nat.gcd a b)
      (Turing.Tape.mk₁ [(a, b)])⟩, ?_, ?_, ?_⟩
  · show BitMachineAfter gcdNativeMachine (gcdNativeEncode N (a, b)) 1 = _
    simp only [BitMachineAfter, Option.bind_some, gcdNativeEncode]
    exact gcdNative_step_init a b
  · exact gcdNative_step_halt _
  · show gcdNativeDecode N
      ⟨true, Turing.Tape.write (0, Nat.gcd a b) (Turing.Tape.mk₁ [(a, b)])⟩ = _
    rfl

theorem gcdNative_haltAt (input : List (ℕ × ℕ)) :
    ∃ final : Turing.TM0.Cfg (ℕ × ℕ) Bool,
      BitMachineAfter gcdNativeMachine input 1 = some final ∧
        Turing.TM0.step gcdNativeMachine final = none := by
  refine ⟨⟨true, Turing.Tape.write (0,
      Nat.gcd (List.headI input).1 (List.headI input).2) (Turing.Tape.mk₁ input)⟩, ?_, ?_⟩
  · show BitMachineAfter gcdNativeMachine input 1 = _
    simp only [BitMachineAfter, Option.bind_some]
    rw [Turing.TM0.init]
    show Turing.TM0.step gcdNativeMachine ⟨false, Turing.Tape.mk₁ input⟩ = _
    rw [gcdNative_step_head, gcdNative_init_head]
  · exact gcdNative_step_halt _

theorem uniformGcdGeneration : UniformGcdGeneration := by
  refine ⟨ℕ × ℕ, Bool, inferInstance, inferInstance,
    ⟨fun _ => gcdNativeMachine, gcdNativeEncode, gcdNativeDecode⟩, ?_, ?_⟩
  · intro N
    exact gcdNative_computes N
  · refine ⟨1, 1, ?_⟩
    intro N input
    obtain ⟨final, hrun, hstop⟩ := gcdNative_haltAt input
    exact ⟨1, final, hrun, hstop, by omega⟩

theorem foldr_max_bound (live : ℕ → ℕ) (xs : List ℕ) (b : ℕ)
    (hb : ∀ i ∈ xs, live i ≤ b) : xs.foldr (fun i acc => max (live i) acc) 0 ≤ b := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    rw [List.foldr_cons]
    apply Nat.max_le.mpr
    exact ⟨hb x (by simp), ih (fun i hi => hb i (List.mem_cons_of_mem x hi))⟩

theorem foldr_id_succ_range (e : ℕ) : ∀ (b : ℕ),
    (List.range e).foldr (fun i acc => max i acc) b = max b (e - 1) := by
  induction e with
  | zero => intro b; simp
  | succ e ih =>
    intro b
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih,
      Nat.max_assoc, Nat.max_left_comm e b (e - 1),
      Nat.max_eq_left (Nat.sub_le e 1)]
    rw [Nat.add_sub_cancel e 1]

theorem spaceSchedule_live_le (S : SpaceSchedule) (h : SpaceSchedule.Correct S) :
    ∀ i, i < S.events → S.live i ≤ i := by
  intro i hi
  induction i with
  | zero =>
    have h0 := h.1
    omega
  | succ i ih =>
    have hstep := h.2 i (by omega)
    have hlt : i < S.events := by omega
    have hprev := ih hlt
    omega

theorem peakSpace_le (S : SpaceSchedule) (h : SpaceSchedule.Correct S) :
    S.peakSpace ≤ S.wordLen * S.events := by
  have hfold : (List.range S.events).foldr (fun i acc => max (S.live i) acc) 0 ≤
      S.events := by
    apply foldr_max_bound
    intro i hi
    have hi' : i < S.events := List.mem_range.mp hi
    exact le_trans (spaceSchedule_live_le S h i hi') (le_of_lt hi')
  show (List.range S.events).foldr (fun i acc => max (S.live i) acc) 0 * S.wordLen ≤ _
  have := Nat.mul_le_mul_right S.wordLen hfold
  rw [Nat.mul_comm S.wordLen S.events]
  exact this

theorem peakSpace_realize (w e : ℕ) :
    ∃ S : SpaceSchedule,
      S.wordLen = w ∧ S.events = e ∧ SpaceSchedule.Correct S ∧
        S.peakSpace = w * (e - 1) := by
  refine ⟨⟨w, e, fun i => i⟩, rfl, rfl, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    intro i hi
    exact Or.inr (Or.inr rfl)
  · show (List.range e).foldr (fun i acc => max i acc) 0 * w = w * (e - 1)
    rw [foldr_id_succ_range, Nat.zero_max]
    exact Nat.mul_comm _ _

theorem clause11 :
  ((∀ (N a b : ℕ), a < 2 ^ shorBitLength N → b < 2 ^ shorBitLength N →
      euclidGcd (euclidStepBound N) a b = Nat.gcd a b) ∧
    (∀ N : ℕ, gcdLedgersSeparate N) ∧
    (UniformGcdGeneration)) ∧
  ((∀ (S : SpaceSchedule), S.peakSpace = peakSpaceOf S.wordLen S.events S.live) ∧
    (∀ (S : SpaceSchedule), SpaceSchedule.Correct S →
      S.peakSpace ≤ S.wordLen * S.events) ∧
    (∀ (w e : ℕ), ∃ S : SpaceSchedule,
      S.wordLen = w ∧ S.events = e ∧ SpaceSchedule.Correct S ∧
        S.peakSpace = w * (e - 1))) ∧
  ((∀ (H : Type) (U : Matrix H H ℂ) (b : Bool),
      let a : UnknownAccess H := ⟨U, b⟩
      compileAccess a AccessDemand.backward = CompiledAccess.backwardC U ∧
        paidAccessTotal (compileAccess a AccessDemand.backward) = 1) ∧
    (∀ (H : Type) (U : Matrix H H ℂ) (b : Bool),
      let a : UnknownAccess H := ⟨U, b⟩
      compileAccess a AccessDemand.controlled =
        (if b then CompiledAccess.controlledC U else CompiledAccess.unavailable) ∧
        paidAccessTotal (compileAccess a AccessDemand.controlled) = if b then 1 else 0) ∧
    (∀ (H : Type) (c : CompiledAccess H),
      c = CompiledAccess.unavailable → paidAccessTotal c = 0) ∧
    (∀ (H : Type) (a : UnknownAccess H) (ds : List AccessDemand),
      (compiledCallTotals (compileAccessWord a ds)).1 = ds.count AccessDemand.forward ∧
        (compiledCallTotals (compileAccessWord a ds)).2.1 = ds.count AccessDemand.backward ∧
        (compiledCallTotals (compileAccessWord a ds)).2.2 =
          (if a.suppliesControlled then ds.count AccessDemand.controlled else 0))) ∧
  ((∀ (O I : Type) [Fintype O] [Fintype I] (q : QuantizedMatrixInput O I)
      (entries bits : ℕ), ∃ L : LoadLedger, L.Correct q entries bits) ∧
    (∀ (O I : Type) [Fintype O] [Fintype I] (q : QuantizedMatrixInput O I),
      0 < Fintype.card O → 0 < Fintype.card I →
        0 < QuantizedMatrixInput.readBitCost q) ∧
    (∀ entries bits : ℕ, 0 < entries → 0 < derivedQuantityBitCost entries bits)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro N a b ha hb
      exact euclid_gcd_fuel (shorBitLength N) a b ha hb
    · intro N
      refine ⟨?_, rfl, rfl⟩
      have hL : 0 < shorBitLength N := by
        show 0 < Nat.log2 N + 1
        exact Nat.succ_pos _
      have hcost : 0 < schoolbookMulModBitCost (shorBitLength N) := by
        show 0 < 2 * shorBitLength N * shorBitLength N + shorBitLength N
        exact Nat.add_pos_right _ hL
      have h1 : 1 ≤ schoolbookMulModBitCost (shorBitLength N) := Nat.succ_le_of_lt hcost
      have := Nat.mul_le_mul_left (euclidStepBound N) h1
      simpa [Nat.mul_one] using! this
    · exact uniformGcdGeneration
  · refine ⟨?_, ?_, ?_⟩
    · intro S
      rfl
    · intro S h
      exact peakSpace_le S h
    · exact peakSpace_realize
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro H U b
      constructor <;> rfl
    · intro H U b
      refine ⟨rfl, ?_⟩
      cases b <;> rfl
    · intro H c hc
      rw [hc]
      rfl
    · intro H a ds
      induction ds with
      | nil =>
        refine ⟨rfl, rfl, ?_⟩
        cases a.suppliesControlled <;> rfl
      | cons d ds ih =>
        obtain ⟨ih1, ih2, ih3⟩ := ih
        rcases d with - | - | -
        all_goals
          cases a
          rename_i U bs
          cases bs
        all_goals
          simp [compileAccessWord, compiledCallTotals, compileAccess,
            CompiledAccess.callCounts] at ih1 ih2 ih3 ⊢
        all_goals omega
  · refine ⟨?_, ?_, ?_⟩
    · intro O I _ _ q entries bits
      exact ⟨⟨QuantizedMatrixInput.readBitCost q, derivedQuantityBitCost entries bits⟩,
        rfl, rfl⟩
    · intro O I _ _ q hO hI
      show 0 < Fintype.card O * Fintype.card I * (2 * (q.bits + 1))
      exact mul_pos (mul_pos hO hI) (Nat.mul_pos two_pos (Nat.succ_pos _))
    · intro entries bits _
      show 0 < (entries + 1) * 4 * (bits + 1) ^ 3
      positivity

theorem thresholdGoal_quantization_conjunct_refutable :
    ¬ (∀ (k : ℕ) (x : ℝ),
        0 ≤ realQuantizeSlack k x ∧ realQuantizeSlack k x < (1 / 2 : ℝ) ^ k ∧
          0 < realQuantizeBits k) := by
  intro hall
  have hs : realQuantizeSlack 0 (-1) = -1 := by
    rw [realQuantizeSlack, realQuantize]
    have hle : (2 : ℝ) ^ 0 * (-1 : ℝ) ≤ 0 := by norm_num
    rw [dyadicRat, Nat.floor_of_nonpos hle]
    norm_num
  have h := (hall 0 (-1)).1
  rw [hs] at h
  norm_num at h

theorem thresholdGoal_complexQuantize_refutable :
    ¬ (∀ (d : ℕ) (z : ℂ), ‖z - complexQuantize d z‖ ≤ Real.sqrt 2 * (1 / 2 : ℝ) ^ d) := by
  intro hall
  have hdre : dyadicRat 3 ((-100 : ℝ) : ℂ).re = 0 := by
    rw [dyadicRat]
    have hle : (2 : ℝ) ^ 3 * ((-100 : ℝ) : ℂ).re ≤ 0 := by rw [Complex.ofReal_re]; norm_num
    rw [Nat.floor_of_nonpos hle]
    norm_num
  have hdim : dyadicRat 3 ((-100 : ℝ) : ℂ).im = 0 := by
    rw [dyadicRat]
    have hle : (2 : ℝ) ^ 3 * ((-100 : ℝ) : ℂ).im ≤ 0 := by rw [Complex.ofReal_im]; norm_num
    rw [Nat.floor_of_nonpos hle]
    norm_num
  have hz : complexQuantize 3 ((-100 : ℝ) : ℂ) = 0 := by
    show (dyadicRat 3 ((-100 : ℝ) : ℂ).re : ℂ) +
      (dyadicRat 3 ((-100 : ℝ) : ℂ).im : ℂ) * Complex.I = 0
    rw [hdre, hdim]
    norm_num
  have h := hall 3 ((-100 : ℝ) : ℂ)
  rw [hz] at h
  have hcalc : (‖((-100 : ℝ) : ℂ) - 0‖ : ℝ) = 100 := by simp
  rw [hcalc] at h
  have h2 : Real.sqrt 2 ≤ 2 := by
    have h3 := Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 4)
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at h3
    exact h3
  nlinarith

open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

theorem not_thresholdGoal : ¬ (

  (∀ (k : ℕ) (x : ℝ),
    0 ≤ realQuantizeSlack k x ∧ realQuantizeSlack k x < (1 / 2 : ℝ) ^ k ∧
      0 < realQuantizeBits k) ∧

  (∃ A : AngleFinder, A.Correct) ∧

  (∃ P : PhaseInverse, P.Correct) ∧

  ((∀ (d : ℕ) (z : ℂ), ‖z - complexQuantize d z‖ ≤ Real.sqrt 2 * (1 / 2 : ℝ) ^ d) ∧
    (∀ (D : ℕ) (v : Fin D → ℂ) (d : ℕ) (i : Fin D),
      ‖v i - complexQuantize d (v i)‖ ≤ Real.sqrt 2 * (1 / 2 : ℝ) ^ d) ∧
    (∀ (R C : Type) [Fintype R] [Fintype C] (F : Matrix R C ℂ) (d : ℕ),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F →
        ‖Matrix.conjTranspose (quantizeFrame d F) * quantizeFrame d F - 1‖ ≤
          frameGramDefect (Fintype.card R) (Fintype.card C) d) ∧
    (∀ D : ℕ, 0 < D → ∃ p : PrepareParameter, p.Reliable D)) ∧

  ((∀ (d x : ℚ) (k : ℕ), 0 < d →
      (rationalHHLGamma d x : ℝ) = uniformHHLGamma d x ∧
        rationalHHLRotation d x k ∈ Matrix.unitaryGroup Bool ℂ ∧
        ‖rationalHHLRotation d x k - uniformHHLRotation d x‖ ≤ 32 / 2 ^ k ∧
        rationalHHLRotation d 0 k = 1) ∧
    (∀ (Y : Type) [Fintype Y] [DecidableEq Y] (decode : Y → ℚ) (d : ℚ) (k : ℕ),
      0 < d → layeredResultRotation decode d k ∈ Matrix.unitaryGroup (Y × Bool) ℂ) ∧
    (∀ (d : ℚ) (k : ℕ), 0 < d → resultRotation d 0 k = 1)) ∧

  (∃ G : UniformFixedGate, G.Correct ∧ G.Uniform) ∧

  ((∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A : Matrix O I ℂ) (s : ℝ), 0 < s →
      (∀ o : O, (∑ i, ‖A o i‖) ≤ s) → (∀ i : I, (∑ o, ‖A o i‖) ≤ s) →
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (sparseOverlapLeft A s) ∧
        Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (sparseOverlapRight A s) ∧
        Matrix.conjTranspose (sparseOverlapLeft A s) * sparseOverlapRight A s =
          (s : ℂ)⁻¹ • A) ∧
    (∀ (O I : Type) (n : ℕ) (d : SparseOracleData O I),
      let L := sparsePipelineLedger d (twoQueryPipeline n)
      L.positionCalls = 1 ∧ L.valueCalls = 1 ∧
        L.elementaryGates = d.rowCallGates + d.valueCallGates ∧
        L.classicalBitOps = d.arithBits ∧
        L.forwardCalls = 0 ∧ L.backwardCalls = 0 ∧ L.controlledCalls = 0) ∧
    (∀ (O I : Type) (d : SparseOracleData O I),
      ∃ e : TwoQueryEncoding O I, e.data = d ∧ e.Correct ∧ e.queryCount = 2) ∧
    (∀ (n m : ℕ) (e : Fin m ↪ Reg n) (F : Matrix (Reg n) (Fin m) ℂ),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F →
        ∃ gs : List (ReflectionGate (n + (n + 1))), reflectionLegal gs ∧
          gs.length ≤ continuousSynthesisGateBound n ∧
          ∀ ψ : QState (Fin m),
            Run 1 (reflectionCompile gs)
                (knownFrameEmbed n (Matrix.mulVec (coordinateKnownFrame n m e) ψ)) =
              knownFrameEmbed n (Matrix.mulVec F ψ)))
) := by
  intro h
  exact thresholdGoal_quantization_conjunct_refutable h.1

end Qatlib.Concepts.RiskEstimation.PopulationGap
