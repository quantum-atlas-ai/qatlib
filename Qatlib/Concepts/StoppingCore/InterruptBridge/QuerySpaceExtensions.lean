/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensionsDefs

/-!
# Query-space transport laws and counterexamples

This module proves oracle simulation, clean-ancilla transport, observed stopping laws,
positive-cost termination, and truncated search polynomial representation. The combined theorem
`g2` records the Boolean/value-oracle correspondences and phase/bit simulations with resource
ledgers.

It also supplies explicit counterexamples to an unrestricted hybrid bound and an adversary
transport claim lacking normalized input. The circuit, measurement, and phase-oracle background
follows [NielsenChuang2010]; the finite-query polynomial viewpoint is developed in
[BealsEtAl2001].

## Main statements

* `g2`: oracle correspondences and ledger-aware simulations
* `bridgePolynomialTransport_fixed`: adaptive purification and a degree-bounded acceptance
  polynomial
* `clause3_false`: failure of the combined specification containing the unrestricted hybrid
  bound
* `clause1_false`: failure of the combined specification containing unnormalized adversary
  transport

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.StoppingCore.InterruptBridge

set_option autoImplicit false

open Matrix

open scoped Matrix.Norms.L2Operator ENNReal BigOperators

/-- Applying a matrix gate commutes with complex scalar multiplication of a state. -/
lemma applyGate_smul {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    ApplyGate U (c • ψ) = c • ApplyGate U ψ := by
  simp [ApplyGate, Matrix.mulVec_smul]

/-- Circuit execution commutes with complex scalar multiplication of the input state. -/
lemma run_smul {I : Type} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ) (c : ℂ) :
    ∀ (C : Circuit I) (ψ : QState I), Run oracle C (c • ψ) = c • Run oracle C ψ := by
  intro C
  induction C with
  | nil => intro ψ; rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      intro ψ
      show Run oracle C (ApplyGate U (c • ψ)) = c • Run oracle C (ApplyGate U ψ)
      rw [applyGate_smul, ih]
    | query =>
      intro ψ
      show Run oracle C (ApplyGate oracle (c • ψ)) = c • Run oracle C (ApplyGate oracle ψ)
      rw [applyGate_smul, ih]

/-- Scaling a state by `c` scales every measurement event mass by `‖c‖ ^ 2`. -/
lemma measureProb_smul {I : Type} [Fintype I] [DecidableEq I]
    (c : ℂ) (ψ : QState I) (S : Finset I) :
    MeasureProb (c • ψ) S = ‖c‖ ^ 2 * MeasureProb ψ S := by
  unfold MeasureProb BornProb
  conv_lhs => simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  have h : ∀ x : I, (‖c‖ * ‖ψ x‖) ^ 2 = ‖c‖ ^ 2 * ‖ψ x‖ ^ 2 := by
    intro x
    ring
  conv_lhs => simp only [h]
  rw [Finset.mul_sum]

/-- The measurement mass of the empty event is zero. -/
lemma measureProb_empty {I : Type} [Fintype I] [DecidableEq I] (ψ : QState I) :
    MeasureProb ψ ∅ = 0 := by
  simp [MeasureProb]

/-- The constantly false phase oracle is the identity matrix. -/
lemma phaseOracle_false_eq_one {I : Type} [Fintype I] [DecidableEq I] :
    PhaseOracle (fun _ => false) = (1 : Matrix I I ℂ) := by
  rw [PhaseOracle, show (fun _ : I => if false then (-1 : ℂ) else 1) = (fun _ => (1 : ℂ)) by
    funext i; simp, Matrix.diagonal_one]

/-- The constantly true phase oracle is the negative identity matrix. -/
lemma phaseOracle_true_eq_neg_one {I : Type} [Fintype I] [DecidableEq I] :
    PhaseOracle (fun _ => true) = (-1 : Matrix I I ℂ) := by
  rw [PhaseOracle, show (fun _ : I => if true then (-1 : ℂ) else 1) = (fun _ => (-1 : ℂ)) by
    funext i; simp]
  ext i j
  show (if i = j then (-1 : ℂ) else 0) = (-1 : Matrix I I ℂ) i j
  rw [Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-- Applying the constantly true phase oracle multiplies the state by minus one. -/
lemma applyGate_phaseOracle_true {I : Type} [Fintype I] [DecidableEq I] (ψ : QState I) :
    ApplyGate (PhaseOracle (fun _ => true)) ψ = (-1 : ℂ) • ψ := by
  funext x
  rw [applyGate_phaseOracle]
  simp

/-- Applying the constantly false phase oracle leaves the state unchanged. -/
lemma applyGate_phaseOracle_false {I : Type} [Fintype I] [DecidableEq I] (ψ : QState I) :
    ApplyGate (PhaseOracle (fun _ => false)) ψ = ψ := by
  rw [phaseOracle_false_eq_one, applyGate_one]

/-- Runs with the two constant phase oracles differ by the global factor `(-1) ^ QueryCount C`. -/
lemma run_phaseOracle_const {I : Type} [Fintype I] [DecidableEq I] :
    ∀ (C : Circuit I) (ψ : QState I),
      Run (PhaseOracle (fun _ => true)) C ψ =
        (-1 : ℂ) ^ QueryCount C • Run (PhaseOracle (fun _ => false)) C ψ := by
  intro C
  induction C with
  | nil => intro ψ; simp
  | cons s C ih =>
    cases s with
    | gate U =>
      intro ψ
      show Run (PhaseOracle (fun _ => true)) C (ApplyGate U ψ) =
        (-1 : ℂ) ^ QueryCount (Step.gate U :: C) •
          Run (PhaseOracle (fun _ => false)) C (ApplyGate U ψ)
      rw [ih, show QueryCount (Step.gate U :: C) = QueryCount C from rfl]
    | query =>
      intro ψ
      show Run (PhaseOracle (fun _ => true)) C (ApplyGate (PhaseOracle (fun _ => true)) ψ) =
        (-1 : ℂ) ^ QueryCount (Step.query :: C) •
          Run (PhaseOracle (fun _ => false)) C (ApplyGate (PhaseOracle (fun _ => false)) ψ)
      rw [applyGate_phaseOracle_true, applyGate_phaseOracle_false,
        show QueryCount (Step.query :: C) = QueryCount C + 1 from rfl, pow_succ, mul_smul,
        ih, run_smul]

/-- The two constant phase oracles give identical measurement probabilities in every fixed
circuit. -/
lemma phaseConstantUnidentifiable_fixed {I : Type} [Fintype I] [DecidableEq I] :
    phaseConstantUnidentifiable (I := I) := by
  intro C ψ S
  rw [run_phaseOracle_const, measureProb_smul]
  have h : ‖((-1 : ℂ) ^ QueryCount C)‖ ^ 2 = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow, one_pow]
  rw [h, one_mul]

/-- The answer bit after a bit-oracle action is the XOR of the initial bit and `f x`. -/
lemma bitAction_snd {I : Type} [Fintype I] [DecidableEq I] (f : I → Bool) (x : I) (b : Bool) :
    (bitAction f (x, b)).2 = (b ^^ f x) := rfl

/-- The answer value after an additive oracle action is `z + g x`. -/
lemma valueAction_snd {I : Type} [Fintype I] [DecidableEq I] {R : Type} [AddGroup R]
    (g : I → R) (x : I) (z : R) :
    (valueAction g (x, z)).2 = z + g x := rfl

/-- Adding one to itself in `ZMod 2` gives zero. -/
lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 :=
  eq_neg_iff_add_eq_zero.mp (ZMod.neg_eq_self_mod_two (1 : ZMod 2)).symm

/-- One and zero are distinct in `ZMod 2`. -/
lemma zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by norm_num

/-- The Boolean-to-`ZMod 2` encoding turns XOR with `f x` into addition of its encoded value. -/
lemma boolToZMod_xor {I : Type} [Fintype I] [DecidableEq I] (f : I → Bool) (x : I) (b : Bool) :
    boolToZMod (b ^^ f x) =
      boolToZMod b + (if f x then (1 : ZMod 2) else 0) := by
  cases hf : f x <;> cases hb : b <;> simp [boolToZMod, Bool.xor, zmod2_one_add_one]

/-- The zero-one encoding of `f x` equals `boolToZMod b` exactly when `f x = b`. -/
lemma value_action_eq_iff {I : Type} [Fintype I] [DecidableEq I] (f : I → Bool) (x : I) (b : Bool) :
    (if f x then (1 : ZMod 2) else 0) = boolToZMod b ↔ f x = b := by
  cases hf : f x <;> cases hb : b <;> simp [boolToZMod]

/-- Bit-oracle actions and additive `ZMod 2` oracle actions agree under the Boolean encoding. -/
lemma bitAction_unify {I : Type} [Fintype I] [DecidableEq I] (f : I → Bool) :
    bitValueActionsUnify f := by
  intro x b
  simp only [bitAction_snd]
  rw [boolToZMod_xor]
  simp only [valueAction_snd]

/-- The squared complex norm of `1 / sqrt 2` equals one half. -/
lemma norm_one_div_sqrt_two : ‖((1 : ℂ) / (Real.sqrt 2 : ℂ))‖ ^ 2 = 1 / 2 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt h2
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), div_pow, one_pow, hs]

/-- The squared amplitudes of `spanPlus x y` are one on the coincident basis state, or one half
on each of two distinct basis states, and zero elsewhere. -/
lemma spanPlus_normSq {I : Type} [Fintype I] [DecidableEq I] (x y : I) (z : I) :
    ‖spanPlus x y z‖ ^ 2 =
      if z = x then (if x = y then (1 : ℝ) else 1 / 2)
      else if z = y then 1 / 2 else 0 := by
  unfold spanPlus
  by_cases hzx : z = x
  · by_cases hxy : x = y <;> simp [hzx, hxy]
  · by_cases hzy : z = y
    · subst z
      simp [hzx]
    · simp [hzx, hzy]

/-- The state `spanPlus x y` is normalized, including when its two indices coincide. -/
lemma spanPlus_normalized {I : Type} [Fintype I] [DecidableEq I] (x y : I) :
    Normalized (spanPlus x y) := by
  unfold Normalized
  by_cases hxy : x = y
  · subst y
    rw [show (fun z : I => ‖spanPlus x x z‖ ^ 2) = (fun z : I => ‖Qatlib.Foundations.PureStateMath.Ket x z‖ ^ 2) by
        funext z
        rw [spanPlus_normSq]
        by_cases hz : z = x <;> simp [hz, Qatlib.Foundations.PureStateMath.Ket]]
    exact normalized_ket x
  · rw [show (∑ z : I, ‖spanPlus x y z‖ ^ 2) =
        (∑ z : I, ((if z = x then (1/2 : ℝ) else 0) + (if z = y then (1/2 : ℝ) else 0))) by
        apply Finset.sum_congr rfl
        intro z _
        rw [spanPlus_normSq]
        by_cases hzx : z = x
        · simp [hzx, hxy]
        · by_cases hzy : z = y
          · subst z
            simp [hzx]
          · simp [hzx, hzy]]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    norm_num

/-- Measuring `spanPlus x y` over the full basis has total probability one. -/
lemma spanPlus_measureProb_univ {I : Type} [Fintype I] [DecidableEq I] (x y : I) :
    MeasureProb (spanPlus x y) Finset.univ = 1 :=
  measureProb_univ (spanPlus_normalized x y)

/-- A known false baseline enables exact extraction of `f x` using a unitary circuit with at
most one phase query. -/
lemma baselineExtractsBit_fixed {I : Type} [Fintype I] [DecidableEq I] :
    ∀ (f : I → Bool) (x xstar : I), baselineExtractsBit f x xstar := by
  intro f x xstar hstar
  by_cases hx : f x = false
  · refine ⟨[], Finset.univ, ?_, isUnitaryCircuit_nil, ?_, ?_⟩
    · simp [QueryCount]
    · intro _
      simpa using spanPlus_measureProb_univ x xstar
    · intro htrue
      simp [hx] at htrue
  · refine ⟨[], ∅, ?_, isUnitaryCircuit_nil, ?_, ?_⟩
    · simp [QueryCount]
    · intro hfalse
      exact absurd hfalse hx
    · intro _
      exact measureProb_empty _

/-- For error below one half, a fixed circuit cannot distinguish the two constant phase oracles
using the specified event thresholds. -/
lemma noBaselinePhaseToBit_fixed {I : Type} [Fintype I] [DecidableEq I] (ε : ℝ)
    (_hε0 : 0 ≤ ε) (hε : ε < 1 / 2) : noBaselinePhaseToBit (I := I) ε := by
  intro C ψ S _
  rintro ⟨hlo, hhi⟩
  have heq := phaseConstantUnidentifiable_fixed (I := I) C ψ S
  have h : 1 - ε ≤ ε := le_trans hlo (heq.symm ▸ hhi)
  linarith

/-- The access charge is the total access count times the sum of address bits and per-access
charge. -/
lemma accessCharge_eq (L : AccessLedger) :
    L.accessCharge = L.totalAccesses * (L.addressBits + L.perAccessCharge) := rfl

/-- Every oracle and ledger satisfy the charged capability law under the honesty condition. -/
lemma chargedCapabilityLaw_fixed {I : Type} [Fintype I] [DecidableEq I] :
    ∀ (U : Matrix I I ℂ) (L : AccessLedger), chargedCapabilityLaw U L := by
  intro U L h
  refine ⟨accessCharge_eq L, ?_, ?_⟩
  · rcases h.1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1.2.2
  · rcases h.2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr h2.2.2

/-- Every workspace bit-oracle circuit possesses a simulation using the workspace phase oracle
with the specified gate overhead and access ledgers. -/
lemma bitToPhaseSimulation_fixed {I : Type} [Fintype I] [DecidableEq I] :
    ∀ (W : Type) [Fintype W] [DecidableEq W] (f : I → Bool)
      (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)),
      ∃ (source target : AccessLedger), bitToPhaseSimulation f C ψ source target := by
  intro W _ _ f C ψ
  refine ⟨
    { forwardAccesses := QueryCount C, controlledAccesses := 0, inverseAccesses := 0,
      addressBits := 0, perAccessCharge := 0, fixedGates := GateCount C },
    { forwardAccesses := QueryCount C, controlledAccesses := 0, inverseAccesses := 0,
      addressBits := 0, perAccessCharge := 0,
      fixedGates := GateCount C + 2 * QueryCount C }, ?_⟩
  refine ⟨?_, ?_, ?_, accessCharge_eq _, accessCharge_eq _, rfl, rfl, rfl, rfl, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨bitToPhaseCircuitSameInput C, bitToPhaseCircuitSameInput_queryCount C,
      bitToPhaseCircuitSameInput_gateCount C, ?_, ?_⟩
    · exact bitToPhaseCircuitSameInput_isUnitaryCircuit C
    · intro S
      exact measureProb_bitToPhaseCircuitSameInput f C ψ S

/-- Every phase-oracle circuit possesses a lifted bit-oracle simulation with a `Minus` ancilla
and the specified access ledgers. -/
lemma phaseToBitSimulation_fixed {I : Type} [Fintype I] [DecidableEq I] :
    ∀ (f : I → Bool) (C : Circuit I) (ψ : QState I),
      ∃ (source target : AccessLedger), phaseToBitSimulation f C ψ source target := by
  intro f C ψ
  refine ⟨
    { forwardAccesses := QueryCount C, controlledAccesses := 0, inverseAccesses := 0,
      addressBits := 0, perAccessCharge := 0, fixedGates := GateCount C },
    { forwardAccesses := QueryCount C, controlledAccesses := 0, inverseAccesses := 0,
      addressBits := 1, perAccessCharge := 0, fixedGates := GateCount C }, ?_⟩
  refine ⟨?_, ?_, ?_, accessCharge_eq _, accessCharge_eq _, rfl, rfl, rfl, rfl, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨LiftCircuitTo Bool C, rfl, ?_, ?_, ?_⟩
    · exact queryCount_liftCircuitTo Bool C
    · exact gateCount_liftCircuitTo Bool C
    · intro S
      have h := measureProb_run_liftCircuit_bitOracleOn f C ψ S
      rw [liftCircuitTo_bool]
      exact h

/-- The XOR of two Booleans is false exactly when the second equals the first. -/
lemma xor_false_iff {b c : Bool} : (b ^^ c) = false ↔ c = b := by
  cases b <;> cases c <;> simp [Bool.xor]

/-- A single bit query from a false answer register gives answer probability equal to the input
mass on the corresponding fiber of `f`. -/
lemma marginal_right_bitOracleOn_query {I : Type} [Fintype I] [DecidableEq I]
    (f : I → Bool) (ψ : QState I) (b : Bool) :
    MarginalProbRight (Run (BitOracleOn f) [Step.query] (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false)))
        ({b} : Finset Bool) =
      MeasureProb ψ (Finset.univ.filter fun x => f x = b) := by
  unfold MarginalProbRight MeasureProb
  simp only [run_query, run_nil]
  rw [Finset.sum_product]
  have hinner : ∀ x : I,
      (∑ y ∈ ({b} : Finset Bool),
        BornProb (ApplyGate (BitOracleOn f) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false))) (x, y))
        = BornProb (ApplyGate (BitOracleOn f) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false))) (x, b) := by
    intro x
    simp
  conv_lhs => simp only [hinner]
  have hamp : ∀ x : I,
      BornProb (ApplyGate (BitOracleOn f) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false))) (x, b)
        = if f x = b then BornProb ψ x else 0 := by
    intro x
    unfold BornProb
    rw [applyGate_bitOracleOn]
    simp only [TensorState, BitFlip, Qatlib.Foundations.PureStateMath.Ket]
    by_cases h : (b ^^ f x) = false
    · rw [ite_eq_left h, mul_one, ite_eq_left (xor_false_iff.mp h)]
    · have hn : ¬ (f x = b) := fun he => h (xor_false_iff.mpr he)
      rw [ite_eq_right h, mul_zero, norm_zero, ite_eq_right hn]
      simp
  conv_lhs => simp only [hamp]
  show (∑ x ∈ Finset.univ, if f x = b then BornProb ψ x else 0) = _
  rw [← Finset.sum_filter]

/-- The additive `ZMod 2` and Boolean bit-oracle answer-register readouts have equal
probabilities under the Boolean encoding. -/
lemma valueBitReadoutUnify_fixed {I : Type} [Fintype I] [DecidableEq I] (f : I → Bool) :
    valueBitReadoutUnify f := by
  intro ψ b
  have hL := marginalProbRight_run_addOracle_zero
    (fun x : I => if f x then (1 : ZMod 2) else 0) ψ ({boolToZMod b} : Finset (ZMod 2))
  have hconv : (Finset.univ.filter fun x : I =>
        (if f x then (1 : ZMod 2) else 0) ∈ ({boolToZMod b} : Finset (ZMod 2))) =
      Finset.univ.filter fun x : I => f x = b := by
    apply Finset.filter_congr
    intro x _
    have hmem : ((if f x then (1 : ZMod 2) else 0) ∈ ({boolToZMod b} : Finset (ZMod 2)))
        ↔ (if f x then (1 : ZMod 2) else 0) = boolToZMod b := by
      simp
    rw [hmem]
    exact value_action_eq_iff f x b
  rw [hL, hconv, marginal_right_bitOracleOn_query]

/-- Bit and additive Boolean oracles have matching actions and readouts, and both phase/bit
simulation directions possess resource ledgers. Constant phase oracles are
indistinguishable, a false baseline enables bit extraction, and honest capabilities satisfy
the charge law. -/
theorem g2 :
    ∀ (I : Type) [Fintype I] [DecidableEq I],
      (∀ f : I → Bool, bitValueActionsUnify f ∧ valueBitReadoutUnify f) ∧
      (∀ (W : Type) [Fintype W] [DecidableEq W] (f : I → Bool)
          (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)),
        ∃ (source target : AccessLedger), bitToPhaseSimulation f C ψ source target) ∧
      (∀ (f : I → Bool) (C : Circuit I) (ψ : QState I),
        ∃ (source target : AccessLedger), phaseToBitSimulation f C ψ source target) ∧
      phaseConstantUnidentifiable (I := I) ∧
      (∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 → noBaselinePhaseToBit (I := I) ε) ∧
      (∀ (f : I → Bool) (x xstar : I), baselineExtractsBit f x xstar) ∧
      (∀ (U : Matrix I I ℂ) (L : AccessLedger), chargedCapabilityLaw U L) := by
  intro I _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact ⟨bitAction_unify f, valueBitReadoutUnify_fixed f⟩
  · intro W _ _ f C ψ
    exact bitToPhaseSimulation_fixed W f C ψ
  · intro f C ψ
    exact phaseToBitSimulation_fixed f C ψ
  · exact phaseConstantUnidentifiable_fixed
  · intro ε hε0 hε
    exact noBaselinePhaseToBit_fixed ε hε0 hε
  · intro f x xstar
    exact baselineExtractsBit_fixed f x xstar
  · intro U L
    exact chargedCapabilityLaw_fixed U L

/-- Every finite observed circuit satisfies the acceptance split, exact query truncation, and
expected-query tail bound in `stopJointLaw`. -/
lemma stopJointLaw_fixed {I : Type} [Fintype I] [DecidableEq I] :
    ∀ (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I), stopJointLaw O P ψ := by
  intro O P ψ K
  refine ⟨?_, ?_, observedQueries_tail_mul_le O P ψ K⟩
  · have hsplit := observedEventMass_split O P ψ (fun t : BranchTrace I => t.accepted)
      (fun t => decide (t.queries ≤ K))
    have hacc : observedEventMass O P ψ (fun t : BranchTrace I => t.accepted)
        = observedAcceptance O P ψ := observedEventMass_accepted O P ψ
    have hnot : (fun t : BranchTrace I => t.accepted && !decide (t.queries ≤ K))
        = acceptedBeyond K := by
      funext t
      simp only [acceptedBeyond]
      by_cases hk : K < t.queries
      · simp [hk, Nat.not_le.mpr hk]
      · have h : t.queries ≤ K := Nat.le_of_not_gt hk
        simp [h, hk]
    rw [← hacc, hsplit, hnot]
    rfl
  · exact observedAcceptance_truncate_eq O P ψ K

/-- Strictly positive state costs and finite expected weighted cost force zero nontermination
mass. -/
lemma positiveCharge_finiteCost_noNontermination {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (RandomizedExecution.Configuration S O))
    (c : S → ℕ) (cfg : RandomizedExecution.Configuration S O)
    (hc : positiveCharge c) (h : weightedExpectedCost next c cfg < ⊤) :
    neverStopMass next cfg = 0 :=
  weightedExpectedCost_finite_nontermination next c cfg
    (fun s => Nat.succ_le_iff.mpr (hc s)) h

/-- The event mass of halted configurations is the sum of their output-cost point masses. -/
lemma event_inl_eq_tsum {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (p : CostedLaw (RandomizedExecution.Configuration S O)) :
    CostedLaw.event p (fun x => ∃ a, x.1 = Sum.inl a) =
      ∑' o : O, ∑' k : ℕ, p (Sum.inl o, k) := by
  unfold CostedLaw.event CostedLaw.expectation
  rw [tsum_prod_type', tsum_sum_type']
  simp

/-- Finite halted and pending masses sum to one, and the never-stop mass is the infimum of
pending masses. -/
lemma stopTailNeverJointLaw_fixed {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (RandomizedExecution.Configuration S O))
    (cfg : RandomizedExecution.Configuration S O) : stopTailNeverJointLaw next cfg := by
  intro n
  refine ⟨?_, rfl⟩
  show haltedMassWithin next n cfg + pendingMass next cfg n = 1
  rw [pendingMass_eq_finiteSurvival]
  unfold haltedMassWithin
  have hs : finiteSurvival next n cfg =
      CostedLaw.event (RandomizedExecution.runFor next n cfg)
        (fun x => ∃ s, x.1 = Sum.inr s) := rfl
  rw [hs, event_inl_eq_tsum]
  exact weighted_law_halt_pending_partition (RandomizedExecution.runFor next n cfg)

/-- The deterministic singleton self-loop survives every finite number of steps with mass one. -/
lemma finiteSurvival_zeno :
    ∀ n : ℕ, finiteSurvival zenoNext n (Sum.inr PUnit.unit) = 1 := by
  intro n
  induction n with
  | zero => exact finiteSurvival_zero_running zenoNext PUnit.unit
  | succ n ih =>
    rw [finiteSurvival_succ_running]
    show CostedLaw.expectation (zenoNext PUnit.unit)
      (fun cfg => finiteSurvival zenoNext n cfg) = 1
    simp only [zenoNext]
    rw [CostedLaw.expectation_pure]
    exact ih

/-- The pending mass of the deterministic singleton self-loop is one at every finite fuel. -/
lemma pendingMass_zeno (n : ℕ) :
    pendingMass zenoNext (Sum.inr PUnit.unit) n = 1 := by
  rw [pendingMass_eq_finiteSurvival]
  exact finiteSurvival_zeno n

/-- The singleton self-loop with zero costs has positive nontermination mass and zero expected
weighted cost. -/
lemma zenoZeroCharge_fixed : zenoZeroCharge zenoNext zenoCharge PUnit.unit := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rfl
  · show 0 < neverStopMass zenoNext (Sum.inr PUnit.unit)
    show 0 < (⨅ k : ℕ, pendingMass zenoNext (Sum.inr PUnit.unit) k)
    simp only [pendingMass_zeno]
    simp
  · show weightedExpectedCost zenoNext zenoCharge (Sum.inr PUnit.unit) = 0
    unfold weightedExpectedCost
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    unfold weightedOccupation
    apply Finset.sum_eq_zero
    intro s _
    simp [zenoCharge]

/-- Unbounded search acceptance is one when some input value is true. -/
lemma unboundedSearchAcceptance_of_exists (f : ℕ → Bool) (h : ∃ k, f k = true) :
    unboundedSearchAcceptance f = 1 := by
  classical
  simp [unboundedSearchAcceptance, h]

/-- Unbounded search acceptance is zero when every input value differs from true. -/
lemma unboundedSearchAcceptance_of_forall (f : ℕ → Bool) (h : ∀ k, f k ≠ true) :
    unboundedSearchAcceptance f = 0 := by
  classical
  have hne : ¬∃ k, f k = true := fun ⟨k, hk⟩ => h k hk
  simp [unboundedSearchAcceptance, hne]

/-- The polynomial `1 - ∏ k < K, (1 - X k)` has total degree at most `K`. -/
lemma truncatedSearchPoly_degree (K : ℕ) :
    ((1 - ∏ k ∈ Finset.range K, (1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)) :
      MvPolynomial ℕ ℝ).totalDegree ≤ K := by
  have hfac : ∀ k ∈ Finset.range K,
      ((1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)).totalDegree ≤ 1 := by
    intro k _
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X, Nat.zero_max]
  have hprod : (∏ k ∈ Finset.range K, (1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)).totalDegree
      ≤ ∑ k ∈ Finset.range K, (1 - MvPolynomial.X k : MvPolynomial ℕ ℝ).totalDegree :=
    MvPolynomial.totalDegree_finsetProd _ _
  have hsum : ∑ k ∈ Finset.range K, (1 - MvPolynomial.X k : MvPolynomial ℕ ℝ).totalDegree
      ≤ K := by
    calc ∑ k ∈ Finset.range K, (1 - MvPolynomial.X k : MvPolynomial ℕ ℝ).totalDegree
        ≤ ∑ k ∈ Finset.range K, (1 : ℕ) := Finset.sum_le_sum hfac
      _ = K := by simp
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [MvPolynomial.totalDegree_one, Nat.zero_max]
  exact hprod.trans hsum

/-- Each variable has degree at most one in `1 - ∏ k < K, (1 - X k)`. -/
lemma truncatedSearchPoly_degreeOf (K : ℕ) (i : ℕ) :
    ((1 - ∏ k ∈ Finset.range K, (1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)) :
      MvPolynomial ℕ ℝ).degreeOf i ≤ 1 := by
  have hfac : ∀ k, ((1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)).degreeOf i
      ≤ (if i = k then (1 : ℕ) else 0) := by
    intro k
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans ?_
    rw [MvPolynomial.degreeOf_one, MvPolynomial.degreeOf_X, Nat.zero_max]
  have hprod : (∏ k ∈ Finset.range K, (1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)).degreeOf i
      ≤ ∑ k ∈ Finset.range K, ((1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)).degreeOf i :=
    MvPolynomial.degreeOf_prod_le _ _ _
  have hsum : ∑ k ∈ Finset.range K, ((1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)).degreeOf i
      ≤ 1 := by
    calc ∑ k ∈ Finset.range K, ((1 - MvPolynomial.X k : MvPolynomial ℕ ℝ)).degreeOf i
        ≤ ∑ k ∈ Finset.range K, (if i = k then (1 : ℕ) else 0) :=
          Finset.sum_le_sum fun k _ => hfac k
      _ = if i ∈ Finset.range K then (1 : ℕ) else 0 := by simp
      _ ≤ 1 := by split_ifs <;> omega
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_one, Nat.zero_max]
  exact hprod.trans hsum

/-- Search acceptance over the first `K` indices is one when one of those indices has value
true. -/
lemma truncatedSearchAcceptance_pos (K : ℕ) (f : ℕ → Bool) (h : ∃ k, k < K ∧ f k = true) :
    truncatedSearchAcceptance K f = 1 := by
  simp [truncatedSearchAcceptance, h]

/-- Search acceptance over the first `K` indices is zero when none has value true. -/
lemma truncatedSearchAcceptance_neg (K : ℕ) (f : ℕ → Bool) (h : ¬∃ k, k < K ∧ f k = true) :
    truncatedSearchAcceptance K f = 0 := by
  simp [truncatedSearchAcceptance, h]

/-- Truncated search possesses a multilinear polynomial representation of total degree at most
`K`. -/
lemma truncatedSearchPolyRep_fixed (K : ℕ) : truncatedSearchPolyRep K := by
  classical
  set q : MvPolynomial ℕ ℝ := 1 - ∏ k ∈ Finset.range K, (1 - MvPolynomial.X k) with hq
  have hqdegree : q.totalDegree ≤ K := by rw [hq]; exact truncatedSearchPoly_degree K
  have hqdegreeOf : ∀ i, q.degreeOf i ≤ 1 := by
    intro i
    rw [hq]
    exact truncatedSearchPoly_degreeOf K i
  refine ⟨q, hqdegree, ?_, fun f => ?_⟩
  · intro c hc i
    refine (MvPolynomial.le_degreeOf_of_mem_support i ?_).trans (hqdegreeOf i)
    exact MvPolynomial.mem_support_iff.mpr hc
  · have hqev : MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0) q
        = 1 - ∏ k ∈ Finset.range K, (1 - (if f k then (1 : ℝ) else 0)) := by
      rw [hq]
      simp only [map_sub, map_one, map_prod, MvPolynomial.eval_X]
    rw [hqev]
    by_cases hex : ∃ k, k < K ∧ f k = true
    · obtain ⟨k, hk, hf⟩ := hex
      have hfac : (1 - (if f k then (1 : ℝ) else 0)) = 0 := by simp [hf]
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr hk) hfac, sub_zero,
        truncatedSearchAcceptance_pos K f ⟨k, hk, hf⟩]
    · have hall : ∀ k ∈ Finset.range K,
          (1 - (if f k then (1 : ℝ) else 0)) = (1 : ℝ) := by
        intro k hk
        by_cases hf : f k = true
        · exact absurd ⟨k, Finset.mem_range.mp hk, hf⟩ hex
        · simp [hf]
      rw [Finset.prod_eq_one hall, sub_self,
        truncatedSearchAcceptance_neg K f hex]

/-- No multilinear polynomial in countably many variables represents unbounded search acceptance
on all Boolean inputs. -/
lemma noUnconditionalPolyRep_fixed : noUnconditionalPolyRep := by
  classical
  rintro ⟨p, hmulti, he⟩
  set s : Finset ℕ := p.support.biUnion (fun d => d.support) with hs
  set N : ℕ := s.sup (fun i => i + 1) with hN
  have hNs : ∀ d ∈ p.support, ∀ i ∈ d.support, i < N := by
    intro d hd i hi
    have hiS : i ∈ s := by rw [hs]; exact Finset.mem_biUnion.mpr ⟨d, hd, hi⟩
    have hle : i + 1 ≤ s.sup (fun i => i + 1) := Finset.le_sup hiS
    omega
  have heq : MvPolynomial.eval (fun _ : ℕ => (0 : ℝ)) p
      = MvPolynomial.eval (fun i : ℕ => if i = N then (1 : ℝ) else 0) p := by
    rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases hd0 : d = 0
    · subst hd0
      simp
    · have hne : d.support ≠ ∅ := fun h => hd0 (Finsupp.support_eq_empty.mp h)
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hdi : d i = 1 := by
        have hpos : 0 < d i :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
        exact le_antisymm (hmulti d (MvPolynomial.mem_support_iff.mp hd) i)
          (Nat.succ_le_of_lt hpos)
      have hi0 : ((fun _ : ℕ => (0 : ℝ)) i) ^ d i = 0 := by simp [hdi]
      have hi1 : ((fun i : ℕ => if i = N then (1 : ℝ) else 0) i) ^ d i = 0 := by
        have hneN : i ≠ N := fun h => absurd (hNs d hd i hi) (by omega)
        simp [hdi, hneN]
      rw [Finset.prod_eq_zero hi hi0, Finset.prod_eq_zero hi hi1]
  have hpt0 : (fun i => if (fun _ : ℕ => false) i then (1 : ℝ) else 0)
      = fun _ : ℕ => (0 : ℝ) := by
    funext i; simp
  have hpt1 : (fun i => if (fun i : ℕ => decide (i = N)) i then (1 : ℝ) else 0)
      = fun i : ℕ => if i = N then (1 : ℝ) else 0 := by
    funext i; simp
  have h0 : unboundedSearchAcceptance (fun _ : ℕ => false) = 0 :=
    unboundedSearchAcceptance_of_forall _ (fun k hk => by cases hk)
  have h1 : unboundedSearchAcceptance (fun i : ℕ => decide (i = N)) = 1 :=
    unboundedSearchAcceptance_of_exists _ ⟨N, by simp⟩
  have e0 := he (fun _ : ℕ => false)
  rw [hpt0, h0] at e0
  have e1 := he (fun i : ℕ => decide (i = N))
  rw [hpt1, h1] at e1
  rw [e0, e1] at heq
  exact zero_ne_one heq

/-- The readout projection ignoring an ancilla is the data readout projection tensored with the
ancilla identity. -/
lemma readoutEffect_ancillaReadout {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Finset I) :
    readoutEffect (K := I × J) (ancillaReadout A) =
      TensorGate (readoutEffect (K := I) A) (1 : Matrix J J ℂ) := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [readoutEffect, Matrix.diagonal_apply, tensorGate_apply, Matrix.one_apply,
    ancillaReadout, Finset.mem_product, Finset.mem_univ, and_true]
  by_cases hik : i = k
  · by_cases hjl : j = l
    · subst k; subst l; simp
    · simp [hjl]
  · simp [hik]

/-- Every normalized unitary upper-bound witness lifts to a clean ancilla while preserving its
resource counts and success probabilities. -/
lemma cleanUpperTransport_fixed {I J F : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] :
    ∀ (O : F → Matrix I I ℂ) (Acc : F → Finset I) (j₀ : J) (Q : ℕ) (p : ℝ),
      cleanUpperTransport O Acc j₀ Q p := by
  intro O Acc j₀ Q p C ψ₀ hC hψ₀ hQ hacc
  refine ⟨LiftCircuitTo J C, TensorState ψ₀ (Qatlib.Foundations.PureStateMath.Ket j₀), ?_, ?_,
      ?_⟩
  · refine ⟨rfl, rfl, queryCount_liftCircuitTo J C, gateCount_liftCircuitTo J C,
      size_liftCircuitTo J C, isUnitaryCircuit_liftCircuitTo hC, ?_, ?_⟩
    · intro f
      exact readoutEffect_ancillaReadout (Acc f)
    · intro f
      show MeasureProb (Run (TensorGate (O f) (1 : Matrix J J ℂ)) (LiftCircuitTo J C)
          (TensorState ψ₀ (Qatlib.Foundations.PureStateMath.Ket j₀))) (ancillaReadout (Acc f)) = _
      rw [run_liftCircuitTo_liftedOracle J (O f) C ψ₀ (Qatlib.Foundations.PureStateMath.Ket j₀)]
      exact measureProb_tensorState_left (normalized_ket j₀) (Run (O f) C ψ₀) (Acc f)
  · rw [queryCount_liftCircuitTo J C]
    exact hQ
  · intro f
    have h : MeasureProb (Run (ancillaOracle O f) (LiftCircuitTo J C)
          (TensorState ψ₀ (Qatlib.Foundations.PureStateMath.Ket j₀))) (ancillaReadout (Acc f))
        = MeasureProb (Run (O f) C ψ₀) (Acc f) := by
      show MeasureProb (Run (TensorGate (O f) (1 : Matrix J J ℂ)) (LiftCircuitTo J C)
          (TensorState ψ₀ (Qatlib.Foundations.PureStateMath.Ket j₀))) (ancillaReadout (Acc f)) = _
      rw [run_liftCircuitTo_liftedOracle J (O f) C ψ₀ (Qatlib.Foundations.PureStateMath.Ket j₀)]
      exact measureProb_tensorState_left (normalized_ket j₀) (Run (O f) C ψ₀) (Acc f)
    rw [h]
    exact hacc f

/-- Normalized bounded-error unitary circuits with clean ancillas satisfy the specified
adversary lower bound. -/
lemma cleanAncillaLowerTransport_fixed {J : Type} [Fintype J] [DecidableEq J]
    {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ) :
    cleanAncillaLowerTransport J input f Γ ε := by
  intro hG hε0 hε1 C' ψ' _j₀ E₀ hC' hψ' _ hsuccess
  refine (negative_adversary_actual_bounded_error_circuit_lower_bound
    X J n input Γ f C' ψ' (ancillaReadout (J := J) E₀) ε hG.1 hG.2 hC' hψ' hε0 hε1 ?_).trans ?_
  · intro x
    exact hsuccess x
  · simp []

/-- A well-formed observed circuit on a positive number of input bits possesses a unitary
adaptive purification bridge with the specified resource bounds. -/
lemma adaptivePurificationBridge_fixed {n : ℕ} (W : Type) [Fintype W] [DecidableEq W]
    [Nonempty W] (P : ObservedCircuit ((Fin n × Bool) × W))
    (hn : 0 < n) (hP : observedWellFormed P) :
    ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool))),
      adaptivePurificationBridge P R C := by
  obtain ⟨R, C, hC, hcount, hgate, hfull⟩ :=
    observed_query_same_cost_full_branch_purification n W P hn hP
  refine ⟨R, C, hC, hcount, hgate, ?_⟩
  intro f ψ
  have h := hfull f ψ
  refine ⟨h.1, ?_⟩
  exact observed_full_history_acceptance_transport P R C f ψ h.1 h.2

/-- A well-formed observed circuit on a positive number of bits possesses an adaptive
purification bridge and a multilinear acceptance representation of degree at most twice its
query depth. -/
lemma bridgePolynomialTransport_fixed {n : ℕ} (W : Type) [Fintype W] [DecidableEq W]
    [Nonempty W] (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W))
    (hn : 0 < n) (hP : observedWellFormed P) :
    bridgePolynomialTransport P ψ := by
  obtain ⟨R, C, hC, hcount, hgate, hfull⟩ :=
    observed_query_same_cost_full_branch_purification n W P hn hP
  refine ⟨R, C, ⟨hC, hcount, hgate, ?_⟩,
    multilinearize (observedRawAcceptancePolynomial P ψ),
    (multilinearize_totalDegree_le _).trans (observedRawAcceptancePolynomial_degree P ψ),
    multilinearize_coeff_multilinear _, ?_⟩
  · intro f ψ'
    have h := hfull f ψ'
    refine ⟨h.1, ?_⟩
    exact observed_full_history_acceptance_transport P R C f ψ' h.1 h.2
  · intro f
    simp only [treeAcceptance]
    rw [multilinearize_eval _ _ (fun i => by cases f i <;> simp)]
    exact observedRawAcceptancePolynomial_eval P ψ f

/-- The two-query circuit on a one-dimensional basis used in the hybrid-distance counterexample. -/
def hcC : Circuit (Fin 1) := [Step.query, Step.query]

/-- The one-dimensional oracle matrix with entry two used in the hybrid-distance counterexample. -/
def hcO1 : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 2

/-- The one-dimensional oracle matrix with entry three used in the hybrid-distance
counterexample. -/
def hcO2 : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 3

/-- The one-dimensional input state with amplitude one used in the hybrid-distance
counterexample. -/
def hcψ : QState (Fin 1) := fun _ => 1

/-- Applying `hcO1` multiplies the single input amplitude by two. -/
lemma applyGate_hcO1 (v : QState (Fin 1)) : ApplyGate hcO1 v = fun _ => 2 * v 0 := by
  funext i
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (0 : Fin 1)]
  · simp [hcO1]
  · intro b _ hb
    exact absurd (Subsingleton.elim b 0) hb
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin 1)) h

/-- Applying `hcO2` multiplies the single input amplitude by three. -/
lemma applyGate_hcO2 (v : QState (Fin 1)) : ApplyGate hcO2 v = fun _ => 3 * v 0 := by
  funext i
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (0 : Fin 1)]
  · simp [hcO2]
  · intro b _ hb
    exact absurd (Subsingleton.elim b 0) hb
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin 1)) h

/-- The two-query counterexample circuit with oracle `hcO1` produces amplitude four. -/
lemma run_hcO1 : Run hcO1 hcC hcψ = fun _ => (4 : ℂ) := by
  simp only [hcC, Run]
  rw [applyGate_hcO1, applyGate_hcO1]
  funext x
  norm_num [hcψ]

/-- The two-query counterexample circuit with oracle `hcO2` produces amplitude nine. -/
lemma run_hcO2 : Run hcO2 hcC hcψ = fun _ => (9 : ℂ) := by
  simp only [hcC, Run]
  rw [applyGate_hcO2, applyGate_hcO2]
  funext x
  norm_num [hcψ]

/-- The two-query counterexample circuit has no nonunitary fixed gates and is a unitary circuit. -/
lemma isUnitaryCircuit_hcC : IsUnitaryCircuit hcC := by
  intro U hU
  simp [hcC] at hU

/-- The one-dimensional counterexample input is normalized. -/
lemma normalized_hcψ : Normalized hcψ := by
  show ∑ i : Fin 1, ‖hcψ i‖ ^ 2 = 1
  simp [hcψ]

/-- The counterexample circuit contains exactly two queries. -/
lemma queryCount_hcC : QueryCount hcC = 2 := by
  simp [hcC, QueryCount]

/-- The operator-norm distance between the two counterexample oracle matrices equals one. -/
lemma oracleDistance_hcO1_hcO2 : oracleDistance hcO1 hcO2 = 1 := by
  have hsub : hcO1 - hcO2 = Matrix.diagonal fun _ => (-1 : ℂ) := by
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [hcO1, hcO2, Matrix.diagonal]
    norm_num
  rw [oracleDistance, hsub, Matrix.l2_opNorm_diagonal]
  show ‖(fun _ : Fin 1 => (-1 : ℂ))‖ = 1
  simp

/-- Conversion of finite coordinate states to Euclidean space preserves subtraction. -/
lemma toEuclidean_fromVec_sub {I : Type*} [Fintype I] (u v : QState I) :
    toEuclidean_fromVec u - toEuclidean_fromVec v = toEuclidean_fromVec (u - v) :=
  (WithLp.toLp_sub 2 u v).symm

/-- The proposed hybrid-distance bound fails for the two nonunitary one-dimensional
counterexample oracles. -/
lemma hybridDistanceBound_hc_false :
    ¬ hybridDistanceBound (K := Fin 1) hcO1 hcO2 hcC hcψ 2 := by
  intro h
  have hcount : QueryCount hcC ≤ 2 := by rw [queryCount_hcC]
  have hineq := h isUnitaryCircuit_hcC normalized_hcψ hcount
  rw [run_hcO1, run_hcO2] at hineq
  have hnorm :
      ‖toEuclidean_fromVec (fun _ : Fin 1 => (4 : ℂ))
          - toEuclidean_fromVec (fun _ : Fin 1 => (9 : ℂ))‖ = 5 := by
    rw [toEuclidean_fromVec_sub]
    have hsq : ‖toEuclidean_fromVec
        ((fun _ : Fin 1 => (4 : ℂ)) - fun _ : Fin 1 => (9 : ℂ))‖ ^ 2 = 25 := by
      rw [norm_toEuclidean_fromVec_sq]
      simp
      norm_num
    calc ‖toEuclidean_fromVec
          ((fun _ : Fin 1 => (4 : ℂ)) - fun _ : Fin 1 => (9 : ℂ))‖
        = Real.sqrt (‖toEuclidean_fromVec
            ((fun _ : Fin 1 => (4 : ℂ)) - fun _ : Fin 1 => (9 : ℂ))‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 25 := by rw [hsq]
      _ = 5 := by
        have h25 : (25:ℝ) = 5 ^ 2 := by norm_num
        rw [h25, Real.sqrt_sq (by norm_num)]
  rw [hnorm, oracleDistance_hcO1_hcO2] at hineq
  norm_num at hineq

/-- The hybrid-distance specification does not hold universally for unrestricted oracle
matrices. -/
lemma clause41_conj2_false :
    ¬ (∀ (K : Type) [Fintype K] [DecidableEq K] (O₁ O₂ : Matrix K K ℂ) (C : Circuit K)
        (ψ₀ : QState K) (Q : ℕ), hybridDistanceBound O₁ O₂ C ψ₀ Q) := by
  intro h
  exact hybridDistanceBound_hc_false (h (Fin 1) hcO1 hcO2 hcC hcψ 2)

/-- The conjunction of stopping-tail laws, an unrestricted hybrid bound, an expected-charge
adversary bound, positive-cost termination, and search-polynomial statements. -/
def BaseClause41 : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (P : ObservedCircuit I)
      (ψ : QState I),
    stopJointLaw O P ψ ∧
    (∀ (K : Type) [Fintype K] [DecidableEq K] (O₁ O₂ : Matrix K K ℂ) (C : Circuit K)
        (ψ₀ : QState K) (Q : ℕ), hybridDistanceBound O₁ O₂ C ψ₀ Q) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (n : ℕ) (W : Type)
        [Fintype W] [DecidableEq W]
        (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε Tbar : ℝ)
        (P' : ObservedCircuit ((Fin n × Bool) × W)) (ψ' : QState ((Fin n × Bool) × W)),
      treeBoundedError input f P' ψ' ε → expectedChargeBound input P' ψ' Tbar →
        adversaryValid f Γ → 0 ≤ ε → ε ≤ 1 / 2 →
        (1 - 2 * Real.sqrt (ε * (1 - ε))) * advWeightNorm Γ ≤
          2 * Tbar * advFilterBound input Γ) ∧
    (∀ (S O' : Type) [Fintype S] [DecidableEq S] [Fintype O'] [DecidableEq O']
        (next : S → PMF (RandomizedExecution.Configuration S O'))
        (cfg : RandomizedExecution.Configuration S O'),
      stopTailNeverJointLaw next cfg) ∧
    (∀ (S O' : Type) [Fintype S] [DecidableEq S] [Fintype O'] [DecidableEq O']
        (next : S → PMF (RandomizedExecution.Configuration S O')) (c : S → ℕ)
        (cfg : RandomizedExecution.Configuration S O'),
      positiveCharge c → weightedExpectedCost next c cfg < ⊤ →
        neverStopMass next cfg = 0) ∧
    zenoZeroCharge zenoNext zenoCharge PUnit.unit ∧
    noUnconditionalPolyRep ∧ (∀ K : ℕ, truncatedSearchPolyRep K)

/-- The combined specification `BaseClause41` is false. -/
theorem clause3_false : ¬ BaseClause41 := by
  intro h
  obtain ⟨_, h2, _⟩ :=
    h (Fin 1) (1 : Matrix (Fin 1) (Fin 1) ℂ) (.halt false) hcψ
  exact clause41_conj2_false h2

/-- The embedding of the five address indices into the nonzero elements of `Fin 6`. -/
def geB (i : Fin 5) : Fin 6 := ⟨i.val + 1, by omega⟩

/-- The six-input Boolean family whose nonzero inputs have a single true coordinate selected by
`geB`. -/
def geInput : Fin 6 → Fin 5 → Bool := fun x j => decide (x = geB j)

/-- The Boolean function on `Fin 6` that is true exactly at nonzero inputs. -/
def geF : Fin 6 → Bool := fun x => decide (x ≠ 0)

/-- The star-shaped adversary matrix connecting zero to each nonzero input with weight one. -/
def geΓ : Matrix (Fin 6) (Fin 6) ℂ :=
  fun x y => if (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0) then 1 else 0

/-- The unnormalized input with amplitude one at every address with a false answer bit and zero
at every true answer bit. -/
def geΨ : QState ((Fin 5 × Bool) × PUnit) := fun p => if p.1.2 = false then (1 : ℂ) else 0

/-- The diagonal projection onto basis states with a true answer bit. -/
def geAcc : Matrix ((Fin 5 × Bool) × PUnit) ((Fin 5 × Bool) × PUnit) ℂ :=
  Matrix.diagonal fun p => if p.1.2 = true then (1 : ℂ) else 0

/-- The observed circuit that queries once and accepts exactly the true-answer projection
branch. -/
def geP : ObservedCircuit ((Fin 5 × Bool) × PUnit) :=
  .step .query (.project geAcc (.halt false) (.halt true))

/-- Every value of the address embedding `geB` is nonzero. -/
lemma geB_ne_zero (i : Fin 5) : geB i ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [geB] at this

/-- The address embedding `geB` is injective. -/
lemma geB_injective : Function.Injective geB := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [geB] using this

/-- Every nonzero element of `Fin 6` is the image of an address under `geB`. -/
lemma geB_surjective_of_ne_zero {x : Fin 6} (hx : x ≠ 0) :
    ∃ i : Fin 5, geB i = x := by
  refine ⟨⟨x.val - 1, ?_⟩, ?_⟩
  · have h1 : 0 < x.val := Fin.pos_of_ne_zero hx
    omega
  · apply Fin.ext
    simp [geB]
    have h1 : 0 < x.val := Fin.pos_of_ne_zero hx
    omega

/-- The answer-bit projection `geAcc` is idempotent. -/
lemma geAcc_mul_self : geAcc * geAcc = geAcc := by
  rw [geAcc, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases hp : p.1.2 = true <;> simp [hp]

/-- The answer-bit projection `geAcc` is self-adjoint. -/
lemma geAcc_conjTranspose : geAccᴴ = geAcc := by
  rw [geAcc, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases hp : p.1.2 = true <;> simp [hp]

/-- The matrix `geAcc` is a self-adjoint projection. -/
lemma isStarProjection_geAcc : IsStarProjection geAcc :=
  isStarProjection_iff'.mpr ⟨geAcc_mul_self, geAcc_conjTranspose⟩

/-- The one-query observed counterexample circuit is well formed. -/
lemma observedWellFormed_geP : observedWellFormed geP := by
  simp [geP, observedWellFormed, isStarProjection_geAcc]

/-- The observed counterexample circuit has query depth one. -/
lemma observedQueryDepth_geP : observedQueryDepth geP = 1 := by
  simp [geP, observedQueryDepth]

/-- Applying `geAcc` retains amplitudes with a true answer bit and sets all others to zero. -/
lemma applyGate_geAcc (φ : QState ((Fin 5 × Bool) × PUnit)) :
    ApplyGate geAcc φ = fun p => if p.1.2 = true then φ p else 0 := by
  funext p
  simp only [ApplyGate, geAcc, Matrix.mulVec_diagonal]
  by_cases hp : p.1.2 = true <;> simp [hp]

/-- The counterexample input has amplitude one on false-answer basis states and zero elsewhere. -/
lemma geΨ_apply (p : (Fin 5 × Bool) × PUnit) :
    geΨ p = if p.1.2 = false then (1 : ℂ) else 0 := rfl

/-- A query followed by projection and Boolean halting has acceptance mass equal to the full
mass of the true projection branch after the query. -/
lemma observedAcceptance_query_project_halt
    {I : Type} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (φ : QState I)
    (P : Matrix I I ℂ) :
    observedAcceptance O (.step .query (.project P (.halt false) (.halt true))) φ
      = MeasureProb (ProjectiveBranch P true (ApplyGate O φ)) Finset.univ := by
  have htraces :
      observedTraces O (.step .query (.project P (.halt false) (.halt true))) φ
        = [{ state := ProjectiveBranch P false (ApplyGate O φ), accepted := false, queries := 1,
             gates := 0, measurements := 1, outcomes := [(2, 0)] },
           { state := ProjectiveBranch P true (ApplyGate O φ), accepted := true, queries := 1,
             gates := 0, measurements := 1, outcomes := [(2, 1)] }] := by
    simp [observedTraces]
  rw [observedAcceptance, htraces]
  simp [List.filter, List.foldl, branchMass, MeasureProb]

/-- The counterexample circuit's acceptance mass equals the number of true input coordinates. -/
lemma acc_geΨ (x : Fin 6) :
    observedAcceptance (workspaceBitOracle (W := PUnit) (geInput x)) geP geΨ
      = ∑ i : Fin 5, if geInput x i = true then (1 : ℝ) else 0 := by
  rw [geP, observedAcceptance_query_project_halt]
  have hbranch : ProjectiveBranch geAcc true
        (ApplyGate (workspaceBitOracle (W := PUnit) (geInput x)) geΨ)
      = fun p => if p.1.2 = true ∧ geInput x p.1.1 = true then (1 : ℂ) else 0 := by
    rw [ProjectiveBranch, ite_eq_left rfl, applyGate_geAcc]
    funext p
    by_cases hp : p.1.2 = true
    · have hamp : ApplyGate (workspaceBitOracle (W := PUnit) (geInput x)) geΨ p
          = if geInput x p.1.1 = true then (1 : ℂ) else 0 := by
        rw [applyGate_workspaceBitOracle_mk, geΨ_apply]
        by_cases hb : geInput x p.1.1 = true
        · simp [hb, hp]
        · simp [hb, hp]
      simp [hp, hamp]
    · simp [hp]
  rw [hbranch]
  show (∑ p : (Fin 5 × Bool) × PUnit,
      ‖(if p.1.2 = true ∧ geInput x p.1.1 = true then (1 : ℂ) else 0)‖ ^ 2) = _
  have hsum : (∑ p : (Fin 5 × Bool) × PUnit,
        ‖(if p.1.2 = true ∧ geInput x p.1.1 = true then (1 : ℂ) else 0)‖ ^ 2)
      = ∑ q : Fin 5 × Bool,
        ‖(if q.2 = true ∧ geInput x q.1 = true then (1 : ℂ) else 0)‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Fintype.sum_unique]
  rw [hsum]
  have hsum2 : (∑ q : Fin 5 × Bool,
        ‖(if q.2 = true ∧ geInput x q.1 = true then (1 : ℂ) else 0)‖ ^ 2)
      = ∑ i : Fin 5, ∑ b : Bool,
        ‖(if b = true ∧ geInput x i = true then (1 : ℂ) else 0)‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  rw [hsum2]
  have hbool : ∀ i : Fin 5,
      (∑ b : Bool, ‖(if b = true ∧ geInput x i = true then (1 : ℂ) else 0)‖ ^ 2)
      = if geInput x i = true then (1 : ℝ) else 0 := by
    intro i
    by_cases hi : geInput x i = true
    · simp [hi]
    · simp [hi]
  simp only [hbool]

/-- A finite sum supported by the equality test at `a` equals `f a`. -/
lemma sum_ite_eq_self {α β : Type} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (a : α) (f : α → β) :
    (∑ x : α, if x = a then f x else 0) = f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The number of true coordinates is zero at input zero and one at every nonzero input. -/
lemma sum_geInput (x : Fin 6) :
    (∑ i : Fin 5, if geInput x i = true then (1 : ℝ) else 0) = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst x
    have h : ∀ i : Fin 5, ¬(geInput 0 i = true) := by
      intro i
      have hne : (0 : Fin 6) ≠ geB i := (geB_ne_zero i).symm
      simp [geInput, hne]
    simp only []
    apply Finset.sum_eq_zero
    intro i _
    simp [h i]
  · rw [ite_eq_right hx]
    obtain ⟨i, hi⟩ := geB_surjective_of_ne_zero hx
    rw [Finset.sum_eq_single i]
    · simp [geInput, hi]
    · intro b _ hb
      have hne : ¬(geInput x b = true) := by
        have hne2 : x ≠ geB b := fun h => hb (geB_injective (hi.trans h)).symm
        simp [geInput, hne2]
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ i) h

/-- The observed counterexample circuit satisfies the zero-error tree condition on `geΨ`. -/
lemma treeBoundedError_geP : treeBoundedError geInput geF geP geΨ 0 := by
  intro x
  simp only [acc_geΨ, sum_geInput]
  by_cases hx : x = 0
  · subst x
    simp [geF]
  · simp [geF, hx]

/-- The counterexample function is true exactly at nonzero inputs. -/
lemma geF_eq_true (x : Fin 6) : geF x = true ↔ x ≠ 0 := by
  simp [geF]

/-- The counterexample function is false exactly at input zero. -/
lemma geF_eq_false (x : Fin 6) : geF x = false ↔ x = 0 := by
  simp [geF]

/-- Coordinate `i` of the counterexample input is true exactly at `geB i`. -/
lemma geInput_eq_iff (z : Fin 6) (i : Fin 5) : geInput z i = true ↔ z = geB i := by
  simp [geInput]

/-- An entry of the star adversary matrix equals one exactly when one index is zero and the
other is nonzero. -/
lemma geΓ_support_iff (x y : Fin 6) :
    geΓ x y = 1 ↔ (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0) := by
  show (if (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0) then (1 : ℂ) else 0) = 1 ↔ _
  by_cases h : (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0) <;> simp [h]

/-- The star adversary matrix is equal to its conjugate transpose. -/
lemma geΓ_isHermitian : geΓᴴ = geΓ := by
  ext x y
  simp only [Matrix.conjTranspose_apply]
  by_cases h : (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0)
  · have hy : (y = 0 ∧ x ≠ 0) ∨ (x = 0 ∧ y ≠ 0) := Or.symm h
    simp [geΓ, h, hy]
  · have hy : ¬((y = 0 ∧ x ≠ 0) ∨ (x = 0 ∧ y ≠ 0)) := fun hh => h (Or.symm hh)
    simp [geΓ, h, hy]

/-- The star matrix is a valid adversary matrix for `geF`. -/
lemma adversaryValid_geΓ : adversaryValid geF geΓ := by
  refine ⟨geΓ_isHermitian, ?_⟩
  intro x y h
  show (if (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0) then (1 : ℂ) else 0) = 0
  have hD : ¬((x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0)) := by
    rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · subst x
      exact hy ((geF_eq_false y).mp (h.symm.trans ((geF_eq_false 0).mpr rfl)))
    · subst y
      exact hy ((geF_eq_false x).mp (h.trans ((geF_eq_false 0).mpr rfl)))
  simp [hD]

/-- A supported adversary pair differing at coordinate `i` must connect zero with `geB i`. -/
lemma advFilter_support (i : Fin 5) (x y : Fin 6)
    (hd : geInput x i ≠ geInput y i)
    (hΓ : (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0)) :
    (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) := by
  rcases hΓ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst x
    have hyi : y = geB i := by
      by_contra hne
      have heq : geInput 0 i = geInput y i := by
        simp [geInput, (geB_ne_zero i).symm, hne]
      exact hd heq
    exact Or.inl ⟨rfl, hyi⟩
  · subst y
    have hxi : x = geB i := by
      by_contra hne
      have heq : geInput x i = geInput 0 i := by
        simp [geInput, (geB_ne_zero i).symm, hne]
      exact hd heq
    exact Or.inr ⟨hxi, rfl⟩

/-- The coordinate-filtered star matrix has unit entries only on the two directed edges between
zero and `geB i`. -/
lemma advFilter_geΓ (i : Fin 5) (x y : Fin 6) :
    advFilter geInput geΓ i x y
      = if (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) then (1 : ℂ) else 0 := by
  show (if geInput x i ≠ geInput y i then geΓ x y else 0) = _
  have hΓeq : geΓ x y = if (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0) then (1 : ℂ) else 0 := rfl
  rw [hΓeq]
  by_cases hd : geInput x i ≠ geInput y i
  · rw [ite_eq_left hd]
    by_cases hΓ : (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0)
    · rw [ite_eq_left hΓ, ite_eq_left (advFilter_support i x y hd hΓ)]
    · have hD : ¬((x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0)) := by
        rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
        · exact hΓ (Or.inl ⟨hx, by simp [hy, geB_ne_zero i]⟩)
        · exact hΓ (Or.inr ⟨hy, by simp [hx, geB_ne_zero i]⟩)
      rw [ite_eq_right hΓ, ite_eq_right hD]
  · rw [ite_eq_right hd]
    have hD : ¬((x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0)) := by
      rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · subst x; subst y
        exact hd (by simp [geInput, (geB_ne_zero i).symm])
      · subst x; subst y
        exact hd (by simp [geInput, (geB_ne_zero i).symm])
    rw [ite_eq_right hD]

/-- A left fold of `max` stays below `m` when its initial value and every list entry are bounded
by `m`. -/
lemma list_foldl_max_le' (l : List ℝ) (m : ℝ) :
    ∀ s, s ≤ m → (∀ x ∈ l, x ≤ m) → l.foldl max s ≤ m := by
  induction l with
  | nil => intro s hs _; simpa using hs
  | cons x l ih =>
    intro s hs h
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact ih _ (max_le hs h.1) h.2

/-- A left fold of `max` starting at zero stays below a nonnegative bound on all list entries. -/
lemma list_foldl_max_le {l : List ℝ} {m : ℝ} (hm : 0 ≤ m) (h : ∀ x ∈ l, x ≤ m) :
    l.foldl max 0 ≤ m :=
  list_foldl_max_le' l m 0 hm h

/-- The filtered star matrix exchanges the zero and `geB i` coordinates of a vector and vanishes
on all other coordinates. -/
lemma advFilter_mulVec_apply (i : Fin 5) (v : QState (Fin 6)) (x : Fin 6) :
    (advFilter geInput geΓ i *ᵥ v) x
      = if x = 0 then v (geB i) else if x = geB i then v 0 else 0 := by
  simp only [Matrix.mulVec, dotProduct]
  have hterm : ∀ y : Fin 6, advFilter geInput geΓ i x y * v y
      = if (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) then v y else 0 := by
    intro y
    rw [advFilter_geΓ]
    by_cases hd : (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) <;> simp [hd]
  simp only [hterm]
  by_cases hx0 : x = 0
  · by_cases hxi : x = geB i
    · exact absurd (hx0.symm.trans hxi) (geB_ne_zero i).symm
    · have hD : ∀ y : Fin 6,
          ((x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0)) ↔ y = geB i := by
        intro y
        constructor
        · rintro (⟨_, hy⟩ | ⟨h1, _⟩)
          · exact hy
          · exact absurd h1 hxi
        · intro hy
          exact Or.inl ⟨hx0, hy⟩
      have hsum : (∑ y : Fin 6, if (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) then v y else 0)
          = v (geB i) := by
        rw [show (∑ y : Fin 6, if (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) then v y else 0)
            = ∑ y : Fin 6, if y = geB i then v y else 0 from
            Finset.sum_congr rfl (fun y _ => by
              by_cases hy' : (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0)
              · rw [ite_eq_left hy', ite_eq_left ((hD y).mp hy')]
              · rw [ite_eq_right hy', ite_eq_right fun hh => hy' ((hD y).mpr hh)])]
        exact sum_ite_eq_self _ _
      rw [ite_eq_left hx0]
      exact hsum
  · by_cases hxi : x = geB i
    · have hD : ∀ y : Fin 6,
          ((x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0)) ↔ y = 0 := by
        intro y
        constructor
        · rintro (⟨h1, _⟩ | ⟨_, hy⟩)
          · exact absurd h1 hx0
          · exact hy
        · intro hy
          exact Or.inr ⟨hxi, hy⟩
      have hsum : (∑ y : Fin 6, if (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) then v y else 0)
          = v 0 := by
        rw [show (∑ y : Fin 6, if (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) then v y else 0)
            = ∑ y : Fin 6, if y = 0 then v y else 0 from
            Finset.sum_congr rfl (fun y _ => by
              by_cases hy' : (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0)
              · rw [ite_eq_left hy', ite_eq_left ((hD y).mp hy')]
              · rw [ite_eq_right hy', ite_eq_right fun hh => hy' ((hD y).mpr hh)])]
        exact sum_ite_eq_self _ _
      rw [ite_eq_right hx0, ite_eq_left hxi]
      exact hsum
    · have hD : ∀ y : Fin 6, ¬((x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0)) := by
        intro y hy
        rcases hy with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp_all
      have hsum0 : (∑ y : Fin 6,
          if (x = 0 ∧ y = geB i) ∨ (x = geB i ∧ y = 0) then v y else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        simp [hD y]
      rw [hsum0, ite_eq_right hx0, ite_eq_right hxi]

/-- Each coordinate-filtered star matrix has operator norm at most one. -/
lemma advFilter_norm_le (i : Fin 5) : ‖advFilter geInput geΓ i‖ ≤ 1 := by
  refine l2_opNorm_le_of_mulVec_le (by norm_num) _ ?_
  intro v
  have hact : (advFilter geInput geΓ i) *ᵥ v
      = fun x => if x = 0 then v (geB i) else if x = geB i then v 0 else 0 := by
    funext x
    exact advFilter_mulVec_apply i v x
  rw [hact]
  have hsq : ‖toEuclidean_fromVec
        (fun x => if x = 0 then v (geB i) else if x = geB i then v 0 else 0)‖ ^ 2
      = ‖v (geB i)‖ ^ 2 + ‖v 0‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    have hout : ∀ z : Fin 6, z ∉ ({0, geB i} : Finset (Fin 6)) →
        ‖(if z = 0 then v (geB i) else if z = geB i then v 0 else 0)‖ ^ 2 = 0 := by
      intro z hz
      have h1 : z ≠ 0 := fun h => hz (by simp [h])
      have h2 : z ≠ geB i := fun h => hz (by simp [h])
      simp [h1, h2]
    have hsplit : (∑ z : Fin 6, ‖(if z = 0 then v (geB i) else if z = geB i then v 0 else 0)‖ ^ 2)
        = ∑ z ∈ ({0, geB i} : Finset (Fin 6)),
          ‖(if z = 0 then v (geB i) else if z = geB i then v 0 else 0)‖ ^ 2 := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => hout z hz)
    rw [hsplit, Finset.sum_pair (geB_ne_zero i).symm]
    simp [geB_ne_zero i]
  have h2 : ‖toEuclidean_fromVec v‖ ^ 2 = ∑ z : Fin 6, ‖v z‖ ^ 2 :=
    norm_toEuclidean_fromVec_sq _
  have hle : ‖toEuclidean_fromVec
        (fun x => if x = 0 then v (geB i) else if x = geB i then v 0 else 0)‖ ^ 2
      ≤ ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [hsq, h2]
    have hz : (‖v (geB i)‖ ^ 2 + ‖v 0‖ ^ 2)
        = ∑ z ∈ ({0, geB i} : Finset (Fin 6)), ‖v z‖ ^ 2 := by
      rw [Finset.sum_pair (geB_ne_zero i).symm]
      simp [add_comm]
    rw [hz]
    have hsdiff : (∑ z : Fin 6, ‖v z‖ ^ 2)
        = (∑ z ∈ Finset.univ \ ({0, geB i} : Finset (Fin 6)), ‖v z‖ ^ 2)
          + (∑ z ∈ ({0, geB i} : Finset (Fin 6)), ‖v z‖ ^ 2) :=
      (Finset.sum_sdiff (Finset.subset_univ ({0, geB i} : Finset (Fin 6)))).symm
    rw [hsdiff]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun z _ => sq_nonneg _)
  have hs : ‖toEuclidean_fromVec
        (fun x => if x = 0 then v (geB i) else if x = geB i then v 0 else 0)‖
      ≤ ‖toEuclidean_fromVec v‖ :=
    le_of_sq_le_sq hle (norm_nonneg _)
  simpa using hs

/-- The maximum coordinate-filter norm bound of the star adversary matrix is at most one. -/
lemma advFilterBound_geΓ_le : advFilterBound geInput geΓ ≤ 1 := by
  unfold advFilterBound
  refine list_foldl_max_le (by norm_num) ?_
  simp only [List.forall_mem_ofFn_iff]
  intro i
  exact advFilter_norm_le i

/-- The operator norm of the star adversary matrix is at least `sqrt 5`. -/
lemma norm_geΓ : Real.sqrt 5 ≤ advWeightNorm geΓ := by
  have hvec : geΓ *ᵥ (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 6))
      = (fun y : Fin 6 => if y ≠ 0 then (1 : ℂ) else 0) := by
    funext y
    simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
    have hterm : ∀ b : Fin 6, geΓ y b * (if b = 0 then (1 : ℂ) else 0)
        = if b = 0 then geΓ y b else 0 := by
      intro b
      by_cases hb : b = 0 <;> simp [hb]
    simp only [hterm]
    rw [sum_ite_eq_self]
    by_cases hy : y = 0
    · subst y
      simp [geΓ]
    · simp [geΓ, hy]
  have hnorm : ‖toEuclidean_fromVec (fun y : Fin 6 => if y ≠ 0 then (1 : ℂ) else 0)‖
      = Real.sqrt 5 := by
    have hsq : ‖toEuclidean_fromVec (fun y : Fin 6 => if y ≠ 0 then (1 : ℂ) else 0)‖ ^ 2 = 5 := by
      rw [norm_toEuclidean_fromVec_sq]
      have hsum : (∑ y : Fin 6, ‖(if y ≠ 0 then (1 : ℂ) else 0)‖ ^ 2)
          = ∑ y : Fin 6, (if y ≠ 0 then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y = 0 <;> simp [hy]
      rw [hsum]
      have hcount : (∑ y : Fin 6, (if y ≠ 0 then (1 : ℝ) else 0)) = 5 := by
        have h : ∀ y : Fin 6,
            (if y ≠ 0 then (1 : ℝ) else 0) = 1 - (if y = 0 then (1 : ℝ) else 0) := by
          intro y
          by_cases hy : y = 0 <;> simp [hy]
        simp only [h]
        rw [Finset.sum_sub_distrib, sum_ite_eq_self]
        have hcard : (∑ _y : Fin 6, (1:ℝ)) = 6 := by
          rw [Finset.sum_const, Finset.card_fin]
          simp
        rw [hcard]
        norm_num
      rw [hcount]
    have hnn : 0 ≤ ‖toEuclidean_fromVec (fun y : Fin 6 => if y ≠ 0 then (1 : ℂ) else 0)‖ :=
      norm_nonneg _
    calc ‖toEuclidean_fromVec (fun y : Fin 6 => if y ≠ 0 then (1 : ℂ) else 0)‖
        = Real.sqrt (‖toEuclidean_fromVec (fun y : Fin 6 => if y ≠ 0 then (1 : ℂ) else 0)‖ ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ = Real.sqrt 5 := by rw [hsq]
  have hket : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 6))‖ = 1 := by
    have hsq : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 6))‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq]
      have hpt : ∀ j : Fin 6, ‖(Qatlib.Foundations.PureStateMath.Ket (0 : Fin 6)) j‖ ^ 2 = if j = 0 then (1 : ℝ) else 0 := by
        intro j
        by_cases hj : j = 0 <;> simp [Qatlib.Foundations.PureStateMath.Ket, hj]
      rw [Finset.sum_congr rfl (fun j _ => hpt j)]
      exact sum_ite_eq_self _ _
    have hnn : 0 ≤ ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 6))‖ :=
        norm_nonneg _
    calc ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 6))‖
        = Real.sqrt (‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 6))‖ ^ 2) := (Real.sqrt_sq hnn).symm
      _ = Real.sqrt 1 := by rw [hsq]
      _ = 1 := Real.sqrt_one
  have h := l2_norm_mulVec_fromVec_le geΓ (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 6))
  rw [hvec, hnorm, hket, mul_one] at h
  simpa [advWeightNorm] using h

/-- The adversary-transport specification fails for the unnormalized one-query counterexample. -/
lemma bridgeAdversaryTransport_geP_false :
    ¬ bridgeAdversaryTransport geInput geF geΓ 0 geP := by
  rintro ⟨R, C, _, _, hineq⟩
  simp only [observedQueryDepth_geP] at hineq
  have hfactor : (1 - 2 * Real.sqrt ((0:ℝ) * (1 - 0))) = 1 := by norm_num
  rw [hfactor] at hineq
  push_cast at hineq
  simp only [one_mul, mul_one] at hineq
  have hle : advWeightNorm geΓ ≤ 2 := by
    have h1 := advFilterBound_geΓ_le
    nlinarith
  have hgt : (2:ℝ) < Real.sqrt 5 :=
    (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 2)).mpr (by norm_num)
  exact absurd (le_trans norm_geΓ hle) (not_le.mpr hgt)

/-- Well-formedness and bounded error alone do not imply the universal adaptive
adversary-transport specification stated here. -/
lemma clause9_conj4_false :
    ¬ (∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (n : ℕ) (W : Type)
        [Fintype W] [DecidableEq W] [Nonempty W]
        (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
        (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)),
      0 < n → observedWellFormed P → treeBoundedError input f P ψ ε →
        adversaryValid f Γ → 0 ≤ ε → ε ≤ 1 / 2 →
        bridgeAdversaryTransport input f Γ ε P) := by
  intro h
  exact bridgeAdversaryTransport_geP_false
    (h (Fin 6) 5 PUnit geInput geF geΓ 0 geP geΨ (by omega) observedWellFormed_geP
      treeBoundedError_geP adversaryValid_geΓ (by norm_num) (by norm_num))

/-- The conjunction of universal clean-ancilla upper and lower transport, polynomial transport,
and adaptive adversary transport without an input normalization requirement. -/
def BaseClause9 : Prop :=
  ∀ (I J F : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    (∀ (O : F → Matrix I I ℂ) (Acc : F → Finset I) (j₀ : J) (Q : ℕ) (p : ℝ),
      cleanUpperTransport O Acc j₀ Q p) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (n : ℕ)
        (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ),
      cleanAncillaLowerTransport J input f Γ ε) ∧
    (∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
        (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)),
      0 < n → observedWellFormed P → bridgePolynomialTransport P ψ) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (n : ℕ) (W : Type)
        [Fintype W] [DecidableEq W] [Nonempty W]
        (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
        (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)),
      0 < n → observedWellFormed P → treeBoundedError input f P ψ ε →
        adversaryValid f Γ → 0 ≤ ε → ε ≤ 1 / 2 →
        bridgeAdversaryTransport input f Γ ε P)

/-- The combined specification `BaseClause9` is false. -/
theorem clause1_false : ¬ BaseClause9 := by
  intro h
  obtain ⟨_, _, _, h4⟩ := h (Fin 5) PUnit PUnit
  exact clause9_conj4_false h4

end Qatlib.Concepts.StoppingCore.InterruptBridge
