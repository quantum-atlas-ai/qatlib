/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ResourceBounds.AsymBounds.GatesBitDefs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline Qatlib.Concepts.NonNormalSpec.ResolventWord Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

noncomputable section

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

open Matrix

/-- Folding dynamic operations increases the gate count by the length of their gate list. -/
theorem gateCount_fold (base : ℕ) (ops : List DynOp) (a : DynAccount) (live : List ℕ) :
    ((ops.foldl (dynStep base) (a, live)).1).gateCount = a.gateCount + (opsGates ops).length := by
  induction ops generalizing a live with
  | nil => simp [opsGates]
  | cons op rest ih =>
      cases op with
      | alloc w => simp [dynStep, opsGates, ih] <;> omega
      | releaseClean w => simp [dynStep, opsGates, ih] <;> omega
      | releaseDirty w => simp [dynStep, opsGates, ih] <;> omega
      | resetWire w => simp [dynStep, opsGates, ih] <;> omega
      | uncomputeWire w => simp [dynStep, opsGates, ih] <;> omega
      | fixedGate g => simp [dynStep, opsGates, ih] <;> omega
      | oracleQuery ws => simp [dynStep, opsGates, ih] <;> omega

/-- Folding dynamic operations increases the query count by the number of oracle queries. -/
theorem queryCount_fold (base : ℕ) (ops : List DynOp) (a : DynAccount) (live : List ℕ) :
    ((ops.foldl (dynStep base) (a, live)).1).queryCount
        = a.queryCount + (ops.filter DynOp.isOracleQuery).length := by
  induction ops generalizing a live with
  | nil => simp
  | cons op rest ih =>
      cases op with
      | alloc w => simp [dynStep, DynOp.isOracleQuery, ih] <;> omega
      | releaseClean w => simp [dynStep, DynOp.isOracleQuery, ih] <;> omega
      | releaseDirty w => simp [dynStep, DynOp.isOracleQuery, ih] <;> omega
      | resetWire w => simp [dynStep, DynOp.isOracleQuery, ih] <;> omega
      | uncomputeWire w => simp [dynStep, DynOp.isOracleQuery, ih] <;> omega
      | fixedGate g => simp [dynStep, DynOp.isOracleQuery, ih] <;> omega
      | oracleQuery ws => simp [dynStep, DynOp.isOracleQuery, ih] <;> omega

/-- Identifies the dynamic account's gate and query counts with the corresponding operation
counts. -/
theorem dynAccount_ledger_binding (base : ℕ) (ops : List DynOp) :
    (dynAccount base ops).gateCount = (opsGates ops).length ∧
      (dynAccount base ops).queryCount = (ops.filter DynOp.isOracleQuery).length := by
  constructor
  · have h := gateCount_fold base ops ⟨0, 0, 0, 0, 0, 0, base, 0⟩ (List.range base)
    simpa [dynAccount, dynInitial] using! h
  · have h := queryCount_fold base ops ⟨0, 0, 0, 0, 0, 0, base, 0⟩ (List.range base)
    simpa [dynAccount, dynInitial] using! h

/-- The register type on zero wires is a subsingleton. -/
private theorem reg0_subsingleton : Subsingleton (Reg 0) :=
  ⟨fun a b => funext fun x => absurd x.isLt (by omega)⟩

/-- The phase factor for a negated angle cancels the complex exponential for that angle. -/
private theorem phase_cancel (a : ℝ) :
    phaseFactor (-a) * Complex.exp (a * Complex.I) = 1 := by
  have h0 : (((-a : ℝ) : ℂ) * Complex.I + (a : ℂ) * Complex.I) = 0 := by
    push_cast; ring
  rw [phaseFactor, ← Complex.exp_add, h0, Complex.exp_zero]

/-- Every unitary on a zero-wire register acts as the identity after multiplication by a
suitable global phase. -/
theorem reg0_unitary_phase (U : Matrix (Reg 0) (Reg 0) ℂ) (hU : U ∈ unitaryGroup (Reg 0) ℂ) :
    ∃ phi : ℝ, ∀ ψ : QState (Reg 0), phaseFactor phi • (U *ᵥ ψ) = ψ := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hu : ∀ i : Reg 0, U i i * (star (U i i)) = 1 := by
    intro i
    have h2 : (U * star U) i i = (1 : Matrix (Reg 0) (Reg 0) ℂ) i i := by
      rw [h1]
    rw [Matrix.mul_apply] at h2
    rw [Fintype.sum_subsingleton _ i] at h2
    simpa [Matrix.one_apply] using! h2
  refine ⟨-(Complex.arg (U default default)), fun ψ => ?_⟩
  have habs : ‖U default default‖ = 1 := by
    have h2 : ‖U default default * star (U default default)‖ = 1 := by
      rw [hu default]; simp
    rw [Complex.norm_mul, norm_star] at h2
    nlinarith [Complex.norm_nonneg (U default default)]
  have hu1 : U default default
      = Complex.exp (Complex.arg (U default default) * Complex.I) := by
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I (U default default)]
    rw [habs]
    norm_num
  have heq : phaseFactor (-(Complex.arg (U default default)))
      * Complex.exp (Complex.arg (U default default) * Complex.I)
      = phaseFactor (-(Complex.arg (U default default))) * U default default :=
    congrArg (fun w => phaseFactor (-(Complex.arg (U default default))) * w) hu1.symm
  have key : phaseFactor (-(Complex.arg (U default default))) * U default default = 1 :=
    heq.symm.trans (phase_cancel _)
  funext i
  rw [Subsingleton.elim i default]
  rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fintype.sum_subsingleton _ default, ← mul_assoc, key, one_mul]

def bigEndianVal : List Bool → ℕ :=
  fun bs => bs.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0

/-- Evaluates `parseSdnat` on a prefix of true bits followed by false and a remaining payload. -/
theorem parseSdnat_replicate_succ (k : ℕ) (rest : List Bool) :
    parseSdnat (List.replicate k true ++ false :: rest) = k + bigEndianVal rest := by
  induction k generalizing rest with
  | zero =>
      simp [List.replicate, bigEndianVal]
      rfl
  | succ k ih =>
      have hsplit : List.replicate (k + 1) true ++ false :: rest
          = true :: (List.replicate k true ++ false :: rest) := by
        simp [List.replicate_succ]
      rw [hsplit]
      show parseSdnat (List.replicate k true ++ false :: rest) + 1 = _
      rw [ih]
      simp [bigEndianVal]
      omega

/-- Evaluates `bitLengthTask` on the specified prefixed input as the self-delimited bit length
of the parsed value. -/
theorem bitLengthTask_replicate_value (k : ℕ) (rest : List Bool) :
    bitLengthTask (List.replicate k true ++ false :: rest)
      = Qatlib.Concepts.ResourceBounds.AsymBounds.selfDelimitBits
          ((k + bigEndianVal rest).bits.length) := by
  unfold bitLengthTask
  rw [parseSdnat_replicate_succ k rest]

/-- Evaluates `parseSdnat2` by splitting off a first payload of the stated length. -/
theorem parseSdnat2_split (k₁ k₂ : ℕ) (p₁ rest₂ : List Bool) (hp : p₁.length = k₁) :
    parseSdnat2 (List.replicate k₁ true ++ false ::
        (p₁ ++ List.replicate k₂ true ++ false :: rest₂))
      = (bigEndianVal p₁, k₂ + bigEndianVal rest₂) := by
  have hinput : List.replicate k₁ true ++ false ::
      (p₁ ++ List.replicate k₂ true ++ false :: rest₂)
      = List.replicate k₁ true ++ (false :: p₁)
          ++ (List.replicate k₂ true ++ false :: rest₂) := by
    simp [List.cons_append]
  rw [hinput]
  have htakewhile : (List.replicate k₁ true ++ (false :: p₁)
      ++ (List.replicate k₂ true ++ false :: rest₂)).takeWhile (fun b => b = true)
        = List.replicate k₁ true := by
    rw [List.takeWhile_append]
    simp [List.takeWhile]
  have hdrop : ∀ n : ℕ, (List.replicate k₁ true ++ (false :: p₁)
      ++ (List.replicate k₂ true ++ false :: rest₂)).drop (k₁ + n)
        = (false :: p₁ ++ (List.replicate k₂ true ++ false :: rest₂)).drop n := by
    intro n
    have h1 : ∀ (m : ℕ) (L : List Bool),
        (List.replicate k₁ true ++ L).drop (k₁ + m) = L.drop m := by
      intro m L
      have hl : (List.replicate k₁ true).length = k₁ := List.length_replicate
      rw [List.drop_append,
        show k₁ + m - (List.replicate k₁ true).length = m by simp [hl]]
      simp
    rw [List.append_assoc, h1]
  simp only [parseSdnat2, htakewhile, List.length_replicate]
  have hd1 := hdrop 1
  rw [hd1]
  have hcone : (false :: p₁ ++ (List.replicate k₂ true ++ false :: rest₂)).drop 1
      = p₁ ++ (List.replicate k₂ true ++ false :: rest₂) := rfl
  rw [hcone]
  have htake1 : (p₁ ++ (List.replicate k₂ true ++ false :: rest₂)).take k₁ = p₁ := by
    rw [List.take_append_of_le_length (by omega), ← hp]
    exact List.take_length
  rw [htake1]
  have hd2' : (List.replicate k₁ true ++ false :: p₁ ++ (List.replicate k₂ true ++ false :: rest₂)).drop (2 * k₁ + 1)
      = (List.replicate k₂ true ++ false :: rest₂) := by
    have h2 := hdrop (k₁ + 1)
    rw [show k₁ + (k₁ + 1) = 2 * k₁ + 1 from by omega] at h2
    have h4 : (p₁ ++ (List.replicate k₂ true ++ false :: rest₂)).drop k₁
        = (List.replicate k₂ true ++ false :: rest₂) := by
      rw [List.drop_append, show k₁ - p₁.length = 0 by omega, ← hp, List.drop_length]
      simp
    have h3 : (false :: p₁ ++ (List.replicate k₂ true ++ false :: rest₂)).drop (k₁ + 1)
        = (List.replicate k₂ true ++ false :: rest₂) := by
      rw [show (false :: p₁ ++ (List.replicate k₂ true ++ false :: rest₂)).drop (k₁ + 1)
          = (p₁ ++ (List.replicate k₂ true ++ false :: rest₂)).drop k₁ from rfl]
      exact h4
    exact h2.trans h3
  rw [hd2', parseSdnat_replicate_succ k₂ rest₂]
  rfl

/-- Evaluates `gcdTask` on the specified split input as the self-delimited greatest common
divisor of the parsed values. -/
theorem gcdTask_value (k₁ k₂ : ℕ) (p₁ rest₂ : List Bool) (hp : p₁.length = k₁) :
    gcdTask (List.replicate k₁ true ++ false ::
        (p₁ ++ List.replicate k₂ true ++ false :: rest₂))
      = Qatlib.Concepts.ResourceBounds.AsymBounds.selfDelimitBits
          (Nat.gcd (bigEndianVal p₁) (k₂ + bigEndianVal rest₂)) := by
  unfold gcdTask
  rw [parseSdnat2_split k₁ k₂ p₁ rest₂ hp]

/-- Evaluates `mulTask` on the specified split input as the self-delimited product of the parsed
values. -/
theorem mulTask_value (k₁ k₂ : ℕ) (p₁ rest₂ : List Bool) (hp : p₁.length = k₁) :
    mulTask (List.replicate k₁ true ++ false ::
        (p₁ ++ List.replicate k₂ true ++ false :: rest₂))
      = Qatlib.Concepts.ResourceBounds.AsymBounds.selfDelimitBits
          (bigEndianVal p₁ * (k₂ + bigEndianVal rest₂)) := by
  unfold mulTask
  rw [parseSdnat2_split k₁ k₂ p₁ rest₂ hp]

end Qatlib.Concepts.UnbiasedBases.ThreeBasis

end
