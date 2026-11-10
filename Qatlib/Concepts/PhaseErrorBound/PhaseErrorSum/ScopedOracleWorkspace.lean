/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Matrix
open scoped Classical

inductive ScopedOracleStep (n : ℕ) where

  | data : Matrix (Reg n) (Reg n) ℂ → ScopedOracleStep n

  | phase : ℂ → ScopedOracleStep n

noncomputable def scopedAncillaPhase (z : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun a : Bool => if a then z else 1)

noncomputable def scopedPhaseCircuit {n : ℕ} (z : ℂ) : Circuit (Bool × Reg n) :=
  [Step.query,
    Step.gate (TensorGate (scopedAncillaPhase z) (1 : Matrix (Reg n) (Reg n) ℂ)),
    Step.query]

noncomputable def scopedDataCircuit {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) :
    Circuit (Bool × Reg n) :=
  [Step.gate (TensorGate (1 : Matrix Bool Bool ℂ) U)]

noncomputable def scopedStepCircuit {n : ℕ} : ScopedOracleStep n → Circuit (Bool × Reg n)
  | .data U => scopedDataCircuit U
  | .phase z => scopedPhaseCircuit z

noncomputable def scopedCompile {n : ℕ} : List (ScopedOracleStep n) → Circuit (Bool × Reg n)
  | [] => []
  | s :: w => scopedStepCircuit s ++ scopedCompile w

noncomputable def scopedPhaseGate {n : ℕ} (f : Reg n → Bool) (z : ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x => if f x then z else 1)

noncomputable def scopedStepMatrix {n : ℕ} (f : Reg n → Bool) : ScopedOracleStep n →
    Matrix (Reg n) (Reg n) ℂ
  | .data U => U
  | .phase z => scopedPhaseGate f z

noncomputable def scopedLogicalMatrix {n : ℕ} (f : Reg n → Bool) :
    List (ScopedOracleStep n) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | s :: w => scopedLogicalMatrix f w * scopedStepMatrix f s

def scopedPhaseCount {n : ℕ} : List (ScopedOracleStep n) → ℕ
  | [] => 0
  | .phase _ :: w => scopedPhaseCount w + 1
  | .data _ :: w => scopedPhaseCount w

def scopedGapTrace {n : ℕ} : ℕ → List (Step (Bool × Reg n)) → List ℕ
  | live, [] => [live]
  | live, _ :: rest => live :: scopedGapTrace live rest

noncomputable def scopedWireTrace {n : ℕ} (w : List (ScopedOracleStep n)) : List ℕ :=
  n :: (scopedGapTrace (n + 1) (scopedCompile w) ++ [n])

noncomputable def scopedBitOracle {n : ℕ} (f : Reg n → Bool) :
    Matrix (Bool × Reg n) (Bool × Reg n) ℂ :=
  relabelGate (Equiv.prodComm (Reg n) Bool) (BitOracleOn f)

noncomputable def scopedAllocationFrame (n : ℕ) : Matrix (Bool × Reg n) (Reg n) ℂ :=
  fun p x => if p = (false, x) then 1 else 0

theorem applyGate_scopedBitOracle {n : ℕ} (f : Reg n → Bool) (χ : QState (Bool × Reg n))
    (a : Bool) (x : Reg n) :
    ApplyGate (scopedBitOracle f) χ (a, x) = χ (a ^^ f x, x) := by
  set e := Equiv.prodComm (Reg n) Bool with hE
  have h := applyGate_relabelGate e (BitOracleOn f) (relabelState e.symm χ)
  have hχ : relabelState e (relabelState e.symm χ) = χ := by
    have h := relabelState_relabelState e.symm χ
    rwa [Equiv.symm_symm] at h
  calc ApplyGate (scopedBitOracle f) χ (a, x)
      = ApplyGate (relabelGate e (BitOracleOn f)) (relabelState e (relabelState e.symm χ))
          (a, x) := by rw [scopedBitOracle, hE, hχ]
    _ = relabelState e (ApplyGate (BitOracleOn f) (relabelState e.symm χ)) (a, x) := by rw [h]
    _ = ApplyGate (BitOracleOn f) (relabelState e.symm χ) (x, a) := rfl
    _ = relabelState e.symm χ (BitFlip f (x, a)) := applyGate_bitOracleOn f _ (x, a)
    _ = χ (a ^^ f x, x) := rfl

private theorem applyGate_tensorGate_apply {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (U : Matrix I I ℂ) (V : Matrix J J ℂ)
    (χ : QState (I × J)) (i : I) (j : J) :
    ApplyGate (TensorGate U V) χ (i, j) = ∑ k, U i k * (∑ l, V j l * χ (k, l)) := by
  calc ApplyGate (TensorGate U V) χ (i, j)
      = ∑ p, (U i p.1 * V j p.2) * χ p := by
        simp only [ApplyGate, TensorGate, Matrix.kroneckerMap, Matrix.of_apply, Matrix.mulVec,
          dotProduct]
    _ = ∑ k, ∑ l, (U i k * V j l) * χ (k, l) := by rw [Fintype.sum_prod_type]
    _ = ∑ k, ∑ l, U i k * (V j l * χ (k, l)) :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => mul_assoc _ _ _
    _ = ∑ k, U i k * (∑ l, V j l * χ (k, l)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact (Finset.mul_sum Finset.univ _ _).symm

private theorem applyGate_tensorGate_ancilla {n : ℕ} (U : Matrix Bool Bool ℂ)
    (χ : QState (Bool × Reg n)) (a : Bool) (x : Reg n) :
    ApplyGate (TensorGate U (1 : Matrix (Reg n) (Reg n) ℂ)) χ (a, x)
      = ∑ b, U a b * χ (b, x) := by
  rw [applyGate_tensorGate_apply]
  have hone : ∀ (g : Reg n → ℂ) (y : Reg n),
      (∑ l, (1 : Matrix (Reg n) (Reg n) ℂ) y l * g l) = g y := by
    intro g y
    rw [Finset.sum_eq_single y]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro hb
      exact (hb (Finset.mem_univ y)).elim
  simp only [hone]

theorem applyGate_scopedPhaseGate {n : ℕ} (f : Reg n → Bool) (z : ℂ)
    (ψ : QState (Reg n)) (x : Reg n) :
    ApplyGate (scopedPhaseGate f z) ψ x = (if f x then z else 1) * ψ x := by
  unfold scopedPhaseGate ApplyGate
  rw [Matrix.mulVec_diagonal]

theorem run_scopedDataCircuit {n : ℕ} (f : Reg n → Bool) (U : Matrix (Reg n) (Reg n) ℂ)
    (ψ : QState (Reg n)) :
    Run (scopedBitOracle f) (scopedDataCircuit U) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ)
      = TensorState (Qatlib.Foundations.PureStateMath.Ket false) (ApplyGate U ψ) := by
  simp only [scopedDataCircuit, run_gate, run_nil]
  rw [applyGate_tensorGate, applyGate_one]

theorem run_scopedPhaseCircuit {n : ℕ} (f : Reg n → Bool) (z : ℂ) (ψ : QState (Reg n)) :
    Run (scopedBitOracle f) (scopedPhaseCircuit z) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ)
      = TensorState (Qatlib.Foundations.PureStateMath.Ket false) (ApplyGate (scopedPhaseGate f z) ψ) := by
  funext p
  obtain ⟨a, x⟩ := p

  have hclean : ∀ (b : Bool) (y : Reg n),
      ApplyGate (scopedBitOracle f) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) (b, y)
        = Qatlib.Foundations.PureStateMath.Ket false (b ^^ f y) * ψ y := by
    intro b y
    rw [applyGate_scopedBitOracle, TensorState]

  have hgate : ∀ (b : Bool) (y : Reg n),
      ApplyGate (TensorGate (scopedAncillaPhase z) (1 : Matrix (Reg n) (Reg n) ℂ))
          (ApplyGate (scopedBitOracle f) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ)) (b, y)
        = (if b then z else 1) * (Qatlib.Foundations.PureStateMath.Ket false (b ^^ f y) * ψ y) := by
    intro b y
    rw [applyGate_tensorGate_ancilla]
    simp only [hclean, scopedAncillaPhase, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · intro hb
      exact (hb (Finset.mem_univ b)).elim
  have hR : TensorState (Qatlib.Foundations.PureStateMath.Ket false) (ApplyGate (scopedPhaseGate f z) ψ) (a, x)
      = Qatlib.Foundations.PureStateMath.Ket false a * ((if f x then z else 1) * ψ x) := by
    rw [tensorState_apply, applyGate_scopedPhaseGate]
  simp only [scopedPhaseCircuit, run_query, run_gate, run_nil]
  rw [hR, applyGate_scopedBitOracle, hgate]
  cases a <;> cases f x <;> simp [Qatlib.Foundations.PureStateMath.Ket]

theorem scoped_bit_oracle_actual_toggle_unitary :
    ∀ (n : ℕ) (f : Reg n → Bool) (a b : Bool) (x y : Reg n),
      scopedBitOracle f (a,x) (b,y) = (if x=y ∧ a=(b ^^ f y) then 1 else 0) ∧
      scopedBitOracle f ∈ Matrix.unitaryGroup (Bool × Reg n) ℂ := by
  intro n f a b x y
  have hpt : scopedBitOracle f (a,x) (b,y) = BitOracleOn f (x,a) (y,b) := by
    simp only [scopedBitOracle, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]
    rfl
  constructor
  · rw [hpt]
    simp only [BitOracleOn, permMatrix, Matrix.of_apply, BitFlip]
    by_cases h : (x, a) = (y, b ^^ f y)
    · rw [if_pos h, if_pos]
      exact Prod.mk.inj h
    · rw [if_neg h, if_neg]
      intro h'
      exact h (Prod.ext h'.1 h'.2)
  · exact (relabelGate_mem_unitaryGroup (Equiv.prodComm (Reg n) Bool) (BitOracleOn f)).2
      (bitOracleOn_unitary f)

theorem scoped_phase_word_actual_compile :
    ∀ (n : ℕ) (z : ℂ),
      scopedCompile [ScopedOracleStep.phase (n:=n) z] =
        [Step.query, Step.gate (TensorGate (Matrix.diagonal (fun a : Bool => if a then z else 1)) (1:Matrix (Reg n) (Reg n) ℂ)), Step.query] :=
  by
    intro n z
    show scopedStepCircuit (ScopedOracleStep.phase (n := n) z) ++ scopedCompile []
      = _
    rfl

theorem scoped_run_clean {n : ℕ} (f : Reg n → Bool) :
    ∀ (w : List (ScopedOracleStep n)) (ψ : QState (Reg n)),
      Run (scopedBitOracle f) (scopedCompile w) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ)
        = TensorState (Qatlib.Foundations.PureStateMath.Ket false) (scopedLogicalMatrix f w *ᵥ ψ) := by
  intro w
  induction w with
  | nil =>
      intro ψ
      simp only [scopedCompile, run_nil, scopedLogicalMatrix]
      rw [Matrix.one_mulVec]
  | cons s w ih =>
      intro ψ
      cases s with
      | data U =>
          rw [scopedCompile, run_append, scopedStepCircuit, run_scopedDataCircuit, ih,
            scopedLogicalMatrix]
          show TensorState (Qatlib.Foundations.PureStateMath.Ket false)
              (scopedLogicalMatrix f w *ᵥ (U *ᵥ ψ)) = _
          rw [Matrix.mulVec_mulVec, scopedStepMatrix]
      | phase z =>
          rw [scopedCompile, run_append, scopedStepCircuit, run_scopedPhaseCircuit, ih,
            scopedLogicalMatrix]
          show TensorState (Qatlib.Foundations.PureStateMath.Ket false)
              (scopedLogicalMatrix f w *ᵥ (scopedPhaseGate f z *ᵥ ψ)) = _
          rw [Matrix.mulVec_mulVec, scopedStepMatrix]

theorem scoped_phaseGate_neg_eq_preparedMark {n : ℕ} (f : Reg n → Bool) :
    scopedPhaseGate f (-1) = preparedMark (Finset.univ.filter (fun x => f x=true)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have hmem : ∀ x : Reg n, (x ∈ Finset.univ.filter (fun y => f y = true)) ↔ f x = true := by
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hf : f i = true
    · have hiS : i ∈ Finset.univ.filter (fun y => f y = true) := (hmem i).2 hf
      simp only [scopedPhaseGate, Matrix.diagonal_apply, preparedMark, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, Projector, Matrix.diagonal_apply, if_pos hf,
        if_pos hiS]
      norm_num
    · have hiS : ¬ (i ∈ Finset.univ.filter (fun y => f y = true)) :=
        fun h => hf ((hmem i).mp h)
      simp only [scopedPhaseGate, Matrix.diagonal_apply, preparedMark, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, Projector, Matrix.diagonal_apply, if_neg hf,
        if_neg hiS]
      norm_num
  · simp [hij, scopedPhaseGate, preparedMark, Projector]

theorem scoped_program_clean_semantics :
    ∀ (n : ℕ) (f : Reg n → Bool) (w : List (ScopedOracleStep n)) (ψ : QState (Reg n)),
      Run (scopedBitOracle f) (scopedCompile w) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) =
        TensorState (Qatlib.Foundations.PureStateMath.Ket false) (scopedLogicalMatrix f w *ᵥ ψ) ∧
      scopedPhaseGate f (-1) = preparedMark (Finset.univ.filter (fun x => f x=true)) := by
  intro n f w ψ
  exact ⟨scoped_run_clean f w ψ, scoped_phaseGate_neg_eq_preparedMark f⟩

theorem scoped_program_actual_query_and_gate_counts :
    ∀ (n : ℕ) (w : List (ScopedOracleStep n)),
      scopedPhaseCount w = (w.filter (fun s => match s with | .phase _ => true | .data _ => false)).length ∧
      QueryCount (scopedCompile w) = 2*scopedPhaseCount w ∧ GateCount (scopedCompile w) = w.length := by
  intro n w
  have hq : ∀ (v : List (ScopedOracleStep n)),
      QueryCount (scopedCompile v) = 2 * scopedPhaseCount v := by
    intro v
    induction v with
    | nil => rfl
    | cons s v ih =>
        cases s with
        | data U =>
            rw [scopedCompile, scopedStepCircuit, queryCount_append, scopedDataCircuit]
            simp only [queryCount_nil, queryCount_gate, ih, scopedPhaseCount]
            omega
        | phase z =>
            rw [scopedCompile, scopedStepCircuit, queryCount_append, scopedPhaseCircuit]
            simp only [queryCount_nil, queryCount_query, queryCount_gate, ih, scopedPhaseCount]
            ring
  have hg : ∀ (v : List (ScopedOracleStep n)),
      GateCount (scopedCompile v) = v.length := by
    intro v
    induction v with
    | nil => rfl
    | cons s v ih =>
        cases s with
        | data U =>
            rw [scopedCompile, scopedStepCircuit, gateCount_append, scopedDataCircuit]
            simp only [gateCount_nil, gateCount_gate, List.length_cons, ih]
            omega
        | phase z =>
            rw [scopedCompile, scopedStepCircuit, gateCount_append, scopedPhaseCircuit]
            simp only [gateCount_nil, gateCount_query, gateCount_gate, List.length_cons, ih]
            omega
  refine ⟨?_, hq w, hg w⟩
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simp [scopedPhaseCount, ih]

private theorem scopedAncillaPhase_unitary {z : ℂ} (hz : ‖z‖ = 1) :
    scopedAncillaPhase z ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, scopedAncillaPhase,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.one_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    cases i
    · simp
    · have hzz : (starRingEnd ℂ) z * z = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz, sq]
        norm_num
      simp [hzz]
  · simp [hij]

theorem scoped_program_unitarity_from_instruction_data :
    ∀ (n : ℕ) (w : List (ScopedOracleStep n)),
      (∀ U, ScopedOracleStep.data U ∈ w → U ∈ Matrix.unitaryGroup (Reg n) ℂ) →
      (∀ z, ScopedOracleStep.phase z ∈ w → ‖z‖=1) → IsUnitaryCircuit (scopedCompile w) := by
  intro n w
  have hone₁ : (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ := Submonoid.one_mem _
  have hone₂ : (1 : Matrix (Reg n) (Reg n) ℂ) ∈ Matrix.unitaryGroup (Reg n) ℂ :=
    Submonoid.one_mem _
  intro hU hZ
  induction w with
  | nil => exact isUnitaryCircuit_nil
  | cons s w ih =>
      have hU' : ∀ U, ScopedOracleStep.data U ∈ w → U ∈ Matrix.unitaryGroup (Reg n) ℂ :=
        fun U h => hU U (List.mem_cons_of_mem _ h)
      have hZ' : ∀ z, ScopedOracleStep.phase z ∈ w → ‖z‖ = 1 :=
        fun z h => hZ z (List.mem_cons_of_mem _ h)
      rw [scopedCompile, isUnitaryCircuit_append]
      refine ⟨?_, ih hU' hZ'⟩
      cases s with
      | data U =>
          rw [scopedStepCircuit, scopedDataCircuit, isUnitaryCircuit_gate]
          exact ⟨tensorGate_unitary hone₁ (hU U List.mem_cons_self), isUnitaryCircuit_nil⟩
      | phase z =>
          rw [scopedStepCircuit, scopedPhaseCircuit, isUnitaryCircuit_query,
            isUnitaryCircuit_gate, isUnitaryCircuit_query]
          exact ⟨tensorGate_unitary (scopedAncillaPhase_unitary (hZ z List.mem_cons_self))
            hone₂, isUnitaryCircuit_nil⟩

theorem scoped_allocationFrame_conjTranspose_mul {n : ℕ} :
    (scopedAllocationFrame n)ᴴ * scopedAllocationFrame n = 1 := by
  ext x y
  have hstar : ∀ p : Bool × Reg n, (starRingEnd ℂ) (if p = (false, x) then 1 else 0)
      = (if p = (false, x) then 1 else 0) := by
    intro p
    by_cases h : p = (false, x) <;> simp [h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    scopedAllocationFrame, RCLike.star_def, hstar]
  rw [Finset.sum_eq_single (false, x)]
  · by_cases hxy : x = y <;> simp [hxy]
  · intro p _ hp
    simp [hp]
  · intro hb
    exact (hb (Finset.mem_univ (false, x))).elim

theorem scoped_allocationFrame_mulVec {n : ℕ} (ψ : QState (Reg n)) :
    scopedAllocationFrame n *ᵥ ψ = TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ := by
  funext p
  obtain ⟨a, y⟩ := p
  by_cases ha : a = false
  · subst ha
    simp [Matrix.mulVec, dotProduct, scopedAllocationFrame,
        Qatlib.Foundations.PureStateMath.Ket, TensorState]
  · simp [Matrix.mulVec, dotProduct, scopedAllocationFrame,
      Qatlib.Foundations.PureStateMath.Ket, TensorState, ha]

theorem scopedGapTrace_eq {n : ℕ} (live : ℕ) (C : List (Step (Bool × Reg n))) :
    scopedGapTrace live C = List.replicate (C.length + 1) live := by
  induction C with
  | nil => simp [scopedGapTrace, List.replicate]
  | cons s C ih => simp [scopedGapTrace, List.replicate, ih]

theorem scoped_allocation_release_and_peak_trace :
    ∀ (n : ℕ) (w : List (ScopedOracleStep n)),
      (scopedAllocationFrame n)ᴴ * scopedAllocationFrame n = 1 ∧
      (∀ ψ : QState (Reg n), scopedAllocationFrame n *ᵥ ψ = TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) ∧
      scopedWireTrace w = [n] ++ List.replicate ((scopedCompile w).length+1) (n+1) ++ [n] ∧
      (scopedWireTrace w).foldl max 0 = n+1 := by
  intro n w
  have hrep : ∀ (m : ℕ) (a b : ℕ), a ≤ b →
      (List.replicate m b).foldl max a = if m = 0 then a else b := by
    intro m
    induction m with
    | zero =>
        intro a b h
        simp [List.replicate]
    | succ m ih =>
        intro a b h
        have hstep : (List.replicate (m + 1) b).foldl max a
            = (List.replicate m b).foldl max (max a b) := by
          rw [List.replicate_succ, List.foldl_cons]
        rw [hstep, max_eq_right h, ih b b (le_refl b)]
        simp
  have hshape : scopedWireTrace w
      = [n] ++ List.replicate ((scopedCompile w).length+1) (n+1) ++ [n] := by
    rw [scopedWireTrace, scopedGapTrace_eq]
    rfl
  have hone : List.foldl max 0 [n] = n := by simp [List.foldl]
  have hmid : (List.replicate ((scopedCompile w).length+1) (n+1)).foldl max n = n+1 := by
    have h := hrep ((scopedCompile w).length+1) n (n+1) (Nat.le_succ n)
    rw [if_neg (by omega : ¬((scopedCompile w).length+1 = 0))] at h
    exact h
  refine ⟨scoped_allocationFrame_conjTranspose_mul, scoped_allocationFrame_mulVec,
    hshape, ?_⟩
  rw [hshape, List.foldl_append]
  simp [hmid]

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
