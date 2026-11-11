/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Counted phase reflections

This module constructs `phaseReflectionWord` from repeated phase detection, reflection about the
all-zero readout event, and inverse detection. It formalizes the phase-estimation reflection
method of [MagniezNayakRolandSantha2011] with explicit forward and inverse query counts.

The execution lemmas express eigenstate readout as `phaseKernelPacket` and bound reflection
errors using the zero-label QPE kernel. An orthonormal eigenfamily with a separated zero-phase
target gives a uniform error estimate for every linear combination in its span.

## Main statements

* `phase_reflection_actual_queries_and_macros`: exact query and gate counts for the reflection
  word.
* `phase_reflection_actual_eigenstate_error`: exact zero-phase action and a kernel bound on the
  residual.
* `phase_reflection_reachable_source_error`: error relative to reflection about a distinguished
  zero-phase eigenvector.

## References

* [Magniez et al., 2011, Theorem 6][MagniezNayakRolandSantha2011]
* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.SpectralFilter.PhaseReadout

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator

set_option autoImplicit false

/-- Four times the circular distance of a phase from zero is bounded by the chord length from
its unit complex exponential to one. -/
theorem phase_chord_lower_bound (φ : ℝ) :
    4 * phaseDistance φ 0 ≤ ‖Complex.exp (2 * Real.pi * Complex.I * φ) - 1‖ := by
  let n : ℤ := ⌊φ + 1 / 2⌋
  let δ : ℝ := φ - (n : ℝ)
  have hlo : -(1 / 2 : ℝ) ≤ δ := by
    have hn := Int.floor_le (φ + 1 / 2)
    dsimp [δ, n]
    linarith
  have hhi : δ ≤ 1 / 2 := by
    have hn := Int.lt_floor_add_one (φ + 1 / 2)
    dsimp [δ, n]
    linarith
  have habs : |δ| ≤ 1 / 2 := abs_le.mpr ⟨hlo, hhi⟩
  have he : Complex.exp (2 * Real.pi * Complex.I * φ) =
      Complex.exp (2 * Real.pi * Complex.I * δ) := by
    have hφ : φ = δ + (n : ℝ) := by dsimp [δ]; ring
    rw [hφ, Complex.ofReal_add, show (2 * Real.pi * Complex.I * (δ + (n : ℝ)) : ℂ) =
      2 * Real.pi * Complex.I * δ + 2 * Real.pi * Complex.I * (n : ℝ) by push_cast; ring,
      Complex.exp_add, exp_two_pi_I_int, mul_one]
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi * δ) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  rw [abs_mul, abs_of_pos Real.pi_pos,
    show 2 / Real.pi * (Real.pi * |δ|) = 2 * |δ| by field_simp] at hs
  have hd : phaseDistance φ 0 = |δ| := by simp only [phaseDistance, sub_zero]; rfl
  rw [hd, he, show (2 * Real.pi * Complex.I * δ : ℂ) =
      Complex.I * ((2 * Real.pi * δ : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2 * Real.pi * δ) / 2 = Real.pi * δ by ring, Real.norm_eq_abs, abs_mul]
  norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  linarith

/-- A phase at circular distance at least `η > 0` from zero has zero-label QPE amplitude at most
`1 / (2*M*η)`. -/
theorem phase_detection_zero_label_gap_bound (M : ℕ) (hM : 0 < M) (φ η : ℝ)
    (hη : 0 < η) (hgap : η ≤ phaseDistance φ 0) :
    ‖qpeKernel M φ (⟨0, hM⟩ : Fin M)‖ ≤ 1 / (2 * (M : ℝ) * η) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hd : 4 * η ≤ ‖Complex.exp (2 * Real.pi * Complex.I * φ) - 1‖ :=
    (mul_le_mul_of_nonneg_left hgap (by norm_num)).trans (phase_chord_lower_bound φ)
  have he := qpeKernel_geometric_identity M φ (⟨0, hM⟩ : Fin M) hM
  simp at he
  have hn := congrArg norm he
  rw [norm_mul, norm_mul, Complex.norm_natCast] at hn
  have hnum : ‖Complex.exp (2 * Real.pi * Complex.I * ((M : ℝ) * φ)) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (2 * Real.pi * Complex.I * ((M : ℝ) * φ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [← Complex.ofReal_mul, norm_exp_two_pi_I, norm_one]; norm_num
  push_cast at hnum
  apply (le_div_iff₀ (by positivity : 0 < 2 * (M : ℝ) * η)).mpr
  have hp := mul_le_mul_of_nonneg_left hd
    (mul_nonneg hMr.le (norm_nonneg (qpeKernel M φ (⟨0, hM⟩ : Fin M))))
  nlinarith [hn, hnum]

/-- The basis index type for `k` phase registers, one control bit, and the data register. -/
abbrev PhaseReflectionSpace (I : Type) (M k : ℕ) := (Fin k → Fin M) × (Bool × I)

/-- Split off the first phase register, leaving the remaining phase registers together with the
control and data registers. -/
def phaseTailSplit (I : Type) (M k : ℕ) :
    PhaseReflectionSpace I M (k + 1) ≃ Fin M × PhaseReflectionSpace I M k where
  toFun p := (p.1 0, (fun j => p.1 j.succ, p.2))
  invFun p := (Fin.cons p.1 p.2.1, p.2.2)
  left_inv p := by
    rcases p with ⟨x, d⟩
    (try dsimp only)
    refine Prod.ext ?_ rfl
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    rcases p with ⟨x, xs, d⟩
    refine Prod.ext (by simp) ?_
    refine Prod.ext ?_ rfl
    funext i
    simp

/-- Rearrange the registers so that the first phase register is grouped with the control and
data registers. -/
def phaseHeadSplit (I : Type) (M k : ℕ) :
    PhaseReflectionSpace I M (k + 1) ≃
      (Fin k → Fin M) × (Fin M × (Bool × I)) :=
  (phaseTailSplit I M k).trans
    { toFun := fun p => (p.2.1, (p.1, p.2.2))
      invFun := fun p => (p.2.1, (p.1, p.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Lift the matrix gate in an adjoint instruction through `F`, retaining forward and backward
oracle instructions. -/
noncomputable def phaseLiftStep {H K : Type}
    (F : Matrix H H ℂ → Matrix K K ℂ) : AdjointStep H → AdjointStep K
  | .gate U => .gate (F U)
  | .forward => .forward
  | .backward => .backward

/-- Lift all matrix gates of an adjoint circuit word through `F`. -/
noncomputable def phaseLiftWord {H K : Type}
    (F : Matrix H H ℂ → Matrix K K ℂ) (cs : List (AdjointStep H)) :
    List (AdjointStep K) := cs.map (phaseLiftStep F)

/-- Lifting an adjoint word preserves its query and gate counts. -/
theorem phaseLiftWord_counts {H K : Type}
    (F : Matrix H H ℂ → Matrix K K ℂ) (cs : List (AdjointStep H)) :
    adjointQueryCount (phaseLiftWord F cs) = adjointQueryCount cs ∧
      adjointGateCount (phaseLiftWord F cs) = adjointGateCount cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih => cases c <;> simp [phaseLiftWord, phaseLiftStep, adjointQueryCount,
      adjointGateCount, ← ih.1, ← ih.2]

/-- A gate lift that preserves unitary matrices preserves well-formedness of adjoint circuit
words. -/
theorem phaseLiftWord_wellFormed {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (F : Matrix H H ℂ → Matrix K K ℂ)
    (hF : ∀ U, U ∈ Matrix.unitaryGroup H ℂ → F U ∈ Matrix.unitaryGroup K ℂ)
    {cs : List (AdjointStep H)} (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (phaseLiftWord F cs) := by
  intro V hV
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hV
  cases c with
  | gate U =>
    simp only [phaseLiftStep, AdjointStep.gate.injEq] at he
    rw [← he]
    exact hF U (hcs U hc)
  | forward => cases he
  | backward => cases he

/-- Translate a circuit step into an adjoint instruction, sending a query to a forward oracle
call. -/
noncomputable def phaseForwardStep {H : Type} : Step H → AdjointStep H
  | .gate U => .gate U
  | .query => .forward

/-- Compile a circuit into an adjoint word by reversing its step list and translating queries to
forward calls. -/
noncomputable def phaseCompileCircuit {H : Type} (cs : Circuit H) : List (AdjointStep H) :=
  cs.reverse.map phaseForwardStep

/-- Compilation preserves the query and gate counts of a circuit. -/
theorem phaseCompileCircuit_counts {H : Type} (cs : Circuit H) :
    adjointQueryCount (phaseCompileCircuit cs) = QueryCount cs ∧
      adjointGateCount (phaseCompileCircuit cs) = GateCount cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [phaseCompileCircuit, List.reverse_cons, adjointQueryCount_append,
      adjointGateCount_append, phaseForwardStep, adjointQueryCount, adjointGateCount,
      QueryCount, GateCount, ← ih.1, ← ih.2]

/-- Compiling a unitary circuit yields a well-formed adjoint circuit word. -/
theorem phaseCompileCircuit_wellFormed {H : Type} [Fintype H] [DecidableEq H]
    {cs : Circuit H} (hcs : IsUnitaryCircuit cs) :
    WellFormedAdjointCircuit (phaseCompileCircuit cs) := by
  intro V hV
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hV
  have hc' : c ∈ cs := List.mem_reverse.mp hc
  cases c with
  | gate U =>
    simp only [phaseForwardStep, AdjointStep.gate.injEq] at he
    subst V
    exact hcs U hc'
  | query => cases he

section PhaseWords

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Extend a gate on the tail phase registers, control, and data by the identity on the first
phase register. -/
noncomputable def phaseTailGate (M k : ℕ)
    (U : Matrix (PhaseReflectionSpace I M k) (PhaseReflectionSpace I M k) ℂ) :
    Matrix (PhaseReflectionSpace I M (k + 1)) (PhaseReflectionSpace I M (k + 1)) ℂ :=
  relabelGate (phaseTailSplit I M k).symm (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) U)

/-- Extend a gate on the first phase register, control, and data by the identity on the
remaining phase registers. -/
noncomputable def phaseHeadGate (M k : ℕ)
    (U : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ) :
    Matrix (PhaseReflectionSpace I M (k + 1)) (PhaseReflectionSpace I M (k + 1)) ℂ :=
  relabelGate (phaseHeadSplit I M k).symm
    (TensorGate (1 : Matrix (Fin k → Fin M) (Fin k → Fin M) ℂ) U)

/-- The recursive adjoint word performing one counted phase-estimation circuit for each phase
register. -/
noncomputable def phaseDetectionWord (M : ℕ) : (k : ℕ) →
    List (AdjointStep (PhaseReflectionSpace I M k))
  | 0 => []
  | k + 1 =>
      phaseLiftWord (phaseTailGate M k) (phaseDetectionWord M k) ++
      phaseLiftWord (phaseHeadGate M k) (phaseCompileCircuit (countedPhaseCircuit M))

/-- The basis event in which every phase register has label zero. -/
def phaseZeroEvent (M k : ℕ) : Finset (PhaseReflectionSpace I M k) :=
  Finset.univ.filter (fun p => ∀ j, (p.1 j).val = 0)

/-- Reflection about the subspace whose phase registers all have label zero. -/
noncomputable def phaseZeroReflection (M k : ℕ) :
    Matrix (PhaseReflectionSpace I M k) (PhaseReflectionSpace I M k) ℂ :=
  ReflectionAbout (Projector (phaseZeroEvent M k))

/-- The adjoint word combining inverse detection, zero-event reflection, and detection to
implement a phase reflection. -/
noncomputable def phaseReflectionWord (M k : ℕ) :
    List (AdjointStep (PhaseReflectionSpace I M k)) :=
  adjointCircuit (phaseDetectionWord M k) ++ [.gate (phaseZeroReflection M k)] ++
    phaseDetectionWord M k

/-- For positive `M`, repeated phase detection is well formed and uses `k*(M-1)` queries and
`k*(2*(M-1)+2)` gates. -/
theorem phaseDetectionWord_resources (M k : ℕ) (hM : 0 < M) :
    WellFormedAdjointCircuit (phaseDetectionWord (I := I) M k) ∧
      adjointQueryCount (phaseDetectionWord (I := I) M k) = k * (M - 1) ∧
      adjointGateCount (phaseDetectionWord (I := I) M k) = k * (2 * (M - 1) + 2) := by
  have hr := (counted_offgrid_qpe_clean_flag M hM (1 : Matrix I I ℂ) 0).2
  have hsingle := phaseCompileCircuit_counts (countedPhaseCircuit (I := I) M)
  have hw := phaseCompileCircuit_wellFormed hr.2.2
  induction k with
  | zero => exact ⟨WellFormedAdjointCircuit.nil, by simp [phaseDetectionWord, adjointQueryCount],
      by simp [phaseDetectionWord, adjointGateCount]⟩
  | succ k ih =>
    have htail : WellFormedAdjointCircuit
        (phaseLiftWord (phaseTailGate (I := I) M k) (phaseDetectionWord M k)) :=
      phaseLiftWord_wellFormed _ (fun U hU =>
        (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary (by simp) hU)) ih.1
    have hhead : WellFormedAdjointCircuit (phaseLiftWord (phaseHeadGate (I := I) M k)
        (phaseCompileCircuit (countedPhaseCircuit M))) :=
      phaseLiftWord_wellFormed _ (fun U hU =>
        (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary (by simp) hU)) hw
    refine ⟨htail.append hhead, ?_, ?_⟩
    · rw [phaseDetectionWord, adjointQueryCount_append, (phaseLiftWord_counts _ _).1,
        (phaseLiftWord_counts _ _).1, ih.2.1, hsingle.1, hr.1]
      ring
    · rw [phaseDetectionWord, adjointGateCount_append, (phaseLiftWord_counts _ _).2,
        (phaseLiftWord_counts _ _).2, ih.2.2, hsingle.2, hr.2.1]
      ring

/-- For `M ≥ 2`, the phase-reflection word is well formed and uses `2*k*(M-1)` queries and
`4*k*(M-1)+4*k+1` gates. This gives explicit resources for the reflection construction in
[MagniezNayakRolandSantha2011]. -/
theorem phase_reflection_actual_queries_and_macros (M k : ℕ) (hM : 2 ≤ M) :
    WellFormedAdjointCircuit (phaseReflectionWord (I := I) M k) ∧
      adjointQueryCount (phaseReflectionWord (I := I) M k) = 2 * k * (M - 1) ∧
      adjointGateCount (phaseReflectionWord (I := I) M k) = 4 * k * (M - 1) + 4 * k + 1 := by
  obtain ⟨hw, hq, hg⟩ := phaseDetectionWord_resources (I := I) M k (by omega)
  have hz : WellFormedAdjointCircuit
      ([.gate (phaseZeroReflection (I := I) M k)] : List (AdjointStep (PhaseReflectionSpace I M k))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact reflectionAbout_unitary (projector_isOrthogonalProjector _)
  refine ⟨(hw.adjointCircuit.append hz).append hw, ?_, ?_⟩
  · simp only [phaseReflectionWord, adjointQueryCount_append, adjointQueryCount_adjointCircuit,
      adjointQueryCount, hq]
    ring
  · simp only [phaseReflectionWord, adjointGateCount_append, adjointGateCount_adjointCircuit,
      adjointGateCount, hg]
    ring

end PhaseWords

/-- Embed a data state with the control bit false and all phase registers initialized to zero. -/
noncomputable def phaseReflectionEmbed {I : Type} (M k : ℕ) (ψ : QState I) :
    QState (PhaseReflectionSpace I M k) :=
  fun p => if p.2.1 = false ∧ ∀ j, (p.1 j).val = 0 then ψ p.2.2 else 0

/-- The state obtained by applying the evaluated phase-reflection word to the zero-ancilla
embedding of the input. -/
noncomputable def phaseReflectionState {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (M k : ℕ) (ψ : QState I) :
    QState (PhaseReflectionSpace I M k) :=
  ApplyGate (evaluate (parallelOracle (controlOracle W)) (phaseReflectionWord M k))
    (phaseReflectionEmbed M k ψ)

/-- Evaluating the compiled adjoint word and applying it to a state agrees with the original
circuit execution. -/
theorem phaseCompileCircuit_evaluate {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (cs : Circuit H) (ψ : QState H) :
    ApplyGate (evaluate U (phaseCompileCircuit cs)) ψ = Run U cs ψ := by
  induction cs generalizing ψ with
  | nil => simp [phaseCompileCircuit, evaluate, Run, applyGate_one]
  | cons c cs ih =>
    rw [show phaseCompileCircuit (c :: cs) = phaseCompileCircuit cs ++ [phaseForwardStep c] by
      simp only [phaseCompileCircuit, List.reverse_cons, List.map_append, List.map_cons,
          List.map_nil],
      evaluate_append, applyGate_mul, ih]
    cases c <;> simp [phaseForwardStep, evaluate, instructionMatrix, Run]

/-- A lift preserving the identity, multiplication, and adjoints commutes with adjoint-word
evaluation. -/
theorem phaseLiftWord_evaluate {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (F : Matrix H H ℂ → Matrix K K ℂ)
    (h1 : F 1 = 1) (hm : ∀ U V, F (U * V) = F U * F V)
    (ha : ∀ U, F Uᴴ = (F U)ᴴ) (U : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate (F U) (phaseLiftWord F cs) = F (evaluate U cs) := by
  induction cs with
  | nil => exact h1.symm
  | cons c cs ih =>
    simp only [phaseLiftWord] at ih
    cases c <;> simp [phaseLiftWord, phaseLiftStep, evaluate, instructionMatrix, ih, hm, ha]

/-- Taking a conjugate transpose commutes with relabeling a matrix gate. -/
private theorem phase_relabel_adjoint {H K : Type} (e : H ≃ K) (U : Matrix H H ℂ) :
    (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  rfl

section Evaluation

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Lifting the identity gate to the tail registers yields the identity. -/
private theorem phaseTailGate_one (M k : ℕ) : phaseTailGate (I := I) M k 1 = 1 := by
  rw [phaseTailGate, tensorGate_one, CircuitRelabel.relabelGate_one]

/-- Lifting to the tail registers preserves matrix multiplication. -/
private theorem phaseTailGate_mul (M k : ℕ)
    (U V : Matrix (PhaseReflectionSpace I M k) (PhaseReflectionSpace I M k) ℂ) :
    phaseTailGate M k (U * V) = phaseTailGate M k U * phaseTailGate M k V := by
  unfold phaseTailGate
  rw [← CircuitRelabel.relabelGate_mul, tensorGate_mul, Matrix.one_mul]

/-- Lifting to the tail registers commutes with conjugate transpose. -/
private theorem phaseTailGate_adjoint (M k : ℕ)
    (U : Matrix (PhaseReflectionSpace I M k) (PhaseReflectionSpace I M k) ℂ) :
    phaseTailGate M k Uᴴ = (phaseTailGate M k U)ᴴ := by
  rw [phaseTailGate, phaseTailGate, phase_relabel_adjoint, tensorGate_conjTranspose,
    Matrix.conjTranspose_one]

/-- Lifting the identity gate to the head registers yields the identity. -/
private theorem phaseHeadGate_one (M k : ℕ) : phaseHeadGate (I := I) M k 1 = 1 := by
  rw [phaseHeadGate, tensorGate_one, CircuitRelabel.relabelGate_one]

/-- Lifting to the head registers preserves matrix multiplication. -/
private theorem phaseHeadGate_mul (M k : ℕ)
    (U V : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ) :
    phaseHeadGate M k (U * V) = phaseHeadGate M k U * phaseHeadGate M k V := by
  unfold phaseHeadGate
  rw [← CircuitRelabel.relabelGate_mul, tensorGate_mul, Matrix.one_mul]

/-- Lifting to the head registers commutes with conjugate transpose. -/
private theorem phaseHeadGate_adjoint (M k : ℕ)
    (U : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ) :
    phaseHeadGate M k Uᴴ = (phaseHeadGate M k U)ᴴ := by
  rw [phaseHeadGate, phaseHeadGate, phase_relabel_adjoint, tensorGate_conjTranspose,
    Matrix.conjTranspose_one]

/-- Two phase-label tuples of length `k+1` agree exactly when their first labels and their tails
agree. -/
private theorem phase_function_eq_iff (M k : ℕ) (x y : Fin (k + 1) → Fin M) :
    x = y ↔ x 0 = y 0 ∧ (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    funext i
    exact Fin.cases h0 (fun j => congrFun ht j) i

omit [Fintype I] [DecidableEq I] in

/-- Lifting a parallel oracle on the tail registers gives the parallel oracle on all phase
registers. -/
private theorem phaseTailGate_oracle (M k : ℕ) (A : Matrix (Bool × I) (Bool × I) ℂ) :
    phaseTailGate M k (parallelOracle (J := Fin k → Fin M) A) =
      parallelOracle (J := Fin (k + 1) → Fin M) A := by
  ext ⟨x, d⟩ ⟨y, e⟩
  simp only [phaseTailGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    phaseTailSplit, TensorGate, parallelOracle,
    select, Matrix.of_apply]
  by_cases hh : x 0 = y 0 <;> by_cases ht : (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ)
  · have hxy := (phase_function_eq_iff M k x y).mpr ⟨hh, ht⟩
    simp [hxy]
  · have hxy : x ≠ y := fun h => ht ((phase_function_eq_iff M k x y).mp h).2
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((phase_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((phase_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]

omit [Fintype I] [DecidableEq I] in

/-- Lifting a parallel oracle on the head registers gives the parallel oracle on all phase
registers. -/
private theorem phaseHeadGate_oracle (M k : ℕ) (A : Matrix (Bool × I) (Bool × I) ℂ) :
    phaseHeadGate M k (parallelOracle (J := Fin M) A) =
      parallelOracle (J := Fin (k + 1) → Fin M) A := by
  ext ⟨x, d⟩ ⟨y, e⟩
  simp only [phaseHeadGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    phaseHeadSplit, Equiv.trans_apply, phaseTailSplit, TensorGate,
    parallelOracle, select, Matrix.of_apply]
  by_cases hh : x 0 = y 0 <;> by_cases ht : (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ)
  · have hxy := (phase_function_eq_iff M k x y).mpr ⟨hh, ht⟩
    simp [hxy]
  · have hxy : x ≠ y := fun h => ht ((phase_function_eq_iff M k x y).mp h).2
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((phase_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((phase_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]

/-- Evaluation of the successor detection word factors into the lifted tail detection and lifted
head phase-estimation matrices. -/
theorem phaseDetectionWord_evaluate_succ (W : Matrix I I ℂ) (M k : ℕ) :
    evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M (k + 1)) =
      phaseTailGate M k
        (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k)) *
      phaseHeadGate M k
        (evaluate (parallelOracle (controlOracle W)) (phaseCompileCircuit (countedPhaseCircuit M))) := by
  have ht := phaseLiftWord_evaluate (phaseTailGate (I := I) M k)
    (phaseTailGate_one M k) (phaseTailGate_mul M k) (phaseTailGate_adjoint M k)
    (parallelOracle (controlOracle W)) (phaseDetectionWord M k)
  have hh := phaseLiftWord_evaluate (phaseHeadGate (I := I) M k)
    (phaseHeadGate_one M k) (phaseHeadGate_mul M k) (phaseHeadGate_adjoint M k)
    (parallelOracle (controlOracle W)) (phaseCompileCircuit (countedPhaseCircuit M))
  rw [phaseTailGate_oracle] at ht
  rw [phaseHeadGate_oracle] at hh
  rw [phaseDetectionWord, evaluate_append, ht, hh]

end Evaluation

/-- The phase-label tuple that is identically zero. -/
def phaseZeroIndex (M k : ℕ) (hM : 0 < M) : Fin k → Fin M := fun _ => ⟨0, hM⟩

/-- For positive `M`, every phase label has value zero exactly when the label tuple equals
`phaseZeroIndex`. -/
private theorem phase_zero_predicate (M k : ℕ) (hM : 0 < M) (x : Fin k → Fin M) :
    (∀ j, (x j).val = 0) ↔ x = phaseZeroIndex M k hM := by
  constructor
  · intro hx
    funext j
    exact Fin.ext (hx j)
  · rintro rfl
    exact fun _ => rfl

section EigenstateExecution

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- For positive `M`, the embedding is the tensor product of the all-zero phase ket, the false
control ket, and the data state. -/
theorem phaseReflectionEmbed_tensor (M k : ℕ) (hM : 0 < M) (v : QState I) :
    phaseReflectionEmbed M k v =
      TensorState (Qatlib.Foundations.PureStateMath.Ket (phaseZeroIndex M k hM)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) v) := by
  funext ⟨x, b, i⟩
  simp only [phaseReflectionEmbed, phase_zero_predicate M k hM x]
  cases b <;> by_cases hx : x = phaseZeroIndex M k hM <;> simp [TensorState,
      Qatlib.Foundations.PureStateMath.Ket, hx]

/-- For positive `M`, embedding with zero ancillas preserves the Euclidean norm of a state. -/
theorem phaseReflectionEmbed_norm (M k : ℕ) (hM : 0 < M) (v : QState I) :
    ‖toEuclidean_fromVec (phaseReflectionEmbed M k v)‖ = ‖toEuclidean_fromVec v‖ := by
  rw [phaseReflectionEmbed_tensor M k hM, tensorState_l2_norm, tensorState_l2_norm,
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _),
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket false), one_mul, one_mul]

omit [Fintype I] [DecidableEq I] in

/-- Express the zero-ancilla embedding using the head-register splitting and the all-zero tail
ket. -/
private theorem phase_embed_head_split (M k : ℕ) (hM : 0 < M) (v : QState I) :
    phaseReflectionEmbed M (k + 1) v =
      relabelState (phaseHeadSplit I M k).symm
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (phaseZeroIndex M k hM))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) v))) := by
  rw [phaseReflectionEmbed_tensor M (k + 1) hM]
  funext ⟨x, b, i⟩
  have hx := phase_function_eq_iff M k x (phaseZeroIndex M (k + 1) hM)
  simp only [phaseZeroIndex] at hx
  dsimp [relabelState, phaseHeadSplit, phaseTailSplit, TensorState,
      Qatlib.Foundations.PureStateMath.Ket, phaseZeroIndex]
  by_cases hh : x 0 = (⟨0, hM⟩ : Fin M) <;>
    by_cases ht : (fun j : Fin k => x j.succ) = (fun _ => (⟨0, hM⟩ : Fin M)) <;>
    simp [hx, hh, ht] <;> first
    | rw [if_pos (show (fun _ : Fin k => (⟨0, hM⟩ : Fin M)) = phaseZeroIndex M k hM from rfl)]
    | (intro _ he; exact (ht he).elim)

/-- The product QPE-kernel state on the phase registers, tensored with a false control bit and
the input data state. -/
noncomputable def phaseKernelPacket (M k : ℕ) (φ : ℝ) (v : QState I) :
    QState (PhaseReflectionSpace I M k) :=
  fun p => (∏ j : Fin k, qpeKernel M φ (p.1 j)) * (if p.2.1 then 0 else v p.2.2)

omit [Fintype I] [DecidableEq I] in

/-- Splitting off one QPE-kernel factor yields the packet with one additional phase register. -/
private theorem phaseKernelPacket_succ (M k : ℕ) (φ : ℝ) (v : QState I) :
    relabelState (phaseTailSplit I M k).symm
      (TensorState (qpeKernel M φ) (phaseKernelPacket M k φ v)) =
        phaseKernelPacket M (k + 1) φ v := by
  funext ⟨x, b, i⟩
  dsimp [relabelState, phaseTailSplit, TensorState, phaseKernelPacket]
  rw [Fin.prod_univ_succ]
  ring

/-- For an eigenstate, head phase estimation creates the corresponding QPE-kernel factor and
leaves the tail zero-ancilla embedding. -/
private theorem phase_head_qpe_eigen (M k : ℕ) (hM : 0 < M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ)
    (hv : ApplyGate W v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    ApplyGate (phaseHeadGate M k
      (evaluate (parallelOracle (controlOracle W)) (phaseCompileCircuit (countedPhaseCircuit M))))
      (phaseReflectionEmbed M (k + 1) v) =
    relabelState (phaseTailSplit I M k).symm
      (TensorState (qpeKernel M φ) (phaseReflectionEmbed M k v)) := by
  rw [phaseHeadGate, phase_embed_head_split M k hM, applyGate_relabelGate,
    applyGate_tensorGate, applyGate_one, phaseCompileCircuit_evaluate]
  have hs := (counted_offgrid_qpe_clean_flag M hM W v).1
  rw [qpeOutput_eigen M W v φ hv] at hs
  have ho : parallelOracle (J := Fin M) (controlOracle W) =
      TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle W) :=
    parallelOracle_eq_kronecker _
  rw [ho, hs]
  rw [phaseReflectionEmbed_tensor M k hM]
  funext ⟨x, b, i⟩
  cases b <;> simp [relabelState, phaseHeadSplit, phaseTailSplit, TensorState,
      Qatlib.Foundations.PureStateMath.Ket]

/-- On an eigenstate, evaluated repeated phase detection produces the product packet
`phaseKernelPacket`. -/
theorem phaseDetectionWord_eigenstate (M k : ℕ) (hM : 0 < M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ)
    (hv : ApplyGate W v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    ApplyGate (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k))
      (phaseReflectionEmbed M k v) = phaseKernelPacket M k φ v := by
  induction k with
  | zero =>
    simp only [phaseDetectionWord, evaluate, applyGate_one]
    funext ⟨x, b, i⟩
    cases b <;> simp [phaseReflectionEmbed, phaseKernelPacket]
  | succ k ih =>
    rw [phaseDetectionWord_evaluate_succ, applyGate_mul,
      phase_head_qpe_eigen M k hM W v φ hv, phaseTailGate, applyGate_relabelGate,
      applyGate_tensorGate, applyGate_one, ih, phaseKernelPacket_succ]

/-- Projection of a kernel packet onto the all-zero phase event equals the embedded data state
scaled by the kth power of its zero-label kernel amplitude. -/
private theorem phaseKernelPacket_project_zero (M k : ℕ) (hM : 0 < M) (φ : ℝ) (v : QState I) :
    ApplyGate (Projector (phaseZeroEvent M k)) (phaseKernelPacket M k φ v) =
      (qpeKernel M φ (⟨0, hM⟩ : Fin M)) ^ k • phaseReflectionEmbed M k v := by
  change Collapse (phaseKernelPacket M k φ v) (phaseZeroEvent M k) = _
  funext ⟨x, b, i⟩
  by_cases hx : ∀ j, (x j).val = 0
  · have he := (phase_zero_predicate M k hM x).mp hx
    subst x
    cases b <;> simp [collapse_apply, phaseZeroEvent, phaseKernelPacket,
      phaseReflectionEmbed, phaseZeroIndex]
  · cases b <;> simp [collapse_apply, phaseZeroEvent, phaseReflectionEmbed, hx]

/-- A phase at circular distance zero from zero has QPE kernel equal to the zero-label basis
ket. -/
theorem qpeKernel_zero_distance (M : ℕ) (hM : 0 < M) (φ : ℝ)
    (hφ : phaseDistance φ 0 = 0) : qpeKernel M φ = Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M) := by
  have hd : φ - (⌊φ + 1 / 2⌋ : ℤ) = 0 := by
    simpa only [phaseDistance, sub_zero, abs_eq_zero] using hφ
  have he : φ = 0 + ((⌊φ + 1 / 2⌋ : ℤ) : ℝ) := by linarith
  funext z
  rw [he, qpeKernel_int_add]
  have hz := (offgrid_phase_geometric_and_periodic M 0 z hM).2.2 (⟨0, hM⟩ : Fin M)
  simpa using hz

omit [Fintype I] [DecidableEq I] in

/-- A kernel packet at zero circular phase distance equals the zero-ancilla embedding. -/
private theorem phaseKernelPacket_zero_distance (M k : ℕ) (hM : 0 < M) (φ : ℝ)
    (hφ : phaseDistance φ 0 = 0) (v : QState I) :
    phaseKernelPacket M k φ v = phaseReflectionEmbed M k v := by
  have hz := qpeKernel_zero_distance M hM φ hφ
  funext ⟨x, b, i⟩
  cases b with
  | true => simp [phaseKernelPacket, phaseReflectionEmbed]
  | false =>
    by_cases hx : ∀ j, (x j).val = 0
    · have he := (phase_zero_predicate M k hM x).mp hx
      subst x
      simp [phaseKernelPacket, phaseReflectionEmbed, hz, phaseZeroIndex,
          Qatlib.Foundations.PureStateMath.Ket]
    · obtain ⟨j, hj⟩ := not_forall.mp hx
      have hne : x j ≠ (⟨0, hM⟩ : Fin M) := fun he => hj (congrArg Fin.val he)
      have hp : (∏ j : Fin k, qpeKernel M φ (x j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz]; simp [Qatlib.Foundations.PureStateMath.Ket, hne])
      simp [phaseKernelPacket, phaseReflectionEmbed, hx, hp]

/-- For a unitary eigenstate, express the reflection residual as inverse detection applied to
twice the zero-label kernel power times the embedded state. -/
theorem phase_reflection_eigenstate_residual (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : ApplyGate W v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    phaseReflectionState W M k v + phaseReflectionEmbed M k v =
      ApplyGate (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k))ᴴ
        ((2 : ℂ) • ((qpeKernel M φ (⟨0, by omega⟩ : Fin M)) ^ k •
          phaseReflectionEmbed M k v)) := by
  let D := evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord (I := I) M k)
  have hD : D ∈ Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (phaseDetectionWord_resources M k (by omega)).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  have hcancel : ApplyGate Dᴴ (ApplyGate D (phaseReflectionEmbed M k v)) =
      phaseReflectionEmbed M k v := by
    rw [← applyGate_mul, show Dᴴ * D = 1 by
      simpa only [Matrix.star_eq_conjTranspose] using hD.1, applyGate_one]
  have hstate : phaseReflectionState W M k v =
      ApplyGate Dᴴ (ApplyGate (phaseZeroReflection M k) (ApplyGate D (phaseReflectionEmbed M k v))) := by
    simp only [phaseReflectionState, phaseReflectionWord, evaluate_append, evaluate_adjointCircuit,
      evaluate, instructionMatrix, Matrix.mul_one, applyGate_mul, D]
  have hlin : ApplyGate Dᴴ
      ((2 : ℂ) • ApplyGate (Projector (phaseZeroEvent M k))
          (ApplyGate D (phaseReflectionEmbed M k v)) - ApplyGate D (phaseReflectionEmbed M k v)) =
      (2 : ℂ) • ApplyGate Dᴴ (ApplyGate (Projector (phaseZeroEvent M k))
          (ApplyGate D (phaseReflectionEmbed M k v))) - phaseReflectionEmbed M k v := by
    simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul] at hcancel ⊢
    rw [hcancel]
  rw [hstate, phaseZeroReflection, applyGate_reflectionAbout, hlin]
  have hforward := phaseDetectionWord_eigenstate M k (by omega) W v φ hv
  change ApplyGate D (phaseReflectionEmbed M k v) = phaseKernelPacket M k φ v at hforward
  rw [hforward, phaseKernelPacket_project_zero M k (by omega)]
  simp only [ApplyGate, Matrix.mulVec_smul]
  module

/-- The counted reflection fixes zero-phase eigenstates exactly and bounds the residual from
negation on other eigenstates by twice the kth zero-label kernel norm times the input norm.
See [MagniezNayakRolandSantha2011]. -/
theorem phase_reflection_actual_eigenstate_error (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : ApplyGate W v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    (phaseDistance φ 0 = 0 → phaseReflectionState W M k v = phaseReflectionEmbed M k v) ∧
      (phaseDistance φ 0 ≠ 0 →
        ‖toEuclidean_fromVec (phaseReflectionState W M k v + phaseReflectionEmbed M k v)‖ ≤
          2 * ‖qpeKernel M φ (⟨0, by omega⟩ : Fin M)‖ ^ k * ‖toEuclidean_fromVec v‖) := by
  let D := evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord (I := I) M k)
  have hD : D ∈ Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (phaseDetectionWord_resources M k (by omega)).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  constructor
  · intro hφ
    have he : ApplyGate D (phaseReflectionEmbed M k v) = phaseReflectionEmbed M k v :=
      (phaseDetectionWord_eigenstate M k (by omega) W v φ hv).trans
        (phaseKernelPacket_zero_distance M k (by omega) φ hφ v)
    have hp : ApplyGate (Projector (phaseZeroEvent M k)) (phaseReflectionEmbed M k v) =
        phaseReflectionEmbed M k v := by
      have hh := phaseKernelPacket_project_zero M k (by omega) φ v
      rw [phaseKernelPacket_zero_distance M k (by omega) φ hφ v,
        qpeKernel_zero_distance M (by omega) φ hφ] at hh
      simpa [Qatlib.Foundations.PureStateMath.Ket] using hh
    have hc : ApplyGate Dᴴ (phaseReflectionEmbed M k v) = phaseReflectionEmbed M k v := by
      calc
        _ = ApplyGate Dᴴ (ApplyGate D (phaseReflectionEmbed M k v)) :=
          congrArg (ApplyGate Dᴴ) he.symm
        _ = _ := by rw [← applyGate_mul, show Dᴴ * D = 1 by
            simpa only [Matrix.star_eq_conjTranspose] using hD.1, applyGate_one]
    simp only [phaseReflectionState, phaseReflectionWord, evaluate_append, evaluate_adjointCircuit,
      evaluate, instructionMatrix, Matrix.mul_one, applyGate_mul]
    change ApplyGate Dᴴ (ApplyGate (phaseZeroReflection M k)
      (ApplyGate D (phaseReflectionEmbed M k v))) = _
    rw [he, phaseZeroReflection,
      applyGate_reflectionAbout_of_fixed hp, hc]
  · intro _
    rw [phase_reflection_eigenstate_residual M k hM W v φ hW hv,
      norm_applyGate_of_mem_unitaryGroup (adjoint_unitary hD)]
    change ‖(2 : ℂ) • ((qpeKernel M φ (⟨0, by omega⟩ : Fin M)) ^ k •
      toEuclidean_fromVec (phaseReflectionEmbed M k v))‖ ≤ _
    rw [norm_smul, norm_smul, norm_pow, phaseReflectionEmbed_norm M k (by omega)]
    norm_num [mul_assoc]

/-- The zero-ancilla embedding regarded as a complex linear map. -/
private noncomputable def phaseEmbedLinear (M k : ℕ) :
    QState I →ₗ[ℂ] QState (PhaseReflectionSpace I M k) where
  toFun := phaseReflectionEmbed M k
  map_add' x y := by
    funext p
    by_cases h : p.2.1 = false ∧ ∀ j, (p.1 j).val = 0 <;>
      simp [phaseReflectionEmbed, h]
  map_smul' c x := by
    funext p
    by_cases h : p.2.1 = false ∧ ∀ j, (p.1 j).val = 0 <;>
      simp [phaseReflectionEmbed, h]

/-- Matrix application regarded as a complex linear map on states. -/
private noncomputable def phaseApplyLinear {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) : QState H →ₗ[ℂ] QState H where
  toFun := ApplyGate U
  map_add' x y := Matrix.mulVec_add U x y
  map_smul' c x := Matrix.mulVec_smul U c x

/-- A uniform coefficient bound in an orthonormal family gives the corresponding Euclidean norm
bound between linear combinations. -/
private theorem phase_orthonormal_combo_bound {J : Type} [Fintype J] [DecidableEq J]
    (v : J → QState I) (c d : J → ℂ)
    (hv : ∀ a b, Qatlib.Foundations.PureStateMath.Inner (v a) (v b) = if a = b then 1 else 0)
    (C : ℝ) (hC : 0 ≤ C) (hd : ∀ a, ‖d a‖ ≤ C * ‖c a‖) :
    ‖toEuclidean_fromVec (∑ a, d a • v a)‖ ≤ C * ‖toEuclidean_fromVec (∑ a, c a • v a)‖ := by
  have hs : ‖toEuclidean_fromVec (∑ a, d a • v a)‖ ^ 2 ≤
      C ^ 2 * ‖toEuclidean_fromVec (∑ a, c a • v a)‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq,
      sum_norm_sq_orthonormal v d (fun a b => by by_cases h : a = b <;> simpa [h] using hv a b),
      norm_toEuclidean_fromVec_sq,
      sum_norm_sq_orthonormal v c (fun a b => by by_cases h : a = b <;> simpa [h] using hv a b),
      Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (d a)) (hd a) 2
  have hn := norm_nonneg (toEuclidean_fromVec (∑ a, d a • v a))
  have hm := norm_nonneg (toEuclidean_fromVec (∑ a, c a • v a))
  nlinarith [mul_nonneg hC hm]

/-- Reflection about one vector of an orthonormal family keeps its component and negates all
other components of a finite linear combination. -/
theorem phase_source_reflection_sum {J : Type} [Fintype J] [DecidableEq J]
    (j0 : J) (v : J → QState I) (c : J → ℂ)
    (hv : ∀ a b, Qatlib.Foundations.PureStateMath.Inner (v a) (v b) = if a = b then 1 else 0) :
    ApplyGate (ReflectionAbout (outerProduct (v j0))) (∑ a, c a • v a) =
      (2 * c j0) • v j0 - ∑ a, c a • v a := by
  have hi : Qatlib.Foundations.PureStateMath.Inner (v j0) (∑ a, c a • v a) = c j0 := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_sum, dotProduct_smul,
        smul_eq_mul]
    change (∑ a, c a * Qatlib.Foundations.PureStateMath.Inner (v j0) (v a)) = c j0
    simp [hv, mul_ite]
  rw [applyGate_reflectionAbout]
  change (2 : ℂ) • (outerProduct (v j0) *ᵥ (∑ a, c a • v a)) - _ = _
  rw [outerProduct_mulVec, hi, smul_smul]

/-- For an orthonormal eigenfamily with a distinguished zero-phase vector and phase gap `η`,
bound the counted reflection error on its span by `2*(1/(2*M*η))^k` times the input norm. -/
theorem phase_reflection_reachable_source_error (J : Type) [Fintype J] [DecidableEq J]
    (j0 : J) (v : J → QState I) (p : J → ℝ) (W : Matrix I I ℂ) (M k : ℕ) (η : ℝ)
    (hM : 2 ≤ M) (hη : 0 < η) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : ∀ a b, Qatlib.Foundations.PureStateMath.Inner (v a) (v b) = if a = b then 1 else 0)
    (heigen : ∀ a, ApplyGate W (v a) = Complex.exp (2 * Real.pi * Complex.I * p a) • v a)
    (hp0 : p j0 = 0) (hgap : ∀ a, a ≠ j0 → η ≤ phaseDistance (p a) 0)
    (c : J → ℂ) :
    let ψ := ∑ a, c a • v a
    ‖toEuclidean_fromVec (phaseReflectionState W M k ψ -
      phaseReflectionEmbed M k (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ))‖ ≤
        2 * (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec ψ‖ := by
  intro ψ
  let D := evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord (I := I) M k)
  let E := phaseEmbedLinear (I := I) M k
  let R := (phaseApplyLinear (evaluate (parallelOracle (controlOracle W))
    (phaseReflectionWord M k))).comp E
  let L := (phaseApplyLinear Dᴴ).comp ((2 : ℂ) • E)
  let α : J → ℂ := fun a => (qpeKernel M (p a) (⟨0, by omega⟩ : Fin M)) ^ k
  let d : J → ℂ := fun a => if a = j0 then 0 else c a * α a
  let z := ∑ a, d a • v a
  have hD : D ∈ Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (phaseDetectionWord_resources M k (by omega)).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  have hφ0 : phaseDistance (p j0) 0 = 0 := by norm_num [hp0, phaseDistance]
  have hα0 : α j0 = 1 := by
    simp [α, qpeKernel_zero_distance M (by omega) (p j0) hφ0,
        Qatlib.Foundations.PureStateMath.Ket]
  have hfix : ApplyGate D (E (v j0)) = E (v j0) :=
    (phaseDetectionWord_eigenstate M k (by omega) W (v j0) (p j0) (heigen j0)).trans
      (phaseKernelPacket_zero_distance M k (by omega) (p j0) hφ0 (v j0))
  have hinv : ApplyGate Dᴴ (E (v j0)) = E (v j0) := by
    calc
      _ = ApplyGate Dᴴ (ApplyGate D (E (v j0))) := congrArg (ApplyGate Dᴴ) hfix.symm
      _ = _ := by rw [← applyGate_mul, show Dᴴ * D = 1 by
          simpa only [Matrix.star_eq_conjTranspose] using hD.1, applyGate_one]
  have hsum : R ψ + E ψ = L (∑ a, (c a * α a) • v a) := by
    change R (∑ a, c a • v a) + E (∑ a, c a • v a) = _
    rw [map_sum, map_sum, map_sum]
    simp only [map_smul, ← Finset.sum_add_distrib, ← smul_add, mul_smul]
    apply Finset.sum_congr rfl
    intro a _
    have ha := phase_reflection_eigenstate_residual M k hM W (v a) (p a) hW (heigen a)
    have halpha : R (v a) + E (v a) = L (α a • v a) := by
      change phaseReflectionState W M k (v a) + phaseReflectionEmbed M k (v a) =
        ApplyGate Dᴴ ((2 : ℂ) • E (α a • v a))
      rw [E.map_smul]
      exact ha
    rw [halpha, map_smul]
  have hz : (∑ a, (c a * α a) • v a) = z + c j0 • v j0 := by
    calc
      _ = ∑ a, (d a • v a + if a = j0 then c j0 • v j0 else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a = j0
        · subst a; simp [d, hα0]
        · simp [d, ha]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [z]
  have hL0 : L (c j0 • v j0) = (2 * c j0) • E (v j0) := by
    rw [map_smul]
    change c j0 • ApplyGate Dᴴ ((2 : ℂ) • E (v j0)) = _
    have hlin : ApplyGate Dᴴ ((2 : ℂ) • E (v j0)) = (2 : ℂ) • E (v j0) := by
      simpa only [ApplyGate, Matrix.mulVec_smul] using congrArg ((2 : ℂ) • ·) hinv
    rw [hlin, smul_smul, mul_comm]
  have herror : phaseReflectionState W M k ψ -
      phaseReflectionEmbed M k (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ) = L z := by
    change R ψ - E (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ) = _
    rw [phase_source_reflection_sum j0 v c hv, E.map_sub, E.map_smul]
    rw [hz, L.map_add, hL0] at hsum
    change R ψ - ((2 * c j0) • E (v j0) - E ψ) = L z
    calc
      _ = (R ψ + E ψ) - (2 * c j0) • E (v j0) := by abel
      _ = L z := by rw [hsum]; abel
  let C : ℝ := (1 / (2 * (M : ℝ) * η)) ^ k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd : ∀ a, ‖d a‖ ≤ C * ‖c a‖ := by
    intro a
    by_cases ha : a = j0
    · simp [d, ha]; positivity
    · simp only [d, if_neg ha, norm_mul, α, norm_pow]
      have hqa := phase_detection_zero_label_gap_bound M (by omega) (p a) η hη (hgap a ha)
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hqa k) (norm_nonneg (c a))).trans_eq
        (by dsimp [C]; ring)
  have hnorm := phase_orthonormal_combo_bound v c d hv C hC hd
  rw [herror]
  change ‖toEuclidean_fromVec (ApplyGate Dᴴ ((2 : ℂ) • E z))‖ ≤ _
  rw [norm_applyGate_of_mem_unitaryGroup (adjoint_unitary hD)]
  change ‖(2 : ℂ) • toEuclidean_fromVec (phaseReflectionEmbed M k z)‖ ≤ _
  rw [norm_smul, phaseReflectionEmbed_norm M k (by omega)]
  norm_num only [Complex.norm_ofNat]
  nlinarith [hnorm]

omit [Fintype I] [DecidableEq I] in

/-- Zero-ancilla embedding preserves addition of states. -/
theorem phaseReflectionEmbed_add (M k : ℕ) (x y : QState I) :
    phaseReflectionEmbed M k (x + y) = phaseReflectionEmbed M k x + phaseReflectionEmbed M k y :=
  (phaseEmbedLinear M k).map_add x y

omit [Fintype I] [DecidableEq I] in

/-- Zero-ancilla embedding preserves complex scalar multiplication. -/
theorem phaseReflectionEmbed_smul (M k : ℕ) (c : ℂ) (x : QState I) :
    phaseReflectionEmbed M k (c • x) = c • phaseReflectionEmbed M k x :=
  (phaseEmbedLinear M k).map_smul c x

omit [Fintype I] [DecidableEq I] in

/-- Zero-ancilla embedding preserves subtraction of states. -/
theorem phaseReflectionEmbed_sub (M k : ℕ) (x y : QState I) :
    phaseReflectionEmbed M k (x - y) = phaseReflectionEmbed M k x - phaseReflectionEmbed M k y :=
  (phaseEmbedLinear M k).map_sub x y

/-- Applying the phase-reflection word to embedded states preserves addition. -/
theorem phaseReflectionState_add (W : Matrix I I ℂ) (M k : ℕ) (x y : QState I) :
    phaseReflectionState W M k (x + y) = phaseReflectionState W M k x + phaseReflectionState W M k y := by
  simp only [phaseReflectionState, phaseReflectionEmbed_add, ApplyGate, Matrix.mulVec_add]

end EigenstateExecution

end Qatlib.Concepts.SpectralFilter.PhaseReadout
