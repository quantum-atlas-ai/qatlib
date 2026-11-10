/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBound
import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.AdaptiveSignalTree
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

open Matrix
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators ComplexOrder ENNReal Matrix.Norms.L2Operator
set_option warningAsError false

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

noncomputable def GateContraction {H : Type} [Fintype H] [DecidableEq H] :
    AdjointStep H → Prop
  | .gate V => ‖V‖ ≤ 1
  | .forward => True
  | .backward => True

noncomputable def WellFormedGates {H : Type} [Fintype H] [DecidableEq H]
    (word : List (AdjointStep H)) : Prop :=
  ∀ c ∈ word, GateContraction c

noncomputable def BoundedAccessWord {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (word : List (AdjointStep H)) : Prop :=
  ‖O‖ ≤ 1 ∧ WellFormedGates word

theorem boundedAccessWord_guard {H : Type} [Fintype H] [DecidableEq H]
    {O : Matrix H H ℂ} {word : List (AdjointStep H)}
    (h : BoundedAccessWord O word) : ∀ c ∈ word, ‖instructionMatrix O c‖ ≤ 1 := by
  intro c hc
  have hO : ‖O‖ ≤ 1 := h.1
  have hg : GateContraction c := h.2 c hc
  cases c with
  | gate V =>
    simp only [instructionMatrix]
    simpa [GateContraction] using! hg
  | forward =>
    simp only [instructionMatrix]
    exact hO
  | backward =>
    simp only [instructionMatrix, Matrix.l2_opNorm_conjTranspose]
    exact hO

theorem boundedFamily_accessWord {I : Type} [Fintype I] [DecidableEq I]
    {F : MatrixFamily I} {z : ℝ} {word : List (AdjointStep I)}
    (hF : BoundedMatrixFamily F) (hG : WellFormedGates word) :
    BoundedAccessWord (F z) word :=
  ⟨hF z, hG⟩

noncomputable def matrixResponseConstant {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (eps : ℝ) : ℝ :=
  max 0 (‖A - B‖ - 2 * eps)

theorem square_isometry_is_unitary {I : Type} [Fintype I] [DecidableEq I]
    {L : Matrix I I ℂ} (hL : IsIsometry L) : L ∈ Matrix.unitaryGroup I ℂ := by
  have hdet : L.det ≠ 0 := by
    intro hzero
    have hone : (Lᴴ * L).det = 1 := by
      rw [hL]
      exact Matrix.det_one
    have hmul : Lᴴ.det * L.det = 1 := by
      rw [← Matrix.det_mul]
      exact hone
    rw [hzero, mul_zero] at hmul
    exact zero_ne_one hmul
  have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet
  have hLi : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hunit
  have hstar : Lᴴ = L⁻¹ := by
    calc
      Lᴴ = Lᴴ * 1 := (mul_one Lᴴ).symm
      _ = Lᴴ * (L * L⁻¹) := by rw [hLi]
      _ = (Lᴴ * L) * L⁻¹ := (Matrix.mul_assoc Lᴴ L L⁻¹).symm
      _ = 1 * L⁻¹ := by rw [hL]
      _ = L⁻¹ := one_mul L⁻¹
  refine ⟨hL, ?_⟩
  calc
    L * Lᴴ = L * L⁻¹ := by rw [hstar]
    _ = 1 := hLi

theorem compress_norm_eq_of_square_isometry {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] (L R X : Matrix I I ℂ) (hL : IsIsometry L) (hR : IsIsometry R) :
    ‖compress L X R‖ = ‖X‖ := by
  have hLU : L ∈ Matrix.unitaryGroup I ℂ := square_isometry_is_unitary hL
  have hRU : R ∈ Matrix.unitaryGroup I ℂ := square_isometry_is_unitary hR
  have hLone : ‖L‖ = 1 := l2_norm_unitary_eq_one hLU
  have hRone : ‖R‖ = 1 := l2_norm_unitary_eq_one hRU
  have hLstar : ‖Lᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hLone
  have hRstar : ‖Rᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hRone
  have hXR : ‖X * R‖ = ‖X‖ := by
    refine le_antisymm ?_ ?_
    · refine le_trans (Matrix.l2_opNorm_mul X R) ?_
      rw [hRone, mul_one]
    · have hRinv : R * Rᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hRU
      calc
        ‖X‖ = ‖X * 1‖ := by rw [mul_one]
        _ = ‖X * (R * Rᴴ)‖ := by rw [hRinv]
        _ = ‖(X * R) * Rᴴ‖ := by rw [Matrix.mul_assoc X R Rᴴ]
        _ ≤ ‖X * R‖ * ‖Rᴴ‖ := Matrix.l2_opNorm_mul (X * R) Rᴴ
        _ = ‖X * R‖ := by rw [hRstar, mul_one]
  have hupp : ‖compress L X R‖ ≤ ‖X‖ := by
    rw [compress, Matrix.mul_assoc Lᴴ X R]
    refine le_trans (Matrix.l2_opNorm_mul Lᴴ (X * R)) ?_
    rw [hLstar, hXR, one_mul]
  have hlow : ‖X‖ ≤ ‖compress L X R‖ := by
    have hLinv : L * Lᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hLU
    have hY : L * (Lᴴ * (X * R)) = X * R := by
      calc
        L * (Lᴴ * (X * R)) = (L * Lᴴ) * (X * R) :=
          (Matrix.mul_assoc L Lᴴ (X * R)).symm
        _ = 1 * (X * R) := by rw [hLinv]
        _ = X * R := one_mul (X * R)
    calc
      ‖X‖ = ‖X * R‖ := hXR.symm
      _ = ‖L * (Lᴴ * (X * R))‖ := by rw [hY]
      _ ≤ ‖L‖ * ‖Lᴴ * (X * R)‖ := Matrix.l2_opNorm_mul L (Lᴴ * (X * R))
      _ = ‖Lᴴ * (X * R)‖ := by rw [hLone, one_mul]
      _ = ‖compress L X R‖ := by rw [compress, Matrix.mul_assoc Lᴴ X R]
  exact le_antisymm hupp hlow

noncomputable def sharpnessOracleOne : Matrix Unit Unit ℂ := ((1 : ℝ) : ℂ) • 1

noncomputable def sharpnessOracleTwo : Matrix Unit Unit ℂ := ((1 / 2 : ℝ) : ℂ) • 1

noncomputable def sharpnessTargetOne : Matrix Unit Unit ℂ := ((5 / 4 : ℝ) : ℂ) • 1

noncomputable def sharpnessTargetTwo : Matrix Unit Unit ℂ := ((1 / 4 : ℝ) : ℂ) • 1

noncomputable def sharpnessEps : ℝ := 1 / 4

def sharpnessWord : List (AdjointStep Unit) := [AdjointStep.forward]

noncomputable def responseQueryThreshold (c d : ℝ) : ℕ :=
  Nat.ceil (c / d)

theorem responseQueryThreshold_spec {c d : ℝ} {q : ℕ} (hd : 0 < d) :
    responseQueryThreshold c d ≤ q ↔ (q : ℝ) * d ≥ c := by
  constructor
  · intro h
    have h1 : c / d ≤ (Nat.ceil (c / d) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (c / d) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
    have hmul : (c / d) * d = c := by field_simp
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (le_of_lt hd)
  · intro h
    have hdiv : c / d ≤ (q : ℝ) := (div_le_iff₀ hd).mpr h
    exact Nat.ceil_le.mpr hdiv

def branchLevelMass {H : Type} [Fintype H] [DecidableEq H]
    (tree : AdaptiveSignalTree H) (law : SignalBranchLaw) (k : ℕ) : ℝ :=
  ((law.support.filter (fun e => decide (tree.pathQueries e.1 = k))).map (fun e => e.2)).sum

def branchCumulativeMass {H : Type} [Fintype H] [DecidableEq H]
    (tree : AdaptiveSignalTree H) (law : SignalBranchLaw) (k : ℕ) : ℝ :=
  ((law.support.filter (fun e => decide (tree.pathQueries e.1 ≤ k))).map (fun e => e.2)).sum

def branchQualifyingLevelMass {H : Type} [Fintype H] [DecidableEq H]
    (tree : AdaptiveSignalTree H) (law : SignalBranchLaw) (S : List (List Bool)) (k : ℕ) : ℝ :=
  ((law.support.filter (fun e =>
      decide (e.1 ∈ S) && decide (tree.pathQueries e.1 = k))).map (fun e => e.2)).sum

def wordForwardAccesses {I : Type} (word : List (AdjointStep I)) : ℕ :=
  (word.map (fun c => match c with
    | .forward => 1
    | _ => 0)).sum

def wordBackwardAccesses {I : Type} (word : List (AdjointStep I)) : ℕ :=
  (word.map (fun c => match c with
    | .backward => 1
    | _ => 0)).sum

def accessAddressBits (d : ℕ) : ℕ :=
  Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs.addressBitsFor d

def wordAddressBits {I : Type} [Fintype I] (word : List (AdjointStep I)) : ℕ :=
  (wordForwardAccesses word + wordBackwardAccesses word) * accessAddressBits (Fintype.card I)

noncomputable def jointInstanceOracleOne : Matrix Unit Unit ℂ := ((1 : ℝ) : ℂ) • 1

noncomputable def jointInstanceOracleTwo : Matrix Unit Unit ℂ := ((1 / 2 : ℝ) : ℂ) • 1

noncomputable def jointInstanceTargetOne : Matrix Unit Unit ℂ := ((5 / 4 : ℝ) : ℂ) • 1

noncomputable def jointInstanceTargetTwo : Matrix Unit Unit ℂ := 0

noncomputable def jointInstanceEps : ℝ := 1 / 4

def jointInstanceTree : AdaptiveSignalTree Unit :=
  .node [] (.node [.forward] .leaf .leaf) (.node [.forward, .forward] .leaf .leaf)

def jointInstanceQualifying : List (List Bool) := [[true, false], [true, true]]

noncomputable def jointInstanceSupport : List (List Bool × ℝ) :=
  [([false, false], 1 / 2), ([true, false], 1 / 2)]

noncomputable def jointInstanceLaw : SignalBranchLaw where
  support := jointInstanceSupport
  nonneg := by
    intro e he
    have he' : e = ([false, false], 1 / 2) ∨ e = ([true, false], 1 / 2) := by
      rw [jointInstanceSupport] at he
      simpa using! he
    rcases he' with h | h <;> subst h <;> norm_num
  total := by
    simp [jointInstanceSupport]
    norm_num

noncomputable def asymmetricAccessModel : OracleAccessModel Unit where
  realize := fun O b =>
    if b then [Step.gate O.conjTranspose, Step.gate (1 : Matrix Unit Unit ℂ),
        Step.gate (1 : Matrix Unit Unit ℂ)]
      else [Step.gate O]
  queryFree := by intro O b; cases b <;> rfl
  readBits := fun _ b => if b then 2 else 1
  forwardRun := by intro O ψ; simp [Run, ApplyGate]
  backwardRun := by intro O ψ; simp [Run, ApplyGate]

def mixedDirectionWord : List (AdjointStep Unit) :=
  [AdjointStep.forward, AdjointStep.backward]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
