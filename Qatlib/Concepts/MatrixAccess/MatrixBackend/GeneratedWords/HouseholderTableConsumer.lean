/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.InputPhaseColumnWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate
/-! Consume the generated table PREP, its actual rational Born weights and
its expanded logical word. No arbitrary PREP matrix or PREP-unitarity premise
is supplied. Physical two-level decomposition remains a separate transport. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- The finite construction in `HouseholderTableConsumer` satisfies `query_free_evaluate_eq` under the displayed hypotheses. -/
private theorem query_free_evaluate_eq {D : Type} [Fintype D] [DecidableEq D]
    (O U : Matrix D D ℂ) (W : List (AdjointStep D)) (hW : adjointQueryCount W=0) :
    evaluate O W = evaluate U W := by
  induction W with
  | nil => rfl
  | cons c W ih =>
    cases c with
    | gate V =>
      simpa only [evaluate, instructionMatrix] using
        congrArg (fun T => V*T) (ih hW)
    | forward => simp [adjointQueryCount] at hW
    | backward => simp [adjointQueryCount] at hW

/-- The finite construction in `HouseholderTableConsumer` satisfies `tablePreparedColumn_sum_sq` under the displayed hypotheses. -/
theorem tablePreparedColumn_sum_sq {n : ℕ} (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) :
    (∑ a, (tablePreparedColumn rs a)^2) = 1 := by
  have hc : tableHouseholder rs *ᵥ Qatlib.Foundations.PureStateMath.Ket none = fun a => (tablePreparedColumn rs a : ℂ) := by
    funext a
    simpa [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket] using tableHouseholder_origin_column rs a
  have hn := normalized_applyGate (tableHouseholder_unitary rs) (normalized_ket (none : Option (Fin n)))
  change Normalized (tableHouseholder rs *ᵥ Qatlib.Foundations.PureStateMath.Ket none) at hn
  rw [hc] at hn
  have hi := inner_self_eq_one hn
  have hs : (∑ a, (tablePreparedColumn rs a : ℂ)^2) = 1 := by
    simpa [Qatlib.Foundations.PureStateMath.Inner, dotProduct, pow_two] using hi
  exact_mod_cast hs

/-- The finite construction in `HouseholderTableConsumer` satisfies `table_column_phase_coefficient` under the displayed hypotheses. -/
theorem table_column_phase_coefficient {n : ℕ} (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle))
    (φ : Option (Fin n) → ℂ) (a : Option (Fin n)) :
    columnPhaseCoefficient (tableHouseholder rs) φ none a =
      (((tablePreparedColumn rs a)^2 : ℚ) : ℂ)*φ a := by
  simp [columnPhaseCoefficient, tableHouseholder_origin_column, pow_two]

/-- Construction for table Prep Lift Word in the householder table consumer model. -/
def tablePrepLiftWord {n : ℕ} (H : Type) [Fintype H] [DecidableEq H]
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) : List (AdjointStep (Option (Fin n) × H)) :=
  phaseLiftWord (prepareRegister (I := H)) (tableHouseholderWord rs)

/-- The finite construction in `HouseholderTableConsumer` satisfies `tablePrepLiftWord_evaluate` under the displayed hypotheses. -/
theorem tablePrepLiftWord_evaluate {n : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    [outer : DecidableEq (Option (Fin n) × H)]
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle))
    (O : Matrix (Option (Fin n) × H) (Option (Fin n) × H) ℂ) :
    evaluate O (tablePrepLiftWord H rs) = prepareRegister (I := H) (tableHouseholder rs) := by
  have heq : outer=instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  have h1 : prepareRegister (I := H) (1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) = 1 := by
    simp [prepareRegister]
  have hm : ∀ U V : Matrix (Option (Fin n)) (Option (Fin n)) ℂ,
      prepareRegister (I := H) (U*V) = prepareRegister U*prepareRegister V := by
    intro U V
    simp only [prepareRegister, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have ha : ∀ U : Matrix (Option (Fin n)) (Option (Fin n)) ℂ,
      prepareRegister (I := H) Uᴴ = (prepareRegister (I := H) U)ᴴ := by
    intro U
    simp only [prepareRegister, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  -- This word contains no queries: lifting at identity suffices for every O.
  have hzero := (phaseLiftWord_counts (prepareRegister (I := H)) (tableHouseholderWord rs)).1.trans
    (tableHouseholderWord_counts rs).1
  have he := phaseLiftWord_evaluate (prepareRegister (I := H)) h1 hm ha
    (1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (tableHouseholderWord rs)
  have hquery := query_free_evaluate_eq O (1 : Matrix (Option (Fin n) × H) (Option (Fin n) × H) ℂ)
    (tablePrepLiftWord H rs) hzero
  rw [hquery]
  simpa only [tablePrepLiftWord,h1, tableHouseholderWord_evaluate] using he

/-- Construction for householder Input Word in the householder table consumer model. -/
def householderInputWord {n : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (φ : Option (Fin n) → ℂ)
    (W : List (AdjointStep (Option (Fin n) × H))) : List (AdjointStep (Option (Fin n) × H)) :=
  adjointCircuit (tablePrepLiftWord H rs) ++ W ++
    [.gate (prepareRegister (I := H) (Matrix.diagonal φ))] ++ tablePrepLiftWord H rs

/-- The actual finite word or frame satisfies `tablePrepLiftWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem tablePrepLiftWord_legal {n : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    [outer : DecidableEq (Option (Fin n) × H)]
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) : WellFormedAdjointCircuit (tablePrepLiftWord H rs) := by
  have heq : outer=instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  exact phaseLiftWord_wellFormed (prepareRegister (I := H))
    (fun _ h => prepareRegister_unitary h) (tableHouseholderWord_legal rs)

/-- The actual finite word or frame satisfies `householderInputWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem householderInputWord_legal {n : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    [outer : DecidableEq (Option (Fin n) × H)]
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (φ : Option (Fin n) → ℂ)
    (W : List (AdjointStep (Option (Fin n) × H)))
    (hφ : ∀ a, star (φ a)*φ a=1) (hW : WellFormedAdjointCircuit W) :
    WellFormedAdjointCircuit (householderInputWord rs φ W) := by
  have heq : outer=instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  have hp := tablePrepLiftWord_legal (H := H) rs
  have hi := inputColumnPhaseWord_legal (H := H) (tableHouseholder rs) φ []
    (tableHouseholder_unitary rs) hφ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil
  have hD : prepareRegister (I := H) (Matrix.diagonal φ) ∈ unitaryGroup (Option (Fin n) × H) ℂ :=
    hi _ (by simp [inputColumnPhaseWord])
  have hd : WellFormedAdjointCircuit [.gate (prepareRegister (I := H) (Matrix.diagonal φ))] := by
    simpa only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true] using hD
  exact ((hp.adjointCircuit.append hW).append hd).append hp

/-- The finite construction in `HouseholderTableConsumer` satisfies `householderInputWord_evaluate` under the displayed hypotheses. -/
theorem householderInputWord_evaluate {n : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    [outer : DecidableEq (Option (Fin n) × H)]
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (φ : Option (Fin n) → ℂ)
    (O : Matrix (Option (Fin n) × H) (Option (Fin n) × H) ℂ)
    (W : List (AdjointStep (Option (Fin n) × H))) :
    evaluate O (householderInputWord rs φ W) =
      evaluate O (inputColumnPhaseWord (tableHouseholder rs) φ W) := by
  have heq : outer=instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  simp only [householderInputWord, evaluate_append, evaluate_adjointCircuit,
    tablePrepLiftWord_evaluate, evaluate, instructionMatrix, Matrix.mul_one,
    inputColumnPhaseWord_evaluate, Matrix.mul_assoc]

/-- The same emitted instruction list satisfies `householderInputWord_counts` with the displayed gate and query accounting. -/
theorem householderInputWord_counts {n : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (φ : Option (Fin n) → ℂ)
    (W : List (AdjointStep (Option (Fin n) × H))) :
    adjointQueryCount (householderInputWord rs φ W) = adjointQueryCount W ∧
    adjointGateCount (householderInputWord rs φ W) = adjointGateCount W+4*rs.length+3 := by
  have hc := phaseLiftWord_counts (prepareRegister (I := H)) (tableHouseholderWord rs)
  have hr := tableHouseholderWord_counts rs
  constructor
  · simp [householderInputWord, adjointQueryCount_append, adjointQueryCount_adjointCircuit,
      tablePrepLiftWord, hc.1, hr.1, adjointQueryCount]
  · simp only [householderInputWord, adjointGateCount_append, adjointGateCount_adjointCircuit,
      tablePrepLiftWord, hc.2, hr.2, adjointGateCount]
    omega

/-- The actual finite word or frame satisfies `householder_input_phase_encoding` with all displayed legality, input and workspace hypotheses. -/
theorem householder_input_phase_encoding {n : ℕ} {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I]
    [outer : DecidableEq (Option (Fin n) × H)]
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (φ : Option (Fin n) → ℂ)
    (F : Matrix H I ℂ) (O : Matrix (Option (Fin n) × H) (Option (Fin n) × H) ℂ)
    (W : List (AdjointStep (Option (Fin n) × H))) (Y : Option (Fin n) → Matrix I I ℂ)
    (hF : IsIsometry F) (hφ : ∀ a, star (φ a)*φ a=1)
    (hW : evaluate O W ∈ unitaryGroup (Option (Fin n) × H) ℂ)
    (hblock : compress ((1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) ⊗ₖ F) (evaluate O W)
      ((1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) ⊗ₖ F) = select Y) :
    ProjectedUnitaryEncoding
      (∑ a, ((((tablePreparedColumn rs a)^2 : ℚ) : ℂ)*φ a) • Y a)
      (evaluate O (householderInputWord rs φ W)) (tagFrame none F) (tagFrame none F) := by
  have heq : outer=instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  rw [householderInputWord_evaluate]
  refine ⟨inputColumnPhaseWord_unitary _ φ O W (tableHouseholder_unitary rs) hφ hW,
    tagFrame_isIsometry none F hF, tagFrame_isIsometry none F hF, ?_⟩
  rw [inputColumnPhaseWord_evaluate]
  have hc := input_phase_clean_compress F (evaluate O W) Y (tableHouseholder rs) φ none hblock
  simpa only [table_column_phase_coefficient] using hc

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
