/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.RegisterLCUBridge
import Qatlib.Papers.Cbmd26.Algorithms.CountedQSVTBridge
import Qatlib.Papers.Cbmd26.Algorithms.SeparateOracleBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

abbrev OriginalResponseSpace (W : Type) := Bool × (Bool × (Bool × W))

variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]

def originalResponseWord (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (d : ℕ) (base : ℂ) (zs : List ℂ) : List (AdjointStep (J × OriginalResponseSpace W)) :=
  expandedIndexedResponseWord (paddedFirstOrderInputWord α Λ s)
    (tagFrame false (tagFrame false R)) d (fun _ => base) (zs.map (fun z => fun _ => z))

def originalResponseUnitary (U : Matrix W W ℂ) (R : Matrix W I ℂ) (α Λ s : ℝ)
    (d : ℕ) (base : ℂ) (zs : List ℂ) : Matrix (OriginalResponseSpace W) (OriginalResponseSpace W) ℂ :=
  evaluate (parallelOracle (paddedFirstOrderInputUnitary U α Λ s))
    (hermitianResponseWord (tagFrame false (tagFrame false R)) d base zs)

def originalResponseQuery (U : Matrix W W ℂ) :
    Matrix (J × OriginalResponseSpace W) (J × OriginalResponseSpace W) ℂ :=
  parallelOracle (J := J) (parallelOracle (J := Bool)
    (parallelOracle (J := Bool) (controlOracle U)))

omit [DecidableEq I] in

theorem originalResponseWord_evaluate (U : Matrix W W ℂ) (R : Matrix W I ℂ)
    (α Λ : ℝ) (s : J → ℝ) (d : ℕ) (base : ℂ) (zs : List ℂ) :
    evaluate (originalResponseQuery U) (originalResponseWord R α Λ s d base zs) =
      select (fun j => originalResponseUnitary U R α Λ (s j) d base zs) := by
  have he := expandedIndexedResponseWord_evaluate
    (parallelOracle (J := Bool) (controlOracle U)) (paddedFirstOrderInputWord α Λ s)
    (fun j => paddedFirstOrderInputUnitary U α Λ (s j))
    (paddedFirstOrderInputWord_evaluate α Λ s U)
    (tagFrame false (tagFrame false R)) d (fun _ : J => base) (zs.map (fun z => fun _ => z))
  simpa [originalResponseWord, originalResponseUnitary, originalResponseQuery,
    List.map_map, Function.comp_def] using he

omit [DecidableEq I] in

theorem originalResponseWord_cost (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (d : ℕ) (base : ℂ) (zs : List ℂ) :
    adjointQueryCount (originalResponseWord R α Λ s d base zs) = 2 * zs.length ∧
    adjointGateCount (originalResponseWord R α Λ s d base zs) = 9 * zs.length + 1 := by
  obtain ⟨hq,hg⟩ := expandedIndexedResponseWord_cost (paddedFirstOrderInputWord α Λ s)
    (tagFrame false (tagFrame false R)) d (fun _ : J => base) (zs.map (fun z => fun _ => z))
  rw [(paddedFirstOrderInputWord_cost α Λ s).1, List.length_map, Nat.mul_comm] at hq
  rw [(paddedFirstOrderInputWord_cost α Λ s).2, List.length_map] at hg
  refine ⟨hq, hg.trans ?_⟩
  omega

theorem originalResponseWord_wellFormed (R : Matrix W I ℂ) (hR : IsIsometry R)
    (α Λ : ℝ) (s : J → ℝ) (hα : 0 < α) (hΛ : 0 < Λ)
    (hbound : ∀ j, α * Real.sqrt (1 + (s j)^2) ≤ Λ)
    (d : ℕ) (base : ℂ) (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit (originalResponseWord R α Λ s d base zs) := by
  apply expandedIndexedResponseWord_wellFormed
    _ (paddedFirstOrderInputWord_wellFormed α Λ s hα hΛ hbound)
    _ (tagFrame_isIsometry _ _ (tagFrame_isIsometry _ _ hR)) _ _ (fun _ => hb)
  intro z hz j
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  exact hzs w hw

def originalFourSampleUnitary (U : Matrix W W ℂ) (R : Matrix W I ℂ)
    (α Λ s : ℝ) (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    Matrix (Fin 4 × OriginalResponseSpace W) (Fin 4 × OriginalResponseSpace W) ℂ :=
  coefficientLCUUnitary fourBranchCoefficients
    (fun k => originalResponseUnitary U R α Λ s (d k) (base k) (zs k)) 0

def originalFourSampleWord (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    List (AdjointStep (J × (Fin 4 × OriginalResponseSpace W))) :=
  reindexAdjointWord (swapLabelEquiv J (Fin 4) (OriginalResponseSpace W))
    (fourCoefficientWord fourBranchCoefficients
      (fun k => originalResponseWord R α Λ s (d k) (base k) (zs k)))

def originalFourQuery (U : Matrix W W ℂ) :
    Matrix (J × (Fin 4 × OriginalResponseSpace W)) (J × (Fin 4 × OriginalResponseSpace W)) ℂ :=
  (maskedOracle fourActive (originalResponseQuery (J := J) U)).submatrix
    (swapLabelEquiv J (Fin 4) (OriginalResponseSpace W))
    (swapLabelEquiv J (Fin 4) (OriginalResponseSpace W))

omit [DecidableEq I] in

theorem originalFourSampleWord_evaluate (U : Matrix W W ℂ) (R : Matrix W I ℂ)
    (α Λ : ℝ) (s : J → ℝ) (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    evaluate (originalFourQuery U) (originalFourSampleWord R α Λ s d base zs) =
      select (fun j => originalFourSampleUnitary U R α Λ (s j) d base zs) := by
  unfold originalFourQuery originalFourSampleWord
  rw [reindexAdjointWord_evaluate, fourCoefficientWord_evaluate]
  simp_rw [originalResponseWord_evaluate]
  exact coefficientLCUUnitary_swap_labels fourBranchCoefficients 0 _

omit [DecidableEq I] in

theorem originalFourSampleWord_cost (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    adjointQueryCount (originalFourSampleWord R α Λ s d base zs) = 2 * ∑ k, (zs k).length ∧
    adjointGateCount (originalFourSampleWord R α Λ s d base zs) = 9 * (∑ k, (zs k).length) + 13 := by
  simp only [originalFourSampleWord, (reindexAdjointWord_cost _ _).1,
    (reindexAdjointWord_cost _ _).2]
  obtain ⟨hq,hg⟩ := fourCoefficientWord_cost fourBranchCoefficients
    (fun k => originalResponseWord R α Λ s (d k) (base k) (zs k))
  simp_rw [(originalResponseWord_cost R α Λ s _ _ _).1] at hq
  simp_rw [(originalResponseWord_cost R α Λ s _ _ _).2] at hg
  simp only [← Finset.mul_sum] at hq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hg
  exact ⟨hq, hg.trans (by omega)⟩

theorem originalFourSampleWord_wellFormed (R : Matrix W I ℂ) (hR : IsIsometry R)
    (α Λ : ℝ) (s : J → ℝ) (hα : 0 < α) (hΛ : 0 < Λ)
    (hbound : ∀ j, α * Real.sqrt (1 + (s j)^2) ≤ Λ)
    (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ)
    (hp : ∀ k, IsPhase (base k) ∧ ∀ z ∈ zs k, IsPhase z) :
    WellFormedAdjointCircuit (originalFourSampleWord R α Λ s d base zs) := by
  apply reindexAdjointWord_wellFormed
  apply fourCoefficientWord_wellFormed _ (by rw [fourBranchCoefficients_mass]; norm_num)
  intro k
  exact originalResponseWord_wellFormed R hR α Λ s hα hΛ hbound
    (d k) (base k) (hp k).1 (zs k) (hp k).2

abbrev OriginalStaticLabels (J : Type) := J × (Fin 4 × (Bool × (Bool × Bool)))

def originalStaticWorkspaceEquiv (J W : Type) :
    OriginalStaticLabels J × W ≃ J × (Fin 4 × OriginalResponseSpace W) where
  toFun := fun ⟨⟨j,k,b,c,a⟩,w⟩ => (j,k,b,c,a,w)
  invFun := fun ⟨j,k,b,c,a,w⟩ => ((j,k,b,c,a),w)
  left_inv _ := rfl
  right_inv _ := rfl

def originalStaticMask (label : OriginalStaticLabels J) : Bool :=
  fourActive label.2.1 && label.2.2.2.2

omit [Fintype J] [Fintype W] in

theorem originalStaticSource_reindex (U : Matrix W W ℂ) :
    (originalFourQuery (J := J) U).submatrix
      (originalStaticWorkspaceEquiv J W) (originalStaticWorkspaceEquiv J W) =
    maskedOracle originalStaticMask U := by
  ext ⟨⟨j,k,b,c,a⟩,i⟩ ⟨⟨j',k',b',c',a'⟩,l⟩
  by_cases hj : j = j' <;> by_cases hk : k = k' <;>
    by_cases hb : b = b' <;> by_cases hc : c = c' <;> by_cases ha : a = a' <;>
    simp [originalFourQuery, originalResponseQuery, originalStaticWorkspaceEquiv,
      originalStaticMask, swapLabelEquiv, maskedOracle, select, parallelOracle,
      controlOracle, hj, hk, hb, hc, ha]
  all_goals cases hactive : fourActive k <;> cases a <;> simp_all [Matrix.one_apply]

def originalStaticRawOuterWord (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (c : J → ℂ) (j₀ : J) (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    List (AdjointStep (J × (Fin 4 × OriginalResponseSpace W))) :=
  outerCoefficientWord (scaledLCUCoefficients c (fun _ => 4)) j₀
    (originalFourSampleWord R α Λ s d base zs)

def originalStaticOuterWord (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (c : J → ℂ) (j₀ : J) (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    List (AdjointStep (Bool × (OriginalStaticLabels J × W))) :=
  cleanMaskedWord originalStaticMask
    (reindexAdjointWord (originalStaticWorkspaceEquiv J W)
      (originalStaticRawOuterWord R α Λ s c j₀ d base zs))

omit [DecidableEq I] in

theorem originalStaticOuterWord_cost (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (c : J → ℂ) (j₀ : J) (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    adjointQueryCount (originalStaticOuterWord R α Λ s c j₀ d base zs) = 2 * ∑ k, (zs k).length ∧
    adjointGateCount (originalStaticOuterWord R α Λ s c j₀ d base zs) = 13 * (∑ k, (zs k).length) + 16 := by
  obtain ⟨h0q,h0g⟩ := originalFourSampleWord_cost R α Λ s d base zs
  obtain ⟨h1q,h1g⟩ := outerCoefficientWord_cost (scaledLCUCoefficients c (fun _ => 4)) j₀
    (originalFourSampleWord R α Λ s d base zs)
  change adjointQueryCount (originalStaticRawOuterWord R α Λ s c j₀ d base zs) = _ at h1q
  change adjointGateCount (originalStaticRawOuterWord R α Λ s c j₀ d base zs) = _ at h1g
  obtain ⟨hq,hg⟩ := cleanMaskedWord_cost originalStaticMask
    (reindexAdjointWord (originalStaticWorkspaceEquiv J W)
      (originalStaticRawOuterWord R α Λ s c j₀ d base zs))
  rw [(reindexAdjointWord_cost _ _).1, h1q, h0q] at hq
  rw [(reindexAdjointWord_cost _ _).1, (reindexAdjointWord_cost _ _).2,
    h1q, h1g, h0q, h0g] at hg
  exact ⟨hq, hg.trans (by omega)⟩

omit [DecidableEq I] in

theorem originalStaticRawOuterWord_evaluate (U : Matrix W W ℂ) (R : Matrix W I ℂ)
    (α Λ : ℝ) (s : J → ℝ) (c : J → ℂ) (j₀ : J)
    (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    evaluate (originalFourQuery U) (originalStaticRawOuterWord R α Λ s c j₀ d base zs) =
      coefficientLCUUnitary (scaledLCUCoefficients c (fun _ => 4))
        (fun j => originalFourSampleUnitary U R α Λ (s j) d base zs) j₀ :=
  outerCoefficientWord_evaluate _ _ _ _ _ (originalFourSampleWord_evaluate U R α Λ s d base zs)

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
