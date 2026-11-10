/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.PiecewiseGridFreeze
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace CBMD
open Matrix Set
open scoped Matrix.Norms.L2Operator

theorem suppliedGrid_interval_exists {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (huN : u < τ N) :
    ∃ j : ℕ, j < N ∧ τ j ≤ u ∧ u < τ (j+1) := by
  induction N with
  | zero => rw [hτ0] at huN; linarith
  | succ N ih =>
    by_cases hu : u < τ N
    · obtain ⟨j,hj,hjl,hjr⟩ := ih hu
      exact ⟨j,by omega,hjl,hjr⟩
    · exact ⟨N,by omega,le_of_not_gt hu,huN⟩

def suppliedGridAddress (τ : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, j < N ∧ τ j ≤ u ∧ u < τ (j+1)
    then Nat.find h else 0

def suppliedGridSampleTime (τ : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  τ (suppliedGridAddress τ N u)

def suppliedGridOracle {β : Type*} (U : ℝ → β) (τ : ℕ → ℝ) (N : ℕ) (u : ℝ) : β :=
  U (suppliedGridSampleTime τ N u)

theorem suppliedGridAddress_spec {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (huN : u < τ N) :
    suppliedGridAddress τ N u < N ∧
      τ (suppliedGridAddress τ N u) ≤ u ∧ u < τ (suppliedGridAddress τ N u+1) := by
  classical
  have hex := suppliedGrid_interval_exists hτ0 hu0 huN
  simpa only [suppliedGridAddress, dif_pos hex] using Nat.find_spec hex

theorem suppliedGridSampleTime_mem {τ : ℕ → ℝ} (hτ : Monotone τ) (hτ0 : τ 0 = 0)
    {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (huN : u < τ N) :
    suppliedGridSampleTime τ N u ∈ Set.Icc 0 (τ N) := by
  have hs := suppliedGridAddress_spec hτ0 hu0 huN
  constructor
  · simpa only [hτ0] using! hτ (Nat.zero_le (suppliedGridAddress τ N u))
  · exact hτ hs.1.le

variable {I : Type} {W : Type*} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem suppliedGridField_eq_address {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    (B : ℕ → Matrix I I ℂ) {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (huN : u < τ N) :
    suppliedGridField τ B N u = B (suppliedGridAddress τ N u) := by
  classical
  have hex := suppliedGrid_interval_exists hτ0 hu0 huN
  simp only [suppliedGridField, suppliedGridAddress, dif_pos hex]

theorem suppliedGridField_original {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    (A : ℝ → Matrix I I ℂ) {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (huN : u < τ N) :
    suppliedGridField τ (fun j => A (τ j)) N u = A (suppliedGridSampleTime τ N u) :=
  suppliedGridField_eq_address hτ0 (fun j => A (τ j)) hu0 huN

theorem original_timeOracle_suppliedGrid_encoding {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (A : ℝ → Matrix I I ℂ) (U : ℝ → Matrix W W ℂ)
    (L R : Matrix W I ℂ) (N : ℕ) (α ε : ℝ)
    (henc : ∀ t ∈ Set.Icc 0 (τ N), BlockEncoding (A t) (U t) L R α ε)
    {u : ℝ} (hu0 : 0 ≤ u) (huN : u < τ N) :
    BlockEncoding (suppliedGridField τ (fun j => A (τ j)) N u)
      (suppliedGridOracle U τ N u) L R α ε := by
  rw [suppliedGridField_original hτ0 A hu0 huN]
  exact henc _ (suppliedGridSampleTime_mem hτ hτ0 hu0 huN)

theorem uniformGridTime_mem {T : ℝ} (hT : 0 < T) {M : ℕ} (hM : 0 < M)
    (j : Fin M) : 0 ≤ T*j.val/M ∧ T*j.val/M < T := by
  have hMp : 0 < (M:ℝ) := by exact_mod_cast hM
  constructor
  · positivity
  · apply (div_lt_iff₀ hMp).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast j.isLt) hT

theorem original_timeOracle_fineGrid_encoding {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (A : ℝ → Matrix I I ℂ) (U : ℝ → Matrix W W ℂ)
    (L R : Matrix W I ℂ) (N M : ℕ) {T α ε : ℝ}
    (hτN : τ N = T) (hT : 0 < T) (hM : 0 < M)
    (henc : ∀ t ∈ Set.Icc 0 T, BlockEncoding (A t) (U t) L R α ε)
    (j : Fin M) :
    BlockEncoding (suppliedGridField τ (fun k => A (τ k)) N (T*j.val/M))
      (suppliedGridOracle U τ N (T*j.val/M)) L R α ε := by
  have hu := uniformGridTime_mem hT hM j
  apply original_timeOracle_suppliedGrid_encoding hτ hτ0 A U L R N α ε
    (by simpa only [hτN] using henc) hu.1
  simpa only [hτN] using hu.2

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
