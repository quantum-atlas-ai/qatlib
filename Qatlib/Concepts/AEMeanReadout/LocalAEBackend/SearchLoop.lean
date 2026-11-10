/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutCore
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Bound
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchProgram
set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option warningAsError false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

noncomputable def windowLoop {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ)) : ℕ → ℕ → PMF (Option I × ℕ × ℕ)
  | 0, _ => PMF.pure (none, 0, 0)
  | T + 1, off =>
      (round (off + 1)).bind fun out =>
        match out.1 with
        | some _ => PMF.pure out
        | none =>
            (windowLoop A hA j₀ S round T (off + 1)).map fun r =>
              (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2)

noncomputable def sourceQSearchLoop {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    ℕ → ℕ → PMF (Option I × ℕ × ℕ) :=
  windowLoop A hA j₀ S (sourceQSearchRound A hA j₀ S)

theorem windowLoop_zero_eq {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (off : ℕ) :
    windowLoop A hA j₀ S round 0 off = PMF.pure (none, 0, 0) := rfl

theorem windowLoop_succ_eq {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (T off : ℕ) :
    windowLoop A hA j₀ S round (T + 1) off
      = (round (off + 1)).bind fun out =>
        match out.1 with
        | some _ => PMF.pure out
        | none =>
            (windowLoop A hA j₀ S round T (off + 1)).map fun r =>
              (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2) := rfl

theorem windowRound_shape {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) (trial : Fin M → CostedLaw (I × ℕ))
    (ledger : Fin M → ℕ × ℕ) (out : Option I × ℕ × ℕ)
    (hout : out ∈ (windowRound A hA j₀ S M hM trial ledger).support) :
    ∀ y, out.1 = some y → y ∈ S := by
  rw [windowRound] at hout
  obtain ⟨st, hst, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  by_cases hS : st.1.1 ∈ S
  · rw [if_pos hS] at hout
    have hout' : out = (some st.1.1, 1, 1) := by
      simpa [PMF.mem_support_pure_iff] using! hout
    subst hout'
    intro y hy
    rw [← Option.some.inj hy]
    exact hS
  · rw [if_neg hS] at hout
    obtain ⟨j, hj, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    obtain ⟨st2, hst2, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have hout' : out = (if st2.1.1 ∈ S then some st2.1.1 else none,
        (ledger j).1, (ledger j).2) := by
      simpa [PMF.mem_support_pure_iff] using! hout
    subst hout'
    intro y hy
    by_cases h2 : st2.1.1 ∈ S
    · rw [if_pos h2] at hy
      rw [← Option.some.inj hy]
      exact h2
    · rw [if_neg h2] at hy
      exact absurd hy (by simp)

theorem windowLoop_shape {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ))
    (hround : ∀ l out, out ∈ (round l).support → ∀ y, out.1 = some y → y ∈ S) :
    ∀ (T off : ℕ) (out : Option I × ℕ × ℕ),
      out ∈ (windowLoop A hA j₀ S round T off).support →
      ∀ y, out.1 = some y → y ∈ S := by
  intro T
  induction T with
  | zero =>
    intro off out hout y hy
    rw [windowLoop_zero_eq] at hout
    have hout' : out = (none, 0, 0) := by
      simpa [PMF.mem_support_pure_iff] using! hout
    subst hout'
    exact absurd hy (by simp)
  | succ T ih =>
    intro off out hout y hy
    rw [windowLoop_succ_eq] at hout
    obtain ⟨out1, hout1, hout2⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    obtain ⟨o1, o2, o3⟩ := out1
    cases o1 with
    | none =>
      obtain ⟨r, hr, hgr⟩ := (PMF.mem_support_map_iff _ _ _).mp hout2
      refine ih (off + 1) r hr y ?_
      have hout1' : out.1 = r.1 := by rw [← hgr]
      rw [← hout1']
      exact hy
    | some z =>
      have hpure : out ∈ (PMF.pure (some z, o2, o3)).support := hout2
      have hout2' : out = (some z, o2, o3) := by
        simpa [PMF.mem_support_pure_iff] using! hpure
      subst hout2'
      exact hround (off + 1) _ hout1 y hy

theorem sourceLoop_shape (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) :
    ∀ (T off : ℕ) (out : Option I × ℕ × ℕ),
      out ∈ (sourceQSearchLoop A hA j₀ S T off).support →
      ∀ y, out.1 = some y → y ∈ S :=
  windowLoop_shape A hA j₀ S (sourceQSearchRound A hA j₀ S) fun l out hout =>
    windowRound_shape A hA j₀ S (qSearchWindow l) (qSearchWindow_pos l) _ _ out hout
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
