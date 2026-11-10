/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.MarkovQsampling.Basic
import Qatlib.Papers.AdiabStateGen03.MainResults.MarkovQsampling.Overlap
import Qatlib.Papers.AdiabStateGen03.MainResults.Simulation.TransferChain
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.MarkovQsampling

open Qatlib.Papers.AdiabStateGen03.MainResults
open Qatlib.Papers.AdiabStateGen03.MainResults.Simulation

variable {n : ℕ}

theorem SlowlyVarying.nonneg_overlap {T : ℕ} {π : Fin (T + 1) → Dim n → ℝ}
    (hπ : ∀ t i, 0 ≤ π t i) (h : SlowlyVarying π) (t : Fin T) :
    NonNegligibleAt n
      (⟪ketOfDist (π (Fin.castSucc t)), ketOfDist (π t.succ)⟫_ℂ).re := by
  rw [slowlyVarying_overlap_eq_inner π hπ t]
  exact h t

theorem groundstate_overlap_le_one {T : ℕ} (π : Fin (T + 1) → Dim n → ℝ)
    (hπ : ∀ t i, 0 ≤ π t i) (hsum : ∀ t, ∑ i, π t i = 1) (t : Fin T) :
    (⟪ketOfDist (π (Fin.castSucc t)), ketOfDist (π t.succ)⟫_ℂ).re ≤ 1 := by
  rw [slowlyVarying_overlap_eq_inner π hπ t]
  exact overlap_le_one_prob _ _ (hπ _) (hπ _) (hsum _) (hsum _)

theorem slowlyVarying_overlap_pos_groundstate {T : ℕ}
    {π : Fin (T + 1) → Dim n → ℝ} (h : SlowlyVarying π) (t : Fin T) :
    0 < (⟪ketOfDist (π (Fin.castSucc t)), ketOfDist (π t.succ)⟫_ℂ).re
      ∨ 0 < ∑ i : Dim n, Real.sqrt (π (Fin.castSucc t) i * π t.succ i) := by
  exact Or.inr (slowlyVarying_overlap_pos π h t)

theorem qsampling_chain {T : ℕ} (φ : Fin (T + 1) → State n)
    (hstep : ∀ t : Fin T, TransfersState (φ (Fin.castSucc t)) (φ (Fin.succ t)))
    (h₀ : QSamples (φ 0)) : QSamples (φ (Fin.last T)) := by
  unfold QSamples at h₀ ⊢
  exact Generable.trans h₀ (transfersState_chain φ hstep)

theorem rapidlyMixing_gap (M : MC n) (π : Dim n → ℝ) (h : RapidlyMixing M π) :
    ∃ γ : ℝ, 0 < γ ∧ SpectralGapAtLeast (HM M π) (ketOfDist π) γ ∧
      ∃ c k : ℕ, 0 < c ∧ 1 / ((c : ℝ) * ((n : ℝ) + 1) ^ k) ≤ γ := by
  obtain ⟨γ, ⟨c, k, hc, hle⟩, hgap⟩ := h
  exact ⟨γ, lt_of_lt_of_le (by positivity) hle, hgap, c, k, hc, hle⟩

end Qatlib.Papers.AdiabStateGen03.MainResults.MarkovQsampling
