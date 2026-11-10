/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.SortDistinct01.MainResults.Algorithm

abbrev QIdx (Z N : ℕ) : Type := Fin Z × Fin N

abbrev QState (Z N : ℕ) : Type := EuclideanSpace ℂ (QIdx Z N)

def mkQ {Z N : ℕ} (f : QIdx Z N → ℂ) : QState Z N := WithLp.toLp 2 f

def phaseOracle {Z N : ℕ} (x : Fin N → ℂ) (u : QState Z N) : QState Z N :=
  mkQ fun j => x j.2 * u j

def signOf {N : ℕ} (x : Fin N → Bool) : Fin N → ℂ :=
  fun i => if x i then -1 else 1

theorem ones_of_ne_zero {N : ℕ} {x : Fin N → Bool} (hx : x ≠ fun _ => false) :
    ∃ i, x i = true := by
  by_contra h
  apply hx
  funext i
  cases hi : x i
  · rfl
  · exact absurd ⟨i, hi⟩ h

theorem exists_index {N : ℕ} {x : Fin N → Bool} (hx : x ≠ fun _ => false) :
    ∃ n, ∃ _h : n < N, x ⟨n, _h⟩ = true := by
  obtain ⟨i, hi⟩ := ones_of_ne_zero hx
  exact ⟨i.1, i.2, hi⟩

def firstOne {N : ℕ} (x : {x : Fin N → Bool // x ≠ fun _ => false}) : ℕ :=
  Nat.find (exists_index x.2)

def runState {Z N : ℕ} (U : QState Z N ≃ₗᵢ[ℂ] QState Z N) (x : Fin N → ℂ) :
    QState Z N → ℕ → QState Z N
  | ψ, 0 => ψ
  | ψ, k + 1 => U (phaseOracle x (runState U x ψ k))

def ExactOrderedSearch (N T : ℕ) : Prop :=
  ∃ (Z : ℕ) (U : QState Z N ≃ₗᵢ[ℂ] QState Z N) (init : QState Z N)
    (readout : QState Z N → ℕ),
    ‖init‖ = 1 ∧
    ∀ (x : Fin N → Bool) (hx : x ≠ fun _ => false),
      readout (runState U (signOf x) init T) = firstOne ⟨x, hx⟩

theorem runState_zero {Z N : ℕ} (U : QState Z N ≃ₗᵢ[ℂ] QState Z N)
    (x : Fin N → ℂ) (init : QState Z N) : runState U x init 0 = init := rfl

theorem readout_congr {N T : ℕ} (h : ExactOrderedSearch N T) :
    ∃ (Z : ℕ) (U : QState Z N ≃ₗᵢ[ℂ] QState Z N) (init : QState Z N),
      ‖init‖ = 1 ∧
      ∀ (x y : Fin N → Bool) (hx : x ≠ fun _ => false) (hy : y ≠ fun _ => false),
        runState U (signOf x) init T = runState U (signOf y) init T →
        firstOne ⟨x, hx⟩ = firstOne ⟨y, hy⟩ := by
  obtain ⟨Z, U, init, readout, hunit, hread⟩ := h
  exact ⟨Z, U, init, hunit, fun x y hx hy heq => by
    rw [← hread x hx, ← hread y hy, heq]⟩

end Qatlib.Papers.SortDistinct01.MainResults.Algorithm
