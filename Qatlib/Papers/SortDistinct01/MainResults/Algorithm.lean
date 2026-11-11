/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# An iterative phase-query model for first-index recovery

This module defines workspace/query indices, complex state vectors, and iteration of a phase
oracle followed by a fixed linear isometry. The predicate `ExactOrderedSearch` asks for a
readout returning the first true index of every nonzero Boolean input, and `readout_congr`
extracts equality of answers from equality of final states, supplying model definitions for the
ordered-search setting of [HoyerNeerbekShi2001].

## Main statements

* `ExactOrderedSearch`: The existence of a normalized initial state, a fixed linear isometry,
  and a readout returning the first true index of every nonzero Boolean input after `T` query
  iterations.
* `readout_congr`: A witness to `ExactOrderedSearch` yields a normalized iterative state family
  in which equal final states imply equal first-true indices.

## References

* [Hoyer et al., 2001][HoyerNeerbekShi2001]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.SortDistinct01.MainResults.Algorithm

/-- The joint index type for a workspace of size `Z` and a query register of size `N`. -/
abbrev QIdx (Z N : ℕ) : Type := Fin Z × Fin N

/-- The finite-dimensional complex Euclidean state space on workspace/query indices. -/
abbrev QState (Z N : ℕ) : Type := EuclideanSpace ℂ (QIdx Z N)

/-- The Euclidean state vector with coordinate function `f`. -/
def mkQ {Z N : ℕ} (f : QIdx Z N → ℂ) : QState Z N := WithLp.toLp 2 f

/-- The coordinatewise oracle action multiplying each amplitude by the input value at its query
index. -/
def phaseOracle {Z N : ℕ} (x : Fin N → ℂ) (u : QState Z N) : QState Z N :=
  mkQ fun j => x j.2 * u j

/-- The complex sign vector taking value `-1` at true bits and `1` at false bits. -/
def signOf {N : ℕ} (x : Fin N → Bool) : Fin N → ℂ :=
  fun i => if x i then -1 else 1

/-- A Boolean vector different from the all-false vector contains a true entry. -/
theorem ones_of_ne_zero {N : ℕ} {x : Fin N → Bool} (hx : x ≠ fun _ => false) :
    ∃ i, x i = true := by
  by_contra h
  apply hx
  funext i
  cases hi : x i
  · rfl
  · exact absurd ⟨i, hi⟩ h

/-- A Boolean vector different from the all-false vector has a true entry at some natural-number
index less than `N`. -/
theorem exists_index {N : ℕ} {x : Fin N → Bool} (hx : x ≠ fun _ => false) :
    ∃ n, ∃ _h : n < N, x ⟨n, _h⟩ = true := by
  obtain ⟨i, hi⟩ := ones_of_ne_zero hx
  exact ⟨i.1, i.2, hi⟩

/-- The least natural-number index of a true bit in a nonzero Boolean vector. -/
def firstOne {N : ℕ} (x : {x : Fin N → Bool // x ≠ fun _ => false}) : ℕ :=
  Nat.find (exists_index x.2)

/-- The state after iterating the phase oracle followed by the fixed linear isometry `U` for the
given number of steps. -/
def runState {Z N : ℕ} (U : QState Z N ≃ₗᵢ[ℂ] QState Z N) (x : Fin N → ℂ) :
    QState Z N → ℕ → QState Z N
  | ψ, 0 => ψ
  | ψ, k + 1 => U (phaseOracle x (runState U x ψ k))

/-- The existence of a normalized initial state, a fixed linear isometry, and a readout
returning the first true index of every nonzero Boolean input after `T` query iterations. -/
def ExactOrderedSearch (N T : ℕ) : Prop :=
  ∃ (Z : ℕ) (U : QState Z N ≃ₗᵢ[ℂ] QState Z N) (init : QState Z N)
    (readout : QState Z N → ℕ),
    ‖init‖ = 1 ∧
    ∀ (x : Fin N → Bool) (hx : x ≠ fun _ => false),
      readout (runState U (signOf x) init T) = firstOne ⟨x, hx⟩

/-- Zero query iterations leave the initial state unchanged. -/
theorem runState_zero {Z N : ℕ} (U : QState Z N ≃ₗᵢ[ℂ] QState Z N)
    (x : Fin N → ℂ) (init : QState Z N) : runState U x init 0 = init := rfl

/-- A witness to `ExactOrderedSearch` yields a normalized iterative state family in which equal
final states imply equal first-true indices. -/
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
