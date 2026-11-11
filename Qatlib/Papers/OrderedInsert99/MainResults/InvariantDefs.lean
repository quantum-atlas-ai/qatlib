/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryAlgorithm
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Invariant ordered-insertion states

Defines the phase oracle and momentum-space recurrence for invariant ordered insertion in
[FarhiEtAl1999]. `ExactQueryInsertion` expresses zero-error solvability by a normalized unitary
query circuit, while `ExactInvariantAlgorithm` requires the recurrence to reach the prescribed
parity-supported target state.

## Main statements

* `psi`: the state obtained by alternating query steps and coordinate phases.
* `ExactStage`: equality of the final state with the target amplitudes.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The index type `Fin (2 * N)` for the doubled ordered-insertion space. -/
abbrev Idx (N : ℕ) := Fin (2 * N)

/-- The comparison sign, equal to −1 below `j` and 1 otherwise. -/
def fSign (j x : ℕ) : ℂ := if x < j then -1 else 1

/-- The comparison sign extended to the doubled index space with opposite signs on its two
halves. -/
def Fsign (N j : ℕ) (x : Idx N) : ℂ :=
  if (x : ℕ) < N then fSign j (x : ℕ) else -fSign j ((x : ℕ) - N)

/-- The diagonal phase-oracle matrix with diagonal entries `Fsign N j`. -/
noncomputable def oracleMatrix (N j : ℕ) : Matrix (Idx N) (Idx N) ℂ :=
  Matrix.diagonal (Fsign N j)

/-- The pair of doubled-space indices corresponding to the insertion position `j`. -/
noncomputable def targetSet (N : ℕ) (j : Fin N) : Finset (Idx N) :=
  {⟨(j : ℕ), by have := j.isLt; omega⟩, ⟨(j : ℕ) + N, by have := j.isLt; omega⟩}

/-- The family of insertion-oracle matrices indexed by `Fin N`. -/
noncomputable def insertOracle (N : ℕ) : Fin N → Matrix (Idx N) (Idx N) ℂ :=
  fun j => oracleMatrix N (j : ℕ)

/-- The accepting index sets for the ordered-insertion oracle family. -/
noncomputable def insertAccept (N : ℕ) : Fin N → Finset (Idx N) :=
  fun j => targetSet N j

/-- Existence of a normalized unitary query circuit using at most `k` queries and solving
insertion with zero error. -/
def ExactQueryInsertion (N k : ℕ) : Prop :=
  ∃ (C : Circuit (Idx N)) (ψ₀ : QState (Idx N)),
    IsUnitaryCircuit C ∧ Normalized ψ₀ ∧ QueryCount C ≤ k ∧
      SolvesWithError (insertOracle N) (insertAccept N) C ψ₀ 0

/-- The momentum angle π(q − p)/(2N) for two doubled-space indices. -/
def momAngle (N : ℕ) (p q : Idx N) : ℝ :=
  Real.pi * ((q : ℝ) - (p : ℝ)) / (2 * (N : ℝ))

/-- The complex query-transition amplitude, given by the sine-denominator formula for opposite
parities and zero otherwise. -/
noncomputable def queryAmp (N : ℕ) (p q : Idx N) : ℂ :=
  if ((p : ℕ) + (q : ℕ)) % 2 = 1 then
    Complex.I * Complex.exp ((↑(-(momAngle N p q)) : ℂ) * Complex.I) /
      ((N : ℂ) * (↑(Real.sin (momAngle N p q)) : ℂ))
  else 0

/-- Multiplies each amplitude by the complex phase determined by `α`. -/
def phaseApply {N : ℕ} (α : Idx N → ℝ) (a : Idx N → ℂ) : Idx N → ℂ :=
  fun p => Complex.exp (Complex.I * ((α p : ℝ) : ℂ)) * a p

/-- The linear query update obtained by summing `queryAmp` against the input amplitudes. -/
noncomputable def queryStep (N : ℕ) (a : Idx N → ℂ) : Idx N → ℂ :=
  fun p => ∑ q, queryAmp N p q * a q

/-- The coordinate state supported at index zero. -/
def startState (N : ℕ) : Idx N → ℂ := fun p => if (p : ℕ) = 0 then 1 else 0

/-- The state recurrence starting at `startState` and alternating a query update with the phases
at the next stage. -/
noncomputable def psi (N : ℕ) (α : ℕ → Idx N → ℝ) : ℕ → Idx N → ℂ
  | 0 => startState N
  | ℓ + 1 => phaseApply (α (ℓ + 1)) (queryStep N (psi N α ℓ))

/-- Target amplitudes equal to `1 / √N` on the specified parity class and zero elsewhere. -/
def targetAmp (N : ℕ) (parity : ℕ) (p : Idx N) : ℂ :=
  if (p : ℕ) % 2 = parity then (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) else 0

/-- The inner product of the stage-`k` state with the target of parity `k % 2`. -/
noncomputable def successAmplitude (N k : ℕ) (α : ℕ → Idx N → ℝ) : ℂ :=
  ∑ p, star (targetAmp N (k % 2) p) * psi N α k p

/-- The squared norm of `successAmplitude`. -/
noncomputable def successProbability (N k : ℕ) (α : ℕ → Idx N → ℝ) : ℝ :=
  ‖successAmplitude N k α‖ ^ 2

/-- The condition that the stage-`k` state equals the prescribed target at every index. -/
def ExactStage (N k : ℕ) (α : ℕ → Idx N → ℝ) : Prop :=
  ∀ p, psi N α k p = targetAmp N (k % 2) p

/-- Existence of a phase schedule satisfying `ExactStage N k`. -/
def ExactInvariantAlgorithm (N k : ℕ) : Prop :=
  ∃ α : ℕ → Idx N → ℝ, ExactStage N k α

/-- The comparison sign at insertion position zero is always 1. -/
@[simp] theorem fSign_zero (x : ℕ) : fSign 0 x = 1 := by
  simp [fSign]

/-- The extended sign for insertion position zero is 1 on the first half of the index space. -/
theorem Fsign_zero_first {N x : ℕ} (hx : x < N) :
    Fsign N 0 ⟨x, by omega⟩ = 1 := by
  simp [Fsign, fSign, hx]

/-- The extended sign for insertion position zero is −1 on the second half of the index space. -/
theorem Fsign_zero_second {N x : ℕ} (hN : x < 2 * N) (hx : N ≤ x) :
    Fsign N 0 ⟨x, hN⟩ = -1 := by
  have h1 : ¬ x < N := by omega
  have h2 : ¬ x - N < 0 := by omega
  simp [Fsign, fSign, h1, h2]

/-- Query amplitudes vanish between indices of equal parity. -/
theorem queryAmp_eq_zero_of_parity {N : ℕ} {p q : Idx N}
    (h : (p : ℕ) % 2 = (q : ℕ) % 2) : queryAmp N p q = 0 := by
  have hsum : ((p : ℕ) + (q : ℕ)) % 2 ≠ 1 := by omega
  simp [queryAmp, hsum]

/-- The success probability is nonnegative. -/
theorem successProbability_nonneg (N k : ℕ) (α : ℕ → Idx N → ℝ) :
    0 ≤ successProbability N k α := by
  unfold successProbability
  positivity

/-- The stage-zero state is `startState`, independently of the phase schedule. -/
@[simp] theorem psi_zero (N : ℕ) (α : ℕ → Idx N → ℝ) :
    psi N α 0 = startState N := rfl

end Qatlib.Papers.OrderedInsert99.MainResults
