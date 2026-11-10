/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryAlgorithm
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

abbrev Idx (N : ℕ) := Fin (2 * N)

def fSign (j x : ℕ) : ℂ := if x < j then -1 else 1

def Fsign (N j : ℕ) (x : Idx N) : ℂ :=
  if (x : ℕ) < N then fSign j (x : ℕ) else -fSign j ((x : ℕ) - N)

noncomputable def oracleMatrix (N j : ℕ) : Matrix (Idx N) (Idx N) ℂ :=
  Matrix.diagonal (Fsign N j)

noncomputable def targetSet (N : ℕ) (j : Fin N) : Finset (Idx N) :=
  {⟨(j : ℕ), by have := j.isLt; omega⟩, ⟨(j : ℕ) + N, by have := j.isLt; omega⟩}

noncomputable def insertOracle (N : ℕ) : Fin N → Matrix (Idx N) (Idx N) ℂ :=
  fun j => oracleMatrix N (j : ℕ)

noncomputable def insertAccept (N : ℕ) : Fin N → Finset (Idx N) :=
  fun j => targetSet N j

def ExactQueryInsertion (N k : ℕ) : Prop :=
  ∃ (C : Circuit (Idx N)) (ψ₀ : QState (Idx N)),
    IsUnitaryCircuit C ∧ Normalized ψ₀ ∧ QueryCount C ≤ k ∧
      SolvesWithError (insertOracle N) (insertAccept N) C ψ₀ 0

def momAngle (N : ℕ) (p q : Idx N) : ℝ :=
  Real.pi * ((q : ℝ) - (p : ℝ)) / (2 * (N : ℝ))

noncomputable def queryAmp (N : ℕ) (p q : Idx N) : ℂ :=
  if ((p : ℕ) + (q : ℕ)) % 2 = 1 then
    Complex.I * Complex.exp ((↑(-(momAngle N p q)) : ℂ) * Complex.I) /
      ((N : ℂ) * (↑(Real.sin (momAngle N p q)) : ℂ))
  else 0

def phaseApply {N : ℕ} (α : Idx N → ℝ) (a : Idx N → ℂ) : Idx N → ℂ :=
  fun p => Complex.exp (Complex.I * ((α p : ℝ) : ℂ)) * a p

noncomputable def queryStep (N : ℕ) (a : Idx N → ℂ) : Idx N → ℂ :=
  fun p => ∑ q, queryAmp N p q * a q

def startState (N : ℕ) : Idx N → ℂ := fun p => if (p : ℕ) = 0 then 1 else 0

noncomputable def psi (N : ℕ) (α : ℕ → Idx N → ℝ) : ℕ → Idx N → ℂ
  | 0 => startState N
  | ℓ + 1 => phaseApply (α (ℓ + 1)) (queryStep N (psi N α ℓ))

def targetAmp (N : ℕ) (parity : ℕ) (p : Idx N) : ℂ :=
  if (p : ℕ) % 2 = parity then (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) else 0

noncomputable def successAmplitude (N k : ℕ) (α : ℕ → Idx N → ℝ) : ℂ :=
  ∑ p, star (targetAmp N (k % 2) p) * psi N α k p

noncomputable def successProbability (N k : ℕ) (α : ℕ → Idx N → ℝ) : ℝ :=
  ‖successAmplitude N k α‖ ^ 2

def ExactStage (N k : ℕ) (α : ℕ → Idx N → ℝ) : Prop :=
  ∀ p, psi N α k p = targetAmp N (k % 2) p

def ExactInvariantAlgorithm (N k : ℕ) : Prop :=
  ∃ α : ℕ → Idx N → ℝ, ExactStage N k α

@[simp] theorem fSign_zero (x : ℕ) : fSign 0 x = 1 := by
  simp [fSign]

theorem Fsign_zero_first {N x : ℕ} (hx : x < N) :
    Fsign N 0 ⟨x, by omega⟩ = 1 := by
  simp [Fsign, fSign, hx]

theorem Fsign_zero_second {N x : ℕ} (hN : x < 2 * N) (hx : N ≤ x) :
    Fsign N 0 ⟨x, hN⟩ = -1 := by
  have h1 : ¬ x < N := by omega
  have h2 : ¬ x - N < 0 := by omega
  simp [Fsign, fSign, h1, h2]

theorem queryAmp_eq_zero_of_parity {N : ℕ} {p q : Idx N}
    (h : (p : ℕ) % 2 = (q : ℕ) % 2) : queryAmp N p q = 0 := by
  have hsum : ((p : ℕ) + (q : ℕ)) % 2 ≠ 1 := by omega
  simp [queryAmp, hsum]

theorem successProbability_nonneg (N k : ℕ) (α : ℕ → Idx N → ℝ) :
    0 ≤ successProbability N k α := by
  unfold successProbability
  positivity

@[simp] theorem psi_zero (N : ℕ) (α : ℕ → Idx N → ℝ) :
    psi N α 0 = startState N := rfl

end Qatlib.Papers.OrderedInsert99.MainResults
