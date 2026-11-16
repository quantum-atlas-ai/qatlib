/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import Qatlib.Papers.EigenFilter19.MainResults.SourceProductInequality
public import Qatlib.Papers.EigenFilter19.MainResults.SourceQSVT

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open scoped Classical BigOperators

open Qatlib.Papers.EigenFilter19.MainResults

namespace Qatlib.Papers.EigenFilter19.MainResults

section

/-- Squared norm of a state vector, `sum_i |u_i|^2`. -/
def stateNorm {n : ℕ} (u : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (u i))

/-- The bra-ket `<u|v> = sum_i conj(u_i) v_i`. -/
def braket {n : ℕ} (u v : Fin n → ℂ) : ℂ := ∑ i, starRingEnd ℂ (u i) * v i

/-- Absolute overlap `|<u|v>|`. -/
def overlapR {n : ℕ} (u v : Fin n → ℂ) : ℝ := ‖braket u v‖

/-- Normalisation of a state vector (real scalar `1/||u||`). -/
def normalize {n : ℕ} (u : Fin n → ℂ) : Fin n → ℂ :=
  fun i => Complex.ofReal ((stateNorm u)⁻¹) * u i

end

end Qatlib.Papers.EigenFilter19.MainResults
