/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CarlemanLin24.MainResults.Source.SourceModel
public import Mathlib.Tactic.NormNum

@[expose] public section


set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.CarlemanLin24.MainResults.SourceChecks

open Qatlib.Papers.CarlemanLin24.MainResults.Source

/-- The legacy spectrum set always contains zero because it permits the zero multiplicity vector. -/
theorem zero_in_spectrum_set {n : ℕ} (lam : Fin n → ℂ) (N : ℕ) :
    0 ∈ carlemanSpectrumSet lam N := by
  refine ⟨0, ?_, ?_⟩ <;> simp

/-- Zero is not an eigenvalue of the one-dimensional negative identity. -/
theorem neg_one_no_zero :
    ¬ IsEigenvalue (-1 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  rintro ⟨v, hv, he⟩
  apply hv
  have h := congrFun he 0
  ext i
  fin_cases i
  simpa [Matrix.mulVec, dotProduct] using h

end Qatlib.Papers.CarlemanLin24.MainResults.SourceChecks
