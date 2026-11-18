/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Protocols.ClosedMath

@[expose] public section


/-! # Literal weak contracts, separated from coding and correction theorems

The legacy compression contract defines the rate set to be an open ray.
It supplies no encoder, decoder, error analysis or achievability bridge.
The legacy recovery contract asks for an arbitrary function,
so a constant function satisfies it for every error set and every matrix.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.Protocols

open Qatlib.Papers.QShannonWilde11.MainResults.Model

/-- The infimum of the legacy open rate ray is its endpoint, without a coding claim. -/
theorem sInf_entropy_open_ray {X : Type} [Fintype X] (p : X → ℝ)
    (_hp : IsProb p) :
    sInf {R : ℝ | classicalEntropy p < R} = classicalEntropy p := by
  exact csInf_Ioi

/-- The legacy recovery conclusion holds even without code or error assumptions. -/
theorem exists_constant_recovery_on_error_images {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (Err : Set (Matrix (Fin d) (Fin d) ℂ)) :
    ∃ R : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ,
      ∀ E ∈ Err, R (E * P * E.conjTranspose) = P := by
  exact ⟨fun _ => P, fun _ _ => rfl⟩

/-- The literal old Chernoff target compares the same scalar with itself.
There is no random operator, event, independence assumption or tail estimate. -/
theorem chernoff_scalar_le_self {Ω : Type} [Fintype Ω] (Pr : Ω → ℝ)
    (_hPr : IsProb Pr) (dim K : ℕ) (η a : ℝ) (_hη : 0 < η) (_ha : 0 < a) :
    1 - 2 * (dim : ℝ) * Real.exp (-(K : ℝ) * η ^ 2 * a / 4) ≤
      1 - 2 * (dim : ℝ) * Real.exp (-(K : ℝ) * η ^ 2 * a / 4) := by
  exact le_rfl

end Qatlib.Papers.QShannonWilde11.MainResults.Protocols
