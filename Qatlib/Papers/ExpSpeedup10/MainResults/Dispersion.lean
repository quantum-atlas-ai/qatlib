/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceCore

@[expose] public section


/-! # Preserved conditional dispersiveness support

This retains the closed finite maximum/logarithm argument from the mixed legacy
Theorem II source (arXiv:1010.3654v2, Eqs. (20)–(22)). The squared-entry bound
is an explicit assumption here: constructing and estimating a finite-group QFT
matrix is not covered, nor are the random-design claims.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Qatlib.Papers.ExpSpeedup10.MainResults.Model

namespace Qatlib.Papers.ExpSpeedup10.MainResults.Dispersion

/-- A true squared-entry estimate implies the corresponding logarithmic bound. -/
theorem dispersionBound
    {D N : ℕ} (hD : 0 < D) (hN : 0 < N) (U : Matrix (Fin D) (Fin D) ℂ)
    (hentry : ∀ i j, ‖U i j‖ ^ 2 ≤ (N : ℝ) ^ (-(1 / 2) : ℝ))
    (hpos : 0 < sSup (Set.range fun p : Fin D × Fin D => ‖U p.1 p.2‖ ^ 2)) :
    (1 / 2) * Real.logb 2 (N : ℝ) ≤ sourceC U := by
  -- Eq. (20)-(22), p. 9: bound the max entry by `N^{-1/2}`, then use
  -- monotonicity of `logb 2` and `logb 2 (N^{-1/2}) = -(1/2) logb 2 N`.
  unfold sourceC
  set S : ℝ := sSup (Set.range fun p : Fin D × Fin D => ‖U p.1 p.2‖ ^ 2) with hS
  have hSpos : 0 < S := by rw [hS]; exact hpos
  have hne : (Set.range fun p : Fin D × Fin D => ‖U p.1 p.2‖ ^ 2).Nonempty :=
    ⟨_, ⟨(⟨0, hD⟩, ⟨0, hD⟩), rfl⟩⟩
  have hle : S ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [hS]
    exact csSup_le hne (by rintro _ ⟨p, rfl⟩; exact hentry p.1 p.2)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlog : Real.logb 2 S ≤ Real.logb 2 ((N : ℝ) ^ (-(1 / 2) : ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hSpos hle
  have hrpow : Real.logb 2 ((N : ℝ) ^ (-(1 / 2) : ℝ)) =
      (-(1 / 2)) * Real.logb 2 (N : ℝ) :=
    Real.logb_rpow_eq_mul_logb_of_pos (x := (N : ℝ)) (y := (-(1 / 2) : ℝ)) hNpos
  have hneg : -(Real.logb 2 ((N : ℝ) ^ (-(1 / 2) : ℝ))) ≤ -Real.logb 2 S := by linarith
  calc (1 / 2) * Real.logb 2 (N : ℝ)
      = -(Real.logb 2 ((N : ℝ) ^ (-(1 / 2) : ℝ))) := by rw [hrpow]; ring
    _ ≤ -Real.logb 2 S := hneg

end Qatlib.Papers.ExpSpeedup10.MainResults.Dispersion
