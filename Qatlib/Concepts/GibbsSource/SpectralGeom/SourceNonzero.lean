/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.SourcePositiveGap

@[expose] public section


/-!
# Genuine positive gaps of the original complete CKG parents

For n > 0 and beta > 0 the existing exact kernel theorem, together with
two independent matrix units, proves that each actual parent is nonzero.
Consequently the full positive spectrum is nonempty and its minimum is
attained and strictly positive.  This is finite-system positivity only.
The quantitative comparison consumer still requires the complete source
comparison and a damped form-gap bound; neither is manufactured here.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- A D-by-D matrix space with D > 1 cannot be the span of a single vector. -/
theorem sourceMap_ne_zero_of_kernel_scalar_line (hD : 1 < D)
    (L : Operator D →ₗ[ℂ] Operator D) (W : Operator D)
    (hker : ∀ X, L X = 0 → ∃ c : ℂ, X = c • W) : L ≠ 0 := by
  let i : Fin D := ⟨0, lt_trans Nat.zero_lt_one hD⟩
  let j : Fin D := ⟨1, hD⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  intro hzero
  obtain ⟨c, hc⟩ := hker (matUnit i i 1) (by rw [hzero]; rfl)
  obtain ⟨d, hd⟩ := hker (matUnit i j 1) (by rw [hzero]; rfl)
  have hc00 : (1 : ℂ) = c * W i i := by
    simpa [matUnit_apply, Matrix.smul_apply] using
      congrArg (fun X : Operator D => X i i) hc
  have hc01 : (0 : ℂ) = c * W i j := by
    simpa [matUnit_apply, Matrix.smul_apply, hij, Ne.symm hij] using
      congrArg (fun X : Operator D => X i j) hc
  have hd01 : (1 : ℂ) = d * W i j := by
    simpa [matUnit_apply, Matrix.smul_apply] using
      congrArg (fun X : Operator D => X i j) hd
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at hc00
    exact one_ne_zero hc00
  have hw : W i j = 0 := (mul_eq_zero.mp hc01.symm).resolve_left hc0
  rw [hw, mul_zero] at hd01
  exact one_ne_zero hd01


end Qatlib.Concepts.GibbsSource.SpectralGeom
