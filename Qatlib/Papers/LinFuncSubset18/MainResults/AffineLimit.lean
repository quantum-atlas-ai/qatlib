/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinFuncSubset18.MainResults.Core.SourceCore
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! Functional vanishing on a finite affine space does not imply symbolic divisibility. -/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinFuncSubset18.MainResults

open MvPolynomial
open Qatlib.Papers.LinFuncSubset18.MainResults.Core

/-- The Frobenius polynomial vanishes at every point of the two-dimensional F2 space. -/
theorem frobenius_zero (u : Fin 2 → ZMod 2) :
    eval u ((X (1 : Fin 2)) ^ 2 - X 1) = 0 := by
  simp only [map_sub, map_pow, eval_X]
  exact sub_eq_zero.mpr (ZMod.pow_card (u 1))

/-- The free-coordinate Frobenius polynomial is not divisible by the first coordinate. -/
theorem free_not_dvd :
    ¬ (X (0 : Fin 2) : MvPolynomial (Fin 2) (ZMod 2)) ∣ X 1 ^ 2 - X 1 := by
  let φ : MvPolynomial (Fin 2) (ZMod 2) →+* Polynomial (ZMod 2) :=
    eval₂Hom Polynomial.C (fun i => if i = 0 then 0 else Polynomial.X)
  rintro ⟨q, hq⟩
  have h := congrArg φ hq
  have h0 : φ (X 0) = 0 := by simp [φ]
  have h1 : φ (X 1) = Polynomial.X := by simp [φ]
  simp only [map_sub, map_pow, map_mul, h0, h1, zero_mul] at h
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 2) h
  norm_num [Polynomial.coeff_X] at hc

/-- The exact legacy affine-vanishing implication fails over F2 in dimension two. -/
theorem affine_bad :
    ∃ (ℓ : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (g : MvPolynomial (Fin 2) (ZMod 2)),
      ℓ ≠ 0 ∧ (∀ u, ℓ u = 0 → eval u g = 0) ∧ ¬ (linearPoly ℓ - C 0) ∣ g := by
  let ℓ : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj 0
  refine ⟨ℓ, X 1 ^ 2 - X 1, ?_, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun f : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2 => f (fun _ => 1)) h
    simp [ℓ] at hh
  · intro u _
    exact frobenius_zero u
  · have hlin : linearPoly ℓ = (X 0 : MvPolynomial (Fin 2) (ZMod 2)) := by
      simp [linearPoly, ℓ, Fin.sum_univ_succ]
    simpa [hlin] using free_not_dvd

end Qatlib.Papers.LinFuncSubset18.MainResults
