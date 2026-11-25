/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.MatrixGeometry.AxisRotations.SphericalAngles

@[expose] public section

/-!
# Closed forms for the recursive spherical-angle coefficients

The recursive coefficients of `Qatlib.Foundations.MatrixGeometry.AxisRotations.SphericalAngles`
expand the first angle into a cosine factor and the remaining angles into a chain of sine
factors. This module records that closed form: every nonterminal coefficient is the cosine of
twice its own angle multiplied by the sines of the earlier angles, and the final coefficient is
the pure product of all sines. See [VonBurgEtAl2021], Lemma 8 and Eq. (57).

## Main statements

* `coefficients_eq_cos_mul_prod_sin`: a nonterminal coefficient is `cos (2 θ i)` times the
  product of `sin (2 θ j)` over the strictly earlier angles.
* `coefficients_last`: the last coefficient is the product of all doubled-angle sines.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

namespace Qatlib.Papers.QCatalysis20.MainResults

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.MatrixGeometry.AxisRotations.SphericalAngles

/-- A nonterminal spherical coefficient is the cosine of its own doubled angle multiplied by the
sines of all earlier doubled angles. See [VonBurgEtAl2021], Eq. (57). -/
theorem coefficients_eq_cos_mul_prod_sin (n : ℕ) (θ : Fin n → ℝ) (i : Fin n) :
    coefficients n θ i.castSucc =
      Real.cos (2 * θ i) * ∏ j : Fin i.val, Real.sin (2 * θ ⟨j.val, by omega⟩) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [coefficients, Fin.castSucc_zero, Fin.cons_zero]
      show Real.cos (2 * θ 0) =
        Real.cos (2 * θ 0) * ∏ j : Fin 0, Real.sin (2 * θ ⟨j.val, by omega⟩)
      rw [Fin.prod_univ_zero, mul_one]
    · rw [← Fin.succ_castSucc]
      have hunfold : coefficients (n + 1) θ (Fin.succ (Fin.castSucc k)) =
          Real.sin (2 * θ 0) * coefficients n (fun j => θ j.succ) (Fin.castSucc k) := by
        simp [coefficients]
      rw [hunfold, ih (fun j => θ j.succ) k]
      change Real.sin (2 * θ 0) *
          (Real.cos (2 * θ (Fin.succ k)) *
            ∏ j : Fin k.val, Real.sin (2 * θ (Fin.succ ⟨j.val, by omega⟩))) =
        Real.cos (2 * θ (Fin.succ k)) *
          ∏ j : Fin (k.val + 1), Real.sin (2 * θ ⟨j.val, by omega⟩)
      rw [Fin.prod_univ_succ]
      simp only [Fin.succ_mk, Fin.val_succ, Fin.val_zero, Fin.zero_eta]
      ring

/-- The last spherical coefficient is the product of the sines of all doubled angles. See
[VonBurgEtAl2021], Eq. (57). -/
theorem coefficients_last (n : ℕ) (θ : Fin n → ℝ) :
    coefficients n θ (Fin.last n) = ∏ j : Fin n, Real.sin (2 * θ j) := by
  induction n with
  | zero => simp [coefficients]
  | succ n ih =>
    have hlast : Fin.last (n + 1) = Fin.succ (Fin.last n) := by simp [Fin.succ_last]
    rw [hlast]
    have hunfold : coefficients (n + 1) θ (Fin.succ (Fin.last n)) =
        Real.sin (2 * θ 0) * coefficients n (fun j => θ j.succ) (Fin.last n) := by
      simp [coefficients]
    rw [hunfold, ih (fun j => θ j.succ)]
    simp only [Fin.prod_univ_succ]

end Qatlib.Papers.QCatalysis20.MainResults
