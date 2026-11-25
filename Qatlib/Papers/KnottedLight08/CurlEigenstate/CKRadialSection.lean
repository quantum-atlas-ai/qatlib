/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRadialBounds
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRegularMode

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cartesian section derivatives of regular CK coefficients

At the origin each spatial section of the radius is an absolute
value. The vanishing derivatives of the regular coefficients let
the two smooth sections agree to first order there.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Set
open Qatlib.Papers.KnotLight13.TorusFamily (Spacetime coordinateValue coordinateSection coordinateSection_at)

/-- A differentiable function with derivative zero at zero remains
differentiable there on composition with a scaled absolute value. -/
private theorem hasDerivAt_mul_abs_zero {G : ℝ → ℝ} (hG : HasDerivAt G 0 0) (k : ℝ) :
    HasDerivAt (fun u => G (k * |u|)) 0 0 := by
  have smooth (a : ℝ) : HasDerivAt (fun u => G (a * u)) 0 0 := by
    have hG' : HasDerivAt G 0 (a * id (0 : ℝ)) := by simpa using hG
    simpa only [Function.comp_def, id_eq, zero_mul] using
      hG'.comp (h := fun u : ℝ => a * u) 0 ((hasDerivAt_id (0 : ℝ)).const_mul a)
  have hl : HasDerivWithinAt (fun u => G (k * |u|)) 0 (Iic 0) 0 := by
    refine (smooth (-k)).hasDerivWithinAt.congr_of_mem (fun u hu => ?_) (le_refl _)
    rw [abs_of_nonpos (mem_Iic.mp hu), mul_neg, neg_mul]
  have hr : HasDerivWithinAt (fun u => G (k * |u|)) 0 (Ici 0) 0 := by
    refine (smooth k).hasDerivWithinAt.congr_of_mem (fun u hu => ?_) (le_refl _)
    rw [abs_of_nonneg (mem_Ici.mp hu)]
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

/-- A regular radial coefficient has each Cartesian section derivative
given by the chain rule, with zero derivative at the spatial origin. -/
theorem hasDerivAt_ckRadialSection {G D : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (D u) u) (hD : D 0 = 0) (k : ℝ) (s : Spacetime) (i : Fin 3) :
    let R := fun p : Spacetime => ckRadius p.1 p.2.1 p.2.2.1
    HasDerivAt (fun u => G (k * R (coordinateSection s i.castSucc u)))
      (D (k * R s) * (k * (coordinateValue s i.castSucc / R s))) (coordinateValue s i.castSucc) := by
  let R := fun p : Spacetime => ckRadius p.1 p.2.1 p.2.2.1
  change HasDerivAt (fun u => G (k * R (coordinateSection s i.castSucc u)))
    (D (k * R s) * (k * (coordinateValue s i.castSucc / R s))) (coordinateValue s i.castSucc)
  by_cases hr : R s = 0
  · rcases s with ⟨x, y, z, t⟩
    obtain ⟨rfl, rfl, rfl⟩ := ckRadius_zero_coords hr
    have hs (u : ℝ) : R (coordinateSection (0, 0, 0, t) i.castSucc u) = |u| := by
      fin_cases i <;> simp [R, ckRadius, coordinateSection, Fin.castSucc, Real.sqrt_sq_eq_abs]
    have hc : coordinateValue (0, 0, 0, t) i.castSucc = 0 := by
      fin_cases i <;> simp [coordinateValue, Fin.castSucc]
    simp only [hs, hc, hr, mul_zero, div_zero]
    have hG0 : HasDerivAt G 0 0 := by simpa only [hD] using hG 0
    exact hasDerivAt_mul_abs_zero hG0 k
  · have hR : HasDerivAt (fun u => R (coordinateSection s i.castSucc u))
        (coordinateValue s i.castSucc / R s) (coordinateValue s i.castSucc) := by
      fin_cases i
      · simpa [R, coordinateSection, coordinateValue, Fin.castSucc] using hasDerivAt_ckRadius_x hr
      · simpa [R, coordinateSection, coordinateValue, Fin.castSucc] using hasDerivAt_ckRadius_y hr
      · simpa [R, coordinateSection, coordinateValue, Fin.castSucc] using hasDerivAt_ckRadius_z hr
    have hG' : HasDerivAt G (D (k * R s))
        (k * R (coordinateSection s i.castSucc (coordinateValue s i.castSucc))) := by
      rw [coordinateSection_at]
      exact hG _
    exact hG'.comp (h := fun u => k * R (coordinateSection s i.castSucc u))
      (coordinateValue s i.castSucc) (hR.const_mul k)

/-- A linear bound on the radial derivative gives a quadratic
frequency bound for the Cartesian section derivative. -/
theorem abs_ckRadialSection_le {D : ℝ → ℝ} {c : ℝ}
    (hB : ∀ u, |D u| ≤ |u| * c) (k : ℝ) (s : Spacetime) (i : Fin 3) :
    let r := ckRadius s.1 s.2.1 s.2.2.1
    let q := coordinateValue s i.castSucc
    |D (k * r) * (k * (q / r))| ≤ k ^ 2 * |q| * c := by
  let r := ckRadius s.1 s.2.1 s.2.2.1
  let q := coordinateValue s i.castSucc
  change |D (k * r) * (k * (q / r))| ≤ k ^ 2 * |q| * c
  have hc : 0 ≤ c := by
    have h := (abs_nonneg (D 1)).trans (hB 1)
    simpa only [abs_one, one_mul] using h
  by_cases hr : r = 0
  · rw [hr, div_zero, mul_zero, mul_zero, abs_zero]
    positivity
  · have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
    rw [abs_mul, abs_mul, abs_div, abs_of_nonneg hrpos.le]
    have h := mul_le_mul_of_nonneg_right (hB (k * r))
      (mul_nonneg (abs_nonneg k) (div_nonneg (abs_nonneg q) hrpos.le))
    rw [abs_mul, abs_of_nonneg hrpos.le] at h
    refine h.trans_eq ?_
    rw [← sq_abs k]
    field_simp [hr]

end Qatlib.Papers.KnottedLight08.CurlEigenstate
