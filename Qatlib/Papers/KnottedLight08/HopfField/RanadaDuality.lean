/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaField

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A quarter-turn identifies the electric and magnetic Rañada fields

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
The rotation about the propagation axis interchanges the homogeneous
electric and magnetic chart data up to a constant unit phase. The
phase cancels in the conjugate cross product, so the rotation
identifies the actual oriented fields, including their chart poles.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

open Qatlib.Papers.KnottedLight08.HopfField (cross3)
open scoped ComplexConjugate

/-- The positive quarter-turn about the third Cartesian axis. -/
def quarterTurnCoords {F : Type*} [Neg F] (a : Fin 3 → F) : Fin 3 → F :=
  ![-a 1, a 0, a 2]

/-- The scalar radial letter is invariant under the spatial quarter-turn. -/
private theorem ranadaA_quarterTurn (x y z t : ℝ) :
    ranadaA (-y) x z t = ranadaA x y z t := by
  unfold ranadaA
  ring

/-- The magnetic denominator on the rotated point equals the electric
denominator, including all points where it is zero. -/
theorem etaDen_quarterTurn (x y z t : ℝ) :
    etaDen (-y) x z t = zetaDen x y z t := by
  have hp : ranadaP (-y) x z t = ranadaR x y z t := by
    simp only [ranadaP, ranadaR, ranadaA_quarterTurn]
    ring
  have hs : ranadaS (-y) x z t = ranadaS x y z t := by simp only [ranadaS, ranadaA_quarterTurn]
  simp only [etaDen, zetaDen, hp, hs]

/-- The magnetic numerator at the rotated point is the electric
numerator times the unit phase minus i. -/
theorem etaNum_quarterTurn (x y z t : ℝ) :
    etaNum (-y) x z t = -Complex.I * zetaNum x y z t := by
  have hr : ranadaR (-y) x z t = -ranadaP x y z t := by
    simp only [ranadaR, ranadaP, ranadaA_quarterTurn]
    ring
  have hq : ranadaQ (-y) x z t = ranadaQ x y z t := by simp only [ranadaQ, ranadaA_quarterTurn]
  apply Complex.ext <;>
    simp [etaNum, zetaNum, hr, hq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

/-- A quarter-turn transfers the affine scalar and multiplies its
label by minus i. -/
theorem ranadaEta_quarterTurn (x y z t : ℝ) :
    ranadaEta (-y) x z t = -Complex.I * ranadaZeta x y z t := by
  rw [ranadaEta_def, ranadaZeta_def, etaDen_quarterTurn, etaNum_quarterTurn, mul_div_assoc]

/-- The magnetic denominator gradient is the rotated electric one. -/
private theorem etaDenGrad_quarterTurn (x y z t : ℝ) :
    etaDenGrad (-y) x z t = quarterTurnCoords (zetaDenGrad x y z t) := by
  funext j
  fin_cases j <;> apply Complex.ext <;>
    simp [etaDenGrad, etaDenX, etaDenY, etaDenZ, zetaDenGrad, zetaDenX, zetaDenY, zetaDenZ,
      quarterTurnCoords, ranadaA_quarterTurn, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The magnetic numerator gradient is the rotated electric gradient
times the same unit phase as the numerator. -/
private theorem etaNumGrad_quarterTurn (x y z t : ℝ) :
    etaNumGrad (-y) x z t = fun j => -Complex.I * quarterTurnCoords (zetaNumGrad x y z t) j := by
  funext j
  fin_cases j <;> apply Complex.ext <;>
    simp [etaNumGrad, etaNumX, etaNumY, etaNumZ, zetaNumGrad, zetaNumX, zetaNumY, zetaNumZ,
      quarterTurnCoords, ranadaA_quarterTurn, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The two homogeneous spatial derivative vectors agree up to the
proper rotation and the unit phase. -/
private theorem etaHomog_quarterTurn (x y z t : ℝ) :
    etaHomog (-y) x z t = fun j => -Complex.I * quarterTurnCoords (zetaHomog x y z t) j := by
  funext j
  simp only [etaHomog, etaDen_quarterTurn, etaNum_quarterTurn,
    etaDenGrad_quarterTurn, etaNumGrad_quarterTurn]
  fin_cases j <;> simp [quarterTurnCoords, zetaHomog] <;> ring

/-- The unit phase preserves the homogeneous normalization. -/
private theorem etaSumSq_quarterTurn (x y z t : ℝ) :
    etaSumSq (-y) x z t = zetaSumSq x y z t := by
  have hI : -Complex.I * Complex.I = (1 : ℂ) := by
    rw [neg_mul, ← pow_two, Complex.I_sq, neg_neg]
  rw [etaSumSq, etaNum_quarterTurn, etaDen_quarterTurn, zetaSumSq, map_mul, map_neg,
    Complex.conj_I, neg_neg]
  congr 1
  calc
    _ = (-Complex.I * Complex.I) * (zetaNum x y z t * conj (zetaNum x y z t)) := by ring
    _ = _ := by rw [hI, one_mul]

/-- The proper rotation commutes with a cross product, and constant
scalars factor out of the two slots. -/
private theorem cross3_quarterTurn_scaled (a b : ℂ) (u v : Fin 3 → ℂ) :
    cross3 (fun j => a * quarterTurnCoords u j) (fun j => b * quarterTurnCoords v j) =
      fun j => (a * b) * quarterTurnCoords (cross3 u v) j := by
  funext j
  fin_cases j <;> simp [quarterTurnCoords, cross3] <;> ring

/-- Complex conjugation commutes with the signed coordinate permutation. -/
private theorem conj_quarterTurnCoords (v : Fin 3 → ℂ) (j : Fin 3) :
    conj (quarterTurnCoords v j) = quarterTurnCoords (fun k => conj (v k)) j := by
  fin_cases j <;> simp [quarterTurnCoords]

/-- The homogeneous cross products agree after the proper rotation. -/
private theorem etaCross_quarterTurn (x y z t : ℝ) :
    cross3 (etaHomog (-y) x z t) (fun j => conj (etaHomog (-y) x z t j)) =
      quarterTurnCoords (cross3 (zetaHomog x y z t) (fun j => conj (zetaHomog x y z t j))) := by
  simp only [etaHomog_quarterTurn, map_mul, map_neg, Complex.conj_I, neg_neg,
    conj_quarterTurnCoords]
  rw [cross3_quarterTurn_scaled]
  have hI : -Complex.I * Complex.I = (1 : ℂ) := by
    rw [neg_mul, ← pow_two, Complex.I_sq, neg_neg]
  simp only [hI, one_mul]

/-- The literal magnetic field at the rotated point is the positively
rotated literal electric field, at every real time. -/
theorem ranadaB_quarterTurn_eq_ranadaE (x y z t : ℝ) :
    ranadaB (-y) x z t = quarterTurnCoords (ranadaE x y z t) := by
  funext j
  simp only [ranadaB, etaCross_quarterTurn, etaSumSq_quarterTurn]
  fin_cases j <;> simp [quarterTurnCoords, ranadaE, neg_div]

end Qatlib.Papers.KnottedLight08.HopfField
