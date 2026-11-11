/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ResolventHomotopy
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! The two actual derivatives used in scalar-anchor polygon homotopy.
The total ring inverse agrees with the canonical resolvent on separated panels. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc
open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Construction for homotopy Panel Inverse in the resolvent homotopy calculus model. -/
def homotopyPanelInverse (A : Matrix I I ℂ) (c z₀ u : ℂ) (a h s t : ℝ) :
    Matrix I I ℂ :=
  Ring.inverse (matrixShift (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h t))

/-- The identity or estimate `homotopyPanelInverse_eq_resolvent` holds with the displayed separation, geometry and norm hypotheses. -/
theorem homotopyPanelInverse_eq_resolvent (A : Matrix I I ℂ) (c z₀ u : ℂ)
    (a h s t r : ℝ) (hr : 0 < r) (hc : c ∈ matrixNumericalRange A)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel z₀ u a h t-w‖) :
    homotopyPanelInverse A c z₀ u a h s t =
      matrixResolvent (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h t) :=
  (matrixResolvent_eq_ringInverse_of_separation _ _ r hr
    (scalarAnchorHomotopy_separation A c _ hc s hs r hsep)).symm

/-- The identity or estimate `homotopyPanelInverse_hasDerivAt_s` holds with the displayed separation, geometry and norm hypotheses. -/
theorem homotopyPanelInverse_hasDerivAt_s (A : Matrix I I ℂ) (c z₀ u : ℂ)
    (a h s t : ℝ)
    (hu : IsUnit (matrixShift (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h t))) :
    HasDerivAt (fun v : ℝ => homotopyPanelInverse A c z₀ u a h v t)
      (homotopyPanelInverse A c z₀ u a h s t * (A-c • 1) *
        homotopyPanelInverse A c z₀ u a h s t) s := by
  let M := matrixShift (c • (1 : Matrix I I ℂ)) (contourPanel z₀ u a h t)
  let D := A-c • (1 : Matrix I I ℂ)
  have he (v : ℝ) : matrixShift (scalarAnchorHomotopy A c v) (contourPanel z₀ u a h t) =
      M+v • (-D) := by
    simp only [M, D, matrixShift, scalarAnchorHomotopy,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_neg]
    abel
  have hd := affine_ringInverse_hasDerivAt M (-D) s (by rwa [← he s])
  simpa only [homotopyPanelInverse, he, mul_neg, neg_mul, neg_neg, D] using hd

/-- The identity or estimate `homotopyPanelInverse_hasDerivAt_t` holds with the displayed separation, geometry and norm hypotheses. -/
theorem homotopyPanelInverse_hasDerivAt_t (A : Matrix I I ℂ) (c z₀ u : ℂ)
    (a h s t : ℝ)
    (hu : IsUnit (matrixShift (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h t))) :
    HasDerivAt (fun v : ℝ => homotopyPanelInverse A c z₀ u a h s v)
      (-u • (homotopyPanelInverse A c z₀ u a h s t *
        homotopyPanelInverse A c z₀ u a h s t)) t := by
  let M := matrixShift (scalarAnchorHomotopy A c s)
    (z₀-(((a+h/2 : ℝ) : ℂ)*u))
  have he (v : ℝ) : matrixShift (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h v) =
      M+v • (u • (1 : Matrix I I ℂ)) := by
    ext i j
    simp only [M, matrixShift, contourPanel, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_sub]
    ring
  have hd := affine_ringInverse_hasDerivAt M (u • (1 : Matrix I I ℂ)) t (by rwa [← he t])
  simpa only [homotopyPanelInverse, he, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, neg_smul, smul_neg, neg_mul] using hd

/-- The matrix direction commutes with its actual affine resolvent. -/
theorem homotopyPanelInverse_commute (A : Matrix I I ℂ) (c z₀ u : ℂ)
    (a h s t : ℝ)
    (hu : IsUnit (matrixShift (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h t))) :
    Commute (A-c • 1) (homotopyPanelInverse A c z₀ u a h s t) := by
  let D := A-c • (1 : Matrix I I ℂ)
  let Z := matrixShift (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h t)
  let R := Ring.inverse Z
  have hZ : Z = (contourPanel z₀ u a h t-c) • 1-(s : ℂ) • D := by
    dsimp only [Z, D, matrixShift, scalarAnchorHomotopy]
    rw [sub_smul]
    abel
  have hc : D*Z = Z*D := by
    rw [hZ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hZR : Z*R = 1 := Ring.mul_inverse_cancel _ hu
  have hRZ : R*Z = 1 := Ring.inverse_mul_cancel _ hu
  change D*R = R*D
  calc
    D*R = (R*Z)*(D*R) := by rw [hRZ, Matrix.one_mul]
    _ = R*(Z*D)*R := by simp only [Matrix.mul_assoc]
    _ = R*(D*Z)*R := by rw [hc]
    _ = R*D*(Z*R) := by simp only [Matrix.mul_assoc]
    _ = R*D := by rw [hZR, Matrix.mul_one]

/-- A closed differential form on the actual (homotopy, panel) rectangle.
This is the sign-sensitive identity needed before FTC and Fubini. -/
theorem homotopyPanelInverse_closed_form (A : Matrix I I ℂ) (c z₀ u : ℂ)
    (a h s t : ℝ)
    (hu : IsUnit (matrixShift (scalarAnchorHomotopy A c s) (contourPanel z₀ u a h t))) :
    HasDerivAt (fun v : ℝ => u • homotopyPanelInverse A c z₀ u a h v t)
      (u • (homotopyPanelInverse A c z₀ u a h s t * (A-c • 1) *
        homotopyPanelInverse A c z₀ u a h s t)) s ∧
    HasDerivAt (fun v : ℝ => -(A-c • 1) * homotopyPanelInverse A c z₀ u a h s v)
      (u • (homotopyPanelInverse A c z₀ u a h s t * (A-c • 1) *
        homotopyPanelInverse A c z₀ u a h s t)) t := by
  refine ⟨(homotopyPanelInverse_hasDerivAt_s A c z₀ u a h s t hu).const_smul u, ?_⟩
  have hp : homotopyPanelInverse A c z₀ u a h s t * (A-c • 1) *
      homotopyPanelInverse A c z₀ u a h s t =
      (A-c • 1) * (homotopyPanelInverse A c z₀ u a h s t *
        homotopyPanelInverse A c z₀ u a h s t) := by
    rw [← (homotopyPanelInverse_commute A c z₀ u a h s t hu).eq, Matrix.mul_assoc]
  simpa only [hp, neg_smul, mul_neg, neg_mul, neg_neg, Matrix.mul_smul] using
    (homotopyPanelInverse_hasDerivAt_t A c z₀ u a h s t hu).const_mul (-(A-c • 1))

end Qatlib.Concepts.MatrixContour.ContourCalc
