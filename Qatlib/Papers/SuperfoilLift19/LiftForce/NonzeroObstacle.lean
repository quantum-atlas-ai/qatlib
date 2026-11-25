/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.MovingAirfoil

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A nonzero obstacle-potential regression

[Musser2019Superfoil], equations (1), (2), and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).

The polynomial wave `1 + x²` and the positive obstacle potential
`(1 + x²)⁻¹` give an exact, non-free solution of the zero-interaction GPE.
The potential is genuinely nonzero and its force density is nonzero on the
control rectangle.  The instance consumes both the fixed and translating
dynamic impulse laws, keeping the finite-contour result separate from the
additional compact-support and far-field hypotheses.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Set
open scoped ComplexConjugate

/-- A real polynomial wave, viewed as a complex GPE wave. -/
def nonzeroObstacleWave (p : GPESpacetime) : ℂ :=
  ((1 + p.2.1 ^ 2 : ℝ) : ℂ)

/-- A positive, spatially varying obstacle potential. -/
def nonzeroObstaclePotential (x : ℝ × ℝ) : ℝ :=
  (1 + x.1 ^ 2)⁻¹

/-- The nonzero obstacle potential is smooth enough for the dynamic law. -/
theorem contDiff_nonzeroObstaclePotential :
    ContDiff ℝ 1 nonzeroObstaclePotential := by
  unfold nonzeroObstaclePotential
  apply (contDiff_const.add (contDiff_fst.pow 2)).inv
  intro x
  positivity

/-- The obstacle wave is smooth enough for the dynamic law. -/
theorem contDiff_nonzeroObstacleWave :
    ContDiff ℝ 3 nonzeroObstacleWave := by
  unfold nonzeroObstacleWave
  have h : ContDiff ℝ 3 (fun p : GPESpacetime => 1 + p.2.1 ^ 2) := by
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp h

private theorem nonzeroObstacleWave_time (p : GPESpacetime) :
    gpePartial gpeTimeDirection nonzeroObstacleWave p = 0 := by
  rw [gpePartial_time_eq_deriv p
    (contDiff_nonzeroObstacleWave.differentiable (by norm_num) p)]
  simp [nonzeroObstacleWave]

private theorem nonzeroObstacleWave_dx (p : GPESpacetime) :
    gpePartial (gpeSpaceDirection 0) nonzeroObstacleWave p =
      ((2 * p.2.1 : ℝ) : ℂ) := by
  rw [gpePartial_space_eq_axisLine p 0
    (contDiff_nonzeroObstacleWave.differentiable (by norm_num) p)]
  rcases p with ⟨t, x, y⟩
  change deriv (fun s : ℝ => ((1 + (x + s) ^ 2 : ℝ) : ℂ)) 0 = _
  have hpow := ((hasDerivAt_id (0 : ℝ)).const_add x).pow 2
  have h := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hpow
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 h
  simpa [Function.comp_def, id_eq] using hc.deriv

private theorem nonzeroObstacleWave_dy (p : GPESpacetime) :
    gpePartial (gpeSpaceDirection 1) nonzeroObstacleWave p = 0 := by
  rw [gpePartial_space_eq_axisLine p 1
    (contDiff_nonzeroObstacleWave.differentiable (by norm_num) p)]
  rcases p with ⟨t, x, y⟩
  simp [nonzeroObstacleWave, axisLine]

private theorem nonzeroObstacleWave_dxx (p : GPESpacetime) :
    gpePartial (gpeSpaceDirection 0)
      (gpePartial (gpeSpaceDirection 0) nonzeroObstacleWave) p = 2 := by
  rw [show gpePartial (gpeSpaceDirection 0) nonzeroObstacleWave =
      (fun q => ((2 * q.2.1 : ℝ) : ℂ)) from funext nonzeroObstacleWave_dx]
  rw [gpePartial_space_eq_axisLine p 0]
  · rcases p with ⟨t, x, y⟩
    change deriv (fun s : ℝ => ((2 * (x + s) : ℝ) : ℂ)) 0 = _
    have h := ((hasDerivAt_id (0 : ℝ)).const_add x).const_mul 2
    have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 h
    simpa [Function.comp_def, id_eq] using hc.deriv
  · fun_prop

private theorem nonzeroObstacleWave_dyy (p : GPESpacetime) :
    gpePartial (gpeSpaceDirection 1)
      (gpePartial (gpeSpaceDirection 1) nonzeroObstacleWave) p = 0 := by
  rw [show gpePartial (gpeSpaceDirection 1) nonzeroObstacleWave =
      (fun _ => 0) from funext nonzeroObstacleWave_dy]
  simp [gpePartial]

/-- The translating potential is the fixed obstacle when the contour is at rest. -/
private theorem nonzeroObstaclePotential_rest (p : GPESpacetime) :
    gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential p =
      nonzeroObstaclePotential p.2 := by
  change nonzeroObstaclePotential (p.2 - (0, 0)) = nonzeroObstaclePotential p.2
  congr 1
  ext <;> simp

/-- The polynomial wave solves the exact zero-interaction GPE with the
nonzero obstacle potential on the whole plane. -/
theorem nonzeroObstacleWave_gpe (p : GPESpacetime) :
    GrossPitaevskiiAt 1 0 1
      (gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential)
      nonzeroObstacleWave p := by
  rw [GrossPitaevskiiAt, nonzeroObstacleWave_time, gpeLaplacian,
    Fin.sum_univ_two, nonzeroObstacleWave_dxx, nonzeroObstacleWave_dyy,
    nonzeroObstaclePotential_rest]
  have hden : (1 + p.2.1 ^ 2 : ℝ) ≠ 0 := by positivity
  have hdenC : (1 + (((p.2.1 : ℝ) : ℂ) ^ 2)) ≠ 0 := by
    exact_mod_cast hden
  simp [nonzeroObstacleWave, nonzeroObstaclePotential]
  field_simp [hden, hdenC]
  norm_num

/-- The obstacle potential is nonzero at the center of the obstacle. -/
theorem nonzeroObstaclePotential_ne_zero :
    nonzeroObstaclePotential (0, 0) ≠ 0 := by
  norm_num [nonzeroObstaclePotential]

private theorem nonzeroObstaclePotential_fderiv_at_one :
    fderiv ℝ nonzeroObstaclePotential (1, 0) (1, 0) = -(1 / 2 : ℝ) := by
  have hpow := (hasDerivAt_id (1 : ℝ)).pow 2
  have h := hpow.const_add 1
  have hInv := h.inv (by norm_num)
  have hc := hInv.hasFDerivAt.comp ((1, 0) : ℝ × ℝ)
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)
      (p := ((1, 0) : ℝ × ℝ)))
  have he := congrArg
    (fun D : (ℝ × ℝ) →L[ℝ] ℝ => D ((1, 0) : ℝ × ℝ)) hc.fderiv
  norm_num [nonzeroObstaclePotential, Function.comp_def, id_eq,
    ContinuousLinearMap.toSpanSingleton_apply] at he
  exact he

/-- The actual obstacle force density is nonzero at a point in the control
rectangle.  This is the witness excluded by the free-plane-wave regression. -/
theorem nonzeroObstacle_forceDensity_at_one :
    gpeDensity nonzeroObstacleWave (0, (1, 0)) *
        gpePartial (gpeSpaceDirection 0)
          (gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential)
          (0, (1, 0)) = -2 := by
  have hW := nonzeroObstaclePotential_fderiv_at_one
  have hV :
      gpePartial (gpeSpaceDirection 0)
          (gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential)
          (0, (1, 0)) =
        fderiv ℝ nonzeroObstaclePotential (1, 0) (1, 0) := by
    simpa [gpeSpaceDirection] using
      gpePartial_translatingPotential_space
        (η := fun _ : ℝ => (0, 0)) (W := nonzeroObstaclePotential)
        (0, (1, 0)) 0 (by fun_prop)
        (contDiff_nonzeroObstaclePotential.differentiable (by norm_num) _)
  rw [hV, hW]
  norm_num [gpeDensity, nonzeroObstacleWave, Complex.normSq_apply]

/-- The exact dynamic control-rectangle theorem consumes the nonzero
obstacle and its non-free GPE wave. -/
theorem nonzeroObstacle_rectangle_impulse_balance :
    gpeRectangleMomentum 1 nonzeroObstacleWave 0 (0, 0) (1, 1) 1 -
        gpeRectangleMomentum 1 nonzeroObstacleWave 0 (0, 0) (1, 1) 0 +
        (∫ t in (0 : ℝ)..1,
          rectangleForce (fun x j l =>
            gpeWaveStress 1 0 1 nonzeroObstacleWave j l (t, x)) 0 (0, 0) (1, 1)) =
      -(∫ t in (0 : ℝ)..1, ∫ x in Icc (0, 0) (1, 1),
        gpeDensity nonzeroObstacleWave (t, x) *
          gpePartial (gpeSpaceDirection 0)
            (gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential)
            (t, x)) := by
  have hV : ContDiff ℝ 1
      (gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential) :=
    contDiff_gpeTranslatingPotential contDiff_const contDiff_nonzeroObstaclePotential
  exact gpe_rectangle_impulse_balance 1 0 1
    (V := gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential)
    (ψ := nonzeroObstacleWave) (U := Set.univ)
    hV contDiff_nonzeroObstacleWave isOpen_univ
    (fun p _ => nonzeroObstacleWave_gpe p)
    (t₀ := 0) (t₁ := 1) (by norm_num)
    (a := (0, 0)) (b := (1, 1)) (by constructor <;> norm_num)
    (Set.subset_univ _) 0

/-- The translating version has the same exact impulse law, with a nonzero
potential and nonzero force density in the body term. -/
theorem nonzeroObstacle_moving_rectangle_impulse_balance :
    gpeMovingRectangleMomentum 1 nonzeroObstacleWave (fun _ : ℝ => (0, 0)) 0
        (0, 0) (1, 1) 1 -
        gpeMovingRectangleMomentum 1 nonzeroObstacleWave (fun _ : ℝ => (0, 0)) 0
          (0, 0) (1, 1) 0 +
        (∫ t in (0 : ℝ)..1,
          gpeMovingRectangleFlux 1 0 1 nonzeroObstacleWave
            (fun _ : ℝ => (0, 0)) 0 (0, 0) (1, 1) t) =
      -(∫ t in (0 : ℝ)..1, ∫ x in Icc (0, 0) (1, 1),
        gpeDensity nonzeroObstacleWave (t, x) *
          gpePartial (gpeSpaceDirection 0)
            (gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential)
            (t, x)) := by
  have hV : ContDiff ℝ 1
      (gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential) :=
    contDiff_gpeTranslatingPotential contDiff_const contDiff_nonzeroObstaclePotential
  have hη : ContDiff ℝ 2 (fun _ : ℝ => ((0, 0) : ℝ × ℝ)) := contDiff_const
  simpa using
    gpe_moving_rectangle_impulse_balance 1 0 1
      (V := gpeTranslatingPotential (fun _ : ℝ => (0, 0)) nonzeroObstaclePotential)
      (ψ := nonzeroObstacleWave) (η := fun _ : ℝ => (0, 0)) (U := Set.univ)
      hV contDiff_nonzeroObstacleWave hη isOpen_univ
      (fun p _ => nonzeroObstacleWave_gpe p)
      (t₀ := 0) (t₁ := 1) (by norm_num)
      (a := (0, 0)) (b := (1, 1)) (by constructor <;> norm_num)
      (fun _ _ => Set.mem_univ _) 0

end Qatlib.Papers.SuperfoilLift19.LiftForce
