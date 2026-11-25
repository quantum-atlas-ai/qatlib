/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.Rotation.ConstantSpeedStability

import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Fréchet linearization of the constant-speed rotating droplet

[Saenz2021HydroSpinLattices], Methods equations (31) and (32).
On the nonzero-radius domain the zero-wave-force field is differentiable.
Its full Fréchet derivative at zero radial velocity has the columns used
in the characteristic-polynomial stability calculation.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.Rotation

local notation "State" => ℝ × ℝ × ℝ

/-- The phase-space vector field is differentiable where the radial
denominator in equation (32) is nonzero. -/
theorem differentiableAt_constantSpeedSpinField (k τ u₀ Ω : ℝ) (p : State)
    (hr : p.1 ≠ 0) :
    DifferentiableAt ℝ (constantSpeedSpinField k τ u₀ Ω) p := by
  unfold constantSpeedSpinField coriolisRadialRHS zeroWavePhaseRHS instantaneousRayleighRHS
  fun_prop (disch := assumption)

/-- The three columns of the analyzed matrix are the actual Cartesian
columns of the vector field's Fréchet derivative at zero radial velocity. -/
theorem fderiv_constantSpeedSpinField_columns (k τ u₀ Ω r ω : ℝ) (hr : r ≠ 0)
    (j : Fin 3) :
    let M := constantSpeedJacobian k τ u₀ Ω r ω
    fderiv ℝ (constantSpeedSpinField k τ u₀ Ω) (r, 0, ω)
      (![((1, 0, 0) : State), (0, 1, 0), (0, 0, 1)] j) =
      (M 0 j, M 1 j, M 2 j) := by
  let F := constantSpeedSpinField k τ u₀ Ω
  let L := fderiv ℝ F (r, 0, ω)
  have hd : HasFDerivAt F L (r, 0, ω) :=
    (differentiableAt_constantSpeedSpinField k τ u₀ Ω (r, 0, ω) hr).hasFDerivAt
  have hx : HasDerivAt (fun x : ℝ => (x, (0 : ℝ), ω)) ((1, 0, 0) : State) r :=
    HasDerivAt.prodMk (hasDerivAt_id r)
      (HasDerivAt.prodMk (hasDerivAt_const r (0 : ℝ)) (hasDerivAt_const r ω))
  have hy : HasDerivAt (fun x : ℝ => (r, x, ω)) ((0, 1, 0) : State) 0 :=
    HasDerivAt.prodMk (hasDerivAt_const 0 r)
      (HasDerivAt.prodMk (hasDerivAt_id (0 : ℝ)) (hasDerivAt_const 0 ω))
  have hz : HasDerivAt (fun x : ℝ => (r, (0 : ℝ), x)) ((0, 0, 1) : State) ω :=
    HasDerivAt.prodMk (hasDerivAt_const ω r)
      (HasDerivAt.prodMk (hasDerivAt_const ω (0 : ℝ)) (hasDerivAt_id ω))
  fin_cases j
  · have hd₁ := hd.comp_hasDerivAt r hx
    have hd₂ := HasDerivAt.prodMk (hasDerivAt_const r (0 : ℝ))
      (HasDerivAt.prodMk (coriolisRadialRHS_hasDerivAt_r r ω Ω k)
        (zeroWavePhaseRHS_hasDerivAt_r τ u₀ Ω r ω))
    have h : L (1, 0, 0) =
        (0, ω * ω + 2 * Ω * ω - 12 * k * r ^ 2, -(2 * r * ω ^ 3 / (τ * u₀ ^ 2))) :=
      hd₁.unique hd₂
    simpa [constantSpeedJacobian, L, F] using h
  · have hd₁ := hd.comp_hasDerivAt 0 hy
    have hd₂ := HasDerivAt.prodMk (hasDerivAt_id (0 : ℝ))
      (HasDerivAt.prodMk (hasDerivAt_const 0 (coriolisRadialRHS r ω Ω k))
        (zeroWavePhaseRHS_hasDerivAt_v τ u₀ Ω r 0 ω))
    have h : L (0, 1, 0) = (1, 0, -2 * (Ω + ω) / r) := hd₁.unique hd₂
    simpa [constantSpeedJacobian, L, F] using h
  · have hd₁ := hd.comp_hasDerivAt ω hz
    have hd₂ := HasDerivAt.prodMk (hasDerivAt_const ω (0 : ℝ))
      (HasDerivAt.prodMk (coriolisRadialRHS_hasDerivAt_ω r ω Ω k)
        (zeroWavePhaseRHS_hasDerivAt_ω τ u₀ Ω r ω))
    have h : L (0, 0, 1) =
        (0, 2 * r * (ω + Ω), (1 / τ) * (1 - 3 * r ^ 2 * ω ^ 2 / u₀ ^ 2)) :=
      hd₁.unique hd₂
    simpa [constantSpeedJacobian, L, F] using h

/-- The analyzed matrix is the Cartesian matrix of the full derivative
of the instantaneous-radius vector field. -/
theorem fderiv_constantSpeedSpinField_matrix (k τ u₀ Ω r ω : ℝ) (hr : r ≠ 0) :
    (Matrix.of fun i j : Fin 3 =>
      let u := fderiv ℝ (constantSpeedSpinField k τ u₀ Ω) (r, 0, ω)
        (![((1, 0, 0) : State), (0, 1, 0), (0, 0, 1)] j)
      ![u.1, u.2.1, u.2.2] i) =
      constantSpeedJacobian k τ u₀ Ω r ω := by
  ext i j
  simp only [Matrix.of_apply]
  rw [fderiv_constantSpeedSpinField_columns k τ u₀ Ω r ω hr j]
  fin_cases i <;> rfl

end Qatlib.Papers.HydroSpinLatt21.Rotation
