/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.BesselGkError
public import Qatlib.Papers.HydroSpinLatt21.BesselModel.OrbitProjection

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A quadratic force remainder for Bessel coupling

[Saenz2021HydroSpinLattices], Methods equations (18)–(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
Preserving the cancellation in the normalized azimuthal projection gives
a force remainder quadratic in the orbit radius. At fixed spacing and
wavenumber this leaves a linear remainder after division by the angular
inertia.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel

/-- A radius-independent quadratic force coefficient at fixed spacing
and wavenumber with curvature Lipschitz constant `M`. -/
noncomputable def besselSmallOrbitCoeff (F k L M : ℝ) : ℝ :=
  |F| * (20 * |besselJ0Slope (k * L)| / L ^ 2
    + 28 * |besselJ0Curv (k * L)| * k / L + 27 * M * k ^ 2)

/-- The true instantaneous left Bessel force has a quadratic, phase-uniform
remainder after subtracting the generalized Kuramoto force and the
single-phase term. The profile Lipschitz premise is fixed across the full
allowed radius range. -/
theorem left_azimuth_force_quadratic_error (F k r L φ ψ M : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) (hk : 0 < k) (hM : 0 ≤ M)
    (hLip : ∀ z, |z - k * L| ≤ k * L →
      |besselJ0Curv z - besselJ0Curv (k * L)| ≤ M * |z - k * L|) :
    |leftAzimuthForce F besselJ0Slope k r L φ ψ -
      (besselGkPairForce F k r L φ ψ - F * besselJ0Slope (k * L) * Real.sin φ)|
      ≤ r ^ 2 * besselSmallOrbitCoeff F k L M := by
  let d := pairDist r L φ ψ
  let x := k * d
  let a := k * L
  let P := azimuthProjection r L φ ψ
  let S := Real.sin φ
  let U := Real.cos φ * (Real.sin φ - Real.sin ψ)
  let δ := Real.cos ψ - Real.cos φ
  let u := k * r * δ
  obtain ⟨hP, hP₁, hP₂⟩ := azimuth_projection_bounds r L φ ψ hL hr hrL
  have hδ : |δ| ≤ 2 := by
    exact abs_le.2 ⟨by dsimp [δ]; linarith [Real.neg_one_le_cos ψ, Real.cos_le_one φ],
      by dsimp [δ]; linarith [Real.cos_le_one ψ, Real.neg_one_le_cos φ]⟩
  have hstep : |x - a| ≤ 3 * k * r := by
    dsimp only [x, a]
    rw [← mul_sub, abs_mul, abs_of_pos hk]
    calc
      _ ≤ k * (3 * r) := mul_le_mul_of_nonneg_left (pairDist_sub_L_le r L φ ψ hL hr hrL) hk.le
      _ = _ := by ring
  have hlocal : ∀ z, |z - a| ≤ |x - a| →
      |besselJ0Curv z - besselJ0Curv a| ≤ M * |z - a| := by
    intro z hz
    have hkr : k * r ≤ k * L / 4 :=
      (mul_le_mul_of_nonneg_left hrL hk.le).trans_eq (by ring)
    exact hLip z ((hz.trans hstep).trans (by linarith only [hkr, mul_pos hk hL]))
  have hTaylor : |besselJ0Slope x - besselJ0Slope a - besselJ0Curv a * (x - a)|
      ≤ 9 * M * k ^ 2 * r ^ 2 := by
    have h := taylor_bound_of_lipschitz_deriv hM hasDerivAt_besselJ0Slope hlocal
    have hsquare : (x - a) ^ 2 ≤ (3 * k * r) ^ 2 :=
      sq_le_sq.mpr (by rwa [abs_of_nonneg (show 0 ≤ 3 * k * r by positivity)])
    exact h.trans ((mul_le_mul_of_nonneg_left hsquare hM).trans_eq (by ring))
  have hlong : |x - a - u| ≤ 4 * k * r ^ 2 / L := by
    have hEq : x - a - u = k * (d - (L + r * δ)) := by
      dsimp only [x, a, u]
      ring
    rw [hEq, abs_mul, abs_of_pos hk]
    calc
      _ ≤ k * (4 * r ^ 2 / L) :=
        mul_le_mul_of_nonneg_left (pairDist_sub_longitudinal_le r L φ ψ hL hr hrL) hk.le
      _ = _ := by ring
  let E := besselJ0Slope x - besselJ0Slope a - besselJ0Curv a * u
  have hE : |E| ≤ 9 * M * k ^ 2 * r ^ 2 + |besselJ0Curv a| * (4 * k * r ^ 2 / L) := by
    have hEq : E = (besselJ0Slope x - besselJ0Slope a - besselJ0Curv a * (x - a)) +
        besselJ0Curv a * (x - a - u) := by
      unfold E
      ring
    rw [hEq]
    refine (abs_add_le _ _).trans (add_le_add hTaylor ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hlong (abs_nonneg _)
  have hU : |u| ≤ 2 * k * r := by
    unfold u
    rw [abs_mul, abs_of_pos (mul_pos hk hr)]
    exact (mul_le_mul_of_nonneg_left hδ (mul_pos hk hr).le).trans_eq (by ring)
  have hIdentity : leftAzimuthForce F besselJ0Slope k r L φ ψ -
      (besselGkPairForce F k r L φ ψ - F * besselJ0Slope a * S) =
      -F * (E * P + besselJ0Slope a * (P - (S + (r / L) * U)) +
        (besselJ0Curv a * u) * (P - S)) := by
    unfold leftAzimuthForce besselGkPairForce gkPairForce
    dsimp only [E, P, azimuthProjection, S, U, u, δ, x, a, d]
    ring
  change |leftAzimuthForce F besselJ0Slope k r L φ ψ -
      (besselGkPairForce F k r L φ ψ - F * besselJ0Slope a * S)| ≤
    r ^ 2 * besselSmallOrbitCoeff F k L M
  rw [hIdentity, abs_mul, abs_neg]
  have hTotal : |E * P + besselJ0Slope a * (P - (S + (r / L) * U)) +
        (besselJ0Curv a * u) * (P - S)| ≤
      (9 * M * k ^ 2 * r ^ 2 + |besselJ0Curv a| * (4 * k * r ^ 2 / L)) * 3 +
      |besselJ0Slope a| * (20 * r ^ 2 / L ^ 2) +
      (|besselJ0Curv a| * (2 * k * r)) * (8 * r / L) := by
    calc
      _ ≤ |E * P + besselJ0Slope a * (P - (S + (r / L) * U))| +
          |(besselJ0Curv a * u) * (P - S)| := abs_add_le _ _
      _ ≤ |E * P| + |besselJ0Slope a * (P - (S + (r / L) * U))| +
          |(besselJ0Curv a * u) * (P - S)| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (9 * M * k ^ 2 * r ^ 2 + |besselJ0Curv a| * (4 * k * r ^ 2 / L)) * 3 +
          |besselJ0Slope a| * (20 * r ^ 2 / L ^ 2) +
          (|besselJ0Curv a| * (2 * k * r)) * (8 * r / L) := by
        simp only [abs_mul]
        exact add_le_add
          (add_le_add (mul_le_mul hE hP (abs_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left hP₂ (abs_nonneg _)))
          (mul_le_mul (mul_le_mul_of_nonneg_left hU (abs_nonneg _)) hP₁ (abs_nonneg _) (by positivity))
  refine (mul_le_mul_of_nonneg_left hTotal (abs_nonneg F)).trans_eq ?_
  unfold besselSmallOrbitCoeff a
  ring

/-- Expressing the squared chord by a cosine of the relative phase makes
the phase dependence of the squared separation proportional to the radius. -/
private theorem pair_dist_sq_trig (r L φ ψ : ℝ) :
    pairDist r L φ ψ ^ 2 =
      L ^ 2 + 2 * L * r * (Real.cos ψ - Real.cos φ) + 2 * r ^ 2 * (1 - Real.cos (φ - ψ)) := by
  rw [pairDist_sq_eq, Real.cos_sub]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq φ + r ^ 2 * Real.sin_sq_add_cos_sq ψ

/-- Varying only the emitter phase changes the distance by at most three
times the emitter radius times the phase change. -/
theorem pair_dist_emitter_abs_sub_le (r L φ ψ χ : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) :
    |pairDist r L φ ψ - pairDist r L φ χ| ≤ 3 * r * |ψ - χ| := by
  let x := pairDist r L φ ψ
  let y := pairDist r L φ χ
  let c := |ψ - χ|
  have hsum : L ≤ x + y := by
    linarith only [pairDist_ge_half r L φ ψ hL hr hrL, pairDist_ge_half r L φ χ hL hr hrL]
  have hsumpos : 0 < x + y := hL.trans_le hsum
  have hc : 0 ≤ c := abs_nonneg _
  have hcos : |Real.cos (φ - χ) - Real.cos (φ - ψ)| ≤ c := by
    refine (Real.abs_cos_sub_cos_le _ _).trans_eq ?_
    congr 1
    ring
  have hsq : |x ^ 2 - y ^ 2| ≤ (2 * L * r + 2 * r ^ 2) * c := by
    have heq : x ^ 2 - y ^ 2 =
        2 * L * r * (Real.cos ψ - Real.cos χ) +
          2 * r ^ 2 * (Real.cos (φ - χ) - Real.cos (φ - ψ)) := by
      dsimp only [x, y]
      rw [pair_dist_sq_trig, pair_dist_sq_trig]
      ring
    rw [heq, add_mul]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_pow, abs_of_pos hL, abs_of_pos hr, abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num)]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le ψ χ) (by positivity))
      (mul_le_mul_of_nonneg_left hcos (by positivity))
  have hp : |x - y| * (x + y) ≤ (2 * L * r + 2 * r ^ 2) * c := by
    rw [← abs_of_pos hsumpos, ← abs_mul, show (x - y) * (x + y) = x ^ 2 - y ^ 2 by ring]
    exact hsq
  have hcoeff : 2 * L * r + 2 * r ^ 2 ≤ 3 * L * r := by
    nlinarith only [mul_le_mul_of_nonneg_right hrL hr.le, mul_pos hL hr]
  refine le_of_mul_le_mul_right ?_ hL
  change |x - y| * L ≤ (3 * r * c) * L
  calc
    _ ≤ |x - y| * (x + y) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ (2 * L * r + 2 * r ^ 2) * c := hp
    _ ≤ (3 * L * r) * c := mul_le_mul_of_nonneg_right hcoeff hc
    _ = _ := by ring

/-- The phase sensitivity of the normalized azimuthal projection is
linear in the orbit radius for all receiver phases. -/
theorem azimuth_projection_emitter_abs_sub_le (r L φ ψ χ : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) :
    |azimuthProjection r L φ ψ - azimuthProjection r L φ χ| ≤ (20 * r / L) * |ψ - χ| := by
  let x := pairDist r L φ ψ
  let y := pairDist r L φ χ
  let P := azimuthProjection r L φ χ
  let V := Real.sin (φ - ψ) - Real.sin (φ - χ)
  let c := |ψ - χ|
  have hxge : L / 2 ≤ x := pairDist_ge_half r L φ ψ hL hr hrL
  have hx : 0 < x := (half_pos hL).trans_le hxge
  have hy : 0 < y := (half_pos hL).trans_le (pairDist_ge_half r L φ χ hL hr hrL)
  have hd : |y - x| ≤ 3 * r * c := by rw [abs_sub_comm]; exact pair_dist_emitter_abs_sub_le r L φ ψ χ hL hr hrL
  have hP : |P| ≤ 3 := (azimuth_projection_bounds r L φ χ hL hr hrL).1
  have hV : |V| ≤ c := by
    refine (Real.abs_sin_sub_sin_le _ _).trans_eq ?_
    rw [show φ - ψ - (φ - χ) = -(ψ - χ) by ring, abs_neg]
  have hEq : azimuthProjection r L φ ψ - P = (r * V + (y - x) * P) / x := by
    change (L * Real.sin φ + r * Real.sin (φ - ψ)) / x -
        (L * Real.sin φ + r * Real.sin (φ - χ)) / y =
      (r * V + (y - x) * ((L * Real.sin φ + r * Real.sin (φ - χ)) / y)) / x
    unfold V
    field_simp [hx.ne', hy.ne']
    ring
  rw [hEq, abs_div, abs_of_pos hx]
  have hnum : |r * V + (y - x) * P| ≤ (10 * r) * c := by
    calc
      _ ≤ |r * V| + |(y - x) * P| := abs_add_le _ _
      _ ≤ r * c + (3 * r * c) * 3 := by
        rw [abs_mul, abs_mul, abs_of_pos hr]
        exact add_le_add (mul_le_mul_of_nonneg_left hV hr.le)
          (mul_le_mul hd hP (abs_nonneg _) (by positivity))
      _ = _ := by ring
  calc
    _ ≤ ((10 * r) * c) / x := div_le_div_of_nonneg_right hnum hx.le
    _ ≤ ((10 * r) * c) / (L / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hL) hxge
    _ = _ := by ring

/-- With fixed lattice spacing and wavenumber, the emitter-phase
Lipschitz bound of the instantaneous Bessel force is linear in radius. -/
theorem left_bessel_force_emitter_small_orbit (F k L : ℝ) (hk : 0 < k) (hL : 0 < L) :
    ∃ C ≥ 0, ∀ r, 0 < r → r ≤ L / 4 → ∀ φ ψ χ,
      |leftAzimuthForce F besselJ0Slope k r L φ ψ -
        leftAzimuthForce F besselJ0Slope k r L φ χ| ≤ C * r * |ψ - χ| := by
  let I := Set.Icc (0 : ℝ) (2 * k * L)
  have hGc : IsCompact (besselJ0Slope '' I) :=
    isCompact_Icc.image differentiable_besselJ0Slope.continuous
  have hHc : IsCompact (besselJ0Curv '' I) :=
    isCompact_Icc.image differentiable_besselJ0Curv.continuous
  obtain ⟨G, hG, hGb⟩ := hGc.isBounded.exists_pos_norm_le
  obtain ⟨H, hH, hHb⟩ := hHc.isBounded.exists_pos_norm_le
  have hSlope (x y : ℝ) (hx : x ∈ I) (hy : y ∈ I) :
      |besselJ0Slope x - besselJ0Slope y| ≤ H * |x - y| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => differentiable_besselJ0Slope z)
      (fun z hz => by
        rw [(hasDerivAt_besselJ0Slope z).deriv]
        exact hHb _ ⟨z, hz, rfl⟩)
      (convex_Icc 0 (2 * k * L)) hy hx
    simpa only [Real.norm_eq_abs] using h
  refine ⟨|F| * (9 * k * H + 20 * G / L), by positivity, ?_⟩
  intro r hr hrL φ ψ χ
  let d (η : ℝ) := pairDist r L φ η
  let A (η : ℝ) := azimuthProjection r L φ η
  let g (η : ℝ) := besselJ0Slope (k * d η)
  let c := |ψ - χ|
  have hcoord (η : ℝ) : k * d η ∈ I := by
    have hupper := (abs_le.mp (pairDist_sub_L_le r L φ η hL hr hrL)).2
    have h₂ : d η ≤ 2 * L := by
      dsimp only [d]
      linarith only [hupper, hrL, hL.le]
    exact ⟨mul_nonneg hk.le (pairDist_nonneg r L φ η),
      (mul_le_mul_of_nonneg_left h₂ hk.le).trans_eq (by ring)⟩
  have hGb' : |g χ| ≤ G := by
    rw [← Real.norm_eq_abs]
    exact hGb _ ⟨k * d χ, hcoord χ, rfl⟩
  have hgdiff : |g ψ - g χ| ≤ (3 * k * H) * r * c := by
    have h := hSlope _ _ (hcoord ψ) (hcoord χ)
    rw [← mul_sub, abs_mul, abs_of_pos hk] at h
    refine h.trans ?_
    calc
      _ ≤ H * (k * (3 * r * c)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pair_dist_emitter_abs_sub_le r L φ ψ χ hL hr hrL) hk.le) hH.le
      _ = _ := by ring
  have hAψ : |A ψ| ≤ 3 := (azimuth_projection_bounds r L φ ψ hL hr hrL).1
  have hAdiff : |A ψ - A χ| ≤ (20 * r / L) * c :=
    azimuth_projection_emitter_abs_sub_le r L φ ψ χ hL hr hrL
  have heq : leftAzimuthForce F besselJ0Slope k r L φ ψ -
      leftAzimuthForce F besselJ0Slope k r L φ χ =
      -F * ((g ψ - g χ) * A ψ + g χ * (A ψ - A χ)) := by
    dsimp only [g, d, A, azimuthProjection, leftAzimuthForce]
    ring
  have hTotal : |(g ψ - g χ) * A ψ + g χ * (A ψ - A χ)| ≤
      ((3 * k * H) * r * c) * 3 + G * ((20 * r / L) * c) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hgdiff hAψ (abs_nonneg _) (by positivity))
      (mul_le_mul hGb' hAdiff (abs_nonneg _) hG.le)
  rw [heq, abs_mul, abs_neg]
  exact (mul_le_mul_of_nonneg_left hTotal (abs_nonneg F)).trans_eq (by ring)

end Qatlib.Papers.HydroSpinLatt21.BesselModel
