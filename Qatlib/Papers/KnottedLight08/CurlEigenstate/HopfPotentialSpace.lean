/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfPotentialTime
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRadialBounds
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRegularMode

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Spatial continuity of the positive-frequency Hopf potential

The angular polynomials are locally bounded. Uniform bounds for
the regular radial factors then give a polynomial times the
exponential damping as an integrable majorant.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter MeasureTheory Set
open scoped Topology

/-- The exact potential density has a majorant in terms of its three
Cartesian angular factors, with no inverse powers of the radius. -/
private theorem norm_hopfPotentialDensity_le {k : ℝ} (hk : 0 < k) (x y z t : ℝ) (j : Fin 3) :
    ‖hopfPotentialDensity x y z t j k‖ ≤
      ‖Complex.I / (2 * (Real.pi : ℂ))‖ * Real.exp (-k) *
        (k ^ 3 * (1 / 3) * ‖ckAngular x y z j‖ +
          k ^ 4 * (1 / 15) * ‖ckCurlAngular x y z j‖ +
          k ^ 2 * (1 / 3) * ‖ckConstantCurl j‖) := by
  let u := k * ckRadius x y z
  have hE : ‖Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ))‖ = Real.exp (-k) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.add_re]
  have hNorm (n : ℕ) (f : ℝ) (A : ℂ) :
      ‖((k ^ n * f : ℝ) : ℂ) * A‖ = k ^ n * |f| * ‖A‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg hk.le n)]
  have hMode : ‖hopfDipoleMode k x y z j‖ ≤
      k ^ 4 * (1 / 3) * ‖ckAngular x y z j‖ +
        k ^ 5 * (1 / 15) * ‖ckCurlAngular x y z j‖ +
        k ^ 3 * (1 / 3) * ‖ckConstantCurl j‖ := by
    rw [hopfDipoleMode_eq_regular]
    change ‖((k ^ 4 * ckRadialThree u : ℝ) : ℂ) * ckAngular x y z j +
      ((k ^ 5 * ckRadialFive u : ℝ) : ℂ) * ckCurlAngular x y z j +
      ((k ^ 3 * ckRadialThree u : ℝ) : ℂ) * ckConstantCurl j‖ ≤ _
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [hNorm]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_ckRadialThree_le u) (pow_nonneg hk.le 4)) (norm_nonneg _)
      · rw [hNorm]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_ckRadialFive_le u) (pow_nonneg hk.le 5)) (norm_nonneg _)
    · rw [hNorm]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_ckRadialThree_le u) (pow_nonneg hk.le 3)) (norm_nonneg _)
  rw [hopfPotentialDensity, norm_div, norm_mul, norm_mul, hE, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hk]
  apply (div_le_iff₀ hk).2
  calc
    _ ≤ ‖Complex.I / (2 * (Real.pi : ℂ))‖ * (Real.exp (-k) *
        (k ^ 4 * (1 / 3) * ‖ckAngular x y z j‖ +
          k ^ 5 * (1 / 15) * ‖ckCurlAngular x y z j‖ +
          k ^ 3 * (1 / 3) * ‖ckConstantCurl j‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMode (Real.exp_pos _).le)
        (norm_nonneg _)
    _ = _ := by ring

/-- Every nonnegative integer moment of the real damping is integrable
on the positive frequency half-line. -/
private theorem integrableOn_exp_moment (n : ℕ) :
    IntegrableOn (fun k : ℝ => Real.exp (-k) * k ^ n) (Ioi 0) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using Real.GammaIntegral_convergent hn

/-- The integrated Hopf potential is jointly continuous in space and
time, including at the spatial origin. -/
theorem continuous_hopfPositivePotential (j : Fin 3) :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2 j) := by
  let A := fun p : ℝ × ℝ × ℝ × ℝ => ‖ckAngular p.1 p.2.1 p.2.2.1 j‖
  let B := fun p : ℝ × ℝ × ℝ × ℝ => ‖ckCurlAngular p.1 p.2.1 p.2.2.1 j‖
  let C := ‖ckConstantCurl j‖
  let c := ‖Complex.I / (2 * (Real.pi : ℂ))‖
  have hA : Continuous A := by
    dsimp [A]
    fin_cases j <;> simp only [ckAngular] <;> fun_prop
  have hB : Continuous B := by
    dsimp [B]
    fin_cases j <;> simp only [ckCurlAngular] <;> fun_prop
  refine continuous_iff_continuousAt.2 fun p => ?_
  let majorant := fun k : ℝ => c * Real.exp (-k) *
    (k ^ 3 * (1 / 3) * (A p + 1) + k ^ 4 * (1 / 15) * (B p + 1) + k ^ 2 * (1 / 3) * C)
  have hInt : IntegrableOn majorant (Ioi 0) := by
    have hSum := ((((integrableOn_exp_moment 3).const_mul ((1 / 3) * (A p + 1))).add
      ((integrableOn_exp_moment 4).const_mul ((1 / 15) * (B p + 1)))).add
      ((integrableOn_exp_moment 2).const_mul ((1 / 3) * C))).const_mul c
    refine IntegrableOn.congr_fun hSum (fun k _ => ?_) measurableSet_Ioi
    simp only [majorant, Pi.add_apply]
    ring
  change Tendsto (fun q : ℝ × ℝ × ℝ × ℝ => ∫ k in Ioi (0 : ℝ),
    hopfPotentialDensity q.1 q.2.1 q.2.2.1 q.2.2.2 j k) (𝓝 p) (𝓝 _)
  refine tendsto_integral_filter_of_dominated_convergence majorant ?_ ?_ hInt ?_
  · exact Eventually.of_forall fun q =>
      (integrableOn_hopfPotentialDensity q.1 q.2.1 q.2.2.1 q.2.2.2 j).aestronglyMeasurable
  · have heA : ∀ᶠ q in 𝓝 p, A q < A p + 1 :=
      (tendsto_order.1 hA.continuousAt.tendsto).2 _ (by linarith)
    have heB : ∀ᶠ q in 𝓝 p, B q < B p + 1 :=
      (tendsto_order.1 hB.continuousAt.tendsto).2 _ (by linarith)
    filter_upwards [heA, heB] with q hqA hqB
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun k (hk : 0 < k) =>
      (norm_hopfPotentialDensity_le hk q.1 q.2.1 q.2.2.1 q.2.2.2 j).trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hqA.le (mul_nonneg (pow_nonneg hk.le 3) (by norm_num : 0 ≤ (1 / 3 : ℝ))))
      (mul_le_mul_of_nonneg_left hqB.le (mul_nonneg (pow_nonneg hk.le 4) (by norm_num : 0 ≤ (1 / 15 : ℝ)))))
      (le_refl _)
  · exact Eventually.of_forall fun k => by
      have hE : Continuous (fun q : ℝ × ℝ × ℝ × ℝ =>
          Complex.exp (-(1 + Complex.I * (q.2.2.2 : ℂ)) * (k : ℂ))) := by fun_prop
      have hM : Continuous (fun q : ℝ × ℝ × ℝ × ℝ =>
          hopfDipoleMode k q.1 q.2.1 q.2.2.1 j) :=
        (continuous_hopfDipoleMode k j).comp
          (show Continuous (fun q : ℝ × ℝ × ℝ × ℝ => (q.1, q.2.1, q.2.2.1)) by fun_prop)
      change ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ =>
        hopfPotentialDensity q.1 q.2.1 q.2.2.1 q.2.2.2 j k) p
      exact ((continuous_const.mul (hE.mul hM)).div_const _).continuousAt

end Qatlib.Papers.KnottedLight08.CurlEigenstate
