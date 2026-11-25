/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.Nucleation.Compressibility
public import Mathlib.Analysis.RCLike.Sqrt

import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Exact trailing-edge algebra for a Joukowski airfoil

[Musser2019Superfoil], Supplemental Material, equations (1), (4), (6), and (7),
[arXiv:1904.04908v3](https://arxiv.org/abs/1904.04908v3).
The off-center circle has center `-λ` and radius `a+λ`; its point `z=a`
maps to the trailing edge `Z=2a` under `Z(z)=z+a²/z`.  We retain the
complex velocity numerator exactly.  The circulation
`Γ_KJ=-4π(a+λ)U∞sin α` cancels that numerator at the cusp.  The frequently
quoted chord formula `Γ_KJ≈-πU∞L sin α` is a separate thin-foil approximation
and is not used here.

The main circle-plane limit rescales the squared speed by `|z-a|²`.  Its
nonzero value for `Γ≠Γ_KJ` proves the inverse-first-power velocity singularity
in that coordinate.  The explicit outer inverse branch
`z=a+w/2+sqrt(aw+w²/4)`, with `w=Z-2a`, then gives the physical-plane
`r|u_ideal|²` limit and a scaled `O(√r)` error.  These are analytic ideal-flow
statements; the separate
Gross--Pitaevskii nucleation approximation is not asserted here.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.Nucleation

open Filter Topology Asymptotics

/-- The Joukowski map with cusp parameter `a`, evaluated in the complex plane. -/
def joukowskiMap (a : ℝ) (z : ℂ) : ℂ := z + (a : ℂ) ^ 2 / z

/-- The complex derivative of `joukowskiMap a`. -/
def joukowskiMapDeriv (a : ℝ) (z : ℂ) : ℂ := 1 - (a : ℂ) ^ 2 / z ^ 2

/-- The numerator of the cylinder velocity in Supplemental Material equation
(4), with `w=z+λ` and cylinder radius `R=a+λ`. -/
def cylinderFlowNumerator (radius speed alpha circulation : ℝ) (w : ℂ) : ℂ :=
  (speed : ℂ) *
      (Complex.exp (-(alpha : ℂ) * Complex.I) -
        ((radius : ℂ) / w) ^ 2 * Complex.exp ((alpha : ℂ) * Complex.I)) -
    Complex.I * (circulation : ℂ) / (2 * (Real.pi : ℂ) * w)

/-- The circulation that cancels the exact trailing-edge numerator for a
cylinder of radius `radius`. -/
def kuttaCirculation (radius speed alpha : ℝ) : ℝ :=
  -4 * Real.pi * radius * speed * Real.sin alpha

/-- The complex conjugate velocity `U-iV` in the airfoil plane.  The outer
rotation has unit norm and hence does not affect any speed estimate. -/
def idealComplexVelocity (a offset speed alpha circulation : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((alpha : ℂ) * Complex.I) *
    cylinderFlowNumerator (a + offset) speed alpha circulation (z + (offset : ℂ)) /
      joukowskiMapDeriv a z

/-- The leading squared-speed coefficient after multiplying by `|z-a|²`. -/
def tailLeadingSpeedSqCoefficient (a radius speed alpha circulation : ℝ) : ℝ :=
  a ^ 2 * (kuttaCirculation radius speed alpha - circulation) ^ 2 /
    (16 * Real.pi ^ 2 * radius ^ 2)

/-- The removable factor obtained by multiplying the ideal velocity by `z-a`. -/
def tailRegularizedVelocity (a offset speed alpha circulation : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((alpha : ℂ) * Complex.I) *
    (cylinderFlowNumerator (a + offset) speed alpha circulation (z + (offset : ℂ)) *
      z ^ 2 / (z + (a : ℂ)))

/-- The physical-plane coefficient in the limit of `r|u_ideal|²`. -/
def physicalTailSpeedSqCoefficient (a radius speed alpha circulation : ℝ) : ℝ :=
  tailLeadingSpeedSqCoefficient a radius speed alpha circulation / a

/-- The principal-square-root inverse branch approaching `z=a` in the open
right half-plane when the affine part has positive real part. -/
def outerTailInverse (a : ℝ) (w : ℂ) : ℂ :=
  (a : ℂ) + w / 2 + Complex.sqrt ((a : ℂ) * w + w ^ 2 / 4)

/-- The trailing point `z=a` maps to `Z=2a`. -/
theorem joukowskiMap_tail {a : ℝ} (ha : (a : ℂ) ≠ 0) :
    joukowskiMap a (a : ℂ) = 2 * (a : ℂ) := by
  unfold joukowskiMap
  field_simp [ha]
  ring

/-- The Joukowski derivative vanishes at the trailing cusp. -/
theorem joukowskiMapDeriv_tail (a : ℝ) (ha : (a : ℂ) ≠ 0) :
    joukowskiMapDeriv a (a : ℂ) = 0 := by
  unfold joukowskiMapDeriv
  field_simp [ha]
  ring

/-- Away from the origin the Joukowski derivative factors into its two cusp
factors. -/
theorem joukowskiMapDeriv_eq_factor {a : ℝ} {z : ℂ} (hz : z ≠ 0) :
    joukowskiMapDeriv a z = (z - (a : ℂ)) * (z + (a : ℂ)) / z ^ 2 := by
  unfold joukowskiMapDeriv
  field_simp [hz]
  ring

/-- The exact quadratic trailing-edge identity for the Joukowski map. -/
theorem joukowskiMap_sub_tail {a : ℝ} {z : ℂ} (hz : z ≠ 0) :
    joukowskiMap a z - 2 * (a : ℂ) = (z - (a : ℂ)) ^ 2 / z := by
  unfold joukowskiMap
  field_simp [hz]
  ring

/-- The real part of the principal complex square root is nonnegative. -/
theorem complex_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  positivity

/-- Positivity of the affine part makes the outer inverse point lie in the
open right half-plane. -/
theorem outerTailInverse_re_pos {a : ℝ} {w : ℂ} (_ha : 0 < a)
    (hq : 0 < ((a : ℂ) + w / 2).re) :
    0 < (outerTailInverse a w).re := by
  rw [outerTailInverse, Complex.add_re]
  exact add_pos_of_pos_of_nonneg hq (complex_sqrt_re_nonneg _)

/-- The outer inverse point is nonzero whenever its affine part has positive
real part. -/
theorem outerTailInverse_ne_zero {a : ℝ} {w : ℂ} (ha : 0 < a)
    (hq : 0 < ((a : ℂ) + w / 2).re) :
    outerTailInverse a w ≠ 0 := by
  intro h
  have hr := outerTailInverse_re_pos ha hq
  rw [h] at hr
  exact lt_irrefl 0 hr

/-- The sum of the outer inverse point and `a` is nonzero in the same local
region. -/
theorem outerTailInverse_add_ne_zero {a : ℝ} {w : ℂ} (ha : 0 < a)
    (hq : 0 < ((a : ℂ) + w / 2).re) :
    outerTailInverse a w + (a : ℂ) ≠ 0 := by
  intro h
  have hz := outerTailInverse_re_pos ha hq
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
  linarith

/-- The complete principal-square-root branch exactly inverts the Joukowski
map near the trailing edge, not merely to first order. -/
theorem joukowskiMap_outerTailInverse {a : ℝ} {w : ℂ} (ha : 0 < a)
    (hq : 0 < ((a : ℂ) + w / 2).re) :
    joukowskiMap a (outerTailInverse a w) = 2 * (a : ℂ) + w := by
  have hz := outerTailInverse_ne_zero ha hq
  have hs : Complex.sqrt ((a : ℂ) * w + w ^ 2 / 4) ^ 2 = (a : ℂ) * w + w ^ 2 / 4 :=
    Complex.cpow_nat_inv_pow _ (by norm_num)
  unfold joukowskiMap
  field_simp [hz]
  unfold outerTailInverse
  ring_nf at hs ⊢
  rw [hs]
  ring

/-- The explicit outer inverse branch converges to `z=a` as the physical
displacement converges to zero. -/
theorem tendsto_outerTailInverse (a : ℝ) :
    Tendsto (outerTailInverse a) (nhdsWithin 0 ({0}ᶜ)) (𝓝 (a : ℂ)) := by
  have hinner : ContinuousAt (fun w : ℂ => (a : ℂ) * w + w ^ 2 / 4) 0 := by
    fun_prop
  have hinner0 : Tendsto (fun w : ℂ => (a : ℂ) * w + w ^ 2 / 4) (𝓝 0) (𝓝 0) := by
    simpa using hinner.tendsto
  have hsqrt0 : Tendsto Complex.sqrt (𝓝 0) (𝓝 0) := by
    simpa using (Complex.continuousAt_sqrt (z := 0) (by simp)).tendsto
  have hsqrt : Tendsto (fun w : ℂ => Complex.sqrt ((a : ℂ) * w + w ^ 2 / 4))
      (𝓝 0) (𝓝 0) := by
    change Tendsto (Complex.sqrt ∘ fun w : ℂ => (a : ℂ) * w + w ^ 2 / 4) (𝓝 0) (𝓝 0)
    exact hsqrt0.comp hinner0
  have haff0 : ContinuousAt (fun w : ℂ => (a : ℂ) + w / 2) 0 := by
    fun_prop
  have haff : Tendsto (fun w : ℂ => (a : ℂ) + w / 2) (𝓝 0) (𝓝 (a : ℂ)) := by
    simpa only [zero_div, add_zero] using haff0.tendsto
  have h := (haff.add hsqrt).mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  simp only [add_zero] at h
  change Tendsto (fun w : ℂ => (a : ℂ) + w / 2 + Complex.sqrt ((a : ℂ) * w + w ^ 2 / 4))
    (nhdsWithin 0 ({0}ᶜ)) (𝓝 (a : ℂ))
  exact h

/-- The affine part of the outer inverse has positive real part sufficiently
close to the trailing edge. -/
theorem eventually_outerTailInverse_affine_re_pos {a : ℝ} (ha : 0 < a) :
    ∀ᶠ w in nhdsWithin 0 ({0}ᶜ), 0 < ((a : ℂ) + w / 2).re := by
  have hq : Tendsto (fun w : ℂ => ((a : ℂ) + w / 2).re)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 a) := by
    have h : ContinuousAt (fun w : ℂ => ((a : ℂ) + w / 2).re) 0 := by
      fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  exact hq.eventually (Ioi_mem_nhds ha)

/-- The outer inverse avoids the trailing point on every sufficiently small
punctured physical neighborhood. -/
theorem outerTailInverse_ne_tail {a : ℝ} {w : ℂ} (ha : 0 < a)
    (hq : 0 < ((a : ℂ) + w / 2).re) (hw : w ≠ 0) :
    outerTailInverse a w ≠ (a : ℂ) := by
  intro h
  have hm := joukowskiMap_outerTailInverse ha hq
  rw [h, joukowskiMap_tail (by exact_mod_cast ha.ne')] at hm
  have hw0 : w = 0 := by
    apply add_left_cancel (a := 2 * (a : ℂ))
    simpa using hm.symm
  exact hw hw0

/-- The outer inverse maps the punctured physical neighborhood into the
punctured circle-plane neighborhood of `a`. -/
theorem tendsto_outerTailInverse_punctured {a : ℝ} (ha : 0 < a) :
    Tendsto (outerTailInverse a) (nhdsWithin 0 ({0}ᶜ))
      (nhdsWithin (a : ℂ) ({(a : ℂ)}ᶜ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_outerTailInverse a, ?_⟩
  filter_upwards [self_mem_nhdsWithin, eventually_outerTailInverse_affine_re_pos ha] with w hw hq
  exact outerTailInverse_ne_tail ha hq (by simpa using hw)

/-- The exact map gives `|z-a|²=|Z-2a| |z|` on the explicit outer branch. -/
theorem outerTailInverse_dist_sq {a : ℝ} {w : ℂ} (ha : 0 < a)
    (hq : 0 < ((a : ℂ) + w / 2).re) :
    ‖outerTailInverse a w - (a : ℂ)‖ ^ 2 = ‖w‖ * ‖outerTailInverse a w‖ := by
  have hz := outerTailInverse_ne_zero ha hq
  have h := joukowskiMap_sub_tail (a := a) hz
  rw [joukowskiMap_outerTailInverse ha hq] at h
  have hw : w = (outerTailInverse a w - (a : ℂ)) ^ 2 / outerTailInverse a w := by
    simpa using h
  have hn := congrArg norm hw
  rw [norm_div, norm_pow] at hn
  calc
    ‖outerTailInverse a w - (a : ℂ)‖ ^ 2 =
        (‖outerTailInverse a w - (a : ℂ)‖ ^ 2 / ‖outerTailInverse a w‖) *
          ‖outerTailInverse a w‖ := by
            field_simp [norm_ne_zero_iff.mpr hz]
    _ = ‖w‖ * ‖outerTailInverse a w‖ := by rw [← hn]

/-- The difference of opposite unit-modulus phases is `-2i sin α`. -/
theorem exp_neg_mul_I_sub_exp_mul_I (alpha : ℝ) :
    Complex.exp (-(alpha : ℂ) * Complex.I) - Complex.exp ((alpha : ℂ) * Complex.I) =
      -2 * Complex.I * (Real.sin alpha : ℂ) := by
  rw [show -(alpha : ℂ) * Complex.I = (-(alpha : ℂ)) * Complex.I by ring]
  simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  rw [Complex.ofReal_sin]
  ring

/-- At `w=radius`, the velocity numerator is the imaginary circulation defect
`(Γ_KJ-Γ)/(2π radius)` times `i`. -/
theorem cylinderFlowNumerator_tail {radius speed alpha circulation : ℝ}
    (hradius : (radius : ℂ) ≠ 0) :
    cylinderFlowNumerator radius speed alpha circulation (radius : ℂ) =
      Complex.I * ((kuttaCirculation radius speed alpha - circulation : ℝ) : ℂ) /
        (2 * (Real.pi : ℂ) * (radius : ℂ)) := by
  unfold cylinderFlowNumerator kuttaCirculation
  rw [div_self hradius, one_pow, one_mul, exp_neg_mul_I_sub_exp_mul_I]
  push_cast
  field_simp [hradius, Real.pi_ne_zero]
  ring

/-- The exact Kutta circulation cancels the trailing-edge numerator. -/
theorem cylinderFlowNumerator_tail_kutta {radius speed alpha : ℝ}
    (hradius : (radius : ℂ) ≠ 0) :
    cylinderFlowNumerator radius speed alpha
      (kuttaCirculation radius speed alpha) (radius : ℂ) = 0 := by
  rw [cylinderFlowNumerator_tail hradius]
  simp

/-- A nonzero radius makes vanishing of the trailing numerator equivalent to
the exact Kutta circulation condition. -/
theorem cylinderFlowNumerator_tail_eq_zero_iff {radius speed alpha circulation : ℝ}
    (hradius : (radius : ℂ) ≠ 0) :
    cylinderFlowNumerator radius speed alpha circulation (radius : ℂ) = 0 ↔
      circulation = kuttaCirculation radius speed alpha := by
  rw [cylinderFlowNumerator_tail hradius]
  constructor
  · intro h
    have hdefect : ((kuttaCirculation radius speed alpha - circulation : ℝ) : ℂ) = 0 := by
      have hd : (2 * (Real.pi : ℂ) * (radius : ℂ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) hradius
      have hnum : Complex.I *
          ((kuttaCirculation radius speed alpha - circulation : ℝ) : ℂ) = 0 :=
        (div_eq_zero_iff.mp h).resolve_right hd
      exact (mul_eq_zero.mp hnum).resolve_left Complex.I_ne_zero
    have hreal : kuttaCirculation radius speed alpha - circulation = 0 := by
      exact_mod_cast hdefect
    linarith
  · rintro rfl
    simp

/-- A circulation different from the Kutta value gives a nonzero trailing
numerator, hence a nonvanishing singular coefficient. -/
theorem cylinderFlowNumerator_tail_ne_zero {radius speed alpha circulation : ℝ}
    (hradius : (radius : ℂ) ≠ 0)
    (hcirculation : circulation ≠ kuttaCirculation radius speed alpha) :
    cylinderFlowNumerator radius speed alpha circulation (radius : ℂ) ≠ 0 :=
  mt (cylinderFlowNumerator_tail_eq_zero_iff hradius).mp hcirculation

/-- Multiplication by `z-a` removes the trailing-cusp denominator exactly. -/
theorem tailDisplacement_mul_idealComplexVelocity {a offset speed alpha circulation : ℝ}
    {z : ℂ} (hz : z ≠ 0) (hza : z ≠ (a : ℂ)) (hzplus : z + (a : ℂ) ≠ 0) :
    (z - (a : ℂ)) * idealComplexVelocity a offset speed alpha circulation z =
      Complex.exp ((alpha : ℂ) * Complex.I) *
        (cylinderFlowNumerator (a + offset) speed alpha circulation (z + (offset : ℂ)) *
          z ^ 2 / (z + (a : ℂ))) := by
  unfold idealComplexVelocity
  rw [joukowskiMapDeriv_eq_factor hz]
  field_simp [hz, hza, hzplus]

/-- The rescaled complex velocity has an explicit limit through the punctured
trailing-edge neighborhood. -/
theorem tendsto_tailDisplacement_mul_idealComplexVelocity {a offset speed alpha circulation : ℝ}
    (ha : (a : ℂ) ≠ 0) (hradius : ((a + offset : ℝ) : ℂ) ≠ 0) :
    Tendsto (fun z : ℂ => (z - (a : ℂ)) * idealComplexVelocity a offset speed alpha circulation z)
      (nhdsWithin (a : ℂ) ({(a : ℂ)}ᶜ))
      (𝓝 (Complex.exp ((alpha : ℂ) * Complex.I) *
        (cylinderFlowNumerator (a + offset) speed alpha circulation
            ((a : ℂ) + (offset : ℂ)) * (a : ℂ) ^ 2 / ((a : ℂ) + (a : ℂ))))) := by
  have hsum : (a : ℂ) + (a : ℂ) ≠ 0 := by
    rw [show (a : ℂ) + (a : ℂ) = 2 * (a : ℂ) by ring]
    exact mul_ne_zero (by norm_num) ha
  have hcont : ContinuousAt (fun z : ℂ =>
      Complex.exp ((alpha : ℂ) * Complex.I) *
        (cylinderFlowNumerator (a + offset) speed alpha circulation (z + (offset : ℂ)) *
          z ^ 2 / (z + (a : ℂ)))) (a : ℂ) := by
    unfold cylinderFlowNumerator
    fun_prop (disch := aesop)
  have ht : Tendsto (fun z : ℂ =>
      Complex.exp ((alpha : ℂ) * Complex.I) *
        (cylinderFlowNumerator (a + offset) speed alpha circulation (z + (offset : ℂ)) *
          z ^ 2 / (z + (a : ℂ)))) (nhdsWithin (a : ℂ) ({(a : ℂ)}ᶜ))
      (𝓝 (Complex.exp ((alpha : ℂ) * Complex.I) *
        (cylinderFlowNumerator (a + offset) speed alpha circulation
          ((a : ℂ) + (offset : ℂ)) * (a : ℂ) ^ 2 / ((a : ℂ) + (a : ℂ))))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin ha,
    eventually_ne_nhdsWithin (a := (a : ℂ)) (b := -(a : ℂ))
      (fun h => ha (CharZero.eq_neg_self_iff.mp h))] with z hza hz hzneg
  have hzplus : z + (a : ℂ) ≠ 0 :=
    fun h => hzneg (add_eq_zero_iff_eq_neg.mp h)
  exact (tailDisplacement_mul_idealComplexVelocity hz (by simpa using hza) hzplus).symm

/-- Squaring the rescaled-velocity limit gives the exact real leading
coefficient `a²(Γ_KJ-Γ)²/(16π²R²)`. -/
theorem tendsto_tailDisplacement_norm_sq_mul_idealComplexVelocity_norm_sq
    {a offset speed alpha circulation : ℝ}
    (ha : (a : ℂ) ≠ 0) (hradius : ((a + offset : ℝ) : ℂ) ≠ 0) :
    Tendsto (fun z : ℂ => ‖z - (a : ℂ)‖ ^ 2 * ‖idealComplexVelocity a offset speed alpha circulation z‖ ^ 2)
      (nhdsWithin (a : ℂ) ({(a : ℂ)}ᶜ))
      (𝓝 (tailLeadingSpeedSqCoefficient a (a + offset) speed alpha circulation)) := by
  have ht0 := tendsto_tailDisplacement_mul_idealComplexVelocity
    (a := a) (offset := offset) (speed := speed) (alpha := alpha) (circulation := circulation)
    ha hradius
  have hfrac : (a : ℂ) ^ 2 / ((a : ℂ) + (a : ℂ)) = (a : ℂ) / 2 := by
    field_simp [ha]
    ring
  rw [mul_div_assoc, hfrac] at ht0
  have ht := ht0.norm.pow 2
  simp only [norm_mul, mul_pow] at ht
  convert ht using 1
  congr 1
  rw [show (a : ℂ) + (offset : ℂ) = ((a + offset : ℝ) : ℂ) by push_cast; ring,
    cylinderFlowNumerator_tail hradius]
  simp [tailLeadingSpeedSqCoefficient, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  field_simp [ha, hradius, Real.pi_ne_zero]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  ring

/-- The squared norm of the removable velocity factor at the cusp is the
real leading coefficient. -/
theorem tailRegularizedVelocity_tail_norm_sq {a offset speed alpha circulation : ℝ}
    (ha : (a : ℂ) ≠ 0) (hradius : ((a + offset : ℝ) : ℂ) ≠ 0) :
    ‖tailRegularizedVelocity a offset speed alpha circulation (a : ℂ)‖ ^ 2 =
      tailLeadingSpeedSqCoefficient a (a + offset) speed alpha circulation := by
  unfold tailRegularizedVelocity
  have hfrac : (a : ℂ) ^ 2 / ((a : ℂ) + (a : ℂ)) = (a : ℂ) / 2 := by
    field_simp [ha]
    ring
  rw [mul_div_assoc, hfrac]
  rw [show (a : ℂ) + (offset : ℂ) = ((a + offset : ℝ) : ℂ) by push_cast; ring,
    cylinderFlowNumerator_tail hradius]
  simp [tailLeadingSpeedSqCoefficient, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  field_simp [ha, hradius, Real.pi_ne_zero]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  ring

/-- The removable velocity factor is complex differentiable at the cusp. -/
theorem differentiableAt_tailRegularizedVelocity {a offset speed alpha circulation : ℝ}
    (ha : (a : ℂ) ≠ 0) (hradius : ((a + offset : ℝ) : ℂ) ≠ 0) :
    DifferentiableAt ℂ (tailRegularizedVelocity a offset speed alpha circulation) (a : ℂ) := by
  unfold tailRegularizedVelocity cylinderFlowNumerator
  fun_prop (disch := aesop)

/-- Dividing the removable squared speed by `|z|` gives a real-differentiable
physical scaling, hence a first-order local error in the circle plane. -/
theorem isBigO_tailRegularizedVelocity_norm_sq_div_norm_sub
    {a offset speed alpha circulation : ℝ}
    (ha : 0 < a) (hradius : ((a + offset : ℝ) : ℂ) ≠ 0) :
    (fun z : ℂ => ‖tailRegularizedVelocity a offset speed alpha circulation z‖ ^ 2 / ‖z‖ -
      physicalTailSpeedSqCoefficient a (a + offset) speed alpha circulation) =O[
        nhdsWithin (a : ℂ) ({(a : ℂ)}ᶜ)] fun z => ‖z - (a : ℂ)‖ := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdC := differentiableAt_tailRegularizedVelocity
    (a := a) (offset := offset) (speed := speed) (alpha := alpha) (circulation := circulation)
    haC hradius
  have hs : DifferentiableAt ℝ
      (fun z : ℂ => ‖tailRegularizedVelocity a offset speed alpha circulation z‖ ^ 2) (a : ℂ) := by
    have hfR : DifferentiableAt ℝ (tailRegularizedVelocity a offset speed alpha circulation) (a : ℂ) :=
      hdC.restrictScalars ℝ
    simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    fun_prop
  have hn : DifferentiableAt ℝ (fun z : ℂ => ‖z‖) (a : ℂ) := by
    simp_rw [Complex.norm_eq_sqrt_sq_add_sq]
    apply DifferentiableAt.sqrt
    · fun_prop
    · simpa only [pow_two, ← Complex.normSq_apply] using
        (ne_of_gt (Complex.normSq_pos.mpr haC))
  have hF := hs.isBigO_sub.norm_right.mono
    (nhdsWithin_le_nhds (s := ({(a : ℂ)}ᶜ : Set ℂ)))
  have hInvD := hn.inv (norm_ne_zero_iff.mpr haC)
  have hInv := hInvD.isBigO_sub.norm_right.mono
    (nhdsWithin_le_nhds (s := ({(a : ℂ)}ᶜ : Set ℂ)))
  have hInvBound : (fun z : ℂ => ‖z‖⁻¹) =O[nhdsWithin (a : ℂ) ({(a : ℂ)}ᶜ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    hInvD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.isBigO_one ℝ
  have hTerm1 := hF.mul hInvBound
  simp only [mul_one] at hTerm1
  have hTerm2 := hInv.const_mul_left
    (tailLeadingSpeedSqCoefficient a (a + offset) speed alpha circulation)
  apply (hTerm1.add hTerm2).congr' ?_ EventuallyEq.rfl
  filter_upwards [] with z
  simp only [Pi.inv_apply, physicalTailSpeedSqCoefficient,
    tailRegularizedVelocity_tail_norm_sq haC hradius, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ha]
  ring

/-- On the explicit inverse branch, the exact physical rescaling is the
removable squared speed divided by `|z|`. -/
theorem outerTailInverse_scaled_speed_sq_eq {a offset speed alpha circulation : ℝ} {w : ℂ}
    (ha : 0 < a) (hq : 0 < ((a : ℂ) + w / 2).re) (hw : w ≠ 0) :
    ‖w‖ * ‖idealComplexVelocity a offset speed alpha circulation (outerTailInverse a w)‖ ^ 2 =
      ‖tailRegularizedVelocity a offset speed alpha circulation (outerTailInverse a w)‖ ^ 2 /
        ‖outerTailInverse a w‖ := by
  have hz := outerTailInverse_ne_zero ha hq
  have hza := outerTailInverse_ne_tail ha hq hw
  have hzplus := outerTailInverse_add_ne_zero ha hq
  have hreg := tailDisplacement_mul_idealComplexVelocity
    (a := a) (offset := offset) (speed := speed) (alpha := alpha) (circulation := circulation)
    hz hza hzplus
  change (outerTailInverse a w - (a : ℂ)) *
    idealComplexVelocity a offset speed alpha circulation (outerTailInverse a w) =
      tailRegularizedVelocity a offset speed alpha circulation (outerTailInverse a w) at hreg
  have hn := outerTailInverse_dist_sq ha hq
  rw [← hreg]
  simp only [norm_mul, mul_pow]
  rw [hn]
  field_simp [norm_ne_zero_iff.mpr hz]

/-- The circle-plane displacement on the exact inverse branch is quantitatively
`O(√r)`, with no square-root approximation inserted as a premise. -/
theorem isBigO_outerTailInverse_dist {a : ℝ} (ha : 0 < a) :
    (fun w : ℂ => ‖outerTailInverse a w - (a : ℂ)‖) =O[nhdsWithin 0 ({0}ᶜ)]
      fun w => Real.sqrt ‖w‖ := by
  have hz1 : (fun w : ℂ => ‖outerTailInverse a w‖) =O[nhdsWithin 0 ({0}ᶜ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    (tendsto_outerTailInverse a).norm.isBigO_one ℝ
  have hprod := (isBigO_refl (fun w : ℂ => ‖w‖) (nhdsWithin 0 ({0}ᶜ))).mul hz1
  simp only [mul_one] at hprod
  have hsq : (fun w : ℂ => ‖outerTailInverse a w - (a : ℂ)‖ ^ 2) =O[nhdsWithin 0 ({0}ᶜ)]
      fun w => ‖w‖ := by
    apply hprod.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_outerTailInverse_affine_re_pos ha] with w hq
    exact (outerTailInverse_dist_sq ha hq).symm
  have hsqrt := hsq.sqrt (Eventually.of_forall fun w : ℂ => norm_nonneg w)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using hsqrt

/-- On the same explicit outer inverse branch, `r|u_ideal|²` converges to
`a(Γ_KJ-Γ)²/(16π²R²)`, the circle-plane coefficient divided by `a`. -/
theorem tendsto_outerTailInverse_norm_mul_idealComplexVelocity_norm_sq
    {a offset speed alpha circulation : ℝ} (ha : 0 < a)
    (hradius : ((a + offset : ℝ) : ℂ) ≠ 0) :
    Tendsto (fun w : ℂ => ‖w‖ *
      ‖idealComplexVelocity a offset speed alpha circulation (outerTailInverse a w)‖ ^ 2)
      (nhdsWithin 0 ({0}ᶜ))
      (𝓝 (physicalTailSpeedSqCoefficient a (a + offset) speed alpha circulation)) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdC := differentiableAt_tailRegularizedVelocity
    (a := a) (offset := offset) (speed := speed) (alpha := alpha) (circulation := circulation)
    haC hradius
  have hs : DifferentiableAt ℝ
      (fun z : ℂ => ‖tailRegularizedVelocity a offset speed alpha circulation z‖ ^ 2) (a : ℂ) := by
    have hfR : DifferentiableAt ℝ (tailRegularizedVelocity a offset speed alpha circulation) (a : ℂ) :=
      hdC.restrictScalars ℝ
    simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    fun_prop
  have hn : DifferentiableAt ℝ (fun z : ℂ => ‖z‖) (a : ℂ) := by
    simp_rw [Complex.norm_eq_sqrt_sq_add_sq]
    apply DifferentiableAt.sqrt
    · fun_prop
    · simpa only [pow_two, ← Complex.normSq_apply] using
        (ne_of_gt (Complex.normSq_pos.mpr haC))
  have hInvD := hn.inv (norm_ne_zero_iff.mpr haC)
  have ht : Tendsto (fun z : ℂ =>
      ‖tailRegularizedVelocity a offset speed alpha circulation z‖ ^ 2 / ‖z‖)
      (nhdsWithin (a : ℂ) ({(a : ℂ)}ᶜ))
      (𝓝 (physicalTailSpeedSqCoefficient a (a + offset) speed alpha circulation)) := by
    have hm := hs.continuousAt.tendsto.mul hInvD.continuousAt.tendsto
    simpa only [Pi.inv_apply, div_eq_mul_inv, physicalTailSpeedSqCoefficient,
      tailRegularizedVelocity_tail_norm_sq haC hradius, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ha] using hm.mono_left
        (nhdsWithin_le_nhds (s := ({(a : ℂ)}ᶜ : Set ℂ)))
  apply (ht.comp (tendsto_outerTailInverse_punctured ha)).congr'
  filter_upwards [self_mem_nhdsWithin, eventually_outerTailInverse_affine_re_pos ha] with w hw hq
  exact (outerTailInverse_scaled_speed_sq_eq ha hq (by simpa using hw)).symm

/-- The exact physical speed, after multiplication by `r`, differs from its
leading coefficient by `O(√r)` on the explicit outer inverse branch. -/
theorem isBigO_outerTailInverse_scaled_speed_sq_sub
    {a offset speed alpha circulation : ℝ} (ha : 0 < a)
    (hradius : ((a + offset : ℝ) : ℂ) ≠ 0) :
    (fun w : ℂ => ‖w‖ *
        ‖idealComplexVelocity a offset speed alpha circulation (outerTailInverse a w)‖ ^ 2 -
      physicalTailSpeedSqCoefficient a (a + offset) speed alpha circulation) =O[
        nhdsWithin 0 ({0}ᶜ)] fun w => Real.sqrt ‖w‖ := by
  have hO := (isBigO_tailRegularizedVelocity_norm_sq_div_norm_sub
    (a := a) (offset := offset) (speed := speed) (alpha := alpha) (circulation := circulation)
    ha hradius).comp_tendsto (tendsto_outerTailInverse_punctured ha)
  simp only [Function.comp_def] at hO
  apply (hO.congr' ?_ EventuallyEq.rfl).trans (isBigO_outerTailInverse_dist ha)
  filter_upwards [self_mem_nhdsWithin, eventually_outerTailInverse_affine_re_pos ha] with w hw hq
  exact congrArg (fun t : ℝ => t - physicalTailSpeedSqCoefficient a (a + offset) speed alpha circulation)
    (outerTailInverse_scaled_speed_sq_eq ha hq (by simpa using hw)).symm

end Qatlib.Papers.SuperfoilLift19.Nucleation
