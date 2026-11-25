/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.VanishCharge.ClebschFarFlux
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussHomotopy
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.WritheGeometry
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.KernelBounds
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.ClassicalLimit
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.NonuniformCL
public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonTwist
public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonCylinder
public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonGaussLimit
public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonDiagonal
public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonRegularCWF
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.ClosedWrithe
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BandControl
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BiotSavartContinuity
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BundleNearPairs
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BundleConcentration
public import Qatlib.Papers.SuperfluidHel18.Madelung.LoopCirculation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Regression consumers for the SuperfluidHel18 analytic modules of this repository:
numeric instances of the `C²` field bridge (helicity density, symmetric Hessian), the
jet-level symmetry premise behind the public divergence identity (with a non-symmetric
counterexample showing the premise is needed), coplanar Gauss linking and banded writhe
vanishing on concrete planar curves, the rescaled writhe error bound, and the circle
ribbon twist including a non-integral rotation rate, and numeric consumers of the
self-Gauss-kernel bounds (chord-arc lower bound, vanishing of the near-diagonal bound on a
straight arc, and the unconditional band-shrink limit via kernel integrability), the
explicit near-diagonal band control on the closed unit circle and on a concentric
non-uniform bundle, the normalized bundle truncation error, and the continuous-vorticity
Biot–Savart consumers (nonvanishing parallel box field with vanishing truncated
helicity, separated-box pairing bound, and `L¹`-pairing continuity on a bounded-support
family). -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open Qatlib.Papers.SuperfluidHel18.CenterlineCL
open Qatlib.Papers.SuperfluidHel18.Madelung
open Qatlib.Papers.SuperfluidHel18.SeifertCWF
open MeasureTheory
open Filter
open scoped BigOperators Real Topology

/-- The oriented Gauss-map area density for two skew lines is positive
at their closest parameter pair, with value `1 / (4π)`. -/
example :
    let γ₁ := fun s : ℝ => ![s, 0, 1]
    let γ₂ := fun t : ℝ => ![0, t, 0]
    dot3 (cross3 (deriv (fun t => gaussDirection γ₁ γ₂ 0 t) 0)
      (deriv (fun s => gaussDirection γ₁ γ₂ s 0) 0)) (gaussDirection γ₁ γ₂ 0 0) /
        (4 * π) = (4 * π)⁻¹ := by
  dsimp only
  let γ₁ := fun s : ℝ => ![s, 0, 1]
  let γ₂ := fun t : ℝ => ![0, t, 0]
  have h₁ : HasDerivAt γ₁ ![1, 0, 0] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_id 0
    · exact hasDerivAt_const 0 0
    · exact hasDerivAt_const 0 1
  have h₂ : HasDerivAt γ₂ ![0, 1, 0] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_const 0 0
    · exact hasDerivAt_id 0
    · exact hasDerivAt_const 0 0
  have hDisj : γ₁ 0 ≠ γ₂ 0 := by
    intro h
    have hZ := congrFun h 2
    norm_num [γ₁, γ₂] at hZ
  change dot3 (cross3 (deriv (fun t => gaussDirection γ₁ γ₂ 0 t) 0)
    (deriv (fun s => gaussDirection γ₁ γ₂ s 0) 0)) (gaussDirection γ₁ γ₂ 0 0) /
      (4 * π) = _
  rw [gaussDirection_area_density γ₁ γ₂ 0 0 h₁.differentiableAt h₂.differentiableAt hDisj]
  unfold gaussKernel
  rw [h₁.deriv, h₂.deriv]
  norm_num [γ₁, γ₂, cross3, dot3, euclideanLength, EuclideanSpace.norm_eq, Fin.sum_univ_three]

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.gaussLinking_eq_direction_area

/-- Changing one radius in a disjoint pair of perpendicular circles
preserves the actual Gauss integral. -/
example (a b : ℝ) (hab : a ≤ b) :
    let r := fun u : ℝ => 1 + Real.sin u / 2
    let γ := fun u t : ℝ => (![1 + r u * Real.cos t, 0, r u * Real.sin t] : Fin 3 → ℝ)
    gaussLinking circleCurve (γ a) = gaussLinking circleCurve (γ b) := by
  dsimp only
  let r := fun u : ℝ => 1 + Real.sin u / 2
  let Γ₁ := fun p : ℝ × ℝ => circleCurve p.2
  let Γ₂ := fun p : ℝ × ℝ => (![1 + r p.1 * Real.cos p.2, 0,
    r p.1 * Real.sin p.2] : Fin 3 → ℝ)
  have hr (u : ℝ) : 0 < r u ∧ r u < 2 := by
    dsimp [r]
    constructor <;> linarith [Real.neg_one_le_sin u, Real.sin_le_one u]
  have hc₁ : ContDiff ℝ 2 Γ₁ := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · change ContDiff ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2)
      fun_prop
    · change ContDiff ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2)
      fun_prop
    · exact contDiff_const
  have hRadius : ContDiff ℝ 2 r := by
    dsimp only [r]
    fun_prop
  have hc₂ : ContDiff ℝ 2 Γ₂ := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · change ContDiff ℝ 2 (fun p : ℝ × ℝ => 1 + r p.1 * Real.cos p.2)
      fun_prop
    · exact contDiff_const
    · change ContDiff ℝ 2 (fun p : ℝ × ℝ => r p.1 * Real.sin p.2)
      fun_prop
  have hDisj (u s t : ℝ) : Γ₁ (u, s) ≠ Γ₂ (u, t) := by
    intro h
    have hX : Real.cos s = 1 + r u * Real.cos t := congrFun h 0
    have hY : Real.sin s = 0 := congrFun h 1
    have hZ : (0 : ℝ) = r u * Real.sin t := congrFun h 2
    have ht : Real.sin t = 0 := (mul_eq_zero.mp hZ.symm).resolve_left (hr u).1.ne'
    have hsign (x : ℝ) (hSin : Real.sin x = 0) : Real.cos x = 1 ∨ Real.cos x = -1 := by
      have h := Real.sin_sq_add_cos_sq x
      rw [hSin] at h
      have hh : (Real.cos x - 1) * (Real.cos x + 1) = 0 := by nlinarith only [h]
      rcases mul_eq_zero.mp hh with h₀ | h₀
      · left
        linarith only [h₀]
      · right
        linarith only [h₀]
    obtain ⟨hpos, hlt⟩ := hr u
    rcases hsign s hY with hs | hs <;> rcases hsign t ht with hT | hT <;>
      rw [hs, hT] at hX <;> nlinarith only [hX, hpos, hlt]
  have hp₁ (u : ℝ) : Function.Periodic (fun x => Γ₁ (u, x)) (2 * π) := by
    intro x
    simp [Γ₁, circleCurve, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hp₂ (u : ℝ) : Function.Periodic (fun x => Γ₂ (u, x)) (2 * π) := by
    intro x
    simp [Γ₂, Real.cos_add_two_pi, Real.sin_add_two_pi]
  exact gaussLinking_eq_on_interval Γ₁ Γ₂ hab hc₁.contDiffOn hc₂.contDiffOn
    (fun u _ => hDisj u) (fun u _ => hp₁ u) (fun u _ => hp₂ u)

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.gaussLinking_eq_on_interval

/-- The circle in the closed-ribbon regression has three continuous derivatives. -/
private theorem contDiff_regressionCircle_three : ContDiff ℝ 3 circleCurve := by
  rw [contDiff_pi]
  intro j
  fin_cases j
  · exact Real.contDiff_cos
  · exact Real.contDiff_sin
  · exact contDiff_const

/-- The smooth circle also meets the two-derivative writhe hypothesis. -/
private theorem contDiff_regressionCircle : ContDiff ℝ 2 circleCurve :=
  contDiff_regressionCircle_three.of_le (by norm_num)

/-- The circle parameter is Euclidean arclength. -/
private theorem unitTangent_regressionCircle (s : ℝ) :
    dot3 (deriv circleCurve s) (deriv circleCurve s) = 1 := by
  rw [deriv_circleCurve]
  simpa [dot3, pow_two, add_comm] using Real.sin_sq_add_cos_sq s

/-- The circle closes after a full turn. -/
private theorem periodic_regressionCircle : Function.Periodic circleCurve (2 * π) := by
  intro s
  simp [circleCurve, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The circle is simple before identifying endpoints. -/
private theorem injOn_regressionCircle : Set.InjOn circleCurve (Set.Ico 0 (2 * π)) := by
  intro s hs t ht h
  have hc : Real.cos s = Real.cos t := by simpa [circleCurve] using congrFun h 0
  have hi : Real.sin s = Real.sin t := by simpa [circleCurve] using congrFun h 1
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * π) (by simp) hs ht
  apply Subtype.ext
  apply Complex.ext
  · simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using hc
  · simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using hi

/-- The circle tangent is nonvanishing. -/
private theorem regular_regressionCircle (s : ℝ) : deriv circleCurve s ≠ 0 := by
  intro h
  rw [deriv_circleCurve] at h
  have hs : Real.sin s = 0 := by simpa using congrFun h 0
  have hc : Real.cos s = 0 := by simpa using congrFun h 1
  simpa [hs, hc] using Real.sin_sq_add_cos_sq s

/-- A nonconstant closed curve with identified endpoints satisfies the
actual circular-band limit without a separate uniform-bound hypothesis. -/
example : Tendsto (fun δ => circularWritheBand circleCurve δ) (nhdsWithin 0 (Set.Ioi 0))
    (nhds (gaussLinking circleCurve circleCurve)) :=
  tendsto_circularWritheBand_of_closed_regular circleCurve contDiff_regressionCircle
    periodic_regressionCircle injOn_regressionCircle regular_regressionCircle

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_circularWritheBand_of_closed_regular

/-! The diagonal chord has length `√2`, distinguishing the Euclidean Gauss
denominator from the coordinate sup norm. -/
example : euclideanLength ![1, 0, 1] = Real.sqrt 2 := by
  norm_num [euclideanLength, EuclideanSpace.norm_eq, Fin.sum_univ_three]

/-! ### Field-bridge instances -/

example (x : Fin 3 → ℝ) :
    clebschHelicityDensity (fun y : Fin 3 → ℝ => y 0) (fun y : Fin 3 → ℝ => y 1)
      (fun y : Fin 3 → ℝ => y 2) x = 1 := by
  have hp : ∀ (x : Fin 3 → ℝ) (j : Fin 3), HasFDerivAt (fun y : Fin 3 → ℝ => y j)
      (ContinuousLinearMap.proj j) x := fun x j => by
        exact ContinuousLinearMap.hasFDerivAt
          ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ))
  have hφ := (hp x 0).fderiv
  have hα := (hp x 1).fderiv
  have hβ := (hp x 2).fderiv
  simp only [clebschHelicityDensity, gradJet, dPart, hφ, hα, hβ, clebschVelocity, dot3,
    cross3_apply_zero, cross3_apply_one, cross3_apply_two, ContinuousLinearMap.proj_apply]
  simp [stdBasis]

/-- A smooth compactly supported phase gives nonzero density at the origin
and zero total helicity with the two Cartesian Clebsch labels. -/
example : ∃ φ : (Fin 3 → ℝ) → ℝ,
    HasCompactSupport φ ∧
    clebschHelicityDensity φ (fun y => y 1) (fun y => y 2) 0 = 1 ∧
    (∫ y, clebschHelicityDensity φ (fun x => x 1) (fun x => x 2) y) = 0 := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let g : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
    ⟨1, 2, by norm_num, by norm_num⟩
  let b := fun x : Fin 3 → ℝ => g (e x)
  let φ := fun x : Fin 3 → ℝ => b x * x 0
  have hb : HasCompactSupport b := by
    apply HasCompactSupport.of_support_subset_isCompact
      (e.toHomeomorph.isCompact_preimage.2 g.hasCompactSupport)
    intro x hx
    exact subset_closure hx
  have hφc : HasCompactSupport φ := hb.mul_right
  have hp (n : WithTop ℕ∞) (j : Fin 3) :
      ContDiff ℝ n (fun y : Fin 3 → ℝ => y j) :=
    (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff
  have hφ : ContDiff ℝ 1 φ := (g.contDiff.comp e.contDiff).mul (hp 1 0)
  refine ⟨φ, hφc, ?_, integral_clebschHelicityDensity_eq_zero_of_hasCompactSupport
    φ _ _ hφ (hp 2 1) (hp 2 2) hφc⟩
  have he : Tendsto e (𝓝 (0 : Fin 3 → ℝ)) (𝓝 (0 : EuclideanSpace ℝ (Fin 3))) := by
    rw [← e.map_zero]
    exact e.continuous.continuousAt.tendsto
  have hb₀ : b =ᶠ[𝓝 (0 : Fin 3 → ℝ)] (fun _ => 1) := g.eventuallyEq_one.comp_tendsto he
  have hφ₀ : φ =ᶠ[𝓝 (0 : Fin 3 → ℝ)] (fun y => y 0) :=
    hb₀.mono fun x hx => by simp [φ, show b x = 1 from hx]
  have hD (j : Fin 3) : fderiv ℝ (fun y : Fin 3 → ℝ => y j) 0 =
      (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.fderiv
  have hd := hφ₀.fderiv_eq (𝕜 := ℝ)
  simp only [clebschHelicityDensity, gradJet, dPart, hd, hD, clebschVelocity, dot3,
    cross3_apply_zero, cross3_apply_one, cross3_apply_two, ContinuousLinearMap.proj_apply]
  simp [stdBasis]

#print axioms Qatlib.Papers.SuperfluidHel18.VanishCharge.tendsto_clebschBoxFaceFlux_integral
#print axioms Qatlib.Papers.SuperfluidHel18.VanishCharge.integral_clebschHelicityDensity_eq_zero_of_hasCompactSupport

/-- A meridian surrounding the zero axis of the linear vortex wavefunction
has one positive circulation quantum. -/
example (ℏ m : ℝ) :
    let wave := fun p : Fin 3 → ℝ => (p 0 : ℂ) + Complex.I * (p 1 : ℂ)
    let meridian := fun s : ℝ => ![Real.cos s, Real.sin s, 0]
    (∀ p, wave p = 0 ↔ p 0 = 0 ∧ p 1 = 0) ∧
      (∫ s in 0..(2 * Real.pi), madelungLoopVelocity ℏ m (wave ∘ meridian) s) =
        2 * Real.pi * ℏ / m := by
  let wave := fun p : Fin 3 → ℝ => (p 0 : ℂ) + Complex.I * (p 1 : ℂ)
  let meridian := fun s : ℝ => ![Real.cos s, Real.sin s, 0]
  let ψ := wave ∘ meridian
  change (∀ p, wave p = 0 ↔ p 0 = 0 ∧ p 1 = 0) ∧
    (∫ s in 0..(2 * Real.pi), madelungLoopVelocity ℏ m ψ s) = _
  constructor
  · intro p
    rw [Complex.ext_iff]
    simp [wave, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  · have hmodel : ψ = fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I) := by
      funext s
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp [ψ, wave, meridian, mul_comm]
    have hV (s : ℝ) : madelungLoopVelocity ℏ m ψ s = ℏ / m := by
      have hs : HasDerivAt ψ (Complex.I * Complex.exp ((s : ℂ) * Complex.I)) s := by
        rw [hmodel]
        have hz : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I s := by
          simpa using (hasDerivAt_id s).ofReal_comp.mul_const Complex.I
        simpa only [mul_comm] using hz.cexp
      rw [madelungLoopVelocity, hs.deriv, hmodel,
        mul_div_cancel_right₀ _ (Complex.exp_ne_zero _), Complex.I_im, mul_one]
    simp_rw [hV, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring

#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.madelungLoopVelocity_pullback
#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.exists_int_madelungLoopCirculation

example (x : Fin 3 → ℝ) (i j : Fin 3) :
    hessJet (fun y : Fin 3 → ℝ => y 0 * y 1) x i j
      = hessJet (fun y : Fin 3 → ℝ => y 0 * y 1) x j i :=
  hessJet_symmetric
    (((contDiff_apply (𝕜 := ℝ) (n := 2) (F' := fun _ : Fin 3 => ℝ) (0 : Fin 3)).mul
        (contDiff_apply (𝕜 := ℝ) (n := 2) (F' := fun _ : Fin 3 => ℝ) (1 : Fin 3))).contDiffAt)
    i j

example : hessJet (fun y : Fin 3 → ℝ => y 0 * y 1) ![0, 0, 0] 0 1 = 1 := by
  have hp : ∀ (x : Fin 3 → ℝ) (j : Fin 3), HasFDerivAt (fun y : Fin 3 → ℝ => y j)
      (ContinuousLinearMap.proj j) x := fun x j => by
        exact ContinuousLinearMap.hasFDerivAt
          ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ))
  have hmul : ∀ x : Fin 3 → ℝ, HasFDerivAt (fun y : Fin 3 → ℝ => y 0 * y 1)
      (x 0 • (ContinuousLinearMap.proj (1 : Fin 3))
        + x 1 • (ContinuousLinearMap.proj (0 : Fin 3))) x := fun x => by exact (hp x 0).mul (hp x 1)
  have hd : ∀ x : Fin 3 → ℝ, dPart 1 (fun y : Fin 3 → ℝ => y 0 * y 1) x = x 0 := by
    intro x
    simp only [dPart, (hmul x).fderiv]
    simp [stdBasis]
  have hdfun : dPart 1 (fun y : Fin 3 → ℝ => y 0 * y 1) = fun x => x 0 := funext hd
  simp only [hessJet, hdfun]
  rw [show fderiv ℝ (fun y : Fin 3 → ℝ => y 0) ![0, 0, 0]
      = (ContinuousLinearMap.proj (0 : Fin 3)) from (hp ![0, 0, 0] 0).fderiv]
  simp [stdBasis]

/-! ### Jet-level symmetry premise -/

example : divergenceJet (vorticityJacobian ![1, 0, 0] ![0, 0, 1]
      (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) = 0 :=
  vorticity_divergence_zero ![1, 0, 0] ![0, 0, 1] _ _ (fun _ _ => rfl) (fun _ _ => rfl)

example : divergenceJet (vorticityJacobian ![1, 0, 0] ![0, 0, 1]
      (fun i j => if (0 : Fin 3) = i ∧ (1 : Fin 3) = j then (1 : ℝ) else 0)
      (fun _ _ => (0 : ℝ))) = 1 := by
  simp [divergenceJet, vorticityJacobian, cross3]

/-! ### Coplanar Gauss linking and banded writhe -/

example : gaussLinking (fun s : ℝ => ![s, 0, 0]) (fun s : ℝ => ![0, s, 0]) = 0 := by
  refine gaussLinking_coplanar_eq_zero (fun s : ℝ => ![s, 0, 0]) (fun s : ℝ => ![0, s, 0])
      ![0, 0, 1] (by
      intro h
      have h3 := congrFun h 2
      simp at h3) 0
    (fun s => by simp [dot3]) (fun s => by simp [dot3]) ?_ ?_
  · rw [contDiff_pi]
    intro i
    fin_cases i
    · exact contDiff_id
    · exact contDiff_const
    · exact contDiff_const
  · rw [contDiff_pi]
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id
    · exact contDiff_const

example : writheBand (fun s : ℝ => ![s, 0, 0]) (1 / 2) = 0 := by
  refine writheBand_coplanar_eq_zero (fun s : ℝ => ![s, 0, 0]) ![0, 0, 1] (by
      intro h
      have h3 := congrFun h 2
      simp at h3) 0
    (fun s => by simp [dot3]) ?_ (1 / 2)
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const
  · exact contDiff_const

example : Tendsto (fun δ => writheBand (fun s : ℝ => ![s, 0, 0]) δ)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hz : ∀ p : ℝ × ℝ, writheKernel (fun s : ℝ => ![s, 0, 0]) p.1 p.2 = 0 := fun p =>
    writheKernel_planar_eq_zero (fun s : ℝ => ![s, 0, 0]) ![0, 0, 1]
      (by
        intro h
        have h3 := congrFun h 2
        simp at h3) 0 (fun s => by simp [dot3])
      (by
        rw [contDiff_pi]
        intro i
        fin_cases i <;> [exact contDiff_id; exact contDiff_const; exact contDiff_const])
      p.1 p.2
  have hint : Integrable (fun p : ℝ × ℝ => writheKernel (fun s : ℝ => ![s, 0, 0]) p.1 p.2)
      gaussMeasure :=
    Integrable.congr (f := (0 : ℝ × ℝ → ℝ)) (integrable_zero (α := ℝ × ℝ) (ε' := ℝ) (μ := gaussMeasure))
      (Filter.Eventually.of_forall fun p => (hz p).symm)
  have hlim := tendsto_writheBand_nhds_selfKernel _ hint
  simp only [hz, integral_zero] at hlim
  exact hlim

example : pairLinkingGauss (fun _ : Fin 2 => (1 : ℝ))
      (fun i : Fin 2 => if i = 0 then (fun s : ℝ => ![s, 0, 0]) else fun s : ℝ => ![0, s, 0]) = 0 :=
  pairLinkingGauss_coplanar_eq_zero _ _ ![0, 0, 1]
    (by
      intro h
      have h3 := congrFun h 2
      simp at h3) 0
    (fun i s => by
      fin_cases i <;> simp [dot3])
    (fun i => by
      fin_cases i
      · rw [contDiff_pi]
        intro j
        fin_cases j <;> [exact contDiff_id; exact contDiff_const; exact contDiff_const]
      · rw [contDiff_pi]
        intro j
        fin_cases j <;> [exact contDiff_const; exact contDiff_id; exact contDiff_const])

example : gaussLinking (fun s : ℝ => ![s, 0, 0] + ![1, 1, 1])
      (fun s : ℝ => ![0, s, 0] + ![1, 1, 1])
    = gaussLinking (fun s : ℝ => ![s, 0, 0]) (fun s : ℝ => ![0, s, 0]) := by
  have hc₁ : ContDiff ℝ 1 fun s : ℝ => ![s, 0, 0] := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · exact contDiff_id
    · exact contDiff_const
    · exact contDiff_const
  have hc₂ : ContDiff ℝ 1 fun s : ℝ => ![0, s, 0] := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id
    · exact contDiff_const
  exact gaussLinking_trans_eq (fun s : ℝ => ![s, 0, 0]) (fun s : ℝ => ![0, s, 0]) ![1, 1, 1]
    hc₁ hc₂

example : gaussLinking (fun s : ℝ => (2 : ℝ) • ![s, 0, 0])
      (fun s : ℝ => (2 : ℝ) • ![0, s, 0])
    = gaussLinking (fun s : ℝ => ![s, 0, 0]) (fun s : ℝ => ![0, s, 0]) := by
  have hc₁ : ContDiff ℝ 1 fun s : ℝ => ![s, 0, 0] := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · exact contDiff_id
    · exact contDiff_const
    · exact contDiff_const
  have hc₂ : ContDiff ℝ 1 fun s : ℝ => ![0, s, 0] := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id
    · exact contDiff_const
  exact gaussLinking_const_smul_eq (fun s : ℝ => ![s, 0, 0]) (fun s : ℝ => ![0, s, 0])
    (by norm_num) hc₁ hc₂

example (γ : ℝ → (Fin 3 → ℝ)) : writheBand γ (-1) = gaussLinking γ γ :=
  writheBand_of_nonpos γ (by norm_num)

/-! ### Rescaled writhe error and ribbon twist -/

example : |writhePart (fun _ : Fin 3 => (2 : ℝ)) ![1, -1, 1]| / ((3 : ℝ) * 2) ^ 2
      ≤ 1 / (3 : ℝ) :=
  rescaled_writhe_error 3 2 1 (by norm_num) ![1, -1, 1] (fun i => by fin_cases i <;> norm_num)

example (L : Fin 3 → Fin 3 → ℝ) :
    |centerlineHelicity (fun _ : Fin 3 => (2 : ℝ)) L ![1, -1, 1] / ((3 : ℝ) * 2) ^ 2
        - linkingPart (fun _ : Fin 3 => (2 : ℝ)) L / ((3 : ℝ) * 2) ^ 2| ≤ 1 / (3 : ℝ) :=
  rescaled_centerline_near_linking 3 2 1 (by norm_num) L ![1, -1, 1]
    (fun i => by fin_cases i <;> norm_num)

example : ribbonTwist circleCurve (circleRibbonNormal 3) = -(3 : ℝ) :=
  ribbonTwist_circle_eq 3

example : ribbonTwist circleCurve (circleRibbonNormal (1 / 2)) = -(1 / 2 : ℝ) :=
  ribbonTwist_circle_eq (1 / 2)

example : centerlineHelicityGauss (fun _ : Fin 2 => (1 : ℝ))
      (fun i : Fin 2 => if i = 0 then (fun s : ℝ => ![s, 0, 0]) else fun s : ℝ => ![0, s, 0])
      (fun _ => (3 : ℝ)) = 6 := by
  rw [centerlineHelicityGauss_coplanar_eq_writhe _ _ ![0, 0, 1]
    (by
      intro h
      have h3 := congrFun h 2
      simp at h3) 0
    (fun i s => by
      fin_cases i <;> simp [dot3])
    (fun i => by
      fin_cases i
      · rw [contDiff_pi]
        intro j
        fin_cases j <;> [exact contDiff_id; exact contDiff_const; exact contDiff_const]
      · rw [contDiff_pi]
        intro j
        fin_cases j <;> [exact contDiff_const; exact contDiff_id; exact contDiff_const]) _]
  norm_num [writhePart]

example (wr : Fin 1 → ℝ) :
    centerlineHelicityGauss (fun _ : Fin 1 => (1 : ℝ))
      (fun _ s => (2 : ℝ) • (![s, 0, 0] : Fin 3 → ℝ)) wr
      = centerlineHelicityGauss (fun _ : Fin 1 => (1 : ℝ))
      (fun _ : Fin 1 => fun s : ℝ => ![s, 0, 0]) wr := by
  refine centerlineHelicityGauss_const_smul _ _ (by norm_num) ?_ wr
  intro i
  fin_cases i
  rw [contDiff_pi]
  intro j
  fin_cases j
  · exact contDiff_id
  · exact contDiff_const
  · exact contDiff_const

/-! ### Kernel-bounds consumers -/

private theorem hasDerivAt_lineCurve (u : ℝ) :
    HasDerivAt (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) (![1, 0, 0]) u := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · show HasDerivAt (fun w : ℝ => w) (1 : ℝ) u
    exact hasDerivAt_id u
  · show HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) u
    exact hasDerivAt_const (c := (0 : ℝ)) (x := u)
  · show HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) u
    exact hasDerivAt_const (c := (0 : ℝ)) (x := u)

private theorem deriv_lineCurve (u : ℝ) :
    deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) u = ![1, 0, 0] :=
  (hasDerivAt_lineCurve u).deriv

private theorem contDiff_lineCurve :
    ContDiff ℝ 2 (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const
  · exact contDiff_const

example (s t : ℝ) (hst : s ≤ t) :
    (1 : ℝ) ^ 2 / (6 * 1) * (t - s)
      ≤ ‖(![t, 0, 0] : Fin 3 → ℝ) - ![s, 0, 0]‖ := by
  refine norm_chord_ge_of_sqSpeed_ge (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
    contDiff_lineCurve (τ := 1) (B := 1) (M := 0) (by norm_num) ?_ ?_ ?_ s t hst
    (by norm_num)
  · intro u
    rw [deriv_lineCurve u]
    simp [dot3]
  · intro u
    rw [deriv_lineCurve u]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => by
      fin_cases i <;> simp
  · intro u
    have hfe : deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
        = fun _ : ℝ => (![1, 0, 0] : Fin 3 → ℝ) := funext deriv_lineCurve
    rw [hfe, deriv_const]
    simp

example (s t : ℝ) :
    writheKernel (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) s t = 0 := by
  have hle := abs_writheKernel_le_near (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
    contDiff_lineCurve (τ := 1) (B := 1) (M := 0) (by norm_num) ?_ ?_ ?_ s t (by norm_num)
  · simp at hle
    exact hle
  · intro u
    rw [deriv_lineCurve u]
    simp [dot3]
  · intro u
    rw [deriv_lineCurve u]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => by
      fin_cases i <;> simp
  · intro u
    have hfe : deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
        = fun _ : ℝ => (![1, 0, 0] : Fin 3 → ℝ) := funext deriv_lineCurve
    rw [hfe, deriv_const]
    simp

example : Integrable (fun p : ℝ × ℝ =>
        writheKernel (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) p.1 p.2) gaussMeasure ∧
    Tendsto (fun δ => writheBand (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) δ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gaussLinking (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
        (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)))) := by
  have hinj : ∀ s ∈ Set.Icc (0 : ℝ) (2 * π), ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) s
        = (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) t → s = t := by
    intro s _ t _ he
    have h0 := congrFun he 0
    simp at h0
    exact h0
  have hτ : ∀ u : ℝ, (1 : ℝ) ^ 2
      ≤ dot3 (deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) u)
        (deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) u) := by
    intro u
    rw [deriv_lineCurve u]
    simp [dot3]
  have hB : ∀ u : ℝ, ‖deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) u‖ ≤ 1 := by
    intro u
    rw [deriv_lineCurve u]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => by
      fin_cases i <;> simp
  have hM : ∀ u : ℝ, ‖deriv (deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))) u‖ ≤ 0 := by
    intro u
    have hfe : deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
        = fun _ : ℝ => (![1, 0, 0] : Fin 3 → ℝ) := funext deriv_lineCurve
    rw [hfe, deriv_const]
    simp
  exact ⟨writheKernel_integrable_of_regular _ contDiff_lineCurve (by norm_num)
      hτ hB hM hinj,
    tendsto_writheBand_nhds_selfKernel_of_regular _ contDiff_lineCurve (by norm_num)
      hτ hB hM hinj⟩

example : ∃ m, 0 < m ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (1 / 2 : ℝ) ≤ |t - s| → m ≤ ‖(![t, 0, 0] : Fin 3 → ℝ) - ![s, 0, 0]‖ :=
  exists_pos_le_norm_sub_of_injective_on (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
    contDiff_lineCurve.continuous
    (by
      intro s _ t _ he
      have h0 := congrFun he 0
      simp at h0
      exact h0)
    (by norm_num) (by norm_num)

/-! A genuinely non-planar consumer: the unit-pitch helix, whose curvature bound `M = 1`
is nonzero, so the near-diagonal and far-field bounds are both active. -/

/-- The first derivative of the unit-pitch helix on the unit cylinder. -/
private theorem deriv_helixCurve (u : ℝ) :
    deriv (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) u
      = ![-Real.sin u, Real.cos u, 1] := by
  have h : HasDerivAt (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ))
      ![-Real.sin u, Real.cos u, 1] u := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · show HasDerivAt (fun w : ℝ => Real.cos w) (-Real.sin u) u
      exact Real.hasDerivAt_cos u
    · show HasDerivAt (fun w : ℝ => Real.sin w) (Real.cos u) u
      exact Real.hasDerivAt_sin u
    · show HasDerivAt (fun w : ℝ => w) (1 : ℝ) u
      exact hasDerivAt_id u
  exact h.deriv

/-- The second derivative lies in the plane transverse to the helix axis. -/
private theorem deriv_deriv_helixCurve (u : ℝ) :
    deriv (deriv (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ))) u
      = ![-Real.cos u, -Real.sin u, 0] := by
  have hfe : deriv (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ))
      = fun w : ℝ => (![-Real.sin w, Real.cos w, 1] : Fin 3 → ℝ) :=
    funext deriv_helixCurve
  rw [hfe]
  have h : HasDerivAt (fun w : ℝ => (![-Real.sin w, Real.cos w, 1] : Fin 3 → ℝ))
      ![-Real.cos u, -Real.sin u, 0] u := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · show HasDerivAt (fun w : ℝ => -Real.sin w) (-Real.cos u) u
      exact (Real.hasDerivAt_sin u).neg
    · show HasDerivAt (fun w : ℝ => Real.cos w) (-Real.sin u) u
      exact Real.hasDerivAt_cos u
    · show HasDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ) u
      exact hasDerivAt_const (c := (1 : ℝ)) (x := u)
  exact h.deriv

/-- The unit-pitch helix is twice continuously differentiable. -/
private theorem contDiff_helixCurve :
    ContDiff ℝ 2 (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact Real.contDiff_cos
  · exact Real.contDiff_sin
  · exact contDiff_id

example : Integrable (fun p : ℝ × ℝ =>
        writheKernel (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) p.1 p.2)
      gaussMeasure ∧
    Tendsto (fun δ => writheBand (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) δ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gaussLinking (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ))
        (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)))) := by
  have hinj : ∀ s ∈ Set.Icc (0 : ℝ) (2 * π), ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) s
        = (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) t → s = t := by
    intro s _ t _ he
    have h2 := congrFun he 2
    simp at h2
    exact h2
  have hτ : ∀ u : ℝ, (1 : ℝ) ^ 2
      ≤ dot3 (deriv (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) u)
        (deriv (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) u) := by
    intro u
    rw [deriv_helixCurve u]
    simp [dot3]
    nlinarith [sq_nonneg (Real.sin u), sq_nonneg (Real.cos u)]
  have hB : ∀ u : ℝ,
      ‖deriv (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ)) u‖ ≤ 1 := by
    intro u
    rw [deriv_helixCurve u]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    fin_cases i
    · simpa using Real.abs_sin_le_one u
    · simpa using Real.abs_cos_le_one u
    · simp
  have hM : ∀ u : ℝ,
      ‖deriv (deriv (fun w : ℝ => (![Real.cos w, Real.sin w, w] : Fin 3 → ℝ))) u‖ ≤ 1 := by
    intro u
    rw [deriv_deriv_helixCurve u]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    fin_cases i
    · simpa using Real.abs_cos_le_one u
    · simpa using Real.abs_sin_le_one u
    · simp
  exact ⟨writheKernel_integrable_of_regular _ contDiff_helixCurve (by norm_num)
      hτ hB hM hinj,
    tendsto_writheBand_nhds_selfKernel_of_regular _ contDiff_helixCurve (by norm_num)
      hτ hB hM hinj⟩

/-- The unit twisting normal is smooth on the whole parameter line. -/
private theorem contDiff_onceTwistedNormal : ContDiff ℝ 2 (circleRibbonNormal 1) := by
  rw [contDiff_pi]
  intro j
  fin_cases j
  · change ContDiff ℝ 2 (fun s => Real.cos (1 * s) * Real.cos s)
    fun_prop
  · change ContDiff ℝ 2 (fun s => Real.cos (1 * s) * Real.sin s)
    fun_prop
  · change ContDiff ℝ 2 (fun s => Real.sin (1 * s))
    fun_prop

/-- An integral twist of one full turn gives a genuine closed normal field. -/
private theorem periodic_onceTwistedNormal : Function.Periodic (circleRibbonNormal 1) (2 * π) := by
  intro s
  simp [circleRibbonNormal, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The explicit twisting normal is nonzero by its unit squared length. -/
private theorem nonzero_onceTwistedNormal (s : ℝ) : circleRibbonNormal 1 s ≠ 0 := by
  intro hz
  have h := circleRibbonNormal_self_eq_one 1 s
  rw [hz] at h
  norm_num [dot3] at h

/-- The once-twisted normal realizes an embedded closed cylinder and
its disjoint positive-width edges have the same linking with the core. -/
example :
    (∃ w : ℝ, 0 < w ∧ Topology.IsClosedEmbedding
      (fun p : AddCircle (2 * π) × Set.Icc (-w) w =>
        normalRibbonCylinder circleCurve (circleRibbonNormal 1) (p.1, (p.2 : ℝ)))) ∧
    ∃ ε > 0, ∀ a b : ℝ, 0 < a → a < ε → 0 < b → b < ε →
      (∀ s t, circleCurve s ≠ normalRibbonPoint circleCurve (circleRibbonNormal 1) a t) ∧
      gaussLinking circleCurve (normalRibbonPoint circleCurve (circleRibbonNormal 1) a) =
        gaussLinking circleCurve (normalRibbonPoint circleCurve (circleRibbonNormal 1) b) := by
  refine ⟨?_, ?_⟩
  · exact exists_closedEmbedding_normalRibbonCylinder contDiff_regressionCircle
      (contDiff_onceTwistedNormal.of_le (by norm_num)) periodic_regressionCircle
      periodic_onceTwistedNormal injOn_regressionCircle regular_regressionCircle
      nonzero_onceTwistedNormal (circleRibbonNormal_orth_tangent 1)
  · obtain ⟨ε, hε, _, hdisj, hLk⟩ :=
      exists_normalRibbon_gaussLinking_stable contDiff_regressionCircle contDiff_onceTwistedNormal
        periodic_regressionCircle periodic_onceTwistedNormal injOn_regressionCircle
        regular_regressionCircle nonzero_onceTwistedNormal (circleRibbonNormal_orth_tangent 1)
    refine ⟨ε, hε, fun a b ha hA hb hB => ⟨?_, ?_⟩⟩
    · intro s t
      simpa [normalRibbonPoint] using
        hdisj 0 a s t (by simpa using hε) (by simpa [abs_of_pos ha] using hA) ha.ne
    · simpa only [normalRibbonPoint_zero] using hLk 0 a 0 b (by simpa using hε)
        (by simpa [abs_of_pos ha] using hA) (by simpa using hε)
        (by simpa [abs_of_pos hb] using hB) ha hb

#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.exists_normalRibbon_gaussLinking_stable
#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.exists_closedEmbedding_normalRibbonCylinder

/-- The actual self Gauss kernel of the planar circle vanishes pointwise. -/
private theorem writheKernel_regressionCircle_zero : ∀ s t, writheKernel circleCurve s t = 0 :=
  writheKernel_planar_eq_zero circleCurve ![0, 0, 1] (by
    intro h
    have hz := congrFun h 2
    simp at hz) 0 (fun s => by simp [dot3, circleCurve])
      (contDiff_regressionCircle.of_le (by norm_num))

/-- For the once-twisted ribbon the far integral tends to the circular
core's zero writhe, even though its offset is genuinely nonplanar. -/
example : Tendsto (circularRibbonFar circleCurve (circleRibbonNormal 1) (π / 2))
    (𝓝 0) (𝓝 0) := by
  have hc : ContDiff ℝ 1 circleCurve := contDiff_regressionCircle.of_le (by norm_num)
  have hband : circularWritheBand circleCurve (π / 2) = 0 := by
    unfold circularWritheBand
    simp only [writheKernel_regressionCircle_zero, ite_self, integral_zero]
  simpa only [hband] using tendsto_circularRibbonFar hc
    (contDiff_onceTwistedNormal.of_le (by norm_num)) periodic_regressionCircle
    injOn_regressionCircle (δ := π / 2) (half_pos Real.pi_pos) (by linarith [Real.pi_pos])

/-- At a quarter turn the signed curvature coefficient is one, whereas
the twist coefficient is minus one. Both contribute to the rescaled
Gauss kernel at either side of the diagonal. -/
example (x : ℝ) :
    Tendsto (fun a : ℝ =>
      a * gaussKernel circleCurve (normalRibbonPoint circleCurve (circleRibbonNormal 1) a)
        (π / 2 + a * x) (π / 2))
      (𝓝[>] 0) (𝓝 ((-1 + x) / (4 * π * Real.sqrt (x ^ 2 + 1) ^ 3))) := by
  have hA (s : ℝ) : deriv (deriv circleCurve) s = ![-Real.cos s, -Real.sin s, 0] := by
    apply HasDerivAt.deriv
    rw [show deriv circleCurve = fun u => ![-Real.sin u, Real.cos u, 0] from
      funext deriv_circleCurve, hasDerivAt_pi]
    intro j
    fin_cases j
    · exact (Real.hasDerivAt_sin s).neg
    · exact Real.hasDerivAt_cos s
    · exact hasDerivAt_const s 0
  have htw : ribbonTwistDensity circleCurve (circleRibbonNormal 1) (π / 2) = -1 :=
    twistDensity_circle_eq 1 (π / 2)
  have hbend : ribbonBendDensity circleCurve (circleRibbonNormal 1) (π / 2) = 1 := by
    norm_num [ribbonBendDensity, hA, deriv_circleCurve, circleRibbonNormal, dot3, cross3,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
  simpa only [frozenRibbonKernel, one_pow, one_mul, htw, hbend, mul_one] using
    tendsto_rescaled_normalRibbon_gaussKernel contDiff_regressionCircle
      (contDiff_onceTwistedNormal.differentiable (by norm_num)) (π / 2) x (unitTangent_regressionCircle _)
      (circleRibbonNormal_self_eq_one 1 _) (circleRibbonNormal_orth_tangent 1 _)

/-- The integrated diagonal model of the circle retains the negative
orientation and has the exact finite-band mass. -/
example (a δ : ℝ) (ha : 0 < a) :
    (∫ s in 0..(2 * π), ∫ h in -δ..δ, frozenRibbonKernel circleCurve
      (circleRibbonNormal 1) a s h) = -(δ / Real.sqrt (δ ^ 2 + a ^ 2)) := by
  rw [integral_integral_frozenRibbonKernel _ _ ha.ne', ribbonTwist_circle_eq]
  ring

#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.tendsto_circularRibbonFar
#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.exists_circularRibbonNear_iterated_limit
#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.tendsto_rescaled_normalRibbon_gaussKernel
#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.integral_integral_frozenRibbonKernel

/-- Every sufficiently narrow offset of the once-twisted circle has true
Gauss linking minus one with the core. Its self writhe vanishes and the
entire nonzero value comes from the winding of the normal. -/
private theorem once_twisted_offset_link : ∃ ε > 0, ∀ a : ℝ, 0 < a → a < ε →
    (∀ s t, circleCurve s ≠ normalRibbonPoint circleCurve (circleRibbonNormal 1) a t) ∧
    gaussLinking circleCurve (normalRibbonPoint circleCurve (circleRibbonNormal 1) a) = -1 := by
  obtain ⟨ε, hε, hlink⟩ := exists_normalRibbon_gaussLinking_eq_writhe_add_twist
    contDiff_regressionCircle_three contDiff_onceTwistedNormal periodic_regressionCircle
    periodic_onceTwistedNormal injOn_regressionCircle unitTangent_regressionCircle
    (circleRibbonNormal_self_eq_one 1) (circleRibbonNormal_orth_tangent 1)
  have hw : gaussLinking circleCurve circleCurve = 0 := by
    change (∫ p, writheKernel circleCurve p.1 p.2 ∂gaussMeasure) = _
    simp only [writheKernel_regressionCircle_zero, integral_zero]
  refine ⟨ε, hε, fun a ha haε => ⟨(hlink a ha haε).1, ?_⟩⟩
  rw [(hlink a ha haε).2, hw, ribbonTwist_circle_eq, zero_add]

/-- Two linked circular ribbon curves with positive circulations
can concentrate to zero oriented mass while retaining nonzero
normalized centerline helicity. -/
example :
    let c := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)
    ∃ (κ : Fin 2 → ℝ) (γ : Fin 2 → ℝ → Fin 3 → ℝ) (hγ : ∀ i, ContDiff ℝ 1 (γ i)),
      (∀ i, 0 < κ i) ∧
        Tendsto (fun n => rescaledOrientedBundle κ (fun i s => c n • γ i s)
          (fun i => ContDiff.const_smul (c n) (hγ i))) atTop (𝓝 0) ∧
        ¬ Tendsto (fun n => centerlineHelicityGaussSelf κ (fun i s => c n • γ i s) /
          (∑ i, κ i) ^ 2) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hlink⟩ := once_twisted_offset_link
  let a := ε / 2
  let η := normalRibbonPoint circleCurve (circleRibbonNormal 1) a
  let γ : Fin 2 → ℝ → Fin 3 → ℝ := ![circleCurve, η]
  have h0 : ContDiff ℝ 1 circleCurve := contDiff_regressionCircle_three.of_le (by norm_num)
  have hN : ContDiff ℝ 1 (circleRibbonNormal 1) := contDiff_onceTwistedNormal.of_le (by norm_num)
  have hη : ContDiff ℝ 1 η := h0.add (ContDiff.const_smul a hN)
  have hlinked := hlink a (by dsimp [a]; positivity) (by dsimp [a]; linarith)
  have h01 : gaussLinking circleCurve η = -1 := hlinked.2
  have h10 : gaussLinking η circleCurve = -1 :=
    (gaussLinking_symm η circleCurve hη h0 (fun s t => (hlinked.1 t s).symm)).trans h01
  have hw : gaussLinking circleCurve circleCurve = 0 := by
    change (∫ p, writheKernel circleCurve p.1 p.2 ∂gaussMeasure) = _
    simp only [writheKernel_regressionCircle_zero, integral_zero]
  have hH (b : ℝ) : centerlineHelicityGaussSelf (![b, 1] : Fin 2 → ℝ) γ =
      -2 * b + gaussLinking η η := by
    rw [centerlineHelicityGaussSelf_eq, pairLinkingGauss_eq]
    norm_num [writheGaussPart, gaussWrithe, Fin.sum_univ_two, γ, h01, h10, hw]
    ring
  have hSeed : ∃ b : ℝ, 0 < b ∧ centerlineHelicityGaussSelf (![b, 1] : Fin 2 → ℝ) γ ≠ 0 := by
    by_cases hb : centerlineHelicityGaussSelf (![1, 1] : Fin 2 → ℝ) γ = 0
    · refine ⟨2, by norm_num, fun htwo => ?_⟩
      rw [hH] at hb htwo
      linarith
    · exact ⟨1, by norm_num, hb⟩
  obtain ⟨b, hb, hbH⟩ := hSeed
  let κ : Fin 2 → ℝ := ![b, 1]
  have hγ (i : Fin 2) : ContDiff ℝ 1 (γ i) := by
    fin_cases i
    · exact h0
    · exact hη
  have hκ (i : Fin 2) : 0 < κ i := by
    fin_cases i
    · exact hb
    · norm_num [κ]
  have hsum : (∑ i, κ i) ≠ 0 := by
    simpa only [κ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
      (by linarith : b + 1 ≠ 0)
  refine ⟨κ, γ, hγ, hκ, ?_⟩
  exact concentratedBundle_not_tendsto_zero_helicity κ γ hγ _
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun _ => by positivity)
    (div_ne_zero hbH (pow_ne_zero 2 hsum))

#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.circularRibbonNear_eq_intervalIntegral
#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.exists_abs_normalRibbon_kernel_sub_le
#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.exists_normalRibbon_gaussLinking_eq_writhe_add_twist

/-- The radius-two circle has speed two, and its once-twisted normal gives
Gauss linking minus one for every sufficiently narrow positive offset. -/
example :
    let γ (s : ℝ) := (2 : ℝ) • circleCurve s
    ∃ ε > 0, ∀ a : ℝ, 0 < a → a < ε →
      gaussLinking γ (normalRibbonPoint γ (circleRibbonNormal 1) a) = -1 := by
  let γ (s : ℝ) := (2 : ℝ) • circleCurve s
  change ∃ ε > 0, ∀ a : ℝ, 0 < a → a < ε →
    gaussLinking γ (normalRibbonPoint γ (circleRibbonNormal 1) a) = -1
  have hγ := contDiff_regressionCircle_three.const_smul (2 : ℝ)
  have hderiv (s : ℝ) : deriv γ s = (2 : ℝ) • deriv circleCurve s :=
    ((hasDerivAt_circleCurve s).const_smul (2 : ℝ)).deriv.trans (by rw [deriv_circleCurve])
  have hp : Function.Periodic γ (2 * π) := fun s => by
    simp only [γ, periodic_regressionCircle s]
  have hinj : Set.InjOn γ (Set.Ico 0 (2 * π)) := by
    intro x hx y hy he
    exact injOn_regressionCircle hx hy
      ((smul_right_injective (Fin 3 → ℝ) (by norm_num : (2 : ℝ) ≠ 0)) he)
  have hspeed (s : ℝ) : ribbonSpeed γ s = 2 := by
    unfold ribbonSpeed
    rw [hderiv, dot3_smul_left, dot3_smul_right, unitTangent_regressionCircle]
    norm_num
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hreg (s : ℝ) : deriv γ s ≠ 0 := by
    intro h
    have hzero := ribbonSpeed_sq γ s
    rw [hspeed, h] at hzero
    norm_num [dot3] at hzero
  have horth (s : ℝ) : dot3 (deriv γ s) (circleRibbonNormal 1 s) = 0 := by
    rw [hderiv, dot3_smul_left, circleRibbonNormal_orth_tangent, mul_zero]
  have htangent (s : ℝ) : ribbonUnitTangent γ s = deriv circleCurve s := by
    rw [ribbonUnitTangent, hspeed, hderiv, smul_smul]
    norm_num
  obtain ⟨ε, hε, hlink⟩ := exists_regularRibbon_gaussLinking_eq_writhe_add_twist
    hγ contDiff_onceTwistedNormal hp periodic_onceTwistedNormal hinj hreg
    (circleRibbonNormal_self_eq_one 1) horth
  have hw : gaussLinking γ γ = 0 := by
    have h₁ : ContDiff ℝ 1 circleCurve := contDiff_regressionCircle_three.of_le (by norm_num)
    rw [show gaussLinking γ γ = gaussLinking circleCurve circleCurve from
      gaussLinking_const_smul_eq _ _ (by norm_num : (0 : ℝ) < 2) h₁ h₁]
    change (∫ p, writheKernel circleCurve p.1 p.2 ∂gaussMeasure) = _
    simp only [writheKernel_regressionCircle_zero, integral_zero]
  have htw : regularRibbonTwist γ (circleRibbonNormal 1) = -1 := by
    unfold regularRibbonTwist
    simp_rw [htangent]
    exact ribbonTwist_circle_eq 1
  exact ⟨ε, hε, fun a ha haε => by rw [(hlink a ha haε).2, hw, htw, zero_add]⟩

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.gaussLinking_comp_eq
#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.exists_normalized_arcLength
#print axioms Qatlib.Papers.SuperfluidHel18.SeifertCWF.exists_regularRibbon_gaussLinking_eq_writhe_add_twist

/-! ### Non-uniform circulation normalization and geometric writhe suppression -/

/-- The concentric circle of radius `1 + i` in the `xy`-plane, as a regression curve. -/
private noncomputable def concentricCircle (i : Fin 3) (s : ℝ) : Fin 3 → ℝ :=
  ![(1 + (i : ℝ)) * Real.cos s, (1 + (i : ℝ)) * Real.sin s, 0]

private theorem contDiff_concentricCircle (i : Fin 3) : ContDiff ℝ 1 (concentricCircle i) := by
  rw [contDiff_pi]
  intro j
  fin_cases j
  · exact contDiff_const.mul (ContDiff.cos contDiff_id)
  · exact contDiff_const.mul (ContDiff.sin contDiff_id)
  · exact contDiff_const

private theorem planar_concentricCircle (i : Fin 3) (s : ℝ) :
    dot3 (![0, 0, 1] : Fin 3 → ℝ) (concentricCircle i s) = 0 := by
  simp [concentricCircle, dot3]

/-- Numeric inverse effective bundle size: for circulations `1, 2, 3` it is `7/18`,
strictly between `1/3` (equal circulations) and `1`. -/
example : (∑ i, (![1, 2, 3] : Fin 3 → ℝ) i ^ 2) / (∑ i, (![1, 2, 3] : Fin 3 → ℝ) i) ^ 2
    = 7 / 18 := by
  norm_num [Fin.sum_univ_three]

/-- Equal circulations recover exactly the inverse bundle size `1/n`. -/
example : (∑ _ : Fin 4, (2 : ℝ) ^ 2) / (∑ _ : Fin 4, (2 : ℝ)) ^ 2 = 1 / 4 :=
  selfWeight_const_eq_inv_card (n := 4) (by norm_num) 2 (by norm_num)

/-- The comparable-circulation bound is non-vacuous on `κ = ![1, 2, 3]`: the weight
`7/18` is at most `C / (n c) = 3 / 3`. -/
example : (∑ i, (![1, 2, 3] : Fin 3 → ℝ) i ^ 2)
      / (∑ i, (![1, 2, 3] : Fin 3 → ℝ) i) ^ 2 ≤ 3 / ((3 : ℝ) * 1) :=
  selfWeight_le_of_comparable _ (c := 1) (C := 3)
    (by norm_num)
    (fun i => by fin_cases i <;> norm_num)
    (fun i => by fin_cases i <;> norm_num)
    (by simp only [Fin.sum_univ_three]; norm_num)

set_option maxHeartbeats 500000 in
/-- Geometric non-degenerate instance: three concentric planar circles with non-uniform
circulations `1, 2, 3`. Every actual self Gauss writhe vanishes by coplanarity, the
off-diagonal pairing vanishes, so the fully geometric centerline helicity is exactly
zero, and the rescaled suppression bound holds with the numeric weight `7/18`. -/
example : |centerlineHelicityGaussSelf (![1, 2, 3]) concentricCircle
      / (∑ i, (![1, 2, 3] : Fin 3 → ℝ) i) ^ 2
    - pairLinkingGauss (![1, 2, 3]) concentricCircle
      / (∑ i, (![1, 2, 3] : Fin 3 → ℝ) i) ^ 2|
    ≤ 5 * (7 / 18) := by
  have hne : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp at h2
  have hcd : ∀ i, ContDiff ℝ 1 (concentricCircle i) := fun i => contDiff_concentricCircle i
  have hplanar : ∀ i s, dot3 (![0, 0, 1] : Fin 3 → ℝ) (concentricCircle i s) = 0 :=
    fun i s => planar_concentricCircle i s
  have hw : ∀ i, gaussWrithe (concentricCircle i) = 0 := fun i =>
    gaussLinking_coplanar_eq_zero (concentricCircle i) (concentricCircle i) ![0, 0, 1] hne 0
      (hplanar i) (hplanar i) (hcd i) (hcd i)
  have hkz : ∀ (i : Fin 3) (p : ℝ × ℝ),
      writheKernel (concentricCircle i) p.1 p.2 = 0 := fun i p =>
    writheKernel_planar_eq_zero (concentricCircle i) ![0, 0, 1] hne 0 (hplanar i) (hcd i)
      p.1 p.2
  have hint : ∀ i, Integrable (fun p : ℝ × ℝ => writheKernel (concentricCircle i) p.1 p.2)
      gaussMeasure := fun i =>
    Integrable.congr (f := (0 : ℝ × ℝ → ℝ))
      (integrable_zero (α := ℝ × ℝ) (ε' := ℝ) (μ := gaussMeasure))
      (Filter.Eventually.of_forall fun p => (hkz i p).symm)
  have hκ : ∑ i, (![1, 2, 3] : Fin 3 → ℝ) i ≠ 0 := by
    have hsum6 : ∑ i, (![1, 2, 3] : Fin 3 → ℝ) i = 6 := by
      norm_num [Fin.sum_univ_three]
    rw [hsum6]
    norm_num
  refine le_trans
    (rescaled_centerlineGaussSelf_near_linking (W := 5) (![1, 2, 3]) concentricCircle hκ
      hint (fun i => by rw [hw i, abs_zero]; norm_num)) ?_
  have hweight : (∑ i, (![1, 2, 3] : Fin 3 → ℝ) i ^ 2)
      / (∑ i, (![1, 2, 3] : Fin 3 → ℝ) i) ^ 2 = 7 / 18 := by
    norm_num [Fin.sum_univ_three]
  rw [hweight]

private noncomputable def stageCirculation (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  1 + (i.val : ℝ) / ((n : ℝ) + 1)

private theorem stageCirculation_mem (n : ℕ) (i : Fin (n + 1)) :
    (1 : ℝ) ≤ stageCirculation n i ∧ stageCirculation n i ≤ 2 := by
  have h1 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have h2 : (i.val : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlow : (0 : ℝ) ≤ (i.val : ℝ) / ((n : ℝ) + 1) := div_nonneg h1 hpos.le
  have hhigh : (i.val : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one hpos).2 (by linarith)
  unfold stageCirculation
  constructor <;> linarith

private theorem stageCirculation_sum_pos (n : ℕ) :
    (0 : ℝ) < ∑ i : Fin (n + 1), stageCirculation n i := by
  have h1 : ((n : ℝ) + 1) ≤ ∑ i : Fin (n + 1), stageCirculation n i := by
    calc (n : ℝ) + 1 = ∑ i : Fin (n + 1), 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ i : Fin (n + 1), stageCirculation n i :=
          Finset.sum_le_sum fun i _ => (stageCirculation_mem n i).1
  exact lt_of_lt_of_le (by positivity) h1

set_option maxHeartbeats 500000 in
/-- The non-uniform classical limit applied to an actual geometric bundle sequence:
bundles of `n + 1` concentric planar circles with comparable non-uniform circulations
`stageCirculation n i = 1 + i / (n + 1) ∈ [1, 2]`, whose pairing data are identically
zero, so the rescaled centerline helicity sequence is constantly zero and converges
to `0`. -/
example : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hfun : (fun n : ℕ => 2 / ((n : ℝ) + 1))
        = (fun m : ℕ => 2 / (m : ℝ)) ∘ (fun a : ℕ => a + 1) := by
      funext n
      simp only [Function.comp_def]
      push_cast
      ring
    rw [hfun]
    exact (tendsto_const_div_atTop_nhds_zero_nat 2).comp (tendsto_add_atTop_nat 1)
  refine classical_limit_nonuniform (W := 0) le_rfl
    (fun n => 2 / ((n : ℝ) + 1)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) hs 0
    tendsto_const_nhds ?_
  intro n
  have hne : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp at h2
  have i0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  have hplanar : ∀ (s : ℝ),
      dot3 (![0, 0, 1] : Fin 3 → ℝ) ((2 : ℝ) • circleCurve s) = 0 := by
    intro s
    simp [circleCurve, dot3]
  have hcd : ContDiff ℝ 1 (fun s => (2 : ℝ) • circleCurve s) :=
    ((contDiff_const (c := (2 : ℝ))).smul contDiff_regressionCircle).of_le (by norm_num)
  have hw : gaussWrithe (fun s => (2 : ℝ) • circleCurve s) = 0 :=
    gaussLinking_coplanar_eq_zero _ _ ![0, 0, 1] hne 0 hplanar hplanar hcd hcd
  have hpair : pairLinkingGauss (stageCirculation n)
      (fun _ : Fin (n + 1) => (fun s => (2 : ℝ) • circleCurve s)) = 0 :=
    pairLinkingGauss_coplanar_eq_zero _ _ ![0, 0, 1] hne 0
      (fun i s => hplanar s) (fun i => hcd)
  have hzero : centerlineHelicityGaussSelf (stageCirculation n)
      (fun _ : Fin (n + 1) => (fun s => (2 : ℝ) • circleCurve s)) = 0 := by
    rw [centerlineHelicityGaussSelf_eq, hpair]
    simp [writheGaussPart, hw]
  have hsize := selfWeight_le_of_comparable (stageCirculation n) (c := 1) (C := 2)
    (by norm_num)
    (fun i => (stageCirculation_mem n i).1)
    (fun i => (stageCirculation_mem n i).2)
    (ne_of_gt (stageCirculation_sum_pos n))
  have hint : ∀ i : Fin (n + 1), Integrable
      (fun p : ℝ × ℝ =>
        writheKernel ((fun _ : Fin (n + 1) => (fun s => (2 : ℝ) • circleCurve s)) i) p.1 p.2)
      gaussMeasure := by
    intro i
    have hbeta : ((fun _ : Fin (n + 1) => (fun s => (2 : ℝ) • circleCurve s)) i)
        = (fun s => (2 : ℝ) • circleCurve s) := rfl
    rw [hbeta]
    refine Integrable.congr (f := (0 : ℝ × ℝ → ℝ))
      (integrable_zero (α := ℝ × ℝ) (ε' := ℝ) (μ := gaussMeasure)) ?_
    exact Filter.Eventually.of_forall fun p =>
      (writheKernel_planar_eq_zero _ ![0, 0, 1] hne 0 hplanar hcd p.1 p.2).symm
  exact ⟨stageCirculation n,
    fun _ => (fun s => (2 : ℝ) • circleCurve s),
    ne_of_gt (stageCirculation_sum_pos n), hint,
    fun i => by simp [hw],
    by simpa using hsize,
    by rw [hzero, zero_div], by rw [hpair, zero_div]⟩

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.classical_limit_nonuniform
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.rescaled_centerlineGaussSelf_near_linking
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.selfWeight_const_eq_inv_card

/-! ### Band-control consumers -/

private theorem norm_derivVec_circleCurve_le_one (u : ℝ) :
    ‖(![-Real.sin u, Real.cos u, 0] : Fin 3 → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  fin_cases i <;> simp [Real.abs_sin_le_one, Real.abs_cos_le_one]

private theorem norm_deriv_circleCurve_le_one (u : ℝ) : ‖deriv circleCurve u‖ ≤ 1 := by
  rw [deriv_circleCurve]
  exact norm_derivVec_circleCurve_le_one u

private theorem hasDerivAt_deriv_circleCurve (u : ℝ) :
    HasDerivAt (deriv circleCurve) ![-Real.cos u, -Real.sin u, 0] u := by
  rw [show deriv circleCurve = fun w => ![-Real.sin w, Real.cos w, 0] from
    funext deriv_circleCurve, hasDerivAt_pi]
  intro j
  fin_cases j
  · exact (Real.hasDerivAt_sin u).neg
  · exact Real.hasDerivAt_cos u
  · exact hasDerivAt_const u 0

private theorem deriv2_circleCurve (u : ℝ) :
    deriv (deriv circleCurve) u = ![-Real.cos u, -Real.sin u, 0] :=
  (hasDerivAt_deriv_circleCurve u).deriv

private theorem norm_deriv2Vec_circleCurve_le_one (u : ℝ) :
    ‖(![-Real.cos u, -Real.sin u, 0] : Fin 3 → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  fin_cases i <;> simp [Real.abs_sin_le_one, Real.abs_cos_le_one]

private theorem norm_deriv2_circleCurve_le_one (u : ℝ) :
    ‖deriv (deriv circleCurve) u‖ ≤ 1 := by
  rw [deriv2_circleCurve]
  exact norm_deriv2Vec_circleCurve_le_one u

/-- Closed-circle instance of the explicit near-diagonal band control: a genuinely closed
`C²` centerline with speed bound `B = 1` and curvature bound `M = 1`, at band width
`δ = 1 / 8` (so `3 * M * B * δ = 3 / 8 ≤ τ ^ 2 / 2`). -/
private theorem band_circle_le :
    |gaussWrithe circleCurve - writheBand circleCurve (1 / 8)|
      ≤ 324 * 1 ^ 4 * 1 ^ 2 / (π * 1 ^ 6) * (2 * π * (2 * (1 / 8 : ℝ))) := by
  refine abs_gaussWrithe_sub_writheBand_le_of_closed_regular circleCurve
    contDiff_regressionCircle periodic_regressionCircle injOn_regressionCircle
    regular_regressionCircle (by norm_num) ?_ norm_deriv_circleCurve_le_one
    norm_deriv2_circleCurve_le_one (by norm_num) (by norm_num)
  intro u
  rw [unitTangent_regressionCircle u]
  norm_num

/-- The explicit constant in the circle instance is numerically `162`. -/
example : |gaussWrithe circleCurve - writheBand circleCurve (1 / 8)| ≤ 162 := by
  have h := band_circle_le
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have heq : 324 * 1 ^ 4 * 1 ^ 2 / (π * 1 ^ 6) * (2 * π * (2 * (1 / 8 : ℝ))) = 162 := by
    have h1 : 2 * π * (2 * (1 / 8 : ℝ)) = π / 2 := by ring
    have h2 : π * (1 : ℝ) ^ 6 = π := by ring
    rw [h1, h2]
    field_simp
    ring
  rw [heq] at h
  exact h

/-- The planar circle realizes both sides of the band split as zero, so the explicit
bound, while genuine, is not tight on planar curves. -/
example : gaussWrithe circleCurve - writheBand circleCurve (1 / 8) = 0 := by
  have hne : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp at h2
  have hper : ∀ s : ℝ, dot3 (![0, 0, 1] : Fin 3 → ℝ) (circleCurve s) = 0 :=
    fun s => by simp [dot3, circleCurve]
  have hcd : ContDiff ℝ 1 circleCurve := contDiff_regressionCircle.of_le (by norm_num)
  rw [writheBand_coplanar_eq_zero circleCurve ![0, 0, 1] hne 0 hper hcd, sub_zero]
  exact gaussLinking_coplanar_eq_zero circleCurve circleCurve ![0, 0, 1] hne 0 hper hper
    hcd hcd

/-- Straight-arc consumer via the injectivity route: curvature `M = 0` makes the explicit
bound degenerate to `0`, so the band-regularized writhe equals the full self Gauss
integral identically on a straight arc. -/
example : |gaussWrithe (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
      - writheBand (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) (1 / 2)|
      ≤ 324 * 1 ^ 4 * 0 ^ 2 / (π * 1 ^ 6) * (2 * π * (2 * (1 / 2 : ℝ))) := by
  have hinj : ∀ s ∈ Set.Icc (0 : ℝ) (2 * π), ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) s
        = (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ)) t → s = t := by
    intro s _ t _ he
    have h0 := congrFun he 0
    simp at h0
    exact h0
  exact abs_gaussWrithe_sub_writheBand_le_of_regular (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
    contDiff_lineCurve (by norm_num)
    (fun u => by rw [deriv_lineCurve u]; simp [dot3])
    (fun u => by
      rw [deriv_lineCurve u]
      exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => by
        fin_cases i <;> simp)
    (fun u => by
      have hfe : deriv (fun w : ℝ => (![w, 0, 0] : Fin 3 → ℝ))
          = fun _ : ℝ => (![1, 0, 0] : Fin 3 → ℝ) := funext deriv_lineCurve
      rw [hfe, deriv_const]
      simp)
    hinj (by norm_num) (by norm_num)

private theorem deriv_scaledCircle (c : ℝ) (u : ℝ) :
    deriv (fun s => c • circleCurve s) u = c • deriv circleCurve u :=
  ((hasDerivAt_circleCurve u).const_smul c).deriv.trans (by rw [deriv_circleCurve])

private theorem derivSq_scaledCircle {c : ℝ} (hc : 1 ≤ c) (u : ℝ) :
    (1 : ℝ) ^ 2 ≤ dot3 (deriv (fun s => c • circleCurve s) u)
      (deriv (fun s => c • circleCurve s) u) := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hsq : (1 : ℝ) ≤ c * c := by nlinarith
  simp [deriv_scaledCircle, dot3_smul_left, dot3_smul_right, unitTangent_regressionCircle]
  linarith

private theorem hB_scaledCircle {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2) (u : ℝ) :
    ‖deriv (fun s => c • circleCurve s) u‖ ≤ 2 := by
  rw [deriv_scaledCircle, norm_smul, Real.norm_eq_abs]
  calc |c| * ‖deriv circleCurve u‖ ≤ |c| * 1 :=
        mul_le_mul_of_nonneg_left (norm_deriv_circleCurve_le_one u) (abs_nonneg c)
    _ = |c| := mul_one _
    _ ≤ 2 := by
      rw [abs_of_nonneg hc0]
      exact hc

private theorem hM_scaledCircle {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2) (u : ℝ) :
    ‖deriv (deriv (fun s => c • circleCurve s)) u‖ ≤ 2 := by
  have h1 : deriv (fun s => c • circleCurve s) = fun s => c • deriv circleCurve s :=
    funext fun s => deriv_scaledCircle c s
  rw [h1]
  have h2 : deriv (fun s => c • deriv circleCurve s) u = c • ![-Real.cos u, -Real.sin u, 0] :=
    ((hasDerivAt_deriv_circleCurve u).const_smul c).deriv
  rw [h2, norm_smul, Real.norm_eq_abs]
  calc |c| * ‖(![-Real.cos u, -Real.sin u, 0] : Fin 3 → ℝ)‖ ≤ |c| * 1 :=
        mul_le_mul_of_nonneg_left (norm_deriv2Vec_circleCurve_le_one u) (abs_nonneg c)
    _ = |c| := mul_one _
    _ ≤ 2 := by
      rw [abs_of_nonneg hc0]
      exact hc

private noncomputable def concentricBundle : Fin 2 → ℝ → (Fin 3 → ℝ) :=
  fun i s => ((i.val : ℝ) + 1) • circleCurve s

private theorem hc_concentricBundle (i : Fin 2) :
    (1 : ℝ) ≤ ((i.val : ℝ) + 1) ∧ ((i.val : ℝ) + 1) ≤ 2 := by
  have h1 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have h2 : (i.val : ℝ) ≤ 1 := by
    have hn : i.val ≤ 1 := Nat.lt_succ_iff.mp i.isLt
    exact_mod_cast hn
  constructor <;> linarith

private theorem contDiff_concentricBundle (i : Fin 2) :
    ContDiff ℝ 2 (concentricBundle i) :=
  (contDiff_const (c := ((i.val : ℝ) + 1))).smul contDiff_regressionCircle

private theorem hτ_concentricBundle (i : Fin 2) (u : ℝ) :
    (1 : ℝ) ^ 2 ≤ dot3 (deriv (concentricBundle i) u) (deriv (concentricBundle i) u) :=
  derivSq_scaledCircle (hc_concentricBundle i).1 u

private theorem hB_concentricBundle (i : Fin 2) (u : ℝ) :
    ‖deriv (concentricBundle i) u‖ ≤ 2 :=
  hB_scaledCircle (by linarith [(hc_concentricBundle i).1]) (hc_concentricBundle i).2 u

private theorem hM_concentricBundle (i : Fin 2) (u : ℝ) :
    ‖deriv (deriv (concentricBundle i)) u‖ ≤ 2 :=
  hM_scaledCircle (by linarith [(hc_concentricBundle i).1]) (hc_concentricBundle i).2 u

private theorem hperCircle (s : ℝ) :
    dot3 (![0, 0, 1] : Fin 3 → ℝ) (circleCurve s) = 0 := by
  simp [dot3, circleCurve]

private theorem hint_concentricBundle (i : Fin 2) :
    Integrable (fun p : ℝ × ℝ => writheKernel (concentricBundle i) p.1 p.2) gaussMeasure := by
  have hne : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp at h2
  have hper : ∀ s : ℝ, dot3 (![0, 0, 1] : Fin 3 → ℝ) (concentricBundle i s) = 0 := by
    intro s
    have hsm : concentricBundle i s = ((i.val : ℝ) + 1) • circleCurve s := rfl
    rw [hsm, dot3_smul_right, hperCircle s]
    ring
  refine Integrable.congr (f := fun _ : ℝ × ℝ => (0 : ℝ))
    (integrable_zero (α := ℝ × ℝ) (ε' := ℝ) (μ := gaussMeasure)) ?_
  exact Filter.Eventually.of_forall fun p =>
    (writheKernel_planar_eq_zero (concentricBundle i) ![0, 0, 1] hne 0 hper
      ((contDiff_const (c := ((i.val : ℝ) + 1))).smul
        (contDiff_regressionCircle.of_le (by norm_num))) p.1 p.2).symm

/-- Bundle-level consumer: two concentric circles with radii `1, 2` (speeds bounded by
`B = 2`, curvatures by `M = 2`) and non-uniform circulations `![1, 2]`, at band width
`δ = 1 / 24` (so `3 * M * B * δ = 1 / 2 ≤ τ ^ 2 / 2`). The band-truncated helicity
differs from the fully geometric centerline helicity by at most the sum of squared
circulations times the explicit linear-in-`δ` constant. -/
example : |truncatedGaussHelicity (![1, 2] : Fin 2 → ℝ) concentricBundle (1 / 24)
      - centerlineHelicityGaussSelf (![1, 2] : Fin 2 → ℝ) concentricBundle|
      ≤ (∑ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i ^ 2)
        * (324 * 2 ^ 4 * 2 ^ 2 / (π * 1 ^ 6)) * (2 * π * (2 * (1 / 24 : ℝ))) :=
  abs_truncatedGaussHelicity_sub_centerlineHelicityGaussSelf_le (![1, 2] : Fin 2 → ℝ)
    concentricBundle (by norm_num) (fun i => contDiff_concentricBundle i)
    (fun i u => hτ_concentricBundle i u) (fun i u => hB_concentricBundle i u)
    (fun i u => hM_concentricBundle i u) (fun i => hint_concentricBundle i)
    (by norm_num) (by norm_num)

/-- Normalized consumer on the same bundle: dividing by the squared total circulation
`(1 + 2)² = 9`, the truncation error is governed by the inverse effective bundle size
`(1² + 2²) / 9 = 5 / 9` times the same explicit constant. -/
example : |truncatedGaussHelicity (![1, 2] : Fin 2 → ℝ) concentricBundle (1 / 24)
        / (∑ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i) ^ 2
      - centerlineHelicityGaussSelf (![1, 2] : Fin 2 → ℝ) concentricBundle
        / (∑ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i) ^ 2|
      ≤ ((∑ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i ^ 2)
          / (∑ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i) ^ 2)
        * (324 * 2 ^ 4 * 2 ^ 2 / (π * 1 ^ 6)) * (2 * π * (2 * (1 / 24 : ℝ))) := by
  have hs : (∑ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i) = 3 := by
    simp
    norm_num
  refine abs_rescaled_truncatedGaussHelicity_sub_le (![1, 2] : Fin 2 → ℝ)
    concentricBundle (by norm_num) (fun i => contDiff_concentricBundle i)
    (fun i u => hτ_concentricBundle i u) (fun i u => hB_concentricBundle i u)
    (fun i u => hM_concentricBundle i u) (fun i => hint_concentricBundle i)
    (by norm_num) (by norm_num) ?_
  rw [hs]
  norm_num

/-! ### Continuous-vorticity Biot–Savart consumers -/

private def unitBox : Set (Fin 3 → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

private def farBox : Set (Fin 3 → ℝ) := Set.pi Set.univ fun _ => Set.Icc (3 : ℝ) 4

private theorem hmeasUB : MeasurableSet unitBox :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc

private theorem hmeasFB : MeasurableSet farBox :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc

private theorem volume_unitBox_ne_top : volume unitBox ≠ ⊤ := by
  rw [unitBox, Set.pi_univ_Icc, Real.volume_Icc_pi]
  simp

private theorem volume_farBox_ne_top : volume farBox ≠ ⊤ := by
  rw [farBox, Set.pi_univ_Icc, Real.volume_Icc_pi]
  simp

/-- The characteristic function of a measurable box times the vertical unit vector: the
standing bounded-support parallel field. -/
private noncomputable def boxField (s : Set (Fin 3 → ℝ)) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fun x => s.indicator (fun _ => (1 : ℝ)) x • (![0, 0, 1] : Fin 3 → ℝ)

private theorem hm_boxField {s : Set (Fin 3 → ℝ)} (hm : MeasurableSet s) :
    Measurable fun x => s.indicator (fun _ => (1 : ℝ)) x • (![0, 0, 1] : Fin 3 → ℝ) := by
  have h1 : Measurable fun _ : Fin 3 → ℝ => (1 : ℝ) := measurable_const
  have h2 : Measurable fun _ : Fin 3 → ℝ => (![0, 0, 1] : Fin 3 → ℝ) := measurable_const
  exact (h1.indicator hm).smul h2

private theorem hgi_boxField {s : Set (Fin 3 → ℝ)} (hm : MeasurableSet s)
    (hfin : volume s ≠ ⊤) :
    Integrable fun x => s.indicator (fun _ => (1 : ℝ)) x :=
  (integrableOn_const (C := (1 : ℝ)) hfin).integrable_indicator hm

private theorem hin_boxField {s : Set (Fin 3 → ℝ)} (hm : MeasurableSet s)
    (hfin : volume s ≠ ⊤) :
    Integrable (boxField s) :=
  integrable_smul_const_field (![0, 0, 1]) ((measurable_const.indicator hm))
    (hgi_boxField hm hfin)

private theorem boxInd_zero {s : Set (Fin 3 → ℝ)} {x : Fin 3 → ℝ} (h : x ∉ s) :
    s.indicator (fun _ => (1 : ℝ)) x = 0 := by simp [h]

private theorem boxField_eq_zero {s : Set (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (h : x ∉ s) : boxField s x = 0 := by
  show s.indicator (fun _ => (1 : ℝ)) x • (![0, 0, 1] : Fin 3 → ℝ) = 0
  rw [boxInd_zero h, zero_smul]

private theorem boxField_support {s : Set (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (h : boxField s x ≠ 0) : x ∈ s := by
  by_contra hmem
  exact h (boxField_eq_zero hmem)

/-- The box field is genuinely nonzero at the center of the box, so the vanishing and
pairing consumers below are non-degenerate. -/
private theorem boxField_unitBox_center :
    boxField unitBox ![1 / 2, 1 / 2, 1 / 2] = (![0, 0, 1] : Fin 3 → ℝ) := by
  have hmem : ![1 / 2, 1 / 2, 1 / 2] ∈ unitBox := by
    simp only [unitBox, Set.mem_pi]
    intro i _
    fin_cases i <;> simp [Set.mem_Icc] <;> norm_num
  show unitBox.indicator (fun _ => (1 : ℝ)) ![1 / 2, 1 / 2, 1 / 2]
      • (![0, 0, 1] : Fin 3 → ℝ) = _
  rw [Set.indicator_of_mem (f := fun _ => (1 : ℝ)) hmem, one_smul]

example : boxField unitBox ![1 / 2, 1 / 2, 1 / 2] ≠ 0 := by
  intro h
  have h2 := congrFun (boxField_unitBox_center.symm.trans h) 2
  simp at h2

/-- The truncated Biot–Savart helicity of a parallel field vanishes identically: a
non-degenerate bounded-support consumer at truncation level `δ = 1 / 2`. -/
example : bsHelicityTrunc (boxField unitBox) (1 / 2) = 0 := by
  refine bsHelicityTrunc_parallel_eq_zero (unitBox.indicator (fun _ => (1 : ℝ)))
    (![0, 0, 1]) (measurable_const.indicator hmeasUB) ?_ (by norm_num)
  exact hin_boxField hmeasUB volume_unitBox_ne_top

/-- The two boxes are `2`-separated in chord length. -/
private theorem sep_unitBox_farBox : ∀ x ∈ unitBox, ∀ y ∈ farBox,
    (2 : ℝ) ≤ euclideanLength (x - y) := by
  intro x hx y hy
  have hx0 := Set.mem_pi.mp hx 0 (Set.mem_univ 0)
  have hy0 := Set.mem_pi.mp hy 0 (Set.mem_univ 0)
  obtain ⟨hx01, hx02⟩ := Set.mem_Icc.mp hx0
  obtain ⟨hy01, hy02⟩ := Set.mem_Icc.mp hy0
  have hle : (2 : ℝ) ≤ |(x - y) 0| := by
    rw [show (x - y) 0 = x 0 - y 0 from rfl, abs_of_nonpos (by linarith)]
    linarith
  exact hle.trans ((abs_le_norm_coord (x - y) 0).trans (norm_le_euclideanLength (x - y)))

/-- Separated-box consumer of the explicit pairing bound: a parallel field on the unit
box paired with one on the `[3, 4]` box changes by at most the `d = 2` separated
constant `3 / (2π d²)` times the two `L¹` norms, when the first field is dropped
entirely. -/
example : |crossPairing (boxField unitBox) (boxField farBox)
      - crossPairing (fun _ => (0 : Fin 3 → ℝ)) (boxField farBox)|
    ≤ 3 / (2 * π * 2 ^ 2) * (∫ x, ‖boxField unitBox x - (fun _ => (0 : Fin 3 → ℝ)) x‖)
        * ∫ y, ‖boxField farBox y‖ := by
  refine abs_crossPairing_sub_le (d := 2) (by norm_num) unitBox farBox
    (hm_boxField hmeasUB) measurable_const (hm_boxField hmeasFB)
    (fun _ h => boxField_support h) (fun _ hx => absurd rfl hx)
    (fun _ h => boxField_support h) sep_unitBox_farBox
    (hin_boxField hmeasUB volume_unitBox_ne_top)
    (integrable_zero (α := Fin 3 → ℝ) (ε' := Fin 3 → ℝ) (μ := volume))
    (hin_boxField hmeasFB volume_farBox_ne_top)

/-- `L¹`-pairing-continuity consumer: a bounded-support family constant in `i`
(trivially `L¹`-convergent) still discharges the full hypothesis stack —
measurability, support containment, `2`-separation, and integrability of both
fields — so the pairing converges. -/
example : Tendsto (fun _ : ℕ => crossPairing (boxField unitBox) (boxField farBox)) atTop
      (𝓝 (crossPairing (boxField unitBox) (boxField farBox))) := by
  refine tendsto_crossPairing (fun _ : ℕ => boxField unitBox) (boxField unitBox)
    (boxField farBox) (d := 2) (by norm_num) unitBox farBox
    (fun _ => hm_boxField hmeasUB) (hm_boxField hmeasUB) (hm_boxField hmeasFB)
    (fun _ _ h => boxField_support h) (fun _ h => boxField_support h)
    (fun _ h => boxField_support h) sep_unitBox_farBox
    (fun _ => hin_boxField hmeasUB volume_unitBox_ne_top) (hin_boxField hmeasUB volume_unitBox_ne_top) (hin_boxField hmeasFB volume_farBox_ne_top) ?_
  have h0 : ∀ i : ℕ,
      ∫ x, ‖(fun _ : ℕ => boxField unitBox) i x - boxField unitBox x‖ = 0 := by
    intro i
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [sub_self, norm_zero]), integral_zero]
  rw [funext h0]
  exact tendsto_const_nhds

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.measure_gaussBand_le
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.abs_gaussWrithe_sub_writheBand_le
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.abs_gaussWrithe_sub_writheBand_le_of_closed_regular
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.abs_truncatedGaussHelicity_sub_centerlineHelicityGaussSelf_le
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.abs_rescaled_truncatedGaussHelicity_sub_le
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.crossPairing_sub_eq
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.abs_crossPairing_sub_le
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_crossPairing
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.bsHelicityTrunc_eq
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.bsHelicityTrunc_parallel_eq_zero
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_bsHelicityTrunc
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.integrable_smul_const_field

/-- A continuous tent field is nonzero at the origin and has convergent
Biot–Savart helicity truncations without a separate kernel assumption. -/
example :
    let ω : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun x => max (1 - ‖x‖) 0 • ![0, 0, 1]
    ω 0 ≠ 0 ∧ Tendsto (fun δ => bsHelicityTrunc ω δ) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (crossPairing ω ω)) := by
  let ω : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun x => max (1 - ‖x‖) 0 • ![0, 0, 1]
  have hc : Continuous ω :=
    ((continuous_const.sub continuous_norm).max continuous_const).smul continuous_const
  have hsub : Function.support ω ⊆ Metric.closedBall (0 : Fin 3 → ℝ) 1 := by
    intro x hx
    by_contra! h
    have hx' : 1 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using h
    exact hx (by simp [ω, max_eq_right (sub_nonpos.mpr hx'.le)])
  have hcompact : HasCompactSupport ω :=
    (isCompact_closedBall (0 : Fin 3 → ℝ) 1).of_isClosed_subset isClosed_closure
      (closure_minimal hsub Metric.isClosed_closedBall)
  refine ⟨?_, tendsto_bsHelicityTrunc_of_continuous_compactSupport hc hcompact⟩
  intro h
  have he := congrFun h (2 : Fin 3)
  norm_num [ω] at he

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.integrable_bsPairKernel_of_bounded
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_bsHelicityTrunc_of_continuous_compactSupport

/-- A shrinking sequence of nonzero box fields has convergent mixed and
self-pairings, with the two inputs supported on the same box. -/
example :
    Tendsto (fun n : ℕ => crossPairing (boxField unitBox)
      (fun x => (1 / ((n : ℝ) + 1)) • boxField unitBox x)) atTop
      (𝓝 (crossPairing (boxField unitBox) (fun _ => (0 : Fin 3 → ℝ)))) ∧
    Tendsto (fun n : ℕ => crossPairing
      (fun x => (1 / ((n : ℝ) + 1)) • boxField unitBox x)
      (fun x => (1 / ((n : ℝ) + 1)) • boxField unitBox x)) atTop
      (𝓝 (crossPairing (fun _ => (0 : Fin 3 → ℝ)) (fun _ => (0 : Fin 3 → ℝ)))) := by
  let F := fun n : ℕ => fun x : Fin 3 → ℝ => (1 / ((n : ℝ) + 1)) • boxField unitBox x
  have hmeas : Measurable (boxField unitBox) := hm_boxField hmeasUB
  have hInt : Integrable (boxField unitBox) := hin_boxField hmeasUB volume_unitBox_ne_top
  have hMax (x : Fin 3 → ℝ) : ‖boxField unitBox x‖ ≤ 1 := by
    by_cases hx : x ∈ unitBox
    · rw [boxField, Set.indicator_of_mem hx, one_smul]
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
      intro j
      fin_cases j <;> norm_num
    · rw [boxField_eq_zero hx, norm_zero]
      norm_num
  have hIntegrable (n : ℕ) : Integrable (F n) := hInt.smul (1 / ((n : ℝ) + 1))
  have hFmeas (n : ℕ) : Measurable (F n) := by
    have hconst : Measurable (fun _ : Fin 3 → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) := measurable_const
    exact hconst.smul hmeas
  have hZero : Integrable (fun _ : Fin 3 → ℝ => (0 : Fin 3 → ℝ)) :=
    integrable_zero (α := Fin 3 → ℝ) (ε' := Fin 3 → ℝ) (μ := volume)
  have hExpr : (fun n : ℕ => ∫ y, ‖F n y - (fun _ => (0 : Fin 3 → ℝ)) y‖) =
      fun n : ℕ => (1 / ((n : ℝ) + 1)) * ∫ y, ‖boxField unitBox y‖ := by
    funext n
    have hn : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    simp only [F, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn, integral_const_mul]
  have hL1 : Tendsto (fun n : ℕ => ∫ y, ‖F n y - (fun _ => (0 : Fin 3 → ℝ)) y‖)
      atTop (𝓝 0) := by
    rw [hExpr]
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul tendsto_const_nhds
  have hUniform (n : ℕ) (x : Fin 3 → ℝ) : ‖F n x‖ ≤ 1 := by
    have hNonneg : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hLe : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      simpa only [one_mul] using le_add_of_nonneg_left (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    simp only [F, norm_smul, Real.norm_eq_abs, abs_of_nonneg hNonneg]
    simpa only [one_mul] using mul_le_mul hLe (hMax x) (norm_nonneg _) (zero_le_one' ℝ)
  exact ⟨tendsto_crossPairing_right_of_bounded F hmeas measurable_const
      hFmeas hInt hZero hIntegrable hMax hL1,
    tendsto_crossPairing_self_of_bounded F measurable_const hFmeas hZero hIntegrable
      (fun _ => by simp) hUniform hL1⟩

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_crossPairing_right_of_bounded
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.crossPairing_comm
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_crossPairing_self_of_bounded

/-- Two perpendicular directions separated by a unit chord have nonzero
signed interaction, and a cutoff of two reduces it by a factor of eight. -/
example :
    let p : VorticityElement := (0, ⟨![1, 0, 0], by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
      intro j
      fin_cases j <;> norm_num⟩)
    let q : VorticityElement := (![0, 0, 1], ⟨![0, 1, 0], by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
      intro j
      fin_cases j <;> norm_num⟩)
    gaussSoftKernel 0 p q = -1 / (4 * Real.pi) ∧
      gaussSoftKernel 2 p q = -1 / (32 * Real.pi) := by
  dsimp only
  have hl : euclideanLength ((0 : Fin 3 → ℝ) - ![0, 0, 1]) = 1 := by
    norm_num [euclideanLength, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [gaussSoftKernel, gaussSoftKernel, hl]
  norm_num [dot3, cross3, max_eq_right, max_eq_left]
  rw [show (4 : ℝ) * Real.pi * 8 = 32 * Real.pi by ring]

#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.integral_orientedVorticityMeasure_eq_crossPairing
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.integral_orientedBundle_eq_helicity
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_orientedGaussSelf
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_finiteGaussFullPairing
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.concentratedBundle_not_tendsto_zero_helicity
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_rescaledCenterline_crossPairing
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.setIntegral_rescaledBundle_nearPairs_le
#print axioms Qatlib.Papers.SuperfluidHel18.CenterlineCL.tendsto_rescaledCenterline_of_offNear
