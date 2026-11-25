/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.HelicityTransport

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Energy-normalized helicity of the Bateman power family

[Kedia2013TyingKnots], conserved quantities on page 150404-3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The stereographic latitude and phase fluxes give two whole-space
integration-by-parts identities. They relate the actual initial energy
and helicity integrals without introducing an angular coordinate chart.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta complex_rational_pair_unit)
open Filter MeasureTheory Set
open scoped BigOperators

local notation "MomentSpace" => ℝ × ℝ × ℝ

/-! ## The stereographic latitude -/

/-- Coordinate projections of the product Euclidean coordinates. -/
private def coord (j : Fin 3) : MomentSpace →L[ℝ] ℝ :=
  ![ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ),
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))] j

/-- An affine line in the given positive Cartesian direction. -/
private def shift (s : MomentSpace) (i : Fin 3) (h : ℝ) : MomentSpace :=
  s + h • batemanAxis i

/-- At zero displacement the line is at its base point. -/
private theorem shift_zero (s : MomentSpace) (i : Fin 3) : shift s i 0 = s := by
  simp [shift]

/-- The stereographic denominator. -/
private def stereoD (s : MomentSpace) : ℝ :=
  coord 0 s ^ 2 + coord 1 s ^ 2 + coord 2 s ^ 2 + 1

/-- The distance squared from the vertical axis. -/
private def transverseSq (s : MomentSpace) : ℝ :=
  coord 0 s ^ 2 + coord 1 s ^ 2

/-- The first squared complex coordinate on the unit three-sphere. -/
private noncomputable def stereoU (s : MomentSpace) : ℝ :=
  1 - 4 * transverseSq s / stereoD s ^ 2

/-- The denominator is everywhere at least one. -/
private theorem one_le_stereoD (s : MomentSpace) : 1 ≤ stereoD s := by
  unfold stereoD
  nlinarith only [sq_nonneg (coord 0 s), sq_nonneg (coord 1 s), sq_nonneg (coord 2 s)]

/-- The stereographic denominator is strictly positive. -/
private theorem stereoD_pos (s : MomentSpace) : 0 < stereoD s :=
  zero_lt_one.trans_le (one_le_stereoD s)

/-- The sphere latitude formula agrees with the actual squared Bateman
coordinate on the initial slice. -/
private theorem stereoU_eq_alpha (s : MomentSpace) :
    stereoU s = Complex.normSq (rationalAlpha s.1 s.2.1 s.2.2 0) := by
  rcases s with ⟨x, y, z⟩
  have hb : Complex.normSq (rationalBeta x y z 0) =
      4 * (x ^ 2 + y ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 2 := by
    rw [rational_beta_stereographic_zero_time, Complex.normSq_div, Complex.normSq_apply]
    rw [show Complex.normSq ((x ^ 2 + y ^ 2 + z ^ 2 + 1 : ℝ) : ℂ) =
      (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 2 by
        simp [Complex.normSq_apply, pow_two]]
    congr 1
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring
  change 1 - 4 * (x ^ 2 + y ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 2 = _
  rw [← hb]
  linarith only [complex_rational_pair_unit x y z 0]

/-- The second squared Bateman coordinate is the complementary latitude. -/
private theorem one_sub_stereoU_eq_beta (s : MomentSpace) :
    1 - stereoU s = Complex.normSq (rationalBeta s.1 s.2.1 s.2.2 0) := by
  rw [stereoU_eq_alpha]
  linarith only [complex_rational_pair_unit s.1 s.2.1 s.2.2 0]

/-- Both squared coordinates are constrained by the unit sphere. -/
private theorem stereoU_mem (s : MomentSpace) : stereoU s ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [stereoU_eq_alpha]
    exact Complex.normSq_nonneg _
  · have h : 0 ≤ 1 - stereoU s := (one_sub_stereoU_eq_beta s).symm ▸ Complex.normSq_nonneg _
    linarith only [h]

/-- The derivative of the coordinate function along a Cartesian axis. -/
private theorem hasDerivAt_coord_shift (s : MomentSpace) (i j : Fin 3) :
    HasDerivAt (fun h => coord j (shift s i h)) (if i = j then 1 else 0) 0 := by
  have hcoord : coord j (batemanAxis i) = if i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> simp [coord, batemanAxis]
  simpa only [shift, map_add, map_smul, smul_eq_mul, hcoord, one_mul, id_eq] using
    ((hasDerivAt_id (0 : ℝ)).mul_const (if i = j then 1 else 0)).const_add (coord j s)

/-- Derivative of the ambient radius factor on a Cartesian line. -/
private theorem hasDerivAt_stereoD_shift (s : MomentSpace) (i : Fin 3) :
    HasDerivAt (fun h => stereoD (shift s i h)) (2 * coord i s) 0 := by
  have h0 := (hasDerivAt_coord_shift s i 0).fun_pow 2
  have h1 := (hasDerivAt_coord_shift s i 1).fun_pow 2
  have h2 := (hasDerivAt_coord_shift s i 2).fun_pow 2
  have h := ((h0.fun_add h1).fun_add h2).add_const 1
  fin_cases i <;> simpa [stereoD, shift_zero] using h

/-- Cartesian derivative of the transverse squared radius. -/
private def transversePartial (s : MomentSpace) (i : Fin 3) : ℝ :=
  ![2 * coord 0 s, 2 * coord 1 s, 0] i

/-- The explicit transverse derivative agrees with differentiation on a
Cartesian line. -/
private theorem hasDerivAt_transverseSq_shift (s : MomentSpace) (i : Fin 3) :
    HasDerivAt (fun h => transverseSq (shift s i h)) (transversePartial s i) 0 := by
  have h0 := (hasDerivAt_coord_shift s i 0).fun_pow 2
  have h1 := (hasDerivAt_coord_shift s i 1).fun_pow 2
  have h := h0.fun_add h1
  fin_cases i <;> simpa [transverseSq, transversePartial, shift_zero] using h

/-- Cartesian derivative of the stereographic latitude. -/
private noncomputable def latitudePartial (s : MomentSpace) (i : Fin 3) : ℝ :=
  -(4 * transversePartial s i / stereoD s ^ 2) +
    8 * transverseSq s * (2 * coord i s) / stereoD s ^ 3

/-- The latitude derivative follows by the quotient rule. -/
private theorem hasDerivAt_stereoU_shift (s : MomentSpace) (i : Fin 3) :
    HasDerivAt (fun h => stereoU (shift s i h)) (latitudePartial s i) 0 := by
  have hd := stereoD_pos s
  have h := ((hasDerivAt_transverseSq_shift s i).const_mul (4 : ℝ)).fun_div
    ((hasDerivAt_stereoD_shift s i).fun_pow 2) (by rw [shift_zero]; exact pow_ne_zero _ hd.ne')
  refine (h.const_sub (1 : ℝ)).congr_deriv ?_
  simp only [latitudePartial, shift_zero, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
  field_simp [hd.ne']
  ring

/-! ## The latitude and phase fluxes -/

/-- Numerator of the latitude flux, proportional to the spherical gradient
of the squared first complex coordinate. -/
private noncomputable def latitudeNumerator (s : MomentSpace) (i : Fin 3) : ℝ :=
  ![coord 0 s * (transverseSq s - stereoD s / 2),
    coord 1 s * (transverseSq s - stereoD s / 2),
    coord 2 s * transverseSq s] i

/-- Numerator of the flux obtained by rotating the phase of the first
complex coordinate and multiplying by its imaginary part. -/
private def phaseNumerator (s : MomentSpace) (i : Fin 3) : ℝ :=
  ![-2 * coord 0 s * coord 2 s ^ 2, -2 * coord 1 s * coord 2 s ^ 2,
    coord 2 s * (transverseSq s - coord 2 s ^ 2 - 1)] i

/-- Derivatives of each latitude flux numerator in its own direction. -/
private noncomputable def latitudeDiagonal (s : MomentSpace) (i : Fin 3) : ℝ :=
  ![transverseSq s - stereoD s / 2 + coord 0 s ^ 2,
    transverseSq s - stereoD s / 2 + coord 1 s ^ 2, transverseSq s] i

/-- Derivatives of each phase flux numerator in its own direction. -/
private def phaseDiagonal (s : MomentSpace) (i : Fin 3) : ℝ :=
  ![-2 * coord 2 s ^ 2, -2 * coord 2 s ^ 2,
    transverseSq s - 3 * coord 2 s ^ 2 - 1] i

/-- The latitude numerator's diagonal derivative is obtained by the
product rule. -/
private theorem hasDerivAt_latitudeNumerator_shift (s : MomentSpace) (i : Fin 3) :
    HasDerivAt (fun h => latitudeNumerator (shift s i h) i) (latitudeDiagonal s i) 0 := by
  have hS := hasDerivAt_transverseSq_shift s i
  have hD := hasDerivAt_stereoD_shift s i
  have hA := hS.fun_sub (hD.div_const 2)
  fin_cases i
  · refine (hasDerivAt_coord_shift s 0 0).fun_mul hA |>.congr_deriv ?_
    simp [latitudeDiagonal, transversePartial, shift_zero]
    ring
  · refine (hasDerivAt_coord_shift s 1 1).fun_mul hA |>.congr_deriv ?_
    simp [latitudeDiagonal, transversePartial, shift_zero]
    ring
  · simpa [latitudeNumerator, latitudeDiagonal, transversePartial, shift_zero] using
      (hasDerivAt_coord_shift s 2 2).fun_mul hS

/-- The phase numerator's diagonal derivative follows by differentiating
its cubic polynomials in the corresponding coordinates. -/
private theorem hasDerivAt_phaseNumerator_shift (s : MomentSpace) (i : Fin 3) :
    HasDerivAt (fun h => phaseNumerator (shift s i h) i) (phaseDiagonal s i) 0 := by
  have hX := hasDerivAt_coord_shift s i 0
  have hY := hasDerivAt_coord_shift s i 1
  have hZ := hasDerivAt_coord_shift s i 2
  have hS := hasDerivAt_transverseSq_shift s i
  fin_cases i
  · simpa [phaseNumerator, phaseDiagonal, shift_zero] using
      (hX.const_mul (-2 : ℝ)).fun_mul (hZ.fun_pow 2)
  · simpa [phaseNumerator, phaseDiagonal, shift_zero] using
      (hY.const_mul (-2 : ℝ)).fun_mul (hZ.fun_pow 2)
  · refine (hZ.fun_mul ((hS.fun_sub (hZ.fun_pow 2)).sub_const 1)).congr_deriv ?_
    simp [phaseDiagonal, transversePartial, shift_zero]
    ring

/-- The latitude flux derivative paired with any differentiable scalar
multiplier of the latitude. -/
private theorem latitude_flux_sum (s : MomentSpace) (f f' : ℝ) :
    (∑ i : Fin 3, (f' * latitudePartial s i * (latitudeNumerator s i / stereoD s ^ 4) +
      f * (latitudeDiagonal s i / stereoD s ^ 4 -
        4 * latitudeNumerator s i * (2 * coord i s) / stereoD s ^ 5))) =
      (stereoU s * (1 - stereoU s) * f' + (1 - 2 * stereoU s) * f) / stereoD s ^ 3 := by
  have hd := (stereoD_pos s).ne'
  simp [Fin.sum_univ_three, latitudePartial, latitudeNumerator, latitudeDiagonal,
    transversePartial, stereoU]
  field_simp [hd]
  unfold stereoD transverseSq
  ring

/-- The phase flux derivative paired with a latitude multiplier. Its
tangent component along the latitude vanishes. -/
private theorem phase_flux_sum (s : MomentSpace) (f f' : ℝ) :
    (∑ i : Fin 3, (f' * latitudePartial s i * (phaseNumerator s i / stereoD s ^ 4) +
      f * (phaseDiagonal s i / stereoD s ^ 4 -
        4 * phaseNumerator s i * (2 * coord i s) / stereoD s ^ 5))) =
      f * (stereoD s - 2) / stereoD s ^ 4 := by
  have hd := (stereoD_pos s).ne'
  simp [Fin.sum_univ_three, latitudePartial, phaseNumerator, phaseDiagonal, transversePartial]
  field_simp [hd]
  unfold stereoD transverseSq
  ring

/-- The transverse squared radius is between zero and the ambient denominator. -/
private theorem transverseSq_bounds (s : MomentSpace) : 0 ≤ transverseSq s ∧ transverseSq s ≤ stereoD s := by
  unfold transverseSq stereoD
  constructor
  · positivity
  · nlinarith only [sq_nonneg (coord 2 s)]

/-- The square of every coordinate is bounded by the denominator. -/
private theorem coord_sq_le_stereoD (s : MomentSpace) (i : Fin 3) : coord i s ^ 2 ≤ stereoD s := by
  unfold stereoD
  fin_cases i
  · change coord 0 s ^ 2 ≤ _
    nlinarith only [sq_nonneg (coord 1 s), sq_nonneg (coord 2 s)]
  · change coord 1 s ^ 2 ≤ _
    nlinarith only [sq_nonneg (coord 0 s), sq_nonneg (coord 2 s)]
  · change coord 2 s ^ 2 ≤ _
    nlinarith only [sq_nonneg (coord 0 s), sq_nonneg (coord 1 s)]

/-- The denominator also bounds every absolute coordinate. -/
private theorem abs_coord_le_stereoD (s : MomentSpace) (i : Fin 3) : |coord i s| ≤ stereoD s := by
  have h : coord i s ^ 2 + 1 ≤ stereoD s := by
    unfold stereoD
    fin_cases i
    · change coord 0 s ^ 2 + 1 ≤ _
      nlinarith only [sq_nonneg (coord 1 s), sq_nonneg (coord 2 s)]
    · change coord 1 s ^ 2 + 1 ≤ _
      nlinarith only [sq_nonneg (coord 0 s), sq_nonneg (coord 2 s)]
    · change coord 2 s ^ 2 + 1 ≤ _
      nlinarith only [sq_nonneg (coord 0 s), sq_nonneg (coord 1 s)]
  nlinarith only [h, sq_abs (coord i s), sq_nonneg (|coord i s| - 1 / 2)]

/-- Both flux numerators and their diagonal derivatives have uniform
polynomial bounds in the positive stereographic denominator. -/
private theorem flux_bounds (s : MomentSpace) (i : Fin 3) :
    (|latitudeNumerator s i| ≤ 2 * stereoD s ^ 2 ∧ |latitudeDiagonal s i| ≤ 4 * stereoD s) ∧
    (|phaseNumerator s i| ≤ 2 * stereoD s ^ 2 ∧ |phaseDiagonal s i| ≤ 4 * stereoD s) := by
  let d := stereoD s
  have hd : 0 < d := stereoD_pos s
  obtain ⟨hS₀, hS⟩ := transverseSq_bounds s
  have hx := abs_coord_le_stereoD s 0
  have hy := abs_coord_le_stereoD s 1
  have hz := abs_coord_le_stereoD s 2
  have hxs := coord_sq_le_stereoD s 0
  have hys := coord_sq_le_stereoD s 1
  have hzs := coord_sq_le_stereoD s 2
  have hA : |transverseSq s - d / 2| ≤ d := by
    apply abs_le.2
    constructor <;> linarith only [hS₀, hS, hd]
  have hB : |transverseSq s - coord 2 s ^ 2 - 1| ≤ d := by
    unfold d stereoD transverseSq
    apply abs_le.2
    constructor <;> nlinarith only [sq_nonneg (coord 0 s), sq_nonneg (coord 1 s), sq_nonneg (coord 2 s)]
  have one_le_d : 1 ≤ d := one_le_stereoD s
  have hprod {a b : ℝ} (ha : |a| ≤ d) (hb : |b| ≤ d) : |a * b| ≤ 2 * d ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ d * d := mul_le_mul ha hb (abs_nonneg b) hd.le
      _ ≤ 2 * d ^ 2 := by nlinarith only [sq_nonneg d]
  have htwo {a b : ℝ} (ha : |a| ≤ d) (hb : 0 ≤ b) (hbd : b ≤ d) : |-2 * a * b| ≤ 2 * d ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hb]
    norm_num
    calc
      _ ≤ (2 * d) * d := mul_le_mul (by gcongr) hbd hb (by positivity)
      _ = _ := by ring
  have hdiag {a : ℝ} (ha : 0 ≤ a) (had : a ≤ d) : |transverseSq s - d / 2 + a| ≤ 4 * d := by
    apply abs_le.2
    constructor <;> linarith only [ha, had, hS₀, hS, hd]
  have hphase_diag : |transverseSq s - 3 * coord 2 s ^ 2 - 1| ≤ 4 * d := by
    apply abs_le.2
    constructor <;> linarith only [hS₀, hS, hzs, sq_nonneg (coord 2 s), one_le_d]
  fin_cases i
  · exact ⟨⟨hprod hx hA, hdiag (sq_nonneg _) hxs⟩,
      ⟨htwo hx (sq_nonneg _) hzs, by
        change |-2 * coord 2 s ^ 2| ≤ _
        rw [abs_mul, abs_of_nonneg (sq_nonneg (coord 2 s))]
        norm_num
        linarith only [hzs, hd]⟩⟩
  · exact ⟨⟨hprod hy hA, hdiag (sq_nonneg _) hys⟩,
      ⟨htwo hy (sq_nonneg _) hzs, by
        change |-2 * coord 2 s ^ 2| ≤ _
        rw [abs_mul, abs_of_nonneg (sq_nonneg (coord 2 s))]
        norm_num
        linarith only [hzs, hd]⟩⟩
  · exact ⟨⟨hprod hz (by rwa [abs_of_nonneg hS₀]), by
        change |transverseSq s| ≤ _
        rw [abs_of_nonneg hS₀]
        linarith only [hS, hd]⟩, ⟨hprod hz hB, hphase_diag⟩⟩

/-- The latitude derivative is uniformly bounded on physical space. -/
private theorem abs_latitudePartial_le (s : MomentSpace) (i : Fin 3) : |latitudePartial s i| ≤ 24 := by
  let d := stereoD s
  have hOne : 1 ≤ d := one_le_stereoD s
  have hd : 0 < d := stereoD_pos s
  have hD₂ : d ≤ d ^ 2 := by
    calc
      d = d * 1 := by ring
      _ ≤ d * d := mul_le_mul_of_nonneg_left hOne hd.le
      _ = _ := by ring
  have hD₃ : d ^ 2 ≤ d ^ 3 := by
    calc
      _ = d ^ 2 * 1 := by ring
      _ ≤ d ^ 2 * d := mul_le_mul_of_nonneg_left hOne (sq_nonneg d)
      _ = _ := by ring
  have hS : |transversePartial s i| ≤ 2 * d := by
    have h (j : Fin 3) : |2 * coord j s| ≤ 2 * d := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (abs_coord_le_stereoD s j) (by norm_num)
    fin_cases i
    · exact h 0
    · exact h 1
    · change |(0 : ℝ)| ≤ _
      rw [abs_zero]
      positivity
  obtain ⟨hS₀, hSd⟩ := transverseSq_bounds s
  unfold latitudePartial
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_div, abs_div, abs_of_nonneg (sq_nonneg d), abs_of_nonneg (pow_nonneg hd.le 3),
    abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg hS₀]
  have h₁ : 4 * |transversePartial s i| / d ^ 2 ≤ 8 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith only [hS, hD₂]
  have h₂ : 8 * transverseSq s * (2 * |coord i s|) / d ^ 3 ≤ 16 := by
    apply (div_le_iff₀ (by positivity)).2
    calc
      _ ≤ 8 * d * (2 * d) := by
        gcongr
        exact abs_coord_le_stereoD s i
      _ ≤ 16 * d ^ 3 := by nlinarith only [hD₃]
  exact (add_le_add h₁ h₂).trans_eq (by norm_num)

/-! ## Whole-space integration by parts -/

/-- The product Lebesgue volume is additive Haar measure on physical space. -/
private theorem momentSpace_volume_isAddHaarMeasure : (volume : Measure MomentSpace).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
  infer_instance

/-- The common decay profile dominates the fluxes and their first
derivatives in the product Lebesgue measure. -/
private theorem integrable_of_stereo_bound {g : MomentSpace → ℝ}
    (hg : Continuous g) {K : ℝ} (hK : 0 ≤ K) (h : ∀ s, |g s| ≤ K / stereoD s ^ 2) :
    Integrable g := by
  have := momentSpace_volume_isAddHaarMeasure
  have hdim : (Module.finrank ℝ MomentSpace : ℝ) < 4 := by
    simp [Module.finrank_prod]
    norm_num
  have hi : Integrable (fun s : MomentSpace => ((1 + ‖s‖ ^ 2) ^ 2)⁻¹) := by
    convert integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure MomentSpace)) hdim using 2
    rw [show (-4 : ℝ) / 2 = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
    norm_num
  refine (hi.const_mul K).mono' hg.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  refine (h s).trans ?_
  have hD : 1 + ‖s‖ ^ 2 ≤ stereoD s := by
    rcases s with ⟨x, y, z⟩
    change 1 + ‖(x, y, z)‖ ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 1
    simp only [Prod.norm_def, Real.norm_eq_abs, max_def]
    repeat' split
    all_goals
      rw [sq_abs]
      nlinarith only [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hD 2)) hK

/-- The polynomial denominator is smooth on physical space. -/
private theorem contDiff_stereoD : ContDiff ℝ 1 stereoD := by
  unfold stereoD
  exact ((((coord 0).contDiff.pow 2).add ((coord 1).contDiff.pow 2)).add
    ((coord 2).contDiff.pow 2)).add contDiff_const

/-- The polynomial transverse radius is smooth on physical space. -/
private theorem contDiff_transverseSq : ContDiff ℝ 1 transverseSq := by
  unfold transverseSq
  exact ((coord 0).contDiff.pow 2).add ((coord 1).contDiff.pow 2)

/-- The latitude is smooth because the denominator is everywhere positive. -/
private theorem contDiff_stereoU : ContDiff ℝ 1 stereoU := by
  unfold stereoU
  exact contDiff_const.sub ((contDiff_const.mul contDiff_transverseSq).div
    (contDiff_stereoD.pow 2) (fun s => pow_ne_zero _ (stereoD_pos s).ne'))

/-- Every latitude numerator is a smooth polynomial in the coordinates. -/
private theorem contDiff_latitudeNumerator (i : Fin 3) :
    ContDiff ℝ 1 (fun s => latitudeNumerator s i) := by
  have hA := contDiff_transverseSq.sub (contDiff_stereoD.div_const 2)
  fin_cases i
  · exact (coord 0).contDiff.mul hA
  · exact (coord 1).contDiff.mul hA
  · exact (coord 2).contDiff.mul contDiff_transverseSq

/-- Every phase numerator is a smooth polynomial in the coordinates. -/
private theorem contDiff_phaseNumerator (i : Fin 3) :
    ContDiff ℝ 1 (fun s => phaseNumerator s i) := by
  have hZ := (coord 2).contDiff (n := 1)
  fin_cases i
  · exact (contDiff_const.mul (coord 0).contDiff).mul (hZ.pow 2)
  · exact (contDiff_const.mul (coord 1).contDiff).mul (hZ.pow 2)
  · exact hZ.mul ((contDiff_transverseSq.sub (hZ.pow 2)).sub contDiff_const)

/-- A scalar latitude multiplier times a Cartesian flux component. -/
private noncomputable def weightedFlux (f : ℝ → ℝ) (N : MomentSpace → Fin 3 → ℝ)
    (i : Fin 3) (s : MomentSpace) : ℝ :=
  f (stereoU s) * (N s i / stereoD s ^ 4)

/-- The weighted flux is continuously differentiable. -/
private theorem contDiff_weightedFlux (f : ℝ → ℝ) (N : MomentSpace → Fin 3 → ℝ)
    {i : Fin 3} (hf : ContDiff ℝ 1 f) (hN : ContDiff ℝ 1 (fun s => N s i)) :
    ContDiff ℝ 1 (weightedFlux f N i) :=
  (hf.comp contDiff_stereoU).mul (hN.div (contDiff_stereoD.pow 4) (fun s => pow_ne_zero _ (stereoD_pos s).ne'))

/-- The diagonal derivative of the weighted flux is obtained by
one-dimensional differentiation on the corresponding Cartesian line. -/
private theorem fderiv_weightedFlux_axis (f : ℝ → ℝ) (N : MomentSpace → Fin 3 → ℝ)
    (s : MomentSpace) (i : Fin 3) (m : ℝ)
    (hf : ContDiff ℝ 1 f) (hN : ContDiff ℝ 1 (fun s => N s i))
    (hNm : HasDerivAt (fun h => N (shift s i h) i) m 0) :
    fderiv ℝ (weightedFlux f N i) s (batemanAxis i) =
      deriv f (stereoU s) * latitudePartial s i * (N s i / stereoD s ^ 4) +
        f (stereoU s) * (m / stereoD s ^ 4 - 4 * N s i * (2 * coord i s) / stereoD s ^ 5) := by
  have hD := hasDerivAt_stereoD_shift s i
  have hd := (stereoD_pos s).ne'
  have hF := (contDiff_weightedFlux f N hf hN).differentiable (by norm_num) s
  have hs : HasDerivAt (shift s i) (batemanAxis i) 0 := by
    unfold shift
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (batemanAxis i)).const_add s
  have hAxis := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hs (shift_zero s i).symm
  have hfun := (hf.differentiable (by norm_num) (stereoU (shift s i 0))).hasDerivAt
  have hU := hfun.comp 0 (hasDerivAt_stereoU_shift s i)
  have hNdiv := hNm.fun_div (hD.fun_pow 4) (by rw [shift_zero]; exact pow_ne_zero _ hd)
  have hLine := (hU.fun_mul hNdiv).deriv
  change deriv (fun h => weightedFlux f N i (shift s i h)) 0 = _ at hLine
  have hAxis' := hAxis.deriv
  change deriv (fun h => weightedFlux f N i (shift s i h)) 0 = _ at hAxis'
  rw [hAxis'] at hLine
  simp only [Function.comp_apply, shift_zero] at hLine
  rw [hLine]
  norm_num
  field_simp [hd]
  ring_nf
  simp

/-- Each Cartesian derivative of a weighted flux has zero integral. The
field and its derivative both decay at least as the inverse squared
stereographic denominator. -/
private theorem integral_weightedFlux_axis_zero (f : ℝ → ℝ)
    (N N' : MomentSpace → Fin 3 → ℝ) (i : Fin 3) (hf : ContDiff ℝ 1 f)
    (hN : ContDiff ℝ 1 (fun s => N s i))
    (hNd : ∀ s, HasDerivAt (fun h => N (shift s i h) i) (N' s i) 0)
    (hNbound : ∀ s, |N s i| ≤ 2 * stereoD s ^ 2)
    (hN'bound : ∀ s, |N' s i| ≤ 4 * stereoD s) :
    Integrable (fun s : MomentSpace => fderiv ℝ (weightedFlux f N i) s (batemanAxis i)) ∧
      (∫ s : MomentSpace, fderiv ℝ (weightedFlux f N i) s (batemanAxis i)) = 0 := by
  let g := weightedFlux f N i
  let g' := fun s => fderiv ℝ g s (batemanAxis i)
  let v := batemanAxis i
  have hg := contDiff_weightedFlux f N hf hN
  have hc : Continuous (fun u => (f u, deriv f u)) :=
    hf.continuous.prodMk hf.continuous_deriv_one
  obtain ⟨K, hK, hbound⟩ := (isCompact_Icc.image hc).isBounded.exists_pos_norm_le
  have hfbound (s : MomentSpace) : |f (stereoU s)| ≤ K ∧ |deriv f (stereoU s)| ≤ K := by
    have h := hbound (f (stereoU s), deriv f (stereoU s))
      ⟨stereoU s, stereoU_mem s, rfl⟩
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at h
    exact h
  have hg_int : Integrable g := by
    refine integrable_of_stereo_bound hg.continuous (K := 2 * K) (by positivity) (fun s => ?_)
    let d := stereoD s
    have hd := stereoD_pos s
    change |f (stereoU s) * (N s i / d ^ 4)| ≤ 2 * K / d ^ 2
    rw [abs_mul, abs_div, abs_of_nonneg (pow_nonneg hd.le _)]
    calc
      _ ≤ K * (2 * d ^ 2 / d ^ 4) := by
        exact mul_le_mul (hfbound s).1 (div_le_div_of_nonneg_right (hNbound s) (by positivity))
          (by positivity) hK.le
      _ = _ := by field_simp [hd.ne']
  have hg'_int : Integrable g' := by
    refine integrable_of_stereo_bound ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (K := 68 * K) (by positivity) (fun s => ?_)
    let d := stereoD s
    have hd := stereoD_pos s
    have hOne := one_le_stereoD s
    change |fderiv ℝ (weightedFlux f N i) s (batemanAxis i)| ≤ 68 * K / d ^ 2
    rw [fderiv_weightedFlux_axis f N s i (N' s i) hf hN (hNd s)]
    refine (abs_add_le _ _).trans ?_
    have h₁ : |deriv f (stereoU s) * latitudePartial s i * (N s i / d ^ 4)| ≤ 48 * K / d ^ 2 := by
      rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (pow_nonneg hd.le _)]
      calc
        _ ≤ K * 24 * (2 * d ^ 2 / d ^ 4) := by
          exact mul_le_mul (mul_le_mul (hfbound s).2 (abs_latitudePartial_le s i)
            (abs_nonneg _) hK.le) (div_le_div_of_nonneg_right (hNbound s) (by positivity))
            (by positivity) (by positivity)
        _ = _ := by field_simp [hd.ne']; ring
    have hDiag : |N' s i / d ^ 4| ≤ 4 / d ^ 2 := by
      rw [abs_div, abs_of_nonneg (pow_nonneg hd.le _)]
      calc
        _ ≤ 4 * d / d ^ 4 := div_le_div_of_nonneg_right (hN'bound s) (by positivity)
        _ = 4 / d ^ 3 := by field_simp [hd.ne']
        _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          calc
            d ^ 2 = d ^ 2 * 1 := by ring
            _ ≤ d ^ 2 * d := mul_le_mul_of_nonneg_left hOne (sq_nonneg d)
            _ = _ := by ring
    have hDen : |4 * N s i * (2 * coord i s) / d ^ 5| ≤ 16 / d ^ 2 := by
      rw [abs_div, abs_of_nonneg (pow_nonneg hd.le _), abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ 4 * (2 * d ^ 2) * (2 * d) / d ^ 5 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hNbound s) (by norm_num))
            (mul_le_mul_of_nonneg_left (abs_coord_le_stereoD s i) (by norm_num)) (by positivity) (by positivity)
        _ = _ := by field_simp [hd.ne']; ring
    have h₂ : |f (stereoU s) * (N' s i / d ^ 4 -
          4 * N s i * (2 * coord i s) / d ^ 5)| ≤ 20 * K / d ^ 2 := by
      rw [abs_mul]
      calc
        _ ≤ K * (4 / d ^ 2 + 16 / d ^ 2) := mul_le_mul (hfbound s).1
          ((abs_sub _ _).trans (add_le_add hDiag hDen)) (abs_nonneg _) hK.le
        _ = _ := by ring
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  have := momentSpace_volume_isAddHaarMeasure
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure MomentSpace)) (v := v) (f := fun _ => (1 : ℝ)) (g := g)
    (by simp)
    (by simpa only [one_mul] using hg'_int)
    (by simpa only [one_mul] using hg_int) (fun _ _ => differentiableAt_const _)
    (fun s _ => hg.differentiable (by norm_num) s)
  exact ⟨hg'_int, by simpa [v] using hIBP⟩

/-- The latitude integration-by-parts identity on the whole
stereographic chart. -/
private theorem integral_latitude_balance (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∫ s : MomentSpace, (stereoU s * (1 - stereoU s) * deriv f (stereoU s) +
      (1 - 2 * stereoU s) * f (stereoU s)) / stereoD s ^ 3 = 0 := by
  have hi (i : Fin 3) := integral_weightedFlux_axis_zero f latitudeNumerator latitudeDiagonal i
    hf (contDiff_latitudeNumerator i) (fun s => hasDerivAt_latitudeNumerator_shift s i)
    (fun s => (flux_bounds s i).1.1) (fun s => (flux_bounds s i).1.2)
  have hpoint (s : MomentSpace) :
      (stereoU s * (1 - stereoU s) * deriv f (stereoU s) +
        (1 - 2 * stereoU s) * f (stereoU s)) / stereoD s ^ 3 =
      ∑ i : Fin 3, fderiv ℝ (weightedFlux f latitudeNumerator i) s (batemanAxis i) := by
    simp_rw [fderiv_weightedFlux_axis f latitudeNumerator s _ _ hf (contDiff_latitudeNumerator _)
      (hasDerivAt_latitudeNumerator_shift s _)]
    exact (latitude_flux_sum s (f (stereoU s)) (deriv f (stereoU s))).symm
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ => (hi i).1)]
  simp [fun i => (hi i).2]

/-- Rotation of the first complex phase integrates its real part to zero
with any smooth latitude multiplier. -/
private theorem integral_phase_balance (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∫ s : MomentSpace, f (stereoU s) * (stereoD s - 2) / stereoD s ^ 4 = 0 := by
  have hi (i : Fin 3) := integral_weightedFlux_axis_zero f phaseNumerator phaseDiagonal i
    hf (contDiff_phaseNumerator i) (fun s => hasDerivAt_phaseNumerator_shift s i)
    (fun s => (flux_bounds s i).2.1) (fun s => (flux_bounds s i).2.2)
  have hpoint (s : MomentSpace) :
      f (stereoU s) * (stereoD s - 2) / stereoD s ^ 4 =
      ∑ i : Fin 3, fderiv ℝ (weightedFlux f phaseNumerator i) s (batemanAxis i) := by
    simp_rw [fderiv_weightedFlux_axis f phaseNumerator s _ _ hf (contDiff_phaseNumerator _)
      (hasDerivAt_phaseNumerator_shift s _)]
    exact (phase_flux_sum s (f (stereoU s)) (deriv f (stereoU s))).symm
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ => (hi i).1)]
  simp [fun i => (hi i).2]

/-- A bounded continuous latitude multiplier times an inverse power of the
stereographic denominator is integrable when the exponent is at least two. -/
private theorem integrable_latitudeWeight (f : ℝ → ℝ) (hf : Continuous f)
    (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun s : MomentSpace => f (stereoU s) / stereoD s ^ n) := by
  obtain ⟨K, hK, hbound⟩ := (isCompact_Icc.image hf).isBounded.exists_pos_norm_le
  apply integrable_of_stereo_bound
    ((hf.comp contDiff_stereoU.continuous).div (contDiff_stereoD.continuous.pow n)
      (fun s => pow_ne_zero _ (stereoD_pos s).ne')) hK.le
  intro s
  change |f (stereoU s) / stereoD s ^ n| ≤ _
  rw [abs_div, abs_of_nonneg (pow_nonneg (stereoD_pos s).le _)]
  have h := hbound (f (stereoU s)) ⟨stereoU s, stereoU_mem s, rfl⟩
  rw [Real.norm_eq_abs] at h
  calc
    _ ≤ K / stereoD s ^ n := div_le_div_of_nonneg_right h (pow_nonneg (stereoD_pos s).le _)
    _ ≤ _ := div_le_div_of_nonneg_left hK.le (pow_pos (stereoD_pos s) _)
      (pow_le_pow_right₀ (one_le_stereoD s) hn)

/-! ## Exact energy normalization -/

/-- Powers of the two complementary sphere coordinates. -/
private noncomputable def latitudePowers (m n : ℕ) (u : ℝ) : ℝ :=
  u ^ m * (1 - u) ^ n

/-- The latitude polynomial is continuously differentiable. -/
private theorem contDiff_latitudePowers (m n : ℕ) : ContDiff ℝ 1 (latitudePowers m n) :=
  (contDiff_id.pow m).mul ((contDiff_const.sub contDiff_id).pow n)

/-- The exponent times the predecessor power, multiplied by the variable. -/
private theorem mul_exponent_pred_pow (m : ℕ) (u : ℝ) :
    u * ((m : ℝ) * u ^ (m - 1)) = (m : ℝ) * u ^ m := by
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_sub_one, pow_succ]
    ring

/-- The latitude divergence for a polynomial weight gives the recurrence
factor of the beta integral, including zero polynomial exponents. -/
private theorem latitudePowers_balance (m n : ℕ) (u : ℝ) :
    u * (1 - u) * deriv (latitudePowers m n) u +
      (1 - 2 * u) * latitudePowers m n u =
      ((m : ℝ) + 1 - ((m : ℝ) + (n : ℝ) + 2) * u) * latitudePowers m n u := by
  have hd : HasDerivAt (latitudePowers m n)
      ((m : ℝ) * u ^ (m - 1) * (1 - u) ^ n -
       u ^ m * ((n : ℝ) * (1 - u) ^ (n - 1))) u := by
    unfold latitudePowers
    refine (((hasDerivAt_id u).fun_pow m).fun_mul
      (((hasDerivAt_id u).const_sub (1 : ℝ)).fun_pow n)).congr_deriv ?_
    simp only [id_eq, mul_one, mul_neg]
    ring
  rw [hd.deriv]
  calc
    _ = (1 - u) * (u * ((m : ℝ) * u ^ (m - 1))) * (1 - u) ^ n -
        u * u ^ m * ((1 - u) * ((n : ℝ) * (1 - u) ^ (n - 1))) +
          (1 - 2 * u) * latitudePowers m n u := by ring
    _ = _ := by
      rw [mul_exponent_pred_pow, mul_exponent_pred_pow, latitudePowers]
      ring

/-- The exact relation between the two successive latitude moments. -/
private theorem integral_latitudePowers (m n : ℕ) :
    ((m : ℝ) + (n : ℝ) + 2) *
        (∫ s : MomentSpace, stereoU s * latitudePowers m n (stereoU s) / stereoD s ^ 3) =
      ((m : ℝ) + 1) * (∫ s : MomentSpace, latitudePowers m n (stereoU s) / stereoD s ^ 3) := by
  let f := latitudePowers m n
  have hf := contDiff_latitudePowers m n
  have h := integral_latitude_balance (latitudePowers m n) hf
  simp_rw [latitudePowers_balance] at h
  have hFirst := integrable_latitudeWeight f hf.continuous 3 (by norm_num)
  have hSecond := integrable_latitudeWeight (fun u => u * f u) (continuous_id.mul hf.continuous)
    3 (by norm_num)
  have heq (s : MomentSpace) :
      (((m : ℝ) + 1 - ((m : ℝ) + (n : ℝ) + 2) * stereoU s) * f (stereoU s)) / stereoD s ^ 3 =
      ((m : ℝ) + 1) * (f (stereoU s) / stereoD s ^ 3) -
      ((m : ℝ) + (n : ℝ) + 2) * (stereoU s * f (stereoU s) / stereoD s ^ 3) := by ring
  change (∫ s : MomentSpace,
    (((m : ℝ) + 1 - ((m : ℝ) + (n : ℝ) + 2) * stereoU s) * f (stereoU s)) / stereoD s ^ 3) = 0 at h
  simp_rw [heq] at h
  rw [integral_sub (hFirst.const_mul _) (hSecond.const_mul _),
    integral_const_mul, integral_const_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- The radial factor in the energy density contributes a factor of one
half after integration over the first complex coordinate's phase. -/
private theorem integral_latitude_energyWeight (m n : ℕ) :
    2 * (∫ s : MomentSpace, latitudePowers m n (stereoU s) / stereoD s ^ 4) =
      ∫ s : MomentSpace, latitudePowers m n (stereoU s) / stereoD s ^ 3 := by
  let f := latitudePowers m n
  have hf := contDiff_latitudePowers m n
  have h := integral_phase_balance f hf
  have hThird := integrable_latitudeWeight f hf.continuous 3 (by norm_num)
  have hFourth := integrable_latitudeWeight f hf.continuous 4 (by norm_num)
  have heq (s : MomentSpace) :
      f (stereoU s) * (stereoD s - 2) / stereoD s ^ 4 =
      f (stereoU s) / stereoD s ^ 3 - 2 * (f (stereoU s) / stereoD s ^ 4) := by
    field_simp [(stereoD_pos s).ne']
  simp_rw [heq] at h
  rw [integral_sub hThird (hFourth.const_mul _), integral_const_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- Half the sum of the squared electric and magnetic lengths on a
physical time slice of the power family. -/
noncomputable def batemanEnergyDensity (p q : ℕ) (t : ℝ) (s : MomentSpace) : ℝ :=
  (∑ j : Fin 3, Complex.normSq (rationalPowerField p q s.1 s.2.1 s.2.2 t j)) / 2

/-- The physical initial Bateman energy is half of the squared
Riemann–Silberstein field norm, integrated over Cartesian volume. -/
noncomputable def batemanInitialEnergy (p q : ℕ) : ℝ :=
  ∫ s : MomentSpace, (∑ j : Fin 3, Complex.normSq (rationalPowerField p q s.1 s.2.1 s.2.2 0 j)) / 2

/-- The actual initial energy density as a stereographic latitude weight. -/
private theorem initial_energy_density_eq_latitude (m n : ℕ) (s : MomentSpace) :
    (∑ j : Fin 3, Complex.normSq (rationalPowerField (m + 1) (n + 1) s.1 s.2.1 s.2.2 0 j)) / 2 =
      (16 * ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2) *
        (latitudePowers m n (stereoU s) / stereoD s ^ 4) := by
  rcases s with ⟨x, y, z⟩
  rw [rationalPowerField_energy_density_zero_time]
  rw [latitudePowers, one_sub_stereoU_eq_beta, stereoU_eq_alpha]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  change _ = _ * (_ / (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 4)
  ring

/-- Initial energy expressed as a weighted latitude integral. -/
private theorem batemanInitialEnergy_eq_latitude (m n : ℕ) :
    batemanInitialEnergy (m + 1) (n + 1) =
      16 * ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 *
        ∫ s : MomentSpace, latitudePowers m n (stereoU s) / stereoD s ^ 4 := by
  unfold batemanInitialEnergy
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  exact initial_energy_density_eq_latitude m n s

/-- The actual initial energy density is integrable in product Lebesgue
coordinates, including the zero-field cases with a zero power. -/
theorem integrable_batemanInitialEnergyDensity (p q : ℕ) :
    Integrable (fun s : MomentSpace =>
      (∑ j : Fin 3, Complex.normSq (rationalPowerField p q s.1 s.2.1 s.2.2 0 j)) / 2) := by
  cases p with
  | zero => simp [rationalPowerField_eq, rationalPowerFactor]
  | succ m =>
    cases q with
    | zero => simp [rationalPowerField_eq, rationalPowerFactor]
    | succ n =>
      have h := integrable_latitudeWeight (latitudePowers m n)
        (contDiff_latitudePowers m n).continuous 4 (by norm_num)
      refine (h.const_mul (16 * ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2)).congr ?_
      exact Eventually.of_forall fun s => (initial_energy_density_eq_latitude m n s).symm

/-- Initial electric helicity expressed as the shifted latitude moment. -/
private theorem batemanInitialHelicity_eq_latitude (m n : ℕ) :
    (∫ s : MomentSpace, batemanElectricHelicityDensity (m + 1) (n + 1) 0 s) =
      8 * ((m : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 *
        ∫ s : MomentSpace, stereoU s * latitudePowers m n (stereoU s) / stereoD s ^ 3 := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  rcases s with ⟨x, y, z⟩
  rw [batemanElectricHelicityDensity_zero_time]
  rw [latitudePowers, one_sub_stereoU_eq_beta, stereoU_eq_alpha]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  change _ = _ * (_ / (x ^ 2 + y ^ 2 + z ^ 2 + 1) ^ 3)
  ring

/-- The whole-space initial energy is strictly positive for positive
powers. Both coordinates are nonzero on an open set. -/
theorem batemanInitialEnergy_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    0 < batemanInitialEnergy p q := by
  cases p with
  | zero => exact (Nat.not_lt_zero _ hp).elim
  | succ m =>
    cases q with
    | zero => exact (Nat.not_lt_zero _ hq).elim
    | succ n =>
      rw [batemanInitialEnergy_eq_latitude m n]
      have hf := (contDiff_latitudePowers m n).continuous
      have hc : Continuous (fun s : MomentSpace => latitudePowers m n (stereoU s) / stereoD s ^ 4) :=
        (hf.comp contDiff_stereoU.continuous).div (contDiff_stereoD.continuous.pow 4)
          (fun s => pow_ne_zero _ (stereoD_pos s).ne')
      have hInt := integrable_latitudeWeight (latitudePowers m n) hf 4 (by norm_num)
      have h := integral_pos_of_integrable_nonneg_nonzero (x := ((1 / 2, 0, 0) : MomentSpace))
        hc hInt (fun s => by
          have hMem := stereoU_mem s
          exact div_nonneg (mul_nonneg (pow_nonneg hMem.1 _) (pow_nonneg (sub_nonneg.mpr hMem.2) _))
            (by positivity))
        (by
          have hOne : stereoU (1 / 2, 0, 0) = 9 / 25 := by
            change 1 - 4 * ((1 / 2 : ℝ) ^ 2 + 0 ^ 2) /
              ((1 / 2 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 + 1) ^ 2 = _
            norm_num
          rw [hOne, latitudePowers]
          exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
            (pow_ne_zero _ (stereoD_pos _).ne'))
      have hP : 0 < 16 * ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
      exact mul_pos hP h

/-- With the initial physical energy as normalization, both whole-space
helicity integrals have the value `1 / (p + q)` at every real time. -/
theorem bateman_normalized_helicities {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    ((∫ s : MomentSpace, batemanElectricHelicityDensity p q t s) / batemanInitialEnergy p q =
        1 / ((p : ℝ) + (q : ℝ))) ∧
      ((∫ s : MomentSpace, batemanMagneticHelicityDensity p q t s) / batemanInitialEnergy p q =
        1 / ((p : ℝ) + (q : ℝ))) := by
  rw [(integrable_and_conserved_batemanElectricHelicity p q t).2,
    (integrable_and_conserved_batemanMagneticHelicity p q t).2]
  have he : batemanInitialEnergy p q ≠ 0 := (batemanInitialEnergy_pos hp hq).ne'
  have hsum : ((p : ℝ) + (q : ℝ)) ≠ 0 := by positivity
  have hRel : ((p : ℝ) + (q : ℝ)) *
      (∫ s : MomentSpace, batemanElectricHelicityDensity p q 0 s) = batemanInitialEnergy p q := by
    cases p with
    | zero => exact (Nat.not_lt_zero _ hp).elim
    | succ m =>
      cases q with
      | zero => exact (Nat.not_lt_zero _ hq).elim
      | succ n =>
        rw [batemanInitialHelicity_eq_latitude m n, batemanInitialEnergy_eq_latitude m n]
        let H := ∫ s : MomentSpace, stereoU s * latitudePowers m n (stereoU s) / stereoD s ^ 3
        let I := ∫ s : MomentSpace, latitudePowers m n (stereoU s) / stereoD s ^ 3
        let E := ∫ s : MomentSpace, latitudePowers m n (stereoU s) / stereoD s ^ 4
        have hH : ((m : ℝ) + (n : ℝ) + 2) * H = ((m : ℝ) + 1) * I := integral_latitudePowers m n
        have hE : 2 * E = I := integral_latitude_energyWeight m n
        push_cast
        change (((m : ℝ) + 1) + ((n : ℝ) + 1)) *
          (8 * ((m : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 * H) =
          16 * ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 * E
        calc
          _ = 8 * ((m : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 *
              (((m : ℝ) + (n : ℝ) + 2) * H) := by ring
          _ = _ := by rw [hH, ← hE]; ring
  have h : (∫ s : MomentSpace, batemanElectricHelicityDensity p q 0 s) / batemanInitialEnergy p q =
      1 / ((p : ℝ) + (q : ℝ)) := by
    apply (div_eq_div_iff he hsum).2
    rw [one_mul, mul_comm]
    exact hRel
  exact ⟨h, h⟩

/-- The initial energy density is a continuous function of physical position. -/
theorem continuous_batemanEnergyDensity_zero (p q : ℕ) :
    Continuous (batemanEnergyDensity p q 0) := by
  have hcoords : Continuous (fun s : MomentSpace => (s.1, s.2.1, s.2.2, (0 : ℝ))) := by fun_prop
  exact (continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((contDiff_rationalPowerField p q j).continuous.comp hcoords)).div_const 2

/-- Any continuous weight bounded by a multiple of the quadratic radial
factor gives an integrable initial charge density. -/
theorem integrable_batemanInitialEnergy_mul (p q : ℕ) {g : MomentSpace → ℝ}
    (hg : Continuous g) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ s, |g s| ≤ K * (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1)) :
    Integrable fun s => batemanEnergyDensity p q 0 s * g s := by
  cases p with
  | zero => simp [batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
  | succ m =>
    cases q with
    | zero => simp [batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
    | succ n =>
      let A := 16 * ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2
      have hA : 0 ≤ A := by positivity
      refine integrable_of_stereo_bound ((continuous_batemanEnergyDensity_zero _ _).mul hg)
        (K := A * K) (mul_nonneg hA hK) ?_
      intro s
      have hd := stereoD_pos s
      have hD := one_le_stereoD s
      have hU := stereoU_mem s
      have hLat : |latitudePowers m n (stereoU s)| ≤ 1 := by
        have h₁ : 0 ≤ (1 - stereoU s) := sub_nonneg.mpr hU.2
        have h₂ : 1 - stereoU s ≤ 1 := by linarith [hU.1]
        unfold latitudePowers
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg hU.1 _) (pow_nonneg h₁ _))]
        simpa only [one_mul] using mul_le_mul (pow_le_one₀ hU.1 hU.2) (pow_le_one₀ h₁ h₂) (pow_nonneg h₁ _) zero_le_one
      change |((_ / 2) : ℝ) * g s| ≤ _
      rw [initial_energy_density_eq_latitude m n s]
      change |(A * (latitudePowers m n (stereoU s) / stereoD s ^ 4)) * g s| ≤ _
      rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_div, abs_of_nonneg (pow_nonneg hd.le _)]
      have hgs : |g s| ≤ K * stereoD s := h s
      have hp : 0 ≤ latitudePowers m n (stereoU s) := by
        exact mul_nonneg (pow_nonneg hU.1 _) (pow_nonneg (sub_nonneg.mpr hU.2) _)
      change A * (|latitudePowers m n (stereoU s)| / stereoD s ^ 4) * |g s| ≤ _
      calc
        _ ≤ A * (1 / stereoD s ^ 4) * (K * stereoD s) := by
          gcongr
        _ = A * K / stereoD s ^ 3 := by field_simp [hd.ne']
        _ ≤ _ := by
          apply div_le_div_of_nonneg_left (mul_nonneg hA hK) (pow_pos hd _)
          exact pow_le_pow_right₀ hD (by norm_num)

/-- The factor of the radial denominator raises the initial energy
integral by exactly two. -/
theorem integral_batemanInitialEnergy_mul_radial (p q : ℕ) :
    ∫ s : MomentSpace, batemanEnergyDensity p q 0 s *
        (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1) = 2 * batemanInitialEnergy p q := by
  cases p with
  | zero => simp [batemanInitialEnergy, batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
  | succ m =>
    cases q with
    | zero => simp [batemanInitialEnergy, batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
    | succ n =>
      rw [batemanInitialEnergy_eq_latitude m n]
      let A := 16 * ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2
      have h (s : MomentSpace) : batemanEnergyDensity (m + 1) (n + 1) 0 s *
          (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1) =
          A * (latitudePowers m n (stereoU s) / stereoD s ^ 3) := by
        change (_ / 2) * stereoD s = _
        rw [initial_energy_density_eq_latitude]
        change A * (latitudePowers m n (stereoU s) / stereoD s ^ 4) * stereoD s = _
        field_simp [(stereoD_pos s).ne']
      simp_rw [h, integral_const_mul]
      change A * (∫ s : MomentSpace, latitudePowers m n (stereoU s) / stereoD s ^ 3) =
        2 * (A * ∫ s : MomentSpace, latitudePowers m n (stereoU s) / stereoD s ^ 4)
      rw [← integral_latitude_energyWeight m n]
      ring

/-- The transverse part of the initial energy has the exact share
q/(p+q) after weighting by twice the transverse squared radius divided
by the stereographic denominator. -/
theorem integral_batemanInitialEnergy_mul_transverse (p q : ℕ) :
    ((p : ℝ) + (q : ℝ)) *
        (∫ s : MomentSpace, batemanEnergyDensity p q 0 s *
          (2 * (s.1 ^ 2 + s.2.1 ^ 2) / (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1))) =
      (q : ℝ) * batemanInitialEnergy p q := by
  cases p with
  | zero => simp [batemanInitialEnergy, batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
  | succ m =>
    cases q with
    | zero => simp [batemanInitialEnergy, batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
    | succ n =>
      rw [batemanInitialEnergy_eq_latitude m n]
      let f := latitudePowers m n
      let A := 16 * ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2
      have h (s : MomentSpace) : batemanEnergyDensity (m + 1) (n + 1) 0 s *
          (2 * (s.1 ^ 2 + s.2.1 ^ 2) / (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1)) =
          A / 2 * (f (stereoU s) / stereoD s ^ 3 -
            stereoU s * f (stereoU s) / stereoD s ^ 3) := by
        change (_ / 2) * (2 * transverseSq s / stereoD s) = _
        rw [initial_energy_density_eq_latitude]
        change A * (f (stereoU s) / stereoD s ^ 4) * (2 * transverseSq s / stereoD s) = _
        unfold stereoU
        field_simp [(stereoD_pos s).ne']
        ring
      have hFirst := integrable_latitudeWeight f (contDiff_latitudePowers m n).continuous 3 (by norm_num)
      have hSecond := integrable_latitudeWeight (fun u => u * f u)
        (continuous_id.mul (contDiff_latitudePowers m n).continuous) 3 (by norm_num)
      simp_rw [h, integral_const_mul]
      rw [integral_sub hFirst hSecond]
      let I := ∫ s : MomentSpace, f (stereoU s) / stereoD s ^ 3
      let J := ∫ s : MomentSpace, stereoU s * f (stereoU s) / stereoD s ^ 3
      let E := ∫ s : MomentSpace, f (stereoU s) / stereoD s ^ 4
      have hJ : ((m : ℝ) + (n : ℝ) + 2) * J = ((m : ℝ) + 1) * I := integral_latitudePowers m n
      have hE : 2 * E = I := integral_latitude_energyWeight m n
      push_cast
      change (((m : ℝ) + 1) + ((n : ℝ) + 1)) * (A / 2 * (I - J)) =
        ((n : ℝ) + 1) * (A * E)
      linear_combination (A / 2) * ((n : ℝ) + 1) * (-hE) - (A / 2) * hJ

/-- The initial energy density is unchanged by reversing the two
transverse Cartesian coordinates. -/
theorem batemanEnergyDensity_zero_flip_xy (p q : ℕ) (x y z : ℝ) :
    batemanEnergyDensity p q 0 (-x, -y, z) = batemanEnergyDensity p q 0 (x, y, z) := by
  cases p with
  | zero => simp [batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
  | succ m =>
    cases q with
    | zero => simp [batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
    | succ n =>
      change _ / 2 = _ / 2
      rw [initial_energy_density_eq_latitude, initial_energy_density_eq_latitude]
      have hD : stereoD (-x, -y, z) = stereoD (x, y, z) := by
        simp [stereoD, coord]
      have hS : transverseSq (-x, -y, z) = transverseSq (x, y, z) := by
        simp [transverseSq, coord]
      simp only [stereoU, hD, hS]

/-- The initial energy density is unchanged by reversing the vertical
Cartesian coordinate. -/
theorem batemanEnergyDensity_zero_flip_z (p q : ℕ) (x y z : ℝ) :
    batemanEnergyDensity p q 0 (x, y, -z) = batemanEnergyDensity p q 0 (x, y, z) := by
  cases p with
  | zero => simp [batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
  | succ m =>
    cases q with
    | zero => simp [batemanEnergyDensity, rationalPowerField_eq, rationalPowerFactor]
    | succ n =>
      change _ / 2 = _ / 2
      rw [initial_energy_density_eq_latitude, initial_energy_density_eq_latitude]
      have hD : stereoD (x, y, -z) = stereoD (x, y, z) := by
        simp [stereoD, coord]
      have hS : transverseSq (x, y, -z) = transverseSq (x, y, z) := rfl
      simp only [stereoU, hD, hS]

end Qatlib.Papers.KnotLight13.TorusFamily
