/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanChargeDensities

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# Full-space conformal charges of the powered Bateman field

[Kedia2013TyingKnots] reports the energy-normalized momentum, angular
momentum and spatial special conformal charge. The conserved currents
and the remaining conformal charges for the same field are given in
[Hoyos2015NewKnottedMaxwell], sections 2.2–2.3 and appendix A.
Their values follow here from two radial moments, parity and exact
ray change of variables on physical space.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open MeasureTheory
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3 squaredLength)

local notation "ConformalSpace" => ℝ × ℝ × ℝ
local notation "X" => batemanCartesianCoordinates
local notation "V" => batemanVelocity 0

/-- Squared physical radius in product Cartesian coordinates. -/
private def chargeR (s : ConformalSpace) : ℝ := s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2

/-- The stereographic denominator on the initial slice. -/
private def chargeD (s : ConformalSpace) : ℝ := chargeR s + 1

/-- The bounded transverse weight giving the axial angular momentum. -/
private noncomputable def chargeT (s : ConformalSpace) : ℝ :=
  2 * (s.1 ^ 2 + s.2.1 ^ 2) / chargeD s

/-- The stereographic denominator is strictly positive everywhere. -/
private theorem chargeD_pos (s : ConformalSpace) : 0 < chargeD s := by
  unfold chargeD chargeR
  positivity

/-- The Cartesian squared length is the coordinate expression for the radius. -/
private theorem sqLength_X (s : ConformalSpace) : squaredLength (X s) = chargeR s := by
  simp [batemanCartesianCoordinates, squaredLength, dot3, chargeR, pow_two]

/-- Each component of the unit ray velocity has magnitude at most one. -/
private theorem abs_V_le (s : ConformalSpace) (i : Fin 3) : |V s i| ≤ 1 := by
  have h := squaredLength_batemanVelocity_zero s
  change V s 0 * V s 0 + V s 1 * V s 1 + V s 2 * V s 2 = 1 at h
  have hi (j : Fin 3) : V s j ^ 2 ≤ 1 := by
    fin_cases j
    · change V s 0 ^ 2 ≤ 1
      nlinarith [sq_nonneg (V s 1), sq_nonneg (V s 2)]
    · change V s 1 ^ 2 ≤ 1
      nlinarith [sq_nonneg (V s 0), sq_nonneg (V s 2)]
    · change V s 2 ^ 2 ≤ 1
      nlinarith [sq_nonneg (V s 0), sq_nonneg (V s 1)]
  exact abs_le_of_sq_le_sq (by simpa using hi i) zero_le_one

/-- A squared Cartesian coordinate is bounded by the squared radius. -/
private theorem sq_X_le (s : ConformalSpace) (i : Fin 3) : X s i ^ 2 ≤ chargeR s := by
  fin_cases i <;> simp [batemanCartesianCoordinates, chargeR] <;>
    nlinarith [sq_nonneg s.1, sq_nonneg s.2.1, sq_nonneg s.2.2]

/-- The initial radial denominator dominates each Cartesian coordinate. -/
private theorem abs_X_le (s : ConformalSpace) (i : Fin 3) : |X s i| ≤ chargeD s := by
  unfold chargeD
  nlinarith [sq_X_le s i, sq_abs (X s i), sq_nonneg (|X s i| - 1 / 2)]

/-- The initial charge weights in Cartesian coordinates. -/
private theorem initial_weight (c : BatemanChargeKind) (s : ConformalSpace) :
    batemanChargeWeight c 0 s =
      match c with
      | .momentum i => V s i
      | .angularMomentum i => cross3 (V s) (X s) i
      | .boost i => X s i
      | .dilation => -s.2.2
      | .conformalTime => chargeR s
      | .conformalSpace i => -chargeR s * V s i - 2 * X s i * s.2.2 := by
  cases c <;> simp [batemanChargeWeight, maxwellChargeDensity, sqLength_X,
    dot3_position_batemanVelocity_zero, mul_neg]
  ring

/-- Every initial charge weight is continuous on the whole spatial slice. -/
private theorem continuous_initial_weight (c : BatemanChargeKind) :
    Continuous (batemanChargeWeight c 0) := by
  have hd : Continuous chargeD := by unfold chargeD chargeR; fun_prop
  have hr : Continuous chargeR := by unfold chargeR; fun_prop
  have hx (i : Fin 3) : Continuous (fun s : ConformalSpace => X s i) := by
    fin_cases i
    · exact continuous_fst
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd
  have hv (i : Fin 3) : Continuous (fun s : ConformalSpace => V s i) := by
    have he : (fun s : ConformalSpace => V s i) = fun s =>
        ![2 * (s.2.1 - s.2.2 * s.1), -2 * (s.1 + s.2.2 * s.2.1),
          s.1 ^ 2 + s.2.1 ^ 2 - s.2.2 ^ 2 - 1] i / chargeD s := by
      funext s
      exact congrFun (poyntingFlow_initial s.1 s.2.1 s.2.2) i
    rw [he]
    refine Continuous.div ?_ hd (fun s => (chargeD_pos s).ne')
    fin_cases i
    · change Continuous (fun s : ConformalSpace => 2 * (s.2.1 - s.2.2 * s.1))
      fun_prop
    · change Continuous (fun s : ConformalSpace => -2 * (s.1 + s.2.2 * s.2.1))
      fun_prop
    · change Continuous (fun s : ConformalSpace => s.1 ^ 2 + s.2.1 ^ 2 - s.2.2 ^ 2 - 1)
      fun_prop
  change Continuous (fun s : ConformalSpace => batemanChargeWeight c 0 s)
  simp_rw [initial_weight]
  cases c with
  | momentum i => exact hv i
  | angularMomentum i =>
      fin_cases i
      · exact ((hv 1).mul (hx 2)).sub ((hv 2).mul (hx 1))
      · exact ((hv 2).mul (hx 0)).sub ((hv 0).mul (hx 2))
      · exact ((hv 0).mul (hx 1)).sub ((hv 1).mul (hx 0))
  | boost i => exact hx i
  | dilation => exact (hx 2).neg
  | conformalTime => exact hr
  | conformalSpace i =>
      exact (hr.neg.mul (hv i)).sub ((continuous_const.mul (hx i)).mul (hx 2))

/-- All initial charge weights have at most quadratic growth. -/
private theorem abs_initial_weight_le (c : BatemanChargeKind) (s : ConformalSpace) :
    |batemanChargeWeight c 0 s| ≤ 3 * chargeD s := by
  have hr : 0 ≤ chargeR s := by unfold chargeR; positivity
  have hd : 1 ≤ chargeD s := by unfold chargeD; linarith
  have hv (i : Fin 3) := abs_V_le s i
  have hx (i : Fin 3) := abs_X_le s i
  have hprod (i j : Fin 3) : |V s i * X s j| ≤ chargeD s := by
    rw [abs_mul]
    calc
      _ ≤ 1 * chargeD s := mul_le_mul (hv i) (hx j) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hang (i j : Fin 3) (a b : Fin 3) :
      |V s i * X s j - V s a * X s b| ≤ 3 * chargeD s :=
    (abs_sub _ _).trans (by linarith [hprod i j, hprod a b])
  rw [initial_weight]
  cases c with
  | momentum i => exact (hv i).trans (by linarith)
  | angularMomentum i =>
      fin_cases i
      · exact hang 1 2 2 1
      · exact hang 2 0 0 2
      · exact hang 0 1 1 0
  | boost i => exact (hx i).trans (by linarith)
  | dilation =>
      change |-X s 2| ≤ _
      rw [abs_neg]
      exact (hx 2).trans (by linarith)
  | conformalTime =>
      change |chargeR s| ≤ _
      rw [abs_of_nonneg hr]
      unfold chargeD
      linarith
  | conformalSpace i =>
      change |-chargeR s * V s i - 2 * X s i * X s 2| ≤ _
      have hfirst : |-chargeR s * V s i| ≤ chargeR s := by
        rw [abs_mul, abs_neg, abs_of_nonneg hr]
        simpa using mul_le_mul_of_nonneg_left (hv i) hr
      have hsecond : |2 * X s i * X s 2| ≤ 2 * chargeR s := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [sq_X_le s i, sq_X_le s 2, sq_abs (X s i), sq_abs (X s 2),
          sq_nonneg (|X s i| - |X s 2|)]
      exact (abs_sub _ _).trans (by unfold chargeD; linarith)

/-- The physical charge obtained by integrating over the actual spatial slice. -/
noncomputable def batemanCharge (c : BatemanChargeKind) (p q : ℕ) (t : ℝ) : ℝ :=
  ∫ s : ConformalSpace, batemanChargeDensity c p q t s

/-- Each physical Poincaré and conformal charge is absolutely integrable
on all of space and equals its initial value at every real time. -/
theorem integrable_and_conserved_batemanCharge (c : BatemanChargeKind) (p q : ℕ) (t : ℝ) :
    Integrable (batemanChargeDensity c p q t) ∧ batemanCharge c p q t = batemanCharge c p q 0 := by
  refine integrable_and_integral_of_batemanRay t _ _ (batemanChargeDensity_jacobian c p q t) ?_
  rw [funext (batemanChargeDensity_eq_energy_mul_weight c p q 0)]
  exact integrable_batemanInitialEnergy_mul p q (continuous_initial_weight c)
      (by norm_num : 0 ≤ (3 : ℝ)) (abs_initial_weight_le c)

/-- The initial axial momentum weight equals the transverse weight minus one. -/
private theorem initial_axial_momentum (s : ConformalSpace) :
    batemanChargeWeight (.momentum 2) 0 s = chargeT s - 1 := by
  rcases s with ⟨x, y, z⟩
  rw [initial_weight]
  change batemanVelocity 0 (x, y, z) 2 = _
  unfold batemanVelocity
  rw [poyntingFlow_initial]
  have hd := (chargeD_pos (x, y, z)).ne'
  change (x ^ 2 + y ^ 2 - z ^ 2 - 1) / chargeD (x, y, z) = _
  unfold chargeT
  field_simp [hd]
  simp [chargeD, chargeR]
  ring

/-- The initial axial angular momentum is exactly the transverse weight. -/
private theorem initial_axial_angular_momentum (s : ConformalSpace) :
    batemanChargeWeight (.angularMomentum 2) 0 s = chargeT s := by
  rcases s with ⟨x, y, z⟩
  rw [initial_weight]
  change V (x, y, z) 0 * y - V (x, y, z) 1 * x = _
  unfold batemanVelocity
  rw [poyntingFlow_initial]
  have hd := (chargeD_pos (x, y, z)).ne'
  change (2 * (y - z * x) / chargeD (x, y, z)) * y -
    (-2 * (x + z * y) / chargeD (x, y, z)) * x = _
  unfold chargeT
  field_simp [hd]
  simp
  ring

/-- The initial axial spatial conformal weight in terms of the two moments. -/
private theorem initial_axial_conformal (s : ConformalSpace) :
    batemanChargeWeight (.conformalSpace 2) 0 s = chargeT s + 1 - chargeD s := by
  have h := initial_axial_momentum s
  rw [initial_weight] at h ⊢
  change V s 2 = chargeT s - 1 at h
  change -chargeR s * V s 2 - 2 * s.2.2 * s.2.2 = _
  rw [h]
  unfold chargeT
  field_simp [(chargeD_pos s).ne']
  unfold chargeD chargeR
  ring

private def flipXY : ConformalSpace ≃ᵐ ConformalSpace :=
  (Homeomorph.neg ℝ).toMeasurableEquiv.prodCongr
    ((Homeomorph.neg ℝ).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ))

private def flipZ : ConformalSpace ≃ᵐ ConformalSpace :=
  (MeasurableEquiv.refl ℝ).prodCongr
    ((MeasurableEquiv.refl ℝ).prodCongr (Homeomorph.neg ℝ).toMeasurableEquiv)

/-- Reversing both transverse coordinates preserves Cartesian volume. -/
private theorem measurePreserving_flipXY : MeasurePreserving flipXY volume volume := by
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume))

/-- Reversing the vertical coordinate preserves Cartesian volume. -/
private theorem measurePreserving_flipZ : MeasurePreserving flipZ volume volume := by
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod
    ((MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg volume))

/-- An odd charge weight under a volume-preserving symmetry integrates to zero. -/
private theorem initial_integral_eq_zero (c : BatemanChargeKind) (p q : ℕ)
    (f : ConformalSpace ≃ᵐ ConformalSpace) (hf : MeasurePreserving f volume volume)
    (hu : ∀ s, batemanEnergyDensity p q 0 (f s) = batemanEnergyDensity p q 0 s)
    (hw : ∀ s, batemanChargeWeight c 0 (f s) = -batemanChargeWeight c 0 s) :
    batemanCharge c p q 0 = 0 := by
  unfold batemanCharge
  simp only [batemanChargeDensity_eq_energy_mul_weight]
  have h := hf.integral_comp' (fun s => batemanEnergyDensity p q 0 s * batemanChargeWeight c 0 s)
  simp only [hu, hw, mul_neg, integral_neg] at h
  linarith

/-- Transverse charges vanish by reversing both transverse coordinates. -/
private theorem initial_transverse_eq_zero (p q : ℕ) :
    batemanCharge (.momentum 0) p q 0 = 0 ∧ batemanCharge (.momentum 1) p q 0 = 0 ∧
    batemanCharge (.angularMomentum 0) p q 0 = 0 ∧ batemanCharge (.angularMomentum 1) p q 0 = 0 ∧
    batemanCharge (.boost 0) p q 0 = 0 ∧ batemanCharge (.boost 1) p q 0 = 0 ∧
    batemanCharge (.conformalSpace 0) p q 0 = 0 ∧ batemanCharge (.conformalSpace 1) p q 0 = 0 := by
  have he (s : ConformalSpace) : batemanEnergyDensity p q 0 (flipXY s) = batemanEnergyDensity p q 0 s :=
    batemanEnergyDensity_zero_flip_xy p q s.1 s.2.1 s.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply initial_integral_eq_zero _ p q flipXY measurePreserving_flipXY he <;>
    rintro ⟨x, y, z⟩ <;>
    change batemanChargeWeight _ 0 (-x, -y, z) = -batemanChargeWeight _ 0 (x, y, z) <;>
    simp only [initial_weight] <;>
    simp [batemanCartesianCoordinates, batemanVelocity, poyntingFlow_initial, chargeR, cross3] <;>
    ring

/-- The vertical boost and dilation vanish by vertical reflection. -/
private theorem initial_vertical_eq_zero (p q : ℕ) :
    batemanCharge (.boost 2) p q 0 = 0 ∧ batemanCharge .dilation p q 0 = 0 := by
  have he (s : ConformalSpace) : batemanEnergyDensity p q 0 (flipZ s) = batemanEnergyDensity p q 0 s :=
    batemanEnergyDensity_zero_flip_z p q s.1 s.2.1 s.2.2
  constructor <;>
    apply initial_integral_eq_zero _ p q flipZ measurePreserving_flipZ he <;>
    rintro ⟨x, y, z⟩ <;>
    change batemanChargeWeight _ 0 (x, y, -z) = -batemanChargeWeight _ 0 (x, y, z) <;>
    simp [initial_weight, batemanCartesianCoordinates]

/-- The total initial charge is a weighted integral of the initial energy. -/
private theorem initial_integral_weight (c : BatemanChargeKind) (p q : ℕ) :
    batemanCharge c p q 0 = ∫ s : ConformalSpace,
      batemanEnergyDensity p q 0 s * batemanChargeWeight c 0 s := by
  simp only [batemanCharge, batemanChargeDensity_eq_energy_mul_weight]

/-- The initial radial energy moment is absolutely integrable. -/
private theorem integrable_initial_radial (p q : ℕ) :
    Integrable (fun s : ConformalSpace => batemanEnergyDensity p q 0 s * chargeD s) := by
  apply integrable_batemanInitialEnergy_mul p q (K := 1)
  · unfold chargeD chargeR
    fun_prop
  · norm_num
  · intro s
    rw [abs_of_pos (chargeD_pos s), one_mul]
    rfl

/-- The initial transverse energy moment is absolutely integrable. -/
private theorem integrable_initial_transverse (p q : ℕ) :
    Integrable (fun s : ConformalSpace => batemanEnergyDensity p q 0 s * chargeT s) := by
  have ha := (integrable_and_conserved_batemanCharge (.angularMomentum 2) p q 0).1
  rw [funext (batemanChargeDensity_eq_energy_mul_weight (.angularMomentum 2) p q 0)] at ha
  simpa only [initial_axial_angular_momentum] using ha

/-- The remaining initial charges in terms of the physical energy and its transverse moment. -/
private theorem initial_axial_values (p q : ℕ) :
    let u := batemanInitialEnergy p q
    let a := ∫ s : ConformalSpace, batemanEnergyDensity p q 0 s * chargeT s
    batemanCharge (.momentum 2) p q 0 = a - u ∧
    batemanCharge (.angularMomentum 2) p q 0 = a ∧
    batemanCharge .conformalTime p q 0 = u ∧
    batemanCharge (.conformalSpace 2) p q 0 = a - u := by
  dsimp only
  have hu : Integrable (batemanEnergyDensity p q 0) := integrable_batemanInitialEnergyDensity p q
  have hD := integrable_initial_radial p q
  have hT := integrable_initial_transverse p q
  have hrad := integral_batemanInitialEnergy_mul_radial p q
  change (∫ s : ConformalSpace, batemanEnergyDensity p q 0 s * chargeD s) =
    2 * batemanInitialEnergy p q at hrad
  have he : (∫ s : ConformalSpace, batemanEnergyDensity p q 0 s) = batemanInitialEnergy p q := rfl
  simp only [initial_integral_weight, initial_axial_momentum, initial_axial_angular_momentum,
    initial_axial_conformal]
  refine ⟨?_, trivial, ?_, ?_⟩
  · simp_rw [mul_sub, mul_one]
    rw [integral_sub hT hu, he]
  · have h (s : ConformalSpace) : batemanChargeWeight .conformalTime 0 s = chargeD s - 1 := by
      rw [initial_weight]
      unfold chargeD
      ring
    simp_rw [h, mul_sub, mul_one]
    rw [integral_sub hD hu, hrad, he]
    ring
  · simp_rw [mul_sub, mul_add, mul_one]
    have hadd : Integrable (fun s : ConformalSpace =>
        batemanEnergyDensity p q 0 s * chargeT s + batemanEnergyDensity p q 0 s) := hT.add hu
    rw [integral_sub hadd hD, integral_add hT hu, hrad, he]
    ring

/-- The published energy-normalized charges. The angular momentum
uses the supplement's momentum-first cross product. -/
noncomputable def batemanNormalizedCharge (c : BatemanChargeKind) (p q : ℕ) : ℝ :=
  match c with
  | .momentum i | .conformalSpace i => if i = 2 then -(p : ℝ) / ((p : ℝ) + (q : ℝ)) else 0
  | .angularMomentum i => if i = 2 then (q : ℝ) / ((p : ℝ) + (q : ℝ)) else 0
  | .boost _ | .dilation => 0
  | .conformalTime => 1

/-- At each real time, all physical charges of a positive power pair
have their exact published values relative to that slice's own energy. -/
theorem batemanCharge_div_energy (c : BatemanChargeKind) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    batemanCharge c p q t / batemanEnergy p q t = batemanNormalizedCharge c p q := by
  rw [(integrable_and_conserved_batemanCharge c p q t).2,
    (integrable_and_conserved_batemanEnergy p q t).2]
  let E := batemanInitialEnergy p q
  let A := ∫ s : ConformalSpace, batemanEnergyDensity p q 0 s * chargeT s
  have he : E ≠ 0 := (batemanInitialEnergy_pos hp hq).ne'
  have hs : (p : ℝ) + (q : ℝ) ≠ 0 := by positivity
  have ht := integral_batemanInitialEnergy_mul_transverse p q
  change ((p : ℝ) + (q : ℝ)) * A = (q : ℝ) * E at ht
  have hpq : (A - E) / E = -(p : ℝ) / ((p : ℝ) + (q : ℝ)) := by
    apply (div_eq_div_iff he hs).2
    linear_combination ht
  have haq : A / E = (q : ℝ) / ((p : ℝ) + (q : ℝ)) := by
    apply (div_eq_div_iff he hs).2
    linear_combination ht
  obtain ⟨hm, ha, hk, hsct⟩ := initial_axial_values p q
  obtain ⟨hmx, hmy, hax, hay, hbx, hby, hsx, hsy⟩ := initial_transverse_eq_zero p q
  obtain ⟨hbz, hd⟩ := initial_vertical_eq_zero p q
  cases c with
  | momentum i =>
      fin_cases i
      · simp [batemanNormalizedCharge, hmx]
      · simp [batemanNormalizedCharge, hmy]
      · change batemanCharge (.momentum 2) p q 0 / E = _
        rw [hm]
        simpa [batemanNormalizedCharge] using hpq
  | angularMomentum i =>
      fin_cases i
      · simp [batemanNormalizedCharge, hax]
      · simp [batemanNormalizedCharge, hay]
      · change batemanCharge (.angularMomentum 2) p q 0 / E = _
        rw [ha]
        simpa [batemanNormalizedCharge] using haq
  | boost i => fin_cases i <;> simp [batemanNormalizedCharge, hbx, hby, hbz]
  | dilation => simp [batemanNormalizedCharge, hd]
  | conformalTime => simpa only [batemanNormalizedCharge, hk] using div_self he
  | conformalSpace i =>
      fin_cases i
      · simp [batemanNormalizedCharge, hsx]
      · simp [batemanNormalizedCharge, hsy]
      · change batemanCharge (.conformalSpace 2) p q 0 / E = _
        rw [hsct]
        simpa [batemanNormalizedCharge] using hpq

/-- The spatial special conformal density as printed in the
[Kedia2013TyingKnots] supplement, page 2. -/
noncomputable def printedBatemanSpatialConformalDensity (i : Fin 3) (p q : ℕ)
    (t : ℝ) (s : ConformalSpace) : ℝ :=
  let x := X s
  let S := batemanFlux p q t s
  2 * x i * dot3 x S - 2 * t * batemanEnergyDensity p q t s * x i - squaredLength x * S i

/-- Restoring the missing quadratic time term from
[Hoyos2015NewKnottedMaxwell], appendix A, yields the conserved density. -/
theorem printedBatemanSpatialConformalDensity_eq (i : Fin 3) (p q : ℕ)
    (t : ℝ) (s : ConformalSpace) :
    printedBatemanSpatialConformalDensity i p q t s =
      batemanChargeDensity (.conformalSpace i) p q t s -
        t ^ 2 * batemanChargeDensity (.momentum i) p q t s := by
  simp only [printedBatemanSpatialConformalDensity, batemanChargeDensity, maxwellChargeDensity]
  ring

/-- The literal printed density agrees with the conserved charge at
zero time. On other time slices its integral has the stated momentum term. -/
theorem integrable_and_integral_printedBatemanSpatialConformalDensity
    (i : Fin 3) (p q : ℕ) (t : ℝ) :
    Integrable (printedBatemanSpatialConformalDensity i p q t) ∧
      (∫ s, printedBatemanSpatialConformalDensity i p q t s) =
        batemanCharge (.conformalSpace i) p q 0 - t ^ 2 * batemanCharge (.momentum i) p q 0 := by
  obtain ⟨hk, hK⟩ := integrable_and_conserved_batemanCharge (.conformalSpace i) p q t
  obtain ⟨hp, hP⟩ := integrable_and_conserved_batemanCharge (.momentum i) p q t
  have he := funext (printedBatemanSpatialConformalDensity_eq i p q t)
  rw [he]
  have hscaled : Integrable (fun s => t ^ 2 * batemanChargeDensity (.momentum i) p q t s) :=
    hp.const_mul _
  refine ⟨hk.sub hscaled, ?_⟩
  rw [integral_sub hk hscaled, integral_const_mul]
  exact congrArg₂ (fun k p : ℝ => k - t ^ 2 * p) hK hP

end Qatlib.Papers.KnotLight13.TorusFamily
