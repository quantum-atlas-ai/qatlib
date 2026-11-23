/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.UniversalWalk12.MainResults.Fourier.Character
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-!
# Geometric Fourier sums and nonresonant bounds

These are the analytic bounds for the actual finite packet kernels, not assumptions on the final
integral estimates. Finite interval character sums reduce to geometric sums with a unit-modulus
initial factor; their product with the half-angle sine is bounded by one.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.UniversalWalk12.MainResults.Fourier

/-- The finite angular character sum over an integer interval. -/
def angularSum (a b : ℤ) (angle : ℝ) : ℂ :=
  ∑ x ∈ Finset.Icc a b, character (x : ℝ) angle

/-- Every real angular character has unit modulus. -/
theorem character_norm (frequency angle : ℝ) : ‖character frequency angle‖ = 1 := by
  simp [character, Complex.norm_exp]

/-- Integer multiples of the unit frequency are its actual powers. -/
theorem character_nat (n : ℕ) (angle : ℝ) :
    character (n : ℝ) angle = character 1 angle ^ n := by
  unfold character
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A finite interval character sum is its initial unit phase times a genuine geometric sum. -/
theorem angularSum_geometric (a b : ℤ) (angle : ℝ) :
    angularSum a b angle = character (a : ℝ) angle *
      ∑ n ∈ Finset.range (b + 1 - a).toNat, character 1 angle ^ n := by
  unfold angularSum
  rw [Int.Icc_eq_finset_map, Finset.sum_map, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
    Int.cast_add, Int.cast_natCast]
  rw [← character_mul, ← character_nat]

/-- The denominator of the geometric sum is twice the half-angle sine. -/
theorem character_sub_one (angle : ℝ) :
    ‖character 1 angle - 1‖ = 2 * |Real.sin (angle / 2)| := by
  simp only [character, Complex.ofReal_one, mul_one]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [Real.norm_eq_abs]

/-- A finite angular sum times its half-angle sine has norm at most one. -/
theorem angularSum_sine (a b : ℤ) (angle : ℝ) :
    ‖angularSum a b angle‖ * |Real.sin (angle / 2)| ≤ 1 := by
  let q := character 1 angle
  let n := (b + 1 - a).toNat
  have hq : ‖q‖ = 1 := character_norm 1 angle
  have hgeom := geom_sum_mul q n
  have hnum : ‖q ^ n - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖q ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hq]; norm_num
  have hbound : ‖∑ j ∈ Finset.range n, q ^ j‖ * (2 * |Real.sin (angle / 2)|) ≤ 2 := by
    rw [← character_sub_one angle, ← norm_mul, hgeom]
    exact hnum
  have hs : ‖angularSum a b angle‖ = ‖∑ j ∈ Finset.range n, q ^ j‖ := by
    rw [angularSum_geometric, norm_mul, character_norm, one_mul]
  rw [hs]
  nlinarith

/-- Jordan's inequality gives a lower sine bound throughout a nonresonant compact subinterval. -/
theorem sine_nonresonant (δ z : ℝ) (hδ : 0 ≤ δ) (hlow : δ ≤ |z|)
    (hupp : |z| ≤ Real.pi - δ) :
    2 / Real.pi * δ ≤ |Real.sin z| := by
  have hzpi : |z| ≤ Real.pi := by linarith
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hzpi]
  by_cases hhalf : |z| ≤ Real.pi / 2
  · exact (mul_le_mul_of_nonneg_left hlow (by positivity)).trans
      (Real.mul_le_sin (abs_nonneg z) hhalf)
  · have hm : 0 ≤ Real.pi - |z| := by linarith
    have hmhalf : Real.pi - |z| ≤ Real.pi / 2 := by linarith
    have hb := Real.mul_le_sin hm hmhalf
    rw [Real.sin_pi_sub] at hb
    exact (mul_le_mul_of_nonneg_left (by linarith : δ ≤ Real.pi - |z|)
      (by positivity)).trans hb

/-- A nonresonant angular sum is bounded uniformly in its interval length. -/
theorem angularSum_nonresonant (a b : ℤ) (angle δ : ℝ) (hδ : 0 < δ)
    (hlow : δ ≤ |angle / 2|) (hupp : |angle / 2| ≤ Real.pi - δ) :
    ‖angularSum a b angle‖ ≤ Real.pi / (2 * δ) := by
  have hs := sine_nonresonant δ (angle / 2) hδ.le hlow hupp
  have hsum := angularSum_sine a b angle
  have hprod : ‖angularSum a b angle‖ * (2 / Real.pi * δ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans hsum
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hδ)).mpr
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hm := mul_le_mul_of_nonneg_right hprod hp.le
  have heq : ‖angularSum a b angle‖ * (2 / Real.pi * δ) * Real.pi =
      ‖angularSum a b angle‖ * (2 * δ) := by field_simp
  simpa only [heq, one_mul] using hm


/-- A small perturbation of a nonresonant momentum stays uniformly away from both spectral edges. -/
theorem momentum_window (k ε z : ℝ)
    (hdist : ε < min (Real.pi - |k|) |k|) (hz : |z| ≤ 3 * ε / 4) :
    ε / 4 ≤ |k + z| ∧ |k + z| ≤ Real.pi - ε / 4 := by
  have hklo : ε < |k| := (lt_min_iff.mp hdist).2
  have hkhi : ε < Real.pi - |k| := (lt_min_iff.mp hdist).1
  have hup := abs_add_le k z
  have hlo : |k| ≤ |k + z| + |z| := by
    simpa using abs_add_le (k + z) (-z)
  constructor <;> linarith

/-- The two angular deviations move each individual momentum by at most three quarters epsilon. -/
theorem angular_window (φ1 φ2 ε : ℝ) (h1 : |φ1| ≤ ε) (h2 : |φ2| ≤ ε) :
    |φ1 / 4 + φ2 / 2| ≤ 3 * ε / 4 := by
  have hh := abs_add_le (φ1 / 4) (φ2 / 2)
  rw [abs_div, abs_div] at hh
  norm_num at hh
  linarith

/-- The shifted B kernel factors into the actual two finite geometric character sums. -/
theorem kernel_B_factor (M L : ℕ) (φ1 φ2 k : ℝ) :
    Qatlib.Papers.UniversalWalk12.MainResults.Model.AmpB M L φ1 φ2 k =
      ((1 / (L : ℝ) : ℝ) : ℂ) *
        angularSum (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1)) (φ1 / 2 - φ2 - 2 * k) *
        angularSum ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)) (φ1 / 2 + φ2 + 2 * k) := by
  unfold Qatlib.Papers.UniversalWalk12.MainResults.Model.AmpB angularSum
  have hpoint (x y : ℤ) :
      Complex.exp (Complex.I * (φ1 : ℂ) * ((x + y : ℤ) : ℂ) / 2) *
        Complex.exp (Complex.I * ((φ2 : ℂ) + 2 * (k : ℂ)) * ((y - x : ℤ) : ℂ)) =
      character (x : ℝ) (φ1 / 2 - φ2 - 2 * k) *
        character (y : ℝ) (φ1 / 2 + φ2 + 2 * k) := by
    unfold character
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpoint, ← Finset.mul_sum]
  rw [← Finset.sum_mul, mul_assoc]

/-- The physical small-angle window gives a uniform pointwise bound on the shifted B kernel. -/
theorem kernel_B_bound (M L : ℕ) (hL : 0 < L) (k ε φ1 φ2 : ℝ)
    (hε : 0 < ε) (hdist : ε < min (Real.pi - |k|) |k|)
    (h1 : |φ1| ≤ ε) (h2 : |φ2| ≤ ε) :
    ‖Qatlib.Papers.UniversalWalk12.MainResults.Model.AmpB M L φ1 φ2 k‖ ≤
      4 * Real.pi ^ 2 / ((L : ℝ) * ε ^ 2) := by
  have hδ : 0 < ε / 4 := by positivity
  have hs1 := angular_window (-φ1) φ2 ε (by simpa only [abs_neg] using h1) h2
  have hs2 := angular_window φ1 φ2 ε h1 h2
  have hw1 := momentum_window k ε (-φ1 / 4 + φ2 / 2) hdist hs1
  have hw2 := momentum_window k ε (φ1 / 4 + φ2 / 2) hdist hs2
  have heq1 : (φ1 / 2 - φ2 - 2 * k) / 2 = -(k + (-φ1 / 4 + φ2 / 2)) := by ring
  have heq2 : (φ1 / 2 + φ2 + 2 * k) / 2 = k + (φ1 / 4 + φ2 / 2) := by ring
  have hb1 := angularSum_nonresonant (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1))
    (φ1 / 2 - φ2 - 2 * k) (ε / 4) hδ
    (by simpa only [heq1, abs_neg] using hw1.1)
    (by simpa only [heq1, abs_neg] using hw1.2)
  have hb2 := angularSum_nonresonant ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ))
    (φ1 / 2 + φ2 + 2 * k) (ε / 4) hδ
    (by simpa only [heq2] using hw2.1) (by simpa only [heq2] using hw2.2)
  have hcoeff : ‖((1 / (L : ℝ) : ℝ) : ℂ)‖ = 1 / (L : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [kernel_B_factor, norm_mul, norm_mul, hcoeff]
  calc
    _ ≤ (1 / (L : ℝ)) * (Real.pi / (2 * (ε / 4))) * (Real.pi / (2 * (ε / 4))) := by gcongr
    _ = _ := by field_simp; ring


/-- A continuous integrand bounded on a compact angular square obeys its area bound. -/
theorem rectangle_bound (ε : ℝ) (hε : 0 ≤ ε) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (C : ℝ)
    (hbound : ∀ x ∈ Set.Icc (-ε) ε, ∀ y ∈ Set.Icc (-ε) ε, f (x, y) ≤ C) :
    (∫ x in Set.Icc (-ε) ε, ∫ y in Set.Icc (-ε) ε, f (x, y)) ≤ (2 * ε) ^ 2 * C := by
  let s := Set.Icc (-ε) ε
  have hc : IsCompact (s ×ˢ s) := isCompact_Icc.prod isCompact_Icc
  have hfi : MeasureTheory.IntegrableOn f (s ×ˢ s)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    ContinuousOn.integrableOn_compact hc hf.continuousOn
  have hci : MeasureTheory.IntegrableOn (fun _p : ℝ × ℝ => C)
      (s ×ˢ s) (MeasureTheory.volume.prod MeasureTheory.volume) :=
    ContinuousOn.integrableOn_compact hc continuous_const.continuousOn
  have hi := MeasureTheory.setIntegral_mono_on hfi hci
    (measurableSet_Icc.prod measurableSet_Icc)
    (fun p hp => hbound p.1 hp.1 p.2 hp.2)
  rw [MeasureTheory.setIntegral_prod f hfi, MeasureTheory.setIntegral_prod _ hci] at hi
  calc
    _ ≤ ∫ x in s, ∫ _y in s, C := hi
    _ = _ := by
      simp only [s, MeasureTheory.integral_const, Real.volume_Icc, MeasureTheory.measureReal_def,
        MeasureTheory.Measure.restrict_apply_univ, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ ε - -ε)]
      ring

/-- The shifted B kernel has the exact small-window integral bound of Lemma 5. -/
theorem kernel_B_integral (M L : ℕ) (hL : 0 < L) (k ε : ℝ)
    (hε : 0 < ε) (hdist : ε < min (Real.pi - |k|) |k|) :
    Qatlib.Papers.UniversalWalk12.MainResults.Model.setIntegralR (Set.Icc (-ε) ε) (fun φ1 =>
      Qatlib.Papers.UniversalWalk12.MainResults.Model.setIntegralR (Set.Icc (-ε) ε) (fun φ2 =>
        (1 / (4 * Real.pi ^ 2)) *
          ‖Qatlib.Papers.UniversalWalk12.MainResults.Model.AmpB M L φ1 φ2 k‖ ^ 2)) ≤
      16 * Real.pi ^ 2 / ((L : ℝ) ^ 2 * ε ^ 2) := by
  let C := 16 * Real.pi ^ 4 / ((L : ℝ) ^ 2 * ε ^ 4)
  let f : ℝ × ℝ → ℝ := fun p =>
    (1 / (4 * Real.pi ^ 2)) *
      ‖Qatlib.Papers.UniversalWalk12.MainResults.Model.AmpB M L p.1 p.2 k‖ ^ 2
  have hf : Continuous f := by
    unfold f Qatlib.Papers.UniversalWalk12.MainResults.Model.AmpB
    fun_prop
  have hp : ∀ φ1 ∈ Set.Icc (-ε) ε, ∀ φ2 ∈ Set.Icc (-ε) ε,
      f (φ1, φ2) ≤ (1 / (4 * Real.pi ^ 2)) * C := by
    intro φ1 h1 φ2 h2
    have hb := kernel_B_bound M L hL k ε φ1 φ2 hε hdist
      (abs_le.mpr h1) (abs_le.mpr h2)
    have hs : ‖Qatlib.Papers.UniversalWalk12.MainResults.Model.AmpB M L φ1 φ2 k‖ ^ 2 ≤ C := by
      have hh := (sq_le_sq₀ (norm_nonneg _)
        (show 0 ≤ 4 * Real.pi ^ 2 / ((L : ℝ) * ε ^ 2) by positivity)).mpr hb
      have heq : (4 * Real.pi ^ 2 / ((L : ℝ) * ε ^ 2)) ^ 2 = C := by
        dsimp [C]
        field_simp
        ring
      rwa [heq] at hh
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hi := rectangle_bound ε hε.le f hf ((1 / (4 * Real.pi ^ 2)) * C) hp
  unfold Qatlib.Papers.UniversalWalk12.MainResults.Model.setIntegralR
  calc
    _ ≤ (2 * ε) ^ 2 * ((1 / (4 * Real.pi ^ 2)) * C) := hi
    _ = _ := by
      dsimp [C]
      field_simp
      ring

end Qatlib.Papers.UniversalWalk12.MainResults.Fourier
