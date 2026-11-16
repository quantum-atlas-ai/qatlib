/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClusterColumns
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section


/-!
# Physical Gaussian parameters belong to the certificate cube

The global scalar envelope is proved by a first-derivative inequality. It
places every nonnegative physical spacing, including both collision faces,
inside the same closed five-variable cube used by the exact Gram certificate.
No finite matrix positivity certificate is assumed in this module.
-/

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCompactDomain

open ThreeLevelCluster

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

def gain (s : ℝ) : ℝ := Real.exp (-s^2/8+s/4)

def halfWeight (s : ℝ) : ℝ := Real.exp (-s/2)

def envelopeSum (s : ℝ) : ℝ := 2 * gain s + halfWeight s

/-- Has Deriv At envelope Sum for the stated finite source data. -/
theorem hasDerivAt_envelopeSum (s : ℝ) :
    HasDerivAt envelopeSum
      ((1/2 : ℝ) * ((1-s) * gain s - halfWeight s)) s := by
  unfold envelopeSum gain halfWeight
  convert (((((hasDerivAt_id s).pow 2).neg.div_const 8).add
    ((hasDerivAt_id s).div_const 4)).exp.const_mul 2).add
      (((hasDerivAt_id s).neg.div_const 2).exp) using 1
  · funext u
    rfl
  · simp only [Pi.add_apply, Pi.neg_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, mul_one]
    ring

/-- Gain pos for the stated finite source data. -/
theorem gain_pos (s : ℝ) : 0 < gain s := Real.exp_pos _

/-- Half Weight pos for the stated finite source data. -/
theorem halfWeight_pos (s : ℝ) : 0 < halfWeight s := Real.exp_pos _

/-- Half Weight le one for the stated finite source data. -/
theorem halfWeight_le_one {s : ℝ} (hs : 0 ≤ s) : halfWeight s ≤ 1 := by
  unfold halfWeight
  apply Real.exp_le_one_iff.mpr
  linarith

/-- Envelope derivative nonpos for the stated finite source data. -/
theorem envelope_derivative_nonpos {s : ℝ} (hs : 0 ≤ s) :
    (1/2 : ℝ) * ((1-s) * gain s - halfWeight s) ≤ 0 := by
  have hone : 1-s ≤ Real.exp (-s) := by
    have h := Real.add_one_le_exp (-s)
    linarith
  have hprod := mul_le_mul_of_nonneg_right hone (gain_pos s).le
  have hexp : Real.exp (-s) * gain s ≤ halfWeight s := by
    unfold gain halfWeight
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg s]
  nlinarith

/-- Envelope Sum antitone for the stated finite source data. -/
theorem envelopeSum_antitone : AntitoneOn envelopeSum (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
      (by unfold envelopeSum gain halfWeight; fun_prop)
      (fun x _ => (hasDerivAt_envelopeSum x).hasDerivWithinAt)
  intro x hx
  apply envelope_derivative_nonpos
  have hx' : 0 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
  exact hx'.le

/-- The exact global envelope used by the physical compactification. -/
theorem gain_le_envelope {s : ℝ} (hs : 0 ≤ s) :
    gain s ≤ (3-halfWeight s)/2 := by
  have h := envelopeSum_antitone (show (0 : ℝ) ∈ Set.Ici 0 by simp) hs hs
  norm_num [envelopeSum, gain, halfWeight] at h
  dsimp [gain, halfWeight]
  linarith

/-- Compact denominator pos for the stated finite source data. -/
theorem compact_denominator_pos {s : ℝ} (hs : 0 ≤ s) :
    0 < 3-halfWeight s := by
  have h := halfWeight_le_one hs
  linarith

def compactAmplitude (s : ℝ) : ℝ := 2 * gain s / (3-halfWeight s)

/-- Compact Amplitude pos for the stated finite source data. -/
theorem compactAmplitude_pos {s : ℝ} (hs : 0 ≤ s) :
    0 < compactAmplitude s :=
  div_pos (mul_pos (by norm_num) (gain_pos s)) (compact_denominator_pos hs)

/-- Compact Amplitude le one for the stated finite source data. -/
theorem compactAmplitude_le_one {s : ℝ} (hs : 0 ≤ s) :
    compactAmplitude s ≤ 1 := by
  unfold compactAmplitude
  apply (div_le_one (compact_denominator_pos hs)).mpr
  have h := gain_le_envelope hs
  linarith

/-- Gain eq compact Amplitude for the stated finite source data. -/
theorem gain_eq_compactAmplitude {s : ℝ} (hs : 0 ≤ s) :
    gain s = compactAmplitude s * (3-halfWeight s)/2 := by
  unfold compactAmplitude
  field_simp [ne_of_gt (compact_denominator_pos hs)]

def mixedWeight (s t : ℝ) : ℝ := Real.exp (-s*t/4)

/-- Mixed Weight pos for the stated finite source data. -/
theorem mixedWeight_pos (s t : ℝ) : 0 < mixedWeight s t := Real.exp_pos _

/-- Mixed Weight le one for the stated finite source data. -/
theorem mixedWeight_le_one {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    mixedWeight s t ≤ 1 := by
  unfold mixedWeight
  apply Real.exp_le_one_iff.mpr
  have h := mul_nonneg hs ht
  nlinarith

/-- Gain add for the stated finite source data. -/
theorem gain_add (s t : ℝ) :
    gain (s+t) = gain s * gain t * mixedWeight s t := by
  unfold gain mixedWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The actual Gaussian gain is bounded independently of spacing. -/
theorem gain_le_exp_one_eighth (s : ℝ) : gain s ≤ Real.exp (1/8) := by
  unfold gain
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (s-1)]

/-- Exp one quarter lt four thirds for the stated finite source data. -/
theorem exp_one_quarter_lt_four_thirds :
    Real.exp (1/4) < (4/3 : ℝ) := by
  have h := Real.add_one_lt_exp (by norm_num : (-1/4 : ℝ) ≠ 0)
  have hprod : Real.exp (1/4) * Real.exp (-1/4) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul := mul_lt_mul_of_pos_left h (Real.exp_pos (1/4))
  nlinarith

/-- Gain sq lt four thirds for the stated finite source data. -/
theorem gain_sq_lt_four_thirds (s : ℝ) : gain s ^ 2 < (4/3 : ℝ) := by
  calc
    gain s ^ 2 = Real.exp (-s^2/4+s/2) := by
      unfold gain
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (1/4) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (s-1)]
    _ < 4/3 := exp_one_quarter_lt_four_thirds

/-- Half Weight mul gain le one for the stated finite source data. -/
theorem halfWeight_mul_gain_le_one {s : ℝ} (hs : 0 ≤ s) :
    halfWeight s * gain s ≤ 1 := by
  unfold halfWeight gain
  rw [← Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg s]

/-- First cross coefficient le one for the stated finite source data. -/
theorem first_cross_coefficient_le_one {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    halfWeight t * gain t * mixedWeight s t ≤ 1 := by
  have h := mul_le_mul (halfWeight_mul_gain_le_one ht) (mixedWeight_le_one hs ht)
    (mixedWeight_pos s t).le (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using h

/-- Second cross coefficient sq lt four thirds for the stated finite source data. -/
theorem second_cross_coefficient_sq_lt_four_thirds {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (gain s * mixedWeight s t)^2 < (4/3 : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (mixedWeight_le_one hs ht) (gain_pos s).le
  rw [mul_one] at h
  have hn : 0 ≤ gain s * mixedWeight s t :=
    mul_nonneg (gain_pos s).le (mixedWeight_pos s t).le
  exact (pow_le_pow_left₀ hn h 2).trans_lt (gain_sq_lt_four_thirds s)

/-- Sum of the two squared thermal Gaussian amplitudes on an unordered
Hermitian spectral pair. -/
def pairedSquare (s : ℝ) : ℝ :=
  Real.exp (-s^2/4+s/2) + Real.exp (-s^2/4-s/2)

/-- Has Deriv At paired Square for the stated finite source data. -/
theorem hasDerivAt_pairedSquare (s : ℝ) :
    HasDerivAt pairedSquare
      ((1/2 : ℝ) * ((1-s) * Real.exp (-s^2/4+s/2) -
        (1+s) * Real.exp (-s^2/4-s/2))) s := by
  unfold pairedSquare
  convert (((((hasDerivAt_id s).pow 2).neg.div_const 4).add
    ((hasDerivAt_id s).div_const 2)).exp).add
      (((((hasDerivAt_id s).pow 2).neg.div_const 4).sub
        ((hasDerivAt_id s).div_const 2)).exp) using 1
  · funext u
    rfl
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

/-- Paired Square derivative nonpos for the stated finite source data. -/
theorem pairedSquare_derivative_nonpos {s : ℝ} (hs : 0 ≤ s) :
    (1/2 : ℝ) * ((1-s) * Real.exp (-s^2/4+s/2) -
      (1+s) * Real.exp (-s^2/4-s/2)) ≤ 0 := by
  have hone : 1-s ≤ Real.exp (-s) := by
    have h := Real.add_one_le_exp (-s)
    linarith
  have h := mul_le_mul_of_nonneg_right hone (Real.exp_pos (-s^2/4+s/2)).le
  have he : Real.exp (-s) * Real.exp (-s^2/4+s/2) =
      Real.exp (-s^2/4-s/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  nlinarith [Real.exp_pos (-s^2/4-s/2)]

/-- Paired Square antitone for the stated finite source data. -/
theorem pairedSquare_antitone : AntitoneOn pairedSquare (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
      (by unfold pairedSquare; fun_prop)
      (fun x _ => (hasDerivAt_pairedSquare x).hasDerivWithinAt)
  intro x hx
  apply pairedSquare_derivative_nonpos
  have hx' : 0 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
  exact hx'.le

/-- Paired Square neg for the stated finite source data. -/
theorem pairedSquare_neg (s : ℝ) : pairedSquare (-s) = pairedSquare s := by
  unfold pairedSquare
  have h₁ : -(-s)^2/4+(-s)/2 = -s^2/4-s/2 := by ring
  have h₂ : -(-s)^2/4-(-s)/2 = -s^2/4+s/2 := by ring
  rw [h₁, h₂, add_comm]

/-- Paired Square le two for the stated finite source data. -/
theorem pairedSquare_le_two (s : ℝ) : pairedSquare s ≤ 2 := by
  have hnonneg (x : ℝ) (hx : 0 ≤ x) : pairedSquare x ≤ 2 := by
    have h := pairedSquare_antitone (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
    norm_num [pairedSquare] at h
    exact h
  by_cases hs : 0 ≤ s
  · exact hnonneg s hs
  · rw [← pairedSquare_neg]
    exact hnonneg (-s) (by linarith)

/-- The paired sharp/flat square bound is uniform in every signed frequency.
It is the scalar input for the Hermitian Gaussian HS contraction argument. -/
theorem paired_thermal_gaussian_bound (s : ℝ) :
    gain s ^ 2 + (halfWeight s * gain s)^2 ≤ 2 := by
  have h₁ : gain s ^ 2 = Real.exp (-s^2/4+s/2) := by
    unfold gain
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h₂ : (halfWeight s * gain s)^2 = Real.exp (-s^2/4-s/2) := by
    unfold gain halfWeight
    simp only [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h₁, h₂]
  exact pairedSquare_le_two s

/-- The literal complex amplitude used by the existing source modules. -/
theorem smallAmplitude_eq_gain (s : ℝ) : smallAmplitude s = (gain s : ℂ) := rfl

/-- Quarter Amplitude sq eq half Weight for the stated finite source data. -/
theorem quarterAmplitude_sq_eq_halfWeight (s : ℝ) :
    quarterAmplitude s ^ 2 = (halfWeight s : ℂ) := by
  rw [quarterAmplitude_square]
  rfl

/-- Small Amplitude eq compact for the stated finite source data. -/
theorem smallAmplitude_eq_compact {s : ℝ} (hs : 0 ≤ s) :
    smallAmplitude s =
      (compactAmplitude s : ℂ) * (3-(halfWeight s : ℂ))/2 := by
  rw [smallAmplitude_eq_gain, gain_eq_compactAmplitude hs]
  push_cast
  rfl

/-- Collision Parameter eq mixed Weight for the stated finite source data. -/
theorem collisionParameter_eq_mixedWeight (s t : ℝ) :
    collisionParameter s t = (mixedWeight s t : ℂ) := rfl

def cubePoint (s t : ℝ) : Fin 5 → ℝ :=
  ![halfWeight s, halfWeight t, compactAmplitude s, compactAmplitude t, mixedWeight s t]

/-- Cube Point mem Icc for the stated finite source data. -/
theorem cubePoint_mem_Icc {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (i : Fin 5) :
    cubePoint s t i ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i
  · exact ⟨(halfWeight_pos s).le, halfWeight_le_one hs⟩
  · exact ⟨(halfWeight_pos t).le, halfWeight_le_one ht⟩
  · exact ⟨(compactAmplitude_pos hs).le, compactAmplitude_le_one hs⟩
  · exact ⟨(compactAmplitude_pos ht).le, compactAmplitude_le_one ht⟩
  · exact ⟨(mixedWeight_pos s t).le, mixedWeight_le_one hs ht⟩

/-- Cube Point zero for the stated finite source data. -/
theorem cubePoint_zero : cubePoint 0 0 = (fun _ => 1) := by
  funext i
  fin_cases i <;> norm_num [cubePoint, halfWeight, compactAmplitude, gain, mixedWeight]


end

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCompactDomain
