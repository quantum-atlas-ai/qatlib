/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCore
import Qatlib.Concepts.ChoiKraus.ChoiKrausChar.ChannelStructure
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.SpectralSketch.SketchSpectral.SvtGramTransferSamp
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreAuxiliary
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.LinearAlgebra.Lagrange
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureMeasurement
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureNaimark
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
import Qatlib.Concepts.ChannelTheory.TwirlChannel

/-!
# Central binomial sign approximation materials

This module constructs the odd polynomials `spoly` from normalized central binomial coefficients
`cReal`. Trigonometric moment identities and an explicit integral evaluation bound their
magnitude on `[-1, 1]` and their error from one on `[1/2, 1]`, with a linear degree bound in the
truncation index. The mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `elliptic_eq`: an explicit trigonometric integral used to bound the coefficient sum.
* `spoly_tail`: geometric error control on the positive interval.
* `spoly_natDegree_le`: degree at most `2 * K + 1`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped BigOperators



namespace Qatlib.Concepts.QsvtCore.ApproxToolkit
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator Classical BigOperators
open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Module Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib
open Qatlib
set_option autoImplicit false
open Polynomial Real
open scoped BigOperators
open Qatlib
open Real intervalIntegral MeasureTheory Polynomial
set_option warningAsError false
noncomputable section

/-- The central binomial coefficient `choose (2 * i) i`, normalized by `4 ^ i` and viewed as a
real number. -/
noncomputable def cReal (i : ℕ) : ℝ := (2 * i).choose i / (4 : ℝ) ^ i
end
noncomputable section

/-- Every normalized central binomial coefficient `cReal i` is positive. -/
lemma cReal_pos (i : ℕ) : 0 < cReal i := by
  have h : 0 < (2 * i).choose i := Nat.choose_pos (by omega)
  unfold cReal
  positivity
end
noncomputable section

/-- Every normalized central binomial coefficient `cReal i` is at most one. -/
lemma cReal_le_one (i : ℕ) : cReal i ≤ 1 := by
  have h : (2 * i).choose i ≤ 4 ^ i := Nat.centralBinom_le_four_pow i
  rw [cReal, div_le_one (by positivity : (0 : ℝ) < (4 : ℝ) ^ i)]
  exact_mod_cast h
end
noncomputable section

/-- Successive normalized central binomial coefficients have ratio `(2 * i + 1) / (2 * i + 2)`. -/
lemma cReal_succ (i : ℕ) :
    cReal (i + 1) = (2 * i + 1) / (2 * i + 2) * cReal i := by
  have h := Nat.succ_mul_centralBinom_succ i
  have E : (((i + 1) * (2 * (i + 1)).choose (i + 1) : ℕ) : ℝ)
      = ((2 * (2 * i + 1) * (2 * i).choose i : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at E
  show (2 * (i + 1)).choose (i + 1) / (4 : ℝ) ^ (i + 1)
      = (2 * i + 1) / (2 * i + 2) * ((2 * i).choose i / (4 : ℝ) ^ i)
  have h4 : (4 : ℝ) ^ (i + 1) = 4 * (4 : ℝ) ^ i := by rw [pow_succ]; ring
  rw [h4]
  have hne4 : (4 : ℝ) ^ i ≠ 0 := by positivity
  have hne2 : ((2 : ℝ) * ((i : ℝ)) + 2) ≠ 0 := by positivity
  have hne42 : ((4 : ℝ) * (4 : ℝ) ^ i) ≠ 0 := by positivity
  field_simp
  nlinarith [E]
end
noncomputable section

/-- The integral of `sin x ^ (2 * i)` from zero to `π / 2`. -/
noncomputable def mom (i : ℕ) : ℝ := ∫ x in (0 : ℝ)..π / 2, sin x ^ (2 * i)
end
noncomputable section

/-- The zeroth sine moment equals `π / 2`. -/
lemma mom_zero : mom 0 = π / 2 := by
  have h1 : mom 0 = ∫ x in (0 : ℝ)..π / 2, (1 : ℝ) := by
    simp only [mom, Nat.mul_zero, pow_zero]
  rw [h1, intervalIntegral.integral_const]
  ring
end
noncomputable section

/-- Successive even sine moments have ratio `(2 * i + 1) / (2 * i + 2)`. -/
lemma mom_succ (i : ℕ) : mom (i + 1) = (2 * i + 1) / (2 * i + 2) * mom i := by
  have h2 : 2 * (i + 1) = 2 * i + 2 := by ring
  have key := integral_sin_pow (n := 2 * i) (a := (0 : ℝ)) (b := π / 2)
  rw [mom, mom, h2, key]
  have hb : sin (0 : ℝ) ^ (2 * i + 1) * cos 0 = 0 := by
    simp [Real.sin_zero]
  have he : sin (π / 2) ^ (2 * i + 1) * cos (π / 2) = 0 := by
    simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [hb, he, sub_zero, zero_div, _root_.zero_add]
  have hc : ((2 * i : ℕ) : ℝ) = 2 * ((i : ℝ)) := by push_cast; ring
  rw [hc]
end
noncomputable section

/-- The zeroth normalized central binomial coefficient is one. -/
lemma cReal_zero : cReal 0 = 1 := by
  show (2 * 0).choose 0 / (4 : ℝ) ^ 0 = 1
  have h0 : (2 * 0).choose 0 = 1 := by decide
  rw [h0, pow_zero, div_one]
  norm_num
end
noncomputable section

/-- Multiplying the even sine moment by `2 / π` gives the normalized central binomial
coefficient. -/
lemma two_div_pi_mom (i : ℕ) : 2 / π * mom i = cReal i := by
  induction i with
  | zero =>
    have hp : (π : ℝ) ≠ 0 := by positivity
    rw [mom_zero, cReal_zero]
    field_simp
  | succ i ih =>
    rw [mom_succ, cReal_succ, ← ih]
    ring
end
noncomputable section

/-- A finite geometric sum with ratio different from one equals `(1 - s ^ n) / (1 - s)`. -/
lemma geom_sum_formula (s : ℝ) (hs1 : s ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, s ^ i = (1 - s ^ n) / (1 - s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring
end
noncomputable section

/-- A finite geometric sum with ratio in `[0, 1)` is at most `1 / (1 - s)`. -/
lemma geom_sum_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, s ^ i ≤ 1 / (1 - s) := by
  have hlt : 0 < 1 - s := by linarith
  rw [geom_sum_formula s (by linarith : s ≠ 1) n]
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 - s) (by linarith : (0 : ℝ) < 1 - s)]
  have h0 : (0 : ℝ) ≤ s ^ n := pow_nonneg hs0 n
  nlinarith
end
noncomputable section

/-- The cotangent function expressed as `cos x / sin x`. -/
noncomputable def coty (x : ℝ) : ℝ := cos x / sin x
end
noncomputable section

/-- The cotangent of `π / 4` is one. -/
lemma coty_pi_div_four : coty (π / 4) = 1 := by
  have h : sin (π / 4) = cos (π / 4) := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  rw [coty, ← h]
  refine div_self ?_
  rw [Real.sin_pi_div_four]
  positivity
end
noncomputable section

/-- The cotangent of `π / 2` is zero. -/
lemma coty_pi_div_two : coty (π / 2) = 0 := by
  rw [coty, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num
end
noncomputable section

/-- Where the sine is nonzero, the derivative of cotangent is `-(1 + coty x ^ 2)`. -/
lemma hasDerivAt_coty {x : ℝ} (hx : sin x ≠ 0) :
    HasDerivAt coty (-(1 + coty x ^ 2)) x := by
  have h1 : HasDerivAt (fun y => cos y / sin y)
      ((-sin x * sin x - cos x * cos x) / sin x ^ 2) x :=
    (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx
  have he : coty = fun y => cos y / sin y := rfl
  rw [he]
  convert! h1 using 1
  show -(1 + (cos x / sin x) ^ 2) = (-sin x * sin x - cos x * cos x) / sin x ^ 2
  field_simp [sin_sq_add_cos_sq]
  ring
end
noncomputable section

/-- The scaled arctangent expression `(√c)⁻¹ * arctan (√c * tan x)`. -/
noncomputable def A1 (c : ℝ) (x : ℝ) : ℝ := (√c)⁻¹ * arctan (√c * tan x)
end
noncomputable section

/-- The scaled arctangent expression `(√c)⁻¹ * arctan (coty x / √c)`. -/
noncomputable def A2 (c : ℝ) (x : ℝ) : ℝ := (√c)⁻¹ * arctan (coty x / √c)
end
noncomputable section

/-- For positive `c` and nonzero cosine, `A1 c` has derivative `(1 + tan x ^ 2) / (1 + c * tan x
^ 2)`. -/
lemma hasDerivAt_A1 (c : ℝ) (hc : 0 < c) {x : ℝ} (hx : cos x ≠ 0) :
    HasDerivAt (A1 c) ((1 + tan x ^ 2) / (1 + c * tan x ^ 2)) x := by
  have hcs : (√c)⁻¹ * √c = 1 := inv_mul_cancel₀ (by positivity)
  have htan : 1 + tan x ^ 2 = 1 / cos x ^ 2 := by
    have e : 1 + tan x ^ 2 = (sin x ^ 2 + cos x ^ 2) / cos x ^ 2 := by
      rw [Real.tan_eq_sin_div_cos, div_pow]
      field_simp
      ring
    rw [e, sin_sq_add_cos_sq]
  have ht : HasDerivAt tan (1 / cos x ^ 2) x := Real.hasDerivAt_tan hx
  have hT : HasDerivAt (fun y => √c * tan y) (√c * (1 / cos x ^ 2)) x :=
    ht.const_mul _
  have harc : HasDerivAt (fun y => arctan (√c * tan y))
      ((1 / (1 + (√c * tan x) ^ 2)) * (√c * (1 / cos x ^ 2))) x :=
    (Real.hasDerivAt_arctan _).comp x hT
  have hfin : HasDerivAt (A1 c)
      ((√c)⁻¹ * ((1 / (1 + (√c * tan x) ^ 2)) * (√c * (1 / cos x ^ 2)))) x :=
    harc.const_mul _
  have hsq : (√c * tan x) ^ 2 = c * tan x ^ 2 := by
    rw [mul_pow, sq_sqrt (le_of_lt hc)]
  have hde : (√c)⁻¹ * ((1 / (1 + (√c * tan x) ^ 2)) * (√c * (1 / cos x ^ 2)))
      = (1 + tan x ^ 2) / (1 + c * tan x ^ 2) := by
    rw [hsq, ← htan]
    field_simp
  exact hde ▸ hfin
end
noncomputable section

/-- For positive `c` and nonzero sine, `A2 c` has derivative `-((1 + coty x ^ 2) / (c + coty x ^
2))`. -/
lemma hasDerivAt_A2 (c : ℝ) (hc : 0 < c) {x : ℝ} (hx : sin x ≠ 0) :
    HasDerivAt (A2 c) (-((1 + coty x ^ 2) / (c + coty x ^ 2))) x := by
  have hsc : √c ≠ 0 := by positivity
  have hdiv : (coty x / √c) ^ 2 = coty x ^ 2 / c := by
    rw [div_pow, sq_sqrt (le_of_lt hc)]
  have hT : HasDerivAt (fun y => coty y / √c) (-(1 + coty x ^ 2) / √c) x :=
    (hasDerivAt_coty hx).div_const _
  have harc : HasDerivAt (fun y => arctan (coty y / √c))
      ((1 / (1 + (coty x / √c) ^ 2)) * (-(1 + coty x ^ 2) / √c)) x :=
    (Real.hasDerivAt_arctan _).comp x hT
  have hfin : HasDerivAt (A2 c)
      ((√c)⁻¹ * ((1 / (1 + (coty x / √c) ^ 2)) * (-(1 + coty x ^ 2) / √c))) x :=
    harc.const_mul _
  have hde : (√c)⁻¹ * ((1 / (1 + (coty x / √c) ^ 2)) * (-(1 + coty x ^ 2) / √c))
      = -((1 + coty x ^ 2) / (c + coty x ^ 2)) := by
    have hcne : (c : ℝ) ≠ 0 := ne_of_gt hc
    rw [hdiv]
    field_simp
    rw [sq_sqrt (le_of_lt hc)]
  exact hde ▸ hfin
end
noncomputable section

/-- For positive `c`, the expression `cos x ^ 2 + c * sin x ^ 2` is positive. -/
lemma denom_pos (c : ℝ) (hc0 : 0 < c) (x : ℝ) :
    0 < cos x ^ 2 + c * sin x ^ 2 := by
  have hpy : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
  have hcc0 : (0 : ℝ) ≤ cos x ^ 2 := sq_nonneg _
  have hs0 : (0 : ℝ) ≤ sin x ^ 2 := sq_nonneg _
  by_cases h : c ≤ 1
  · have hle : c * (sin x ^ 2 + cos x ^ 2) ≤ cos x ^ 2 + c * sin x ^ 2 := by
      nlinarith
    rw [hpy] at hle
    nlinarith
  · have hle : (1 : ℝ) * (sin x ^ 2 + cos x ^ 2) ≤ cos x ^ 2 + c * sin x ^ 2 := by
      nlinarith
    rw [hpy] at hle
    nlinarith
end
noncomputable section

/-- For positive `c`, the integral of `1 / (1 - (1 - c) * sin x ^ 2)` over `[0, π / 2]` equals
`π / (2 * √c)`. -/
lemma elliptic_eq (c : ℝ) (hc0 : 0 < c) :
    ∫ x in (0 : ℝ)..π / 2, 1 / (1 - (1 - c) * sin x ^ 2) = π / (2 * √c) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hp2 : (0 : ℝ) < π / 2 := by positivity
  have h34 : (π / 4 : ℝ) < π / 2 := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hpi]
  have hle4 : (π / 4 : ℝ) ≤ π / 2 := le_of_lt h34
  have hcos : ∀ x ∈ Set.Icc (0 : ℝ) (π / 4), cos x ≠ 0 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have h1 : x ∈ Set.Ioo (-(π / 2) : ℝ) (π / 2) := by
      constructor
      · have h2 : (0 : ℝ) < π / 2 := by positivity
        linarith
      · linarith
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h1)
  have hsin : ∀ x ∈ Set.Icc (π / 4 : ℝ) (π / 2), sin x ≠ 0 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have h1 : 0 < x := by
      have h2 : (0 : ℝ) < π / 4 := by positivity
      linarith
    have h2 : x < π := by linarith
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have r1 : ∀ x ∈ Set.Icc (0 : ℝ) (π / 4),
      1 / (1 - (1 - c) * sin x ^ 2) = (1 + tan x ^ 2) / (1 + c * tan x ^ 2) := by
    intro x hx
    have hx' := hcos x hx
    have hcc : cos x ^ 2 ≠ 0 := pow_ne_zero _ hx'
    have hpy : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
    have hdp : cos x ^ 2 + c * sin x ^ 2 ≠ 0 := ne_of_gt (denom_pos c hc0 x)
    have e1 : 1 - (1 - c) * sin x ^ 2 = cos x ^ 2 + c * sin x ^ 2 := by
      nlinarith [hpy]
    have h1 : 1 + tan x ^ 2 = (sin x ^ 2 + cos x ^ 2) / cos x ^ 2 := by
      simp only [Real.tan_eq_sin_div_cos, div_pow]
      field_simp
      ring
    have h2 : 1 + c * tan x ^ 2 = (cos x ^ 2 + c * sin x ^ 2) / cos x ^ 2 := by
      simp only [Real.tan_eq_sin_div_cos, div_pow]
      field_simp
    have hstep : ((sin x ^ 2 + cos x ^ 2) / cos x ^ 2) / ((cos x ^ 2 + c * sin x ^ 2) / cos x ^ 2)
        = (sin x ^ 2 + cos x ^ 2) / (cos x ^ 2 + c * sin x ^ 2) := by
      field_simp
    rw [e1, h1, h2, hstep, hpy]
  have r2 : ∀ x ∈ Set.Icc (π / 4 : ℝ) (π / 2),
      1 / (1 - (1 - c) * sin x ^ 2) = (1 + coty x ^ 2) / (c + coty x ^ 2) := by
    intro x hx
    have hx' := hsin x hx
    have hs2 : sin x ^ 2 ≠ 0 := pow_ne_zero _ hx'
    have hpy : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
    have hdp : c * sin x ^ 2 + cos x ^ 2 ≠ 0 := by
      have := denom_pos c hc0 x
      linarith [this]
    have e1 : 1 - (1 - c) * sin x ^ 2 = cos x ^ 2 + c * sin x ^ 2 := by
      nlinarith [hpy]
    have h1 : 1 + coty x ^ 2 = (sin x ^ 2 + cos x ^ 2) / sin x ^ 2 := by
      simp only [coty, div_pow]
      field_simp
    have h2 : c + coty x ^ 2 = (c * sin x ^ 2 + cos x ^ 2) / sin x ^ 2 := by
      simp only [coty, div_pow]
      field_simp
    have hstep : ((sin x ^ 2 + cos x ^ 2) / sin x ^ 2) / ((c * sin x ^ 2 + cos x ^ 2) / sin x ^ 2)
        = (sin x ^ 2 + cos x ^ 2) / (c * sin x ^ 2 + cos x ^ 2) := by
      field_simp
    rw [e1, h1, h2, hstep, hpy]
    congr 1
    ring
  have hcint : ∀ x : ℝ, (1 : ℝ) - (1 - c) * sin x ^ 2 ≠ 0 := by
    intro x
    have hpy : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
    have e1 : 1 - (1 - c) * sin x ^ 2 = cos x ^ 2 + c * sin x ^ 2 := by
      nlinarith [hpy]
    rw [e1]
    exact ne_of_gt (denom_pos c hc0 x)
  have hint1 : IntervalIntegrable (fun x => 1 / (1 - (1 - c) * sin x ^ 2)) volume 0 (π / 4) :=
    (Continuous.div continuous_const (by fun_prop) hcint).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => 1 / (1 - (1 - c) * sin x ^ 2)) volume (π / 4) (π / 2) :=
    (Continuous.div continuous_const (by fun_prop) hcint).intervalIntegrable _ _
  have hint1' : IntervalIntegrable (fun x => (1 + tan x ^ 2) / (1 + c * tan x ^ 2)) volume 0
      (π / 4) := by
    have hsub : Set.Icc (0 : ℝ) (π / 4) ⊆ {x : ℝ | cos x ≠ 0} := fun x hx => hcos x hx
    have htc : ContinuousOn tan (Set.Icc (0 : ℝ) (π / 4)) :=
      Real.continuousOn_tan.mono hsub
    exact ContinuousOn.intervalIntegrable_of_Icc (by positivity)
      (ContinuousOn.div (continuousOn_const.add (htc.pow 2))
        (continuousOn_const.add (continuousOn_const.mul (htc.pow 2)))
        (by
          intro x _
          positivity))
  have hcot : ContinuousOn coty (Set.Icc (π / 4 : ℝ) (π / 2)) := by
    unfold coty
    exact ContinuousOn.div continuous_cos.continuousOn continuous_sin.continuousOn
      (fun x hx => hsin x hx)
  have hint2' : IntervalIntegrable (fun x => (1 + coty x ^ 2) / (c + coty x ^ 2)) volume (π / 4)
      (π / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hle4
      (ContinuousOn.div (continuousOn_const.add (hcot.pow 2))
        (continuousOn_const.add (hcot.pow 2))
        (by
          intro x _
          positivity))
  have I1 : ∫ x in (0 : ℝ)..π / 4, 1 / (1 - (1 - c) * sin x ^ 2)
      = A1 c (π / 4) - A1 c 0 := by
    rw [intervalIntegral.integral_congr (f := fun x => 1 / (1 - (1 - c) * sin x ^ 2))
      (g := fun x => (1 + tan x ^ 2) / (1 + c * tan x ^ 2))
      (by
        intro x hx
        have hx' : x ∈ Set.Icc (0 : ℝ) (π / 4) := by
          have : x ∈ Set.uIcc (0 : ℝ) (π / 4) := hx
          rwa [Set.uIcc_of_le (by positivity)] at this
        exact r1 x hx')]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_A1 c hc0 (hcos x (by
        have : x ∈ Set.uIcc (0 : ℝ) (π / 4) := hx
        rwa [Set.uIcc_of_le (by positivity)] at this)))
      hint1'
  have I2 : ∫ x in π / 4..π / 2, 1 / (1 - (1 - c) * sin x ^ 2)
      = -(A2 c (π / 2)) + A2 c (π / 4) := by
    rw [intervalIntegral.integral_congr (f := fun x => 1 / (1 - (1 - c) * sin x ^ 2))
      (g := fun x => (1 + coty x ^ 2) / (c + coty x ^ 2))
      (by
        intro x hx
        have hx' : x ∈ Set.Icc (π / 4 : ℝ) (π / 2) := by
          have : x ∈ Set.uIcc (π / 4 : ℝ) (π / 2) := hx
          rwa [Set.uIcc_of_le hle4] at this
        exact r2 x hx')]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := π / 4) (b := π / 2)
      (f := fun x => -(A2 c x)) (f' := fun x => (1 + coty x ^ 2) / (c + coty x ^ 2))
      (fun x hx => by
        have hdx : HasDerivAt (A2 c) (-((1 + coty x ^ 2) / (c + coty x ^ 2))) x :=
          hasDerivAt_A2 c hc0 (hsin x (by
            have : x ∈ Set.uIcc (π / 4 : ℝ) (π / 2) := hx
            rwa [Set.uIcc_of_le hle4] at this))
        simpa using! hdx.neg)
      hint2'
    rw [hftc]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, I1, I2]
  simp only [A1, A2, Real.tan_pi_div_four, coty_pi_div_four, coty_pi_div_two,
    Real.tan_zero, Real.arctan_zero, zero_div, mul_zero, mul_one, sub_zero]
  rw [one_div, Real.arctan_inv_of_pos (show (0 : ℝ) < √c by positivity)]
  have hsc : √c ≠ 0 := by positivity
  field_simp
  ring
end
noncomputable section

/-- The sum of `cReal i * s ^ i` over indices from zero through `K`. -/
noncomputable def wsum (K : ℕ) (s : ℝ) : ℝ := ∑ i ∈ Finset.range (K + 1), cReal i * s ^ i
end
noncomputable section

/-- A finite sum of interval integrable real functions is interval integrable. -/
lemma intervalIntegrable_sum_range {f : ℕ → ℝ → ℝ} (n : ℕ) (a b : ℝ)
    (hint : ∀ i, i < n → IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ Finset.range n, f i x) volume a b := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact intervalIntegrable_const
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    exact (ih (fun i hi => hint i (by omega))).add (hint n (Nat.lt_succ_self n))
end
noncomputable section

/-- Integration over a real interval commutes with a finite sum of interval integrable
functions. -/
lemma integral_sum_range {f : ℕ → ℝ → ℝ} (n : ℕ) (a b : ℝ)
    (hint : ∀ i < n, IntervalIntegrable (f i) volume a b) :
    ∫ x in a..b, ∑ i ∈ Finset.range n, f i x = ∑ i ∈ Finset.range n, ∫ x in a..b, f i x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum := intervalIntegrable_sum_range n a b (fun i hi => hint i (by omega))
    have hn := hint n (Nat.lt_succ_self n)
    simp only [Finset.sum_range_succ, intervalIntegral.integral_add hsum hn]
    rw [ih (fun i hi => hint i (by omega))]
end
noncomputable section

/-- The integral of `(s * sin x ^ 2) ^ i` over `[0, π / 2]` equals `s ^ i * (π / 2) * cReal i`. -/
lemma pow_moment (i : ℕ) (s : ℝ) :
    ∫ x in (0 : ℝ)..π / 2, (s * sin x ^ 2) ^ i = s ^ i * (π / 2) * cReal i := by
  have hcongr : ∀ x : ℝ, (s * sin x ^ 2) ^ i = s ^ i * sin x ^ (2 * i) := by
    intro x; rw [mul_pow]; congr 1; ring
  rw [intervalIntegral.integral_congr (by intro x hx; exact hcongr x),
    intervalIntegral.integral_const_mul (s ^ i) (fun x => sin x ^ (2 * i)),
    show ∫ x in (0 : ℝ)..π / 2, sin x ^ (2 * i) = mom i from rfl,
    ← two_div_pi_mom i]
  have hp : (π : ℝ) ≠ 0 := by positivity
  field_simp
end
noncomputable section

/-- The weighted coefficient sum is `2 / π` times the integral of the corresponding finite
geometric sum in `s * sin x ^ 2`. -/
lemma wsum_eq (K : ℕ) (s : ℝ) :
    wsum K s = 2 / π * ∫ x in (0 : ℝ)..π / 2,
      ∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i := by
  have hint : ∀ i < K + 1, IntervalIntegrable (fun x => (s * sin x ^ 2) ^ i) volume 0 (π / 2) :=
    fun i _ => (by fun_prop : Continuous fun x => (s * sin x ^ 2) ^ i).intervalIntegrable _ _
  rw [wsum, integral_sum_range (K + 1) 0 (π / 2) hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_moment i s]
  have hp : (π : ℝ) ≠ 0 := by positivity
  field_simp
end
noncomputable section

/-- The weighted coefficient sum is nonnegative for a nonnegative argument. -/
lemma wsum_nonneg (K : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ wsum K s := by
  unfold wsum
  exact Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (cReal_pos i)) (pow_nonneg hs _)
end
noncomputable section

/-- The square of the sine of any real number is at most one. -/
lemma sin_sq_le_one' (x : ℝ) : sin x ^ 2 ≤ 1 := by
  have h2 := (abs_le.mp (Real.abs_sin_le_one x)).1
  have h3 := (abs_le.mp (Real.abs_sin_le_one x)).2
  nlinarith
end
noncomputable section

/-- For `s` in `[0, 1)`, the weighted coefficient sum is at most `1 / √(1 - s)`. -/
lemma wsum_le (K : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    wsum K s ≤ 1 / √(1 - s) := by
  have hc0 : (0 : ℝ) < 1 - s := by linarith
  have he := elliptic_eq (1 - s) hc0
  rw [show (1 : ℝ) - (1 - s) = s from by ring] at he
  have hint1 : IntervalIntegrable (fun x => 1 / (1 - s * sin x ^ 2)) volume 0 (π / 2) :=
    (Continuous.div continuous_const (by fun_prop)
      (fun x => by
        have := sin_sq_le_one' x
        have := hs1
        nlinarith)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun x => ∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i) volume 0 (π / 2) :=
    (continuous_finsetSum _ fun i _ => by fun_prop).intervalIntegrable _ _
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2),
      (∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i) ≤ 1 / (1 - s * sin x ^ 2) := by
    intro x _
    have hz : 0 ≤ s * sin x ^ 2 := mul_nonneg hs0 (sq_nonneg _)
    have hz1 : s * sin x ^ 2 < 1 := by
      have h1 := sin_sq_le_one' x
      nlinarith
    exact geom_sum_le _ hz hz1 (K + 1)
  calc wsum K s = 2 / π * ∫ x in (0 : ℝ)..π / 2,
        ∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i := wsum_eq K s
    _ ≤ 2 / π * ∫ x in (0 : ℝ)..π / 2, 1 / (1 - s * sin x ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact intervalIntegral.integral_mono_on (by positivity) hint2 hint1 hpt
    _ = 2 / π * (π / (2 * √(1 - s))) := by rw [he]
    _ = 1 / √(1 - s) := by
        have : √(1 - s) ≠ 0 := by positivity
        field_simp
end
noncomputable section

/-- For `s` in `[0, 1)`, the gap from the weighted sum to `1 / √(1 - s)` is at most `s ^ (K + 1)
* cReal (K + 1) / (1 - s)`. -/
lemma wsum_tail (K : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    1 / √(1 - s) ≤ wsum K s + s ^ (K + 1) * cReal (K + 1) / (1 - s) := by
  have hc0 : (0 : ℝ) < 1 - s := by linarith
  have he := elliptic_eq (1 - s) hc0
  rw [show (1 : ℝ) - (1 - s) = s from by ring] at he
  have hint1 : IntervalIntegrable (fun x => 1 / (1 - s * sin x ^ 2)) volume 0 (π / 2) :=
    (Continuous.div continuous_const (by fun_prop)
      (fun x => by
        have := sin_sq_le_one' x
        have := hs1
        nlinarith)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => (s * sin x ^ 2) ^ (K + 1)) volume 0 (π / 2) :=
    (by fun_prop : Continuous fun x => (s * sin x ^ 2) ^ (K + 1)).intervalIntegrable _ _
  have hint3 : IntervalIntegrable
      (fun x => ∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i) volume 0 (π / 2) :=
    (continuous_finsetSum _ fun i _ => by fun_prop).intervalIntegrable _ _
  have hint4a : IntervalIntegrable (fun x => (s * sin x ^ 2) ^ (K + 1) / (1 - s)) volume 0
      (π / 2) := by
    refine (Continuous.div (by fun_prop : Continuous fun x => (s * sin x ^ 2) ^ (K + 1))
      (continuous_const (y := (1 : ℝ) - s)) ?_).intervalIntegrable _ _
    intro x
    nlinarith
  have hint4 : IntervalIntegrable
      (fun x => (∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i)
        + (s * sin x ^ 2) ^ (K + 1) / (1 - s)) volume 0 (π / 2) :=
    hint3.add hint4a
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2),
      1 / (1 - s * sin x ^ 2) ≤ (∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i)
        + (s * sin x ^ 2) ^ (K + 1) / (1 - s) := by
    intro x _
    have hz : 0 ≤ s * sin x ^ 2 := mul_nonneg hs0 (sq_nonneg _)
    have hz1 : s * sin x ^ 2 < 1 := by
      have h1 := sin_sq_le_one' x
      nlinarith
    have hne : 1 - s * sin x ^ 2 ≠ 0 := by nlinarith
    have hne' : (1 : ℝ) - s ≠ 0 := by nlinarith
    have e1 : ∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i
        = (1 - (s * sin x ^ 2) ^ (K + 1)) / (1 - s * sin x ^ 2) :=
      geom_sum_formula _ (by nlinarith : s * sin x ^ 2 ≠ 1) (K + 1)
    have e2 : (1 - (s * sin x ^ 2) ^ (K + 1)) / (1 - s * sin x ^ 2)
        + (s * sin x ^ 2) ^ (K + 1) / (1 - s * sin x ^ 2) = 1 / (1 - s * sin x ^ 2) := by
      rw [← add_div, sub_add_cancel]
    have hzz : (s * sin x ^ 2) ^ (K + 1) / (1 - s * sin x ^ 2)
        ≤ (s * sin x ^ 2) ^ (K + 1) / (1 - s) := by
      have h12 : (1 : ℝ) - s ≤ 1 - s * sin x ^ 2 := by
        have h1 := sin_sq_le_one' x
        nlinarith
      have h3 : 0 ≤ (s * sin x ^ 2) ^ (K + 1) := pow_nonneg hz _
      rw [div_le_div_iff₀ (by nlinarith : (0 : ℝ) < 1 - s * sin x ^ 2)
        (by nlinarith : (0 : ℝ) < 1 - s)]
      exact mul_le_mul_of_nonneg_left h12 h3
    rw [← e1] at e2
    rw [show 1 / (1 - s * sin x ^ 2)
        = (∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i)
          + (s * sin x ^ 2) ^ (K + 1) / (1 - s * sin x ^ 2) from e2.symm]
    linarith
  have hsecond : ∫ x in (0 : ℝ)..π / 2, (s * sin x ^ 2) ^ (K + 1) / (1 - s)
      = (1 / (1 - s)) * ∫ x in (0 : ℝ)..π / 2, (s * sin x ^ 2) ^ (K + 1) := by
    rw [intervalIntegral.integral_div]
    have hne : ((1 : ℝ) - s) ≠ 0 := by nlinarith
    field_simp
  calc 1 / √(1 - s)
      = 2 / π * ∫ x in (0 : ℝ)..π / 2, 1 / (1 - s * sin x ^ 2) := by
        rw [he]
        have hsqrt : √(1 - s) ≠ 0 := by positivity
        have hpi : (π : ℝ) ≠ 0 := by positivity
        field_simp
    _ ≤ 2 / π * ∫ x in (0 : ℝ)..π / 2, ((∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i)
          + (s * sin x ^ 2) ^ (K + 1) / (1 - s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact intervalIntegral.integral_mono_on (by positivity) hint1 hint4 hpt
    _ = 2 / π * ((∫ x in (0 : ℝ)..π / 2, ∑ i ∈ Finset.range (K + 1), (s * sin x ^ 2) ^ i)
          + (1 / (1 - s)) * ∫ x in (0 : ℝ)..π / 2, (s * sin x ^ 2) ^ (K + 1)) := by
        rw [intervalIntegral.integral_add hint3 hint4a, hsecond]
    _ = wsum K s + s ^ (K + 1) * cReal (K + 1) / (1 - s) := by
        rw [wsum_eq, pow_moment]
        have hsqrt : √(1 - s) ≠ 0 := by positivity
        have hpi : (π : ℝ) ≠ 0 := by positivity
        have hne : (1 : ℝ) - s ≠ 0 := by nlinarith
        field_simp
end
noncomputable section

/-- The polynomial `X` times the truncated central binomial sum in `1 - X ^ 2` through index
`K`. -/
noncomputable def spoly (K : ℕ) : Polynomial ℝ :=
  Polynomial.X * ∑ i ∈ Finset.range (K + 1),
    Polynomial.C (cReal i) * (1 - Polynomial.X ^ 2) ^ i
end
noncomputable section

/-- The sign approximation polynomial evaluates to `y * wsum K (1 - y ^ 2)`. -/
lemma spoly_eval (K : ℕ) (y : ℝ) : (spoly K).eval y = y * wsum K (1 - y ^ 2) := by
  have h1 : (spoly K).eval y
      = y * ∑ i ∈ Finset.range (K + 1), cReal i * (1 - y ^ 2) ^ i := by
    simp only [spoly, eval_mul, eval_X, eval_finsetSum, eval_mul, eval_C, eval_sub,
      eval_pow, eval_one]
  rw [h1, wsum]
end
noncomputable section

/-- The sign approximation polynomial is odd as a real function. -/
lemma spoly_odd (K : ℕ) : ∀ x : ℝ, (spoly K).eval (-x) = -(spoly K).eval x := by
  intro x
  rw [spoly_eval, spoly_eval, show 1 - (-x)^2 = 1 - x^2 from by ring]
  ring
end
noncomputable section

/-- The sign approximation polynomial has absolute value at most one on `[0, 1]`. -/
lemma spoly_abs_le_nonneg (K : ℕ) {y : ℝ} (h0 : 0 ≤ y) (hy : y ≤ 1) :
    |(spoly K).eval y| ≤ 1 := by
  rcases eq_or_ne y 0 with rfl | hne
  · rw [spoly_eval]; simp
  · have hpos : 0 < y := lt_of_le_of_ne h0 (Ne.symm hne)
    have hs0 : 0 ≤ 1 - y ^ 2 := by nlinarith
    have hs1 : 1 - y ^ 2 < 1 := by nlinarith
    have hw := wsum_le K hs0 hs1
    have hwn := wsum_nonneg K hs0
    rw [spoly_eval, abs_of_nonneg (mul_nonneg (le_of_lt hpos) hwn)]
    have hsqrt : √(1 - (1 - y ^ 2)) = y := by
      rw [show (1 : ℝ) - (1 - y ^ 2) = y ^ 2 from by ring, sqrt_sq_eq_abs, abs_of_pos hpos]
    rw [hsqrt] at hw
    calc y * wsum K (1 - y ^ 2) ≤ y * (1 / y) := mul_le_mul_of_nonneg_left hw (le_of_lt hpos)
      _ = 1 := by
            have hne : y ≠ 0 := ne_of_gt hpos
            field_simp
end
noncomputable section

/-- The sign approximation polynomial has absolute value at most one on `[-1, 1]`. -/
lemma spoly_abs_le (K : ℕ) : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(spoly K).eval y| ≤ 1 := by
  intro y hy
  rcases le_or_gt 0 y with h0 | h0
  · exact spoly_abs_le_nonneg K h0 hy.2
  · have h1 : 0 ≤ -y := by linarith
    have h2 : -y ≤ 1 := by linarith [hy.1]
    have h := spoly_abs_le_nonneg K h1 h2
    have heq : (spoly K).eval y = -((spoly K).eval (-y)) := by
      rw [spoly_odd]; ring
    rw [heq, abs_neg]
    exact h
end
noncomputable section

/-- On `[1/2, 1]`, the error of the sign approximation from one is at most `2 * (3 / 4) ^ (K +
1)`. -/
lemma spoly_tail (K : ℕ) {y : ℝ} (hy1 : 1 / 2 ≤ y) (hy2 : y ≤ 1) :
    |(spoly K).eval y - 1| ≤ 2 * ((3 / 4 : ℝ) ^ (K + 1)) := by
  have hpos : 0 < y := by linarith
  have hs0 : 0 ≤ 1 - y ^ 2 := by nlinarith
  have hs1 : 1 - y ^ 2 < 1 := by nlinarith
  have hs34 : 1 - y ^ 2 ≤ 3 / 4 := by nlinarith
  have hw := wsum_le K hs0 hs1
  have hge := wsum_tail K hs0 hs1
  have hsqrt : √(1 - (1 - y ^ 2)) = y := by
    rw [show (1 : ℝ) - (1 - y ^ 2) = y ^ 2 from by ring, sqrt_sq_eq_abs, abs_of_pos hpos]
  rw [hsqrt] at hw hge
  have hup : (spoly K).eval y ≤ 1 := by
    have h1 : y * wsum K (1 - y ^ 2) ≤ y * (1 / y) := mul_le_mul_of_nonneg_left hw (le_of_lt hpos)
    have h2 : y * (1 / y) = 1 := by
      have hne : y ≠ 0 := ne_of_gt hpos
      field_simp
    rw [spoly_eval]
    linarith
  have hdown : 1 - 2 * ((3 / 4 : ℝ) ^ (K + 1)) ≤ (spoly K).eval y := by
    have e1 : 1 ≤ y * (wsum K (1 - y ^ 2)
        + (1 - y ^ 2) ^ (K + 1) * cReal (K + 1) / (1 - (1 - y ^ 2))) := by
      have hm : y * (1 / y) ≤ y * (wsum K (1 - y ^ 2)
          + (1 - y ^ 2) ^ (K + 1) * cReal (K + 1) / (1 - (1 - y ^ 2))) :=
        mul_le_mul_of_nonneg_left hge (le_of_lt hpos)
      have hd : y * (1 / y) = 1 := by
        have hne : y ≠ 0 := ne_of_gt hpos
        field_simp
      linarith
    have e2 : y * ((1 - y ^ 2) ^ (K + 1) * cReal (K + 1) / (1 - (1 - y ^ 2)))
        = (1 - y ^ 2) ^ (K + 1) * cReal (K + 1) / y := by
      rw [show (1 : ℝ) - (1 - y ^ 2) = y ^ 2 from by ring]
      field_simp
    rw [mul_add, e2] at e1
    have e3 : (1 - y ^ 2) ^ (K + 1) * cReal (K + 1) / y ≤ 2 * ((3 / 4 : ℝ) ^ (K + 1)) := by
      have hy2b : (1 : ℝ) / y ≤ 2 := by
        rw [div_le_iff₀ hpos]
        nlinarith
      have hsle : (1 - y ^ 2) ^ (K + 1) ≤ (3 / 4 : ℝ) ^ (K + 1) :=
        pow_le_pow_left₀ hs0 hs34 (K + 1)
      have hc := cReal_le_one (K + 1)
      have hp : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ (K + 1) := pow_nonneg (by norm_num) _
      have hmid : (1 - y ^ 2) ^ (K + 1) * cReal (K + 1) / y ≤ (3 / 4 : ℝ) ^ (K + 1) / y := by
        have hprod : (1 - y ^ 2) ^ (K + 1) * cReal (K + 1) ≤ (3 / 4 : ℝ) ^ (K + 1) := by
          calc (1 - y ^ 2) ^ (K + 1) * cReal (K + 1)
              ≤ (3 / 4 : ℝ) ^ (K + 1) * 1 := by
                exact mul_le_mul hsle hc (le_of_lt (cReal_pos (K + 1)))
                  (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) _)
            _ = (3 / 4 : ℝ) ^ (K + 1) := by ring
        rw [div_le_div_iff₀ hpos hpos]
        exact mul_le_mul_of_nonneg_right hprod (le_of_lt hpos)
      calc (1 - y ^ 2) ^ (K + 1) * cReal (K + 1) / y
          ≤ (3 / 4 : ℝ) ^ (K + 1) / y := hmid
        _ = (3 / 4 : ℝ) ^ (K + 1) * (1 / y) := by rw [div_eq_mul_one_div]
        _ ≤ (3 / 4 : ℝ) ^ (K + 1) * 2 := by
            exact mul_le_mul_of_nonneg_left hy2b hp
        _ = 2 * ((3 / 4 : ℝ) ^ (K + 1)) := by ring
    rw [spoly_eval]
    nlinarith [e1, e3]
  rcases le_total ((spoly K).eval y - 1) 0 with h | h
  · rw [abs_of_nonpos h]
    linarith
  · rw [abs_of_nonneg h]
    linarith
end
noncomputable section

/-- The base two logarithm of `4 / 3` is at least `2 / 5`. -/
lemma log2_four_thirds : (2 / 5 : ℝ) ≤ Real.logb 2 ((4 / 3 : ℝ)) := by
  have h2p : (0 : ℝ) < 2 := by norm_num
  have hne : (2 : ℝ) ≠ 1 := by norm_num
  have h1 : Real.logb 2 ((2 : ℝ) ^ ((2 / 5 : ℝ))) = 2 / 5 := Real.logb_rpow h2p hne
  have h4 : ((2 : ℝ) ^ ((2 / 5 : ℝ))) ^ 5 = 4 := by
    have e1 : ((2 : ℝ) ^ ((2 / 5 : ℝ))) ^ 5
        = ((2 : ℝ) ^ ((2 / 5 : ℝ))) ^ ((5 : ℕ) : ℝ) := (Real.rpow_natCast _ 5).symm
    rw [e1, ← Real.rpow_mul (le_of_lt h2p),
      show ((2 / 5 : ℝ) * ((5 : ℕ) : ℝ)) = 2 from by norm_num]
    norm_num
  have hkey : ((2 : ℝ) ^ ((2 / 5 : ℝ))) ≤ ((4 / 3 : ℝ)) := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt : ((4 / 3 : ℝ)) ^ 5 < ((2 : ℝ) ^ ((2 / 5 : ℝ))) ^ 5 :=
      pow_lt_pow_left₀ hcon (le_of_lt (by norm_num : (0 : ℝ) < 4 / 3)) (by norm_num)
    rw [h4] at hlt
    have h43 : (4 : ℝ) < ((4 / 3 : ℝ)) ^ 5 := by norm_num
    linarith
  have h2 : Real.logb 2 ((2 : ℝ) ^ ((2 / 5 : ℝ))) ≤ Real.logb 2 ((4 / 3 : ℝ)) :=
    (Real.logb_le_logb one_lt_two (by positivity : (0 : ℝ) < (2 : ℝ) ^ ((2 / 5 : ℝ)))
      (by positivity : (0 : ℝ) < 4 / 3)).2 hkey
  rw [h1] at h2
  exact h2
end
noncomputable section

/-- The stated logarithmic lower bound on `K` makes the geometric sign error at most `ε / 8` for
positive `ε`. -/
lemma err_bound (ε : ℝ) (hε : 0 < ε) (K : ℕ)
    (hK : (5 / 2 : ℝ) * (Real.logb 2 (1 / ε) + 4) ≤ (K : ℝ)) :
    2 * ((3 / 4 : ℝ) ^ (K + 1)) ≤ ε / 8 := by
  have h2p : (0 : ℝ) < 2 := by norm_num
  have h2ne : (2 : ℝ) ≠ 1 := by norm_num
  have hkey : ((3 / 4 : ℝ) ^ (K + 1)) ≤ (2 : ℝ) ^ (-(Real.logb 2 (1 / ε) + 4)) := by
    have hg := log2_four_thirds
    have h1 : Real.logb 2 ((3 / 4 : ℝ)) = -(Real.logb 2 ((4 / 3 : ℝ))) := by
      have h0 : ((3 / 4 : ℝ)) = ((4 / 3 : ℝ))⁻¹ := by norm_num
      rw [h0, Real.logb_inv]
    have hL : Real.logb 2 ((2 : ℝ) ^ (-(Real.logb 2 (1 / ε) + 4)))
        = -(Real.logb 2 (1 / ε) + 4) :=
      Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    have hP : Real.logb 2 ((3 / 4 : ℝ) ^ (K + 1)) = ((K : ℝ) + 1) * Real.logb 2 ((3 / 4 : ℝ)) := by
      simp [Real.logb_pow]
    have hmono : Real.logb 2 ((3 / 4 : ℝ) ^ (K + 1))
        ≤ Real.logb 2 ((2 : ℝ) ^ (-(Real.logb 2 (1 / ε) + 4))) := by
      rw [hP, hL, h1]
      have h2 : ((K : ℝ) + 1) * (2 / 5 : ℝ) ≥ Real.logb 2 (1 / ε) + 4 := by
        have hK2 : (5 / 2 : ℝ) * (Real.logb 2 (1 / ε) + 4) ≤ (K : ℝ) + 1 := by linarith
        have h3 : ((5 / 2 : ℝ) * (Real.logb 2 (1 / ε) + 4)) * (2 / 5 : ℝ)
            = Real.logb 2 (1 / ε) + 4 := by
          field_simp
        nlinarith [hK2, h3]
      have hprod : ((K : ℝ) + 1) * (2 / 5 : ℝ)
          ≤ ((K : ℝ) + 1) * Real.logb 2 ((4 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      linarith
    exact (Real.logb_le_logb one_lt_two (show (0 : ℝ) < (3 / 4 : ℝ) ^ (K + 1) by positivity)
      (show (0 : ℝ) < (2 : ℝ) ^ (-(Real.logb 2 (1 / ε) + 4)) by positivity)).mp hmono
  have hval : (2 : ℝ) ^ (-(Real.logb 2 (1 / ε) + 4)) = ε / 16 := by
    have he1 : (2 : ℝ) ^ (-(Real.logb 2 (1 / ε) + 4))
        = (2 : ℝ) ^ (-(Real.logb 2 (1 / ε))) * (2 : ℝ) ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_add h2p]
      congr 1
      ring
    have he2 : (2 : ℝ) ^ (-(Real.logb 2 (1 / ε))) = ε := by
      have hle : Real.logb 2 (1 / ε) = -(Real.logb 2 ε) := by
        have h0 : ((1 : ℝ) / ε) = ((ε : ℝ))⁻¹ := one_div ε
        rw [h0, Real.logb_inv]
      rw [hle, neg_neg, Real.rpow_logb h2p h2ne hε]
    have he3 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [Real.rpow_neg (le_of_lt h2p)]
      norm_num
    rw [he1, he2, he3]
    field_simp
  rw [hval] at hkey
  have hfin : (2 : ℝ) * (ε / 16) = ε / 8 := by ring
  linarith
end
noncomputable section

/-- A common bound on the natural degrees of finitely many real polynomials also bounds the
natural degree of their sum. -/
lemma natDegree_sum_range_le (n : ℕ) (f : ℕ → Polynomial ℝ) (b : ℕ)
    (h : ∀ i < n, (f i).natDegree ≤ b) : (∑ i ∈ Finset.range n, f i).natDegree ≤ b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine le_trans (natDegree_add_le _ _) ?_
    exact max_le (ih fun i hi => h i (by omega)) (h n (by omega))
end
noncomputable section

/-- The natural degree of `1 - X ^ 2` is at most two. -/
lemma natDegree_one_sub_X_sq_le : (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
  refine natDegree_le_of_degree_le ?_
  refine le_trans (degree_sub_le (1 : Polynomial ℝ) (Polynomial.X ^ 2)) ?_
  simp
end
noncomputable section

/-- The natural degree of the sign approximation polynomial is at most `2 * K + 1`. -/
lemma spoly_natDegree_le (K : ℕ) : (spoly K).natDegree ≤ 2 * K + 1 := by
  have h1 : ∀ i < K + 1,
      (Polynomial.C (cReal i) * (1 - Polynomial.X ^ 2) ^ i).natDegree ≤ 2 * K := by
    intro i hi
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, _root_.zero_add]
    refine le_trans natDegree_pow_le ?_
    have h2 : (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := natDegree_one_sub_X_sq_le
    have hiK : i ≤ K := by omega
    have hmul : i * (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ i * 2 :=
      Nat.mul_le_mul_left i h2
    have hmul2 : i * 2 ≤ 2 * K := by omega
    omega
  unfold spoly
  refine le_trans natDegree_mul_le ?_
  rw [Polynomial.natDegree_X]
  have hsum := natDegree_sum_range_le (K + 1)
    (fun i => Polynomial.C (cReal i) * (1 - Polynomial.X ^ 2) ^ i) (2 * K) h1
  (try simp only [] at hsum ⊢)
  omega
end
end Qatlib.Concepts.QsvtCore.ApproxToolkit
