/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.Defs

/-!
# Concentration of normalized traces

The quantities `traceDeviation` and `expectedTrace` split a normalized sum of independent phases
into its centered fluctuation and mean. Real and imaginary weighted-sum identities allow
Hoeffding estimates to bound deviations of its complex norm. This development supports the
treatment in [TangWright2025].

## Main statements

* `traceDeviation_re` and `traceDeviation_im`: centered weighted-sum expressions.
* `trace_concentration`: deviation probability at most `0.01` when `d ≥ 48/t^2`.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.AmpInvReqTang26.TraceConcent

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- The normalized sum of coordinate phase values after subtracting their individual complex
expectations. -/
def traceDeviation {d : ℕ} {X : Fin d → Type} [∀ i, Fintype (X i)]
    (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ) (ω : ∀ i, X i) : ℂ :=
  ((d : ℝ)⁻¹ : ℂ) * ∑ i, (phi i (ω i) - cExpect (p i) (phi i))

/-- The normalized sum of the coordinate complex expectations. -/
def expectedTrace {d : ℕ} {X : Fin d → Type} [∀ i, Fintype (X i)]
    (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ) : ℂ :=
  ((d : ℝ)⁻¹ : ℂ) * ∑ i, cExpect (p i) (phi i)

/-- The exponential tail constant `4 * exp(-6)` is at most `0.01`. -/
theorem four_exp_neg_six_le : 4 * Real.exp (-6) ≤ 0.01 := by
  have h6 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    have := Real.exp_nat_mul 6 1
    simp_all
  have hbase : (400 : ℝ) ≤ (Real.exp 1) ^ 6 := by
    have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
    have h2 : (400 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
    calc (400 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := h2
      _ ≤ (Real.exp 1) ^ 6 := by gcongr
  rw [Real.exp_neg, h6]
  have hpos : (0 : ℝ) < (Real.exp 1) ^ 6 := by positivity
  rw [show (0.01 : ℝ) = 4 * (400 : ℝ)⁻¹ by norm_num]
  gcongr

/-- The real part of a finite complex expectation is the probability-weighted sum of the real
parts. -/
theorem cExpect_re {X : Type} [Fintype X] (p : FinDist X) (phi : X → ℂ) :
    (cExpect p phi).re = ∑ x, p.prob x * (phi x).re := by
  rw [cExpect, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.mul_re]
  simp

/-- The imaginary part of a finite complex expectation is the probability-weighted sum of the
imaginary parts. -/
theorem cExpect_im {X : Type} [Fintype X] (p : FinDist X) (phi : X → ℂ) :
    (cExpect p phi).im = ∑ x, p.prob x * (phi x).im := by
  rw [cExpect, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.mul_im]
  simp

/-- The real trace deviation equals the centered real weighted sum under the independent product
law. -/
theorem traceDeviation_re {d : ℕ} {X : Fin d → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ) (ω : ∀ i, X i) :
    (traceDeviation p phi ω).re =
      weightedSum (fun _ : Fin d => (d : ℝ)⁻¹) (fun i x => (phi i x).re) ω -
        (independent p).expect
          (weightedSum (fun _ : Fin d => (d : ℝ)⁻¹) (fun i x => (phi i x).re)) := by
  rw [traceDeviation, Complex.mul_re]
  simp
  rw [ProbabilityInterfaces.independent_weighted_expectation]
  unfold weightedSum
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [cExpect_re]
  rfl

/-- The imaginary trace deviation equals the centered imaginary weighted sum under the
independent product law. -/
theorem traceDeviation_im {d : ℕ} {X : Fin d → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ) (ω : ∀ i, X i) :
    (traceDeviation p phi ω).im =
      weightedSum (fun _ : Fin d => (d : ℝ)⁻¹) (fun i x => (phi i x).im) ω -
        (independent p).expect
          (weightedSum (fun _ : Fin d => (d : ℝ)⁻¹) (fun i x => (phi i x).im)) := by
  rw [traceDeviation, Complex.mul_im]
  simp
  rw [ProbabilityInterfaces.independent_weighted_expectation]
  unfold weightedSum
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [cExpect_im]
  rfl

/-- For independent unit-modulus phases, positive `t`, and `d ≥ 48/t^2`, the probability that
the centered normalized trace has norm at least `t` is at most `0.01` [Tang and Wright,
Lemma 2.6][TangWright2025]. -/
theorem trace_concentration {d : ℕ} (hd : 0 < d) {X : Fin d → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (phi : ∀ i, X i → ℂ)
    (hunit : ∀ i x, ‖phi i x‖ = 1) (t : ℝ) (ht : 0 < t)
    (hdC : 48 / t ^ 2 ≤ (d : ℝ)) :
    eventMass (independent p) (fun ω => t ≤ ‖traceDeviation p phi ω‖) ≤ 0.01 := by
  classical
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hdt : (48 : ℝ) ≤ (d : ℝ) * t ^ 2 := by
    rwa [div_le_iff₀ ht2] at hdC

  set w : Fin d → ℝ := fun _ => (d : ℝ)⁻¹ with hw
  set fr : ∀ i, X i → ℝ := fun i x => (phi i x).re with hfr
  set fi : ∀ i, X i → ℝ := fun i x => (phi i x).im with hfi
  have hSval : (∑ i : Fin d, (w i) ^ 2 * ((1 : ℝ) - (-1)) ^ 2) = 4 / (d : ℝ) := by
    rw [hw]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hd0 : (d : ℝ) ≠ 0 := hdpos.ne'
    have h2 : ((1 : ℝ) - (-1)) = 2 := by norm_num
    rw [h2]
    norm_num
    field_simp
  have hS : 0 < ∑ i : Fin d, (w i) ^ 2 * ((1 : ℝ) - (-1)) ^ 2 := by
    rw [hSval]
    positivity
  have hf_re : ∀ i x, fr i x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i x
    have h := Complex.abs_re_le_norm (phi i x)
    rw [hunit i x] at h
    rw [abs_le] at h
    exact ⟨h.1, h.2⟩
  have hf_im : ∀ i x, fi i x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i x
    have h := Complex.abs_im_le_norm (phi i x)
    rw [hunit i x] at h
    rw [abs_le] at h
    exact ⟨h.1, h.2⟩
  have hu : 0 < t / 2 := by linarith
  have hre := independent_weighted_hoeffding p w fr (-1) 1 (t / 2)
    (fun _ => by norm_num) hf_re hu hS
  have him := independent_weighted_hoeffding p w fi (-1) 1 (t / 2)
    (fun _ => by norm_num) hf_im hu hS

  have hsub : ∀ ω, t ≤ ‖traceDeviation p phi ω‖ →
      ((t / 2 ≤ |weightedSum w fr ω - (independent p).expect (weightedSum w fr)|) ∨
       (t / 2 ≤ |weightedSum w fi ω - (independent p).expect (weightedSum w fi)|)) := by
    intro ω hω
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hre' := traceDeviation_re p phi ω
    have him' := traceDeviation_im p phi ω
    set z := traceDeviation p phi ω with hz
    have hzre : z.re = weightedSum w fr ω - (independent p).expect (weightedSum w fr) := by
      rw [hz]; exact hre'
    have hzim : z.im = weightedSum w fi ω - (independent p).expect (weightedSum w fi) := by
      rw [hz]; exact him'
    rw [← hzre] at h1
    rw [← hzim] at h2
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have h1' : z.re ^ 2 < (t / 2) ^ 2 := by
      nlinarith [sq_abs z.re, abs_nonneg z.re, h1]
    have h2' : z.im ^ 2 < (t / 2) ^ 2 := by
      nlinarith [sq_abs z.im, abs_nonneg z.im, h2]
    have hsqlt : ‖z‖ ^ 2 < t ^ 2 := by
      rw [hnorm]
      nlinarith
    have ht_le : t ^ 2 ≤ ‖z‖ ^ 2 := by
      nlinarith [norm_nonneg z, hω, ht]
    linarith

  have hre' : eventMass (independent p)
      (fun ω => t / 2 ≤ |weightedSum w fr ω - (independent p).expect (weightedSum w fr)|) ≤
        Real.exp (-6) * 2 := by
    refine hre.trans ?_
    have hexp : Real.exp (-2 * (t / 2) ^ 2 /
        (∑ i : Fin d, (w i) ^ 2 * ((1 : ℝ) - (-1)) ^ 2)) ≤ Real.exp (-6) := by
      apply Real.exp_le_exp.mpr
      rw [hSval]
      have hcalc : -2 * (t / 2) ^ 2 / (4 / (d : ℝ)) = -((d : ℝ) * t ^ 2) / 8 := by
        field_simp
        ring
      rw [hcalc]
      nlinarith
    calc 2 * Real.exp (-2 * (t / 2) ^ 2 /
          (∑ i : Fin d, (w i) ^ 2 * ((1 : ℝ) - (-1)) ^ 2))
        ≤ 2 * Real.exp (-6) := by
          exact mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = Real.exp (-6) * 2 := by ring
  have him' : eventMass (independent p)
      (fun ω => t / 2 ≤ |weightedSum w fi ω - (independent p).expect (weightedSum w fi)|) ≤
        Real.exp (-6) * 2 := by
    refine him.trans ?_
    have hexp : Real.exp (-2 * (t / 2) ^ 2 /
        (∑ i : Fin d, (w i) ^ 2 * ((1 : ℝ) - (-1)) ^ 2)) ≤ Real.exp (-6) := by
      apply Real.exp_le_exp.mpr
      rw [hSval]
      have hcalc : -2 * (t / 2) ^ 2 / (4 / (d : ℝ)) = -((d : ℝ) * t ^ 2) / 8 := by
        field_simp
        ring
      rw [hcalc]
      nlinarith
    calc 2 * Real.exp (-2 * (t / 2) ^ 2 /
          (∑ i : Fin d, (w i) ^ 2 * ((1 : ℝ) - (-1)) ^ 2))
        ≤ 2 * Real.exp (-6) := by
          exact mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = Real.exp (-6) * 2 := by ring
  calc eventMass (independent p) (fun ω => t ≤ ‖traceDeviation p phi ω‖)
      ≤ eventMass (independent p)
          (fun ω =>
            (t / 2 ≤ |weightedSum w fr ω - (independent p).expect (weightedSum w fr)|) ∨
            (t / 2 ≤ |weightedSum w fi ω - (independent p).expect (weightedSum w fi)|)) :=
        eventMass_mono _ _ _ hsub
    _ ≤ eventMass (independent p)
          (fun ω => t / 2 ≤ |weightedSum w fr ω - (independent p).expect (weightedSum w fr)|) +
        eventMass (independent p)
          (fun ω => t / 2 ≤ |weightedSum w fi ω - (independent p).expect (weightedSum w fi)|) :=
        eventMass_or_le _ _ _
    _ ≤ Real.exp (-6) * 2 + Real.exp (-6) * 2 := add_le_add hre' him'
    _ ≤ 0.01 := by
        have h := four_exp_neg_six_le
        nlinarith

end Qatlib.Papers.AmpInvReqTang26.TraceConcent
