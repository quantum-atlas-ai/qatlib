/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterDefectTaylor

/-!
# Duhamel estimates for matched product words

This module expresses product-formula error as a Duhamel integral of the left-generator defect
and derives local error bounds for words matching the target exponential through a positive
order. This is the defect-integral approach underlying commutator-scaling estimates
[ChildsEtAl2021Trotter].

General generators produce an exponential norm-growth factor, while skew-Hermitian generators
give unitary words and a bound using only the raw commutator budget and the integrated power of
time.

## Main statements

* `pf_word_duhamel`: integral representation of the product-word error.
* `pf_norm_integral_power_bound`: norm estimate for an integral with a polynomial envelope.
* `pf_matched_word_local_skew`: local error estimate for matched skew-Hermitian words.
* `pf_matched_word_local_general`: local error estimate with exponential growth.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Set MeasureTheory Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
set_option warningAsError false
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The norm of a product-formula exponential word is at most `exp (|t| * suzukiMass xs)`. -/
theorem pf_word_norm_le (xs : List (Matrix I I ℂ)) (t : ℝ) :
    ‖suzukiExponentialWord xs t‖≤Real.exp (|t| *suzukiMass xs) := by
  simpa only [Finset.range_zero,Finset.sum_empty,sub_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one] using! general_trotter_taylor_tail xs t 0

/-- A product-formula word with skew-Hermitian generators is unitary at every real time. -/
theorem pf_word_unitary (xs : List (Matrix I I ℂ)) (t : ℝ) (hxs : ∀ X∈xs,Xᴴ=-X) :
    suzukiExponentialWord xs t∈Matrix.unitaryGroup I ℂ := by
  unfold suzukiExponentialWord
  apply (Matrix.unitaryGroup I ℂ).list_prod_mem
  intro Y hY
  obtain ⟨X,hX,rfl⟩ := List.mem_map.mp hY
  exact general_trotter_exp_unitary X t (hxs X hX)

/-- The Duhamel error integrand built from the target exponential, left-generator defect, and
product word is continuous. -/
private theorem pf_error_integrand_continuous (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) :
    Continuous (fun u=>NormedSpace.exp ((t-u) • H)*((pfLeftGenerator xs u-H)*suzukiExponentialWord xs u)) := by
  have ha : ContDiff ℝ ∞ (fun u : ℝ=>t-u) := contDiff_const.sub contDiff_id
  have he := (trotter_exp_contDiff H).comp ha
  exact he.continuous.mul (((pfLeftGenerator_contDiff xs).continuous.sub continuous_const).mul
    (general_trotter_word_contDiff xs).continuous)

/-- Expresses the difference between a product-formula word and the target exponential as the
Duhamel integral of its left-generator defect. -/
theorem pf_word_duhamel (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) :
    suzukiExponentialWord xs t-NormedSpace.exp (t • H)=
      ∫ u in 0..t,NormedSpace.exp ((t-u) • H)*((pfLeftGenerator xs u-H)*suzukiExponentialWord xs u) := by
  let F := fun u=>NormedSpace.exp ((t-u) • H)*suzukiExponentialWord xs u
  have hd (u : ℝ) : HasDerivAt F
      (NormedSpace.exp ((t-u) • H)*((pfLeftGenerator xs u-H)*suzukiExponentialWord xs u)) u := by
    have he := (hasDerivAt_exp_smul_const (𝕂 := ℝ) H (t-u)).scomp u
      ((hasDerivAt_const u t).sub (hasDerivAt_id u))
    have hh := he.mul (pf_word_hasDerivAt_left_generator xs u)
    convert! hh using 1
    (try dsimp only [F])
    simp only [Function.comp_def,zero_sub,neg_smul,one_smul]
    noncomm_ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _=>hd u)
    ((pf_error_integrand_continuous xs H t).intervalIntegrable 0 t)
  have h0 : suzukiExponentialWord xs 0=1 := by simp [suzukiExponentialWord]
  simpa only [F,sub_self,sub_zero,zero_smul,NormedSpace.exp_zero,one_mul,h0,mul_one] using! hh.symm

/-- A pointwise bound `‖f u‖ ≤ C * |u|^p` on the unoriented interval between zero and `t` gives
the integral bound `C * |t|^(p+1)/(p+1)`. -/
theorem pf_norm_integral_power_bound (f : ℝ→Matrix I I ℂ) (t C : ℝ) (p : ℕ) (_hC : 0≤C)
    (hf : ∀ u∈uIcc 0 t,‖f u‖≤C*|u| ^p) :
    ‖∫ u in 0..t,f u‖≤C*|t| ^(p+1)/(p+1:ℕ) := by
  rw [intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  have hg : IntegrableOn (fun u : ℝ=>C*|u| ^p) (uIoc 0 t) :=
    ((continuous_const.mul (continuous_id.abs.pow p)).intervalIntegrable 0 t).def'
  have hh := MeasureTheory.norm_integral_le_of_norm_le hg (by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    exact hf u (uIoc_subset_uIcc hu))
  apply hh.trans_eq
  rw [integral_const_mul]
  have he : (∫ u in uIoc 0 t,|u| ^p)=|t| ^(p+1)/(p+1:ℕ) := by
    simpa only [sub_zero,Nat.cast_add,Nat.cast_one] using!
        integral_pow_abs_sub_uIoc (a := 0) (b := t) (n := p)
  rw [he]
  ring

/-- Multiplying a matrix on the left and right by matrices of norm at most one does not increase
its norm. -/
private theorem pf_product_norm_le_middle (A D S : Matrix I I ℂ) (hA : ‖A‖≤1) (hS : ‖S‖≤1) :
    ‖A*(D*S)‖≤‖D‖ := by
  calc _≤‖A‖*(‖D‖*‖S‖) := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
       _≤1*(‖D‖*1) := by gcongr
       _=‖D‖ := by ring

/-- For skew-Hermitian generators and target matching through positive order `p`, bounds the
local word error by `pfCommAlphaSelf xs (p+1) * |t|^(p+1)/(p+1)`. -/
theorem pf_matched_word_local_skew (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ) (t : ℝ)
    (hp : 1≤p) (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : ∀ X∈xs,Xᴴ=-X) (hH : Hᴴ=-H) :
    ‖suzukiExponentialWord xs t-NormedSpace.exp (t • H)‖≤pfCommAlphaSelf xs (p+1)*|t| ^(p+1)/(p+1:ℕ) := by
  rw [pf_word_duhamel]
  apply pf_norm_integral_power_bound _ t _ p (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  intro u _
  have hd := pfLeftGenerator_defect_norm_mode true xs H p u hp hc (fun _=>hxs)
  rw [pfWordInflation_true,mul_one] at hd
  exact (pf_product_norm_le_middle _ _ _
    (l2_norm_unitary_le_one (general_trotter_exp_unitary H (t-u) hH))
    (l2_norm_unitary_le_one (pf_word_unitary xs u hxs))).trans hd

/-- If `u` lies between zero and `t`, both `|u|` and `|t-u|` are at most `|t|`. -/
private theorem pf_abs_interval_bound (t u : ℝ) (hu : u∈uIcc 0 t) : |u|≤|t| ∧ |t-u|≤|t| := by
  rcases le_total 0 t with ht | ht
  · rw [uIcc_of_le ht] at hu
    rw [abs_of_nonneg hu.1,abs_of_nonneg ht,abs_of_nonneg (sub_nonneg.mpr hu.2)]
    constructor <;> linarith [hu.1,hu.2]
  · rw [uIcc_of_ge ht] at hu
    rw [abs_of_nonpos hu.2,abs_of_nonpos ht,abs_of_nonpos (sub_nonpos.mpr hu.1)]
    constructor <;> linarith [hu.1,hu.2]

/-- For a word matching the target exponential through positive order `p`, bounds the local
error by the raw commutator budget times `|t|^(p+1)/(p+1)` and the stated exponential growth
factor. -/
theorem pf_matched_word_local_general (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ) (t : ℝ)
    (hp : 1≤p) (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n) :
    ‖suzukiExponentialWord xs t-NormedSpace.exp (t • H)‖≤
      pfCommAlphaSelf xs (p+1)*|t| ^(p+1)/(p+1:ℕ)*Real.exp (4*|t| *(suzukiMass xs+‖H‖)) := by
  let A := pfCommAlphaSelf xs (p+1)
  let E := Real.exp (4*|t| *(suzukiMass xs+‖H‖))
  have hA : 0≤A := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  rw [pf_word_duhamel]
  have hb : ‖∫ u in 0..t,NormedSpace.exp ((t-u) • H)*((pfLeftGenerator xs u-H)*suzukiExponentialWord xs u)‖≤
      (A*E)*|t| ^(p+1)/(p+1:ℕ) := by
    apply pf_norm_integral_power_bound _ t (A*E) p (by dsimp [E];positivity)
    intro u hu
    have hd := pfLeftGenerator_defect_norm_mode false xs H p u hp hc (by simp)
    rw [pfWordInflation_false] at hd
    have hnorm : ‖NormedSpace.exp ((t-u) • H)*((pfLeftGenerator xs u-H)*suzukiExponentialWord xs u)‖≤
        A*|u| ^p*Real.exp (|t-u| *‖H‖+3*|u| *suzukiMass xs) := by
      calc _≤‖NormedSpace.exp ((t-u) • H)‖*(‖pfLeftGenerator xs u-H‖*‖suzukiExponentialWord xs u‖) :=
             (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
           _≤Real.exp (|t-u| *‖H‖)*(A*|u| ^p*Real.exp (2*|u| *suzukiMass xs)*Real.exp (|u| *suzukiMass xs)) := by
             apply mul_le_mul (pf_matrix_exp_norm_le H (t-u)) _ (by positivity) (Real.exp_pos _).le
             exact mul_le_mul hd (pf_word_norm_le xs u) (norm_nonneg _) (by positivity)
           _=A*|u| ^p*Real.exp (|t-u| *‖H‖+3*|u| *suzukiMass xs) := by
             rw [show |t-u| *‖H‖+3*|u| *suzukiMass xs=|t-u| *‖H‖+(2*|u| *suzukiMass xs+|u| *suzukiMass xs) by ring,
               Real.exp_add,Real.exp_add]
             ring
    have he : Real.exp (|t-u| *‖H‖+3*|u| *suzukiMass xs)≤E := by
      apply Real.exp_le_exp.mpr
      have huB := pf_abs_interval_bound t u hu
      have hM := general_trotter_mass_nonneg xs
      have h1 := mul_le_mul_of_nonneg_right huB.1 hM
      have h2 := mul_le_mul_of_nonneg_right huB.2 (norm_nonneg H)
      nlinarith [mul_nonneg (abs_nonneg t) hM,mul_nonneg (abs_nonneg t) (norm_nonneg H)]
    exact hnorm.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  exact hb.trans_eq (by dsimp [A,E];ring)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
