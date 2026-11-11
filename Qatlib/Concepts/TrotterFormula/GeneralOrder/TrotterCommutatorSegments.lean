/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorDuhamel
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.PolynomialPerturbation

/-!
# Segmented matched-order product formulas

This module converts matched-order single-step commutator estimates into bounds for repeated
segments. `pf_segment_word_prod` identifies the executed product with a power, and
`pf_segment_ideal_pow` recovers the full ideal evolution for positive segment count.

The resulting estimates scale as `|t| ^ (p + 1) / r ^ p`, with the explicit factorial
normalization used in this development of commutator scaling [ChildsEtAl2021Trotter]. General
matrices carry an additional exponential norm-inflation factor.

## Main statements

* `pf_matched_word_segmented_skew`: bounds the error for skew-Hermitian matched words.
* `pf_matched_word_segmented_general`: bounds the error for general matched words.
* `pf_segment_commutator_budget`: rewrites the accumulated local budget.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The product of the flattened repeated segment word equals the `r`th power of the
single-segment exponential word. -/
theorem pf_segment_word_prod (xs : List (Matrix I I ℂ)) (t : ℝ) (r : ℕ) :
    ((List.replicate r (xs.map (fun X=>NormedSpace.exp ((t/r) • X)))).flatten).prod=
      suzukiExponentialWord xs (t/r)^r := by simp [List.prod_flatten,suzukiExponentialWord]

/-- For positive `r`, the `r`th power of the ideal evolution at time `t / r` equals the ideal
evolution at time `t`. -/
theorem pf_segment_ideal_pow (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) (hr : 0<r) :
    NormedSpace.exp ((t/r) • H)^r=NormedSpace.exp (t • H) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  congr 1
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  field_simp

/-- The sum of `r` equal local commutator budgets rewrites as the factorial-normalized global
budget with denominator `r ^ p`. -/
theorem pf_segment_commutator_budget (α t : ℝ) (p r : ℕ) (hr : 0<r) :
    (r:ℝ)*(α*|t/r| ^(p+1)/(p+1:ℕ))=
      (p.factorial:ℝ)*α*|t| ^(p+1)/(((p+1).factorial:ℝ)*(r:ℝ)^p) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hf0 : (p.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero p
  rw [abs_div,abs_of_pos hrR,div_pow,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

/-- A segmented skew-Hermitian word matching coefficients through positive order `p` has error
bounded by the stated commutator budget divided by `r ^ p`. -/
theorem pf_matched_word_segmented_skew (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p r : ℕ) (t : ℝ) (hp : 1≤p) (hr : 0<r)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : ∀ X∈xs,Xᴴ=-X) (hH : Hᴴ=-H) :
    ‖suzukiExponentialWord xs (t/r)^r-NormedSpace.exp (t • H)‖≤
      (p.factorial:ℝ)*pfCommAlphaSelf xs (p+1)*|t| ^(p+1)/(((p+1).factorial:ℝ)*(r:ℝ)^p) := by
  rw [← pf_segment_ideal_pow H t r hr]
  have hh := pf_unitary_power_error _ _ (pf_word_unitary xs (t/r) hxs)
    (general_trotter_exp_unitary H (t/r) hH) r
  apply (hh.trans (mul_le_mul_of_nonneg_left
    (pf_matched_word_local_skew xs H p (t/r) hp hc hxs hH) (Nat.cast_nonneg r))).trans_eq
  exact pf_segment_commutator_budget _ t p r hr

/-- The single-step exponential inflation and its propagation over `r` positive segments are
bounded by `exp (4 * |t| * L)` for nonnegative `L`. -/
theorem pf_segment_inflation_le (t L : ℝ) (r : ℕ) (hr : 0<r) (hL : 0≤L) :
    Real.exp (4*|t/r| *L)*(Real.exp (|t/r| *L))^(r-1)≤Real.exp (4*|t| *L) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hr1 : (1:ℝ)≤r := by exact_mod_cast (show 1≤r by omega)
  have hn : ((r-1:ℕ):ℝ)=(r:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤r),Nat.cast_one]
  rw [← Real.exp_nat_mul,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [abs_div,abs_of_pos hrR,hn]
  have hc : ((r:ℝ)+3)/(r:ℝ)≤4 := (div_le_iff₀ hrR).mpr (by nlinarith [hr1])
  calc _=(((r:ℝ)+3)/(r:ℝ))*|t| *L := by ring
       _≤4*|t| *L := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (abs_nonneg _)) hL

/-- A segmented matched-order word has the stated commutator error bound with exponential
inflation `exp (4 * |t| * (suzukiMass xs + ‖H‖))`. -/
theorem pf_matched_word_segmented_general (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p r : ℕ) (t : ℝ) (hp : 1≤p) (hr : 0<r)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n) :
    ‖suzukiExponentialWord xs (t/r)^r-NormedSpace.exp (t • H)‖≤
      (p.factorial:ℝ)*pfCommAlphaSelf xs (p+1)*|t| ^(p+1)/(((p+1).factorial:ℝ)*(r:ℝ)^p)*
        Real.exp (4*|t| *(suzukiMass xs+‖H‖)) := by
  let L := suzukiMass xs+‖H‖
  let M := Real.exp (|t/r| *L)
  have hL : 0≤L := add_nonneg (general_trotter_mass_nonneg xs) (norm_nonneg _)
  have hM : 0≤M := (Real.exp_pos _).le
  have hS : ‖suzukiExponentialWord xs (t/r)‖≤M := by
    apply (pf_word_norm_le xs (t/r)).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg H)) (abs_nonneg _)
  have hE : ‖NormedSpace.exp ((t/r) • H)‖≤M := by
    apply (pf_matrix_exp_norm_le H (t/r)).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (general_trotter_mass_nonneg xs))
        (abs_nonneg _)
  rw [← pf_segment_ideal_pow H t r hr]
  have hpow :=
      Qatlib.Concepts.SpectralSketch.SpectrumPerturb.matrix_norm_pow_sub_pow_le _ _ hM hS hE r
  have hlocal := pf_matched_word_local_general xs H p (t/r) hp hc
  have hα : 0≤pfCommAlphaSelf xs (p+1) := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  calc _≤‖suzukiExponentialWord xs (t/r)-NormedSpace.exp ((t/r) • H)‖*(r:ℝ)*M^(r-1) := hpow
       _≤(pfCommAlphaSelf xs (p+1)*|t/r| ^(p+1)/(p+1:ℕ)*Real.exp (4*|t/r| *L))*(r:ℝ)*M^(r-1) :=
         mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlocal (Nat.cast_nonneg _)) (pow_nonneg hM _)
       _=((r:ℝ)*(pfCommAlphaSelf xs (p+1)*|t/r| ^(p+1)/(p+1:ℕ)))*(Real.exp (4*|t/r| *L)*M^(r-1)) := by ring
       _=((p.factorial:ℝ)*pfCommAlphaSelf xs (p+1)*|t| ^(p+1)/(((p+1).factorial:ℝ)*(r:ℝ)^p))*
           (Real.exp (4*|t/r| *L)*M^(r-1)) := by rw [pf_segment_commutator_budget _ t p r hr]
       _≤_ := mul_le_mul_of_nonneg_left (pf_segment_inflation_le t L r hr hL) (by positivity)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
