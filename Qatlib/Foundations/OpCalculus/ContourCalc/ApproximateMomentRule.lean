/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.BanachPolynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! Actual finite moment defects, rather than equality with an existential
Gauss rule, control Banach-valued quadrature. No node producer is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.OpCalculus.ContourCalc
open MeasureTheory Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Exact decomposition into the moments of the actual finite table. -/
theorem finite_vector_moment_decomposition
    (Q K : ℕ) (a b : ℝ) (node weight : Fin Q → ℝ) (c : Fin (K+1) → E) :
    (∫ t in a..b, finiteVectorPolynomial K c t) -
      ∑ q, weight q • finiteVectorPolynomial K c (node q) =
      ∑ k : Fin (K+1), ((∫ t in a..b, t^(k : ℕ)) -
        ∑ q, weight q * (node q)^(k : ℕ)) • c k := by
  have hi : (∫ t in a..b, finiteVectorPolynomial K c t) =
      ∑ k : Fin (K+1), (∫ t in a..b, t^(k : ℕ)) • c k := by
    unfold finiteVectorPolynomial
    rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun (k : Fin (K+1)) (t : ℝ) => t^(k : ℕ) • c k) (fun k _ =>
      ((continuous_id.pow (k : ℕ)).smul continuous_const).intervalIntegrable a b)]
    simp only [intervalIntegral.integral_smul_const]
  have hq : (∑ q, weight q • finiteVectorPolynomial K c (node q)) =
      ∑ k : Fin (K+1), (∑ q, weight q * (node q)^(k : ℕ)) • c k := by
    simp only [finiteVectorPolynomial, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  rw [hi, hq, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => (sub_smul _ _ _).symm)

/-- Each scalar moment defect is paid against the norm of its actual vector
coefficient; no coordinatewise dimension factor occurs. -/
theorem finite_vector_moment_error
    (Q K : ℕ) (a b : ℝ) (node weight : Fin Q → ℝ) (c : Fin (K+1) → E)
    (η : ℝ) (hmoment : ∀ k : Fin (K+1),
      |(∫ t in a..b, t^(k : ℕ)) - ∑ q, weight q * (node q)^(k : ℕ)| ≤ η) :
    ‖(∫ t in a..b, finiteVectorPolynomial K c t) -
      ∑ q, weight q • finiteVectorPolynomial K c (node q)‖ ≤ η * ∑ k, ‖c k‖ := by
  rw [finite_vector_moment_decomposition]
  calc
    _ ≤ ∑ k : Fin (K+1), ‖((∫ t in a..b, t^(k : ℕ)) -
        ∑ q, weight q * (node q)^(k : ℕ)) • c k‖ := norm_sum_le _ _
    _ ≤ ∑ k, η * ‖c k‖ := Finset.sum_le_sum (fun k _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hmoment k) (norm_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Actual positive weights have their actual mass in the approximation
term; an approximate constant moment is not silently replaced by exact mass. -/
theorem positive_moment_rule_error
    (Q K : ℕ) (a b : ℝ) (node weight : Fin Q → ℝ) (c : Fin (K+1) → E)
    (f : ℝ → E) (e η C : ℝ) (hab : a ≤ b)
    (hnode : ∀ q, node q ∈ Icc a b) (hweight : ∀ q, 0 ≤ weight q)
    (hf : IntervalIntegrable f volume a b) (hη : 0 ≤ η)
    (hmoment : ∀ k : Fin (K+1),
      |(∫ t in a..b, t^(k : ℕ)) - ∑ q, weight q * (node q)^(k : ℕ)| ≤ η)
    (hC : ∑ k, ‖c k‖ ≤ C)
    (happrox : ∀ t ∈ Icc a b, ‖f t - finiteVectorPolynomial K c t‖ ≤ e) :
    ‖(∫ t in a..b, f t) - ∑ q, weight q • f (node q)‖ ≤
      ((b-a) + ∑ q, weight q) * e + C * η := by
  let g := finiteVectorPolynomial K c
  have hg : IntervalIntegrable g volume a b :=
    (finiteVectorPolynomial_continuous K c).intervalIntegrable a b
  have hi : ‖∫ t in a..b, f t - g t‖ ≤ (b-a)*e := by
    have hb : ∀ t ∈ uIoc a b, ‖f t-g t‖ ≤ e := by
      intro t ht
      rw [uIoc_of_le hab] at ht
      exact happrox t ⟨ht.1.le, ht.2⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hq : ‖∑ q, weight q • (f (node q) - g (node q))‖ ≤
      (∑ q, weight q)*e := by
    calc
      _ ≤ ∑ q, ‖weight q • (f (node q)-g (node q))‖ := norm_sum_le _ _
      _ ≤ ∑ q, weight q*e := Finset.sum_le_sum (fun q _ => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight q)]
        exact mul_le_mul_of_nonneg_left (happrox _ (hnode q)) (hweight q))
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hm : ‖(∫ t in a..b, g t) - ∑ q, weight q • g (node q)‖ ≤ C*η :=
    (finite_vector_moment_error Q K a b node weight c η hmoment).trans
      ((mul_le_mul_of_nonneg_left hC hη).trans_eq (mul_comm _ _))
  have he : (∫ t in a..b, f t) - ∑ q, weight q • f (node q) =
      ((∫ t in a..b, f t-g t) +
        ((∫ t in a..b, g t) - ∑ q, weight q • g (node q))) -
          ∑ q, weight q • (f (node q)-g (node q)) := by
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub hf hg, Finset.sum_sub_distrib]
    abel
  rw [he]
  calc
    _ ≤ (‖∫ t in a..b, f t-g t‖ +
      ‖(∫ t in a..b, g t) - ∑ q, weight q • g (node q)‖) +
        ‖∑ q, weight q • (f (node q)-g (node q))‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((b-a)*e+C*η)+(∑ q, weight q)*e :=
      add_le_add (add_le_add hi hm) hq
    _ = _ := by ring

end Qatlib.Foundations.OpCalculus.ContourCalc
