/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Banach Polynomial

A finite vector polynomial is continuous without any dimension assumption.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.OpCalculus.ContourCalc

open scoped BigOperators

/-- Construction for finite Vector Polynomial in the banach polynomial model. -/
noncomputable def finiteVectorPolynomial {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (K : ℕ) (c : Fin (K + 1) → E) (t : ℝ) : E :=
  ∑ i : Fin (K + 1), t ^ (i : ℕ) • c i


open Set MeasureTheory
open scoped BigOperators

/-- A finite vector polynomial is continuous without any dimension assumption. -/
theorem finiteVectorPolynomial_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : ℕ) (c : Fin (K + 1) → E) :
    Continuous (finiteVectorPolynomial K c) := by
  unfold finiteVectorPolynomial
  exact continuous_finsetSum _ fun i _ =>
    (continuous_id.pow (i : ℕ)).smul continuous_const

/-- Scalar polynomial exactness lifts to every finite real-vector coefficient
array, with the same nodes and weights for every Banach space. -/
theorem finiteVectorPolynomial_rule_exact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (Q : ℕ) (a h : ℝ) (node weight : Fin Q → ℝ)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      (∫ t in a..a + h, p.eval t) = ∑ q, weight q * p.eval (node q))
    (K : ℕ) (c : Fin (K + 1) → E) (hK : K ≤ 2 * Q - 1) :
    (∫ t in a..a + h, finiteVectorPolynomial K c t) =
      ∑ q, weight q • finiteVectorPolynomial K c (node q) := by
  have hmono (i : Fin (K + 1)) :
      (∫ t in a..a + h, t ^ (i : ℕ)) =
        ∑ q, weight q * (node q) ^ (i : ℕ) := by
    have hi : (i : ℕ) ≤ 2 * Q - 1 := (Nat.le_of_lt_succ i.isLt).trans hK
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      hexact (Polynomial.X ^ (i : ℕ)) (by simpa using hi)
  have hsumIntegral :
      (∫ t in a..a + h, ∑ i : Fin (K + 1), t ^ (i : ℕ) • c i) =
        ∑ i : Fin (K + 1), ∫ t in a..a + h, t ^ (i : ℕ) • c i :=
    intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (K + 1)) (t : ℝ) => t ^ (i : ℕ) • c i)
      (fun i _ => ((continuous_id.pow (i : ℕ)).smul
        (continuous_const : Continuous (fun _ : ℝ => c i))).intervalIntegrable a (a + h))
  unfold finiteVectorPolynomial
  rw [hsumIntegral]
  simp_rw [intervalIntegral.integral_smul_const, hmono]
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

/-- Positive weights of total mass equal to the cell length give a
dimension-free error bound for uniform approximation by an exact integrand. -/
theorem positive_rule_banach_error_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (Q : ℕ) (a h : ℝ) (node weight : Fin Q → ℝ)
    (f g : ℝ → E) (ε : ℝ) (hh : 0 < h)
    (hnode : ∀ q, node q ∈ Icc a (a + h))
    (hweight : ∀ q, 0 ≤ weight q) (hsum : (∑ q, weight q) = h)
    (hf : IntervalIntegrable f volume a (a + h))
    (hg : IntervalIntegrable g volume a (a + h))
    (hexact : (∫ t in a..a + h, g t) = ∑ q, weight q • g (node q))
    (_hε : 0 ≤ ε) (hbound : ∀ t ∈ Icc a (a + h), ‖f t - g t‖ ≤ ε) :
    ‖(∫ t in a..a + h, f t) - ∑ q, weight q • f (node q)‖ ≤ 2 * h * ε := by
  have hab : a ≤ a + h := by linarith
  have hint : ‖∫ t in a..a + h, f t - g t‖ ≤ h * ε := by
    have hb : ∀ t ∈ Set.uIoc a (a + h), ‖f t - g t‖ ≤ ε := by
      intro t ht
      rw [uIoc_of_le hab] at ht
      exact hbound t ⟨ht.1.le, ht.2⟩
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simpa [abs_of_pos hh, mul_comm] using hi
  have hquad : ‖∑ q, weight q • (f (node q) - g (node q))‖ ≤ h * ε := by
    calc
      _ ≤ ∑ q, ‖weight q • (f (node q) - g (node q))‖ := norm_sum_le _ _
      _ ≤ ∑ q, weight q * ε := by
        apply Finset.sum_le_sum
        intro q _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight q)]
        exact mul_le_mul_of_nonneg_left (hbound (node q) (hnode q)) (hweight q)
      _ = h * ε := by rw [← Finset.sum_mul, hsum]
  have hdecomp : (∫ t in a..a + h, f t) - ∑ q, weight q • f (node q) =
      (∫ t in a..a + h, f t - g t) -
        ∑ q, weight q • (f (node q) - g (node q)) := by
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub hf hg, Finset.sum_sub_distrib, hexact]
    abel
  rw [hdecomp]
  exact (norm_sub_le _ _).trans ((add_le_add hint hquad).trans_eq (by ring))

end Qatlib.Foundations.OpCalculus.ContourCalc
