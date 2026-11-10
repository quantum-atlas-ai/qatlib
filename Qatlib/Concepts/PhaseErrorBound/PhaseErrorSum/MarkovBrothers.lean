/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Polynomial

private theorem markov_endpoint_unit {d : ℕ} {g : Polynomial ℝ}
    (hd : g.natDegree ≤ d) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.eval x| ≤ 1) :
    |g.derivative.eval 1| ≤ (d : ℝ)^2 := by
  have hg : g.degree ≤ d := g.degree_le_natDegree.trans (by exact_mod_cast hd)
  have hp := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (n := d) (k := 1) (x := 1) le_rfl hg hb
  have hn := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (n := d) (k := 1) (x := 1) (P := -g) le_rfl (by simpa using hg)
    (fun x hx => by simpa using hb x hx)
  simp only [Function.iterate_one, Polynomial.derivative_neg, Polynomial.eval_neg,
    Polynomial.Chebyshev.derivative_T_eval_one] at hp hn
  norm_cast at hp hn
  push_cast at hp hn
  exact abs_le.2 ⟨by linarith, hp⟩

private theorem markov_endpoint {d : ℕ} {g : Polynomial ℝ} (hd : g.natDegree ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.eval x| ≤ C) :
    |g.derivative.eval 1| ≤ (d : ℝ)^2*C := by
  rcases hC.eq_or_lt with hc | hc
  · have hz : g = 0 := Polynomial.eq_zero_of_infinite_isRoot g
      ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono (fun x hx => by
        change g.eval x = 0
        apply abs_eq_zero.1
        apply le_antisymm
        · simpa [← hc] using hb x hx
        · exact abs_nonneg _))
    simp [hz, ← hc]
  · have hnorm : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(C⁻¹ • g).eval x| ≤ 1 := by
      intro x hx
      simp only [Polynomial.eval_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left (hb x hx) (inv_nonneg.2 hc.le)).trans_eq
          (inv_mul_cancel₀ hc.ne')
    have he := markov_endpoint_unit ((Polynomial.natDegree_smul_le C⁻¹ g).trans hd) hnorm
    simp only [Polynomial.derivative_smul, Polynomial.eval_smul, smul_eq_mul,
      abs_mul, abs_inv, abs_of_pos hc] at he
    have he' := mul_le_mul_of_nonneg_left he hc.le
    simpa [← mul_assoc, hc.ne', mul_comm] using he'

private theorem markov_affine_degree (g : Polynomial ℝ) (a b : ℝ) :
    (g.comp (Polynomial.C a*Polynomial.X+Polynomial.C b)).natDegree ≤ g.natDegree := by
  have hq : (Polynomial.C a*Polynomial.X+Polynomial.C b).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
    · simp
  exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul_left g.natDegree hq).trans_eq (Nat.mul_one _))

private theorem markov_affine_derivative (g : Polynomial ℝ) (a b x : ℝ) :
    (g.comp (Polynomial.C a*Polynomial.X+Polynomial.C b)).derivative.eval x =
      a*g.derivative.eval (a*x+b) := by
  simp [Polynomial.derivative_comp]

theorem markov_brothers_deriv_le {d : ℕ} {g : Polynomial ℝ} (hd : g.natDegree ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.eval x| ≤ C) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.derivative.eval x| ≤ 2*(d : ℝ)^2*C := by
  intro x hx
  let z : ℝ := if 0 ≤ x then -1 else 1
  let a := (x-z)/2
  let b := (x+z)/2
  have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by dsimp [z]; split_ifs <;> norm_num
  have hab : a+b = x := by dsimp [a,b]; ring
  have ha : (1/2 : ℝ) ≤ |a| := by
    dsimp [a,z]
    split_ifs with h
    · rw [abs_of_nonneg (by linarith : 0 ≤ (x-(-1))/2)]
      linarith
    · rw [abs_of_nonpos (by linarith : (x-1)/2 ≤ 0)]
      linarith
  have hmap (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) : a*u+b ∈ Set.Icc (-1 : ℝ) 1 := by
    have hp : 0 ≤ (1+u)/2 := by linarith [hu.1]
    have hq : 0 ≤ (1-u)/2 := by linarith [hu.2]
    dsimp [a,b]
    constructor
    · nlinarith [mul_nonneg (show 0 ≤ x+1 by linarith [hx.1]) hp,
        mul_nonneg (show 0 ≤ z+1 by linarith [hz.1]) hq]
    · nlinarith [mul_nonneg (show 0 ≤ 1-x by linarith [hx.2]) hp,
        mul_nonneg (show 0 ≤ 1-z by linarith [hz.2]) hq]
  have he := markov_endpoint ((markov_affine_degree g a b).trans hd) hC
    (fun u hu => by simpa using hb (a*u+b) (hmap u hu))
  rw [markov_affine_derivative, mul_one, hab, abs_mul] at he
  have hl := mul_le_mul_of_nonneg_right ha (abs_nonneg (g.derivative.eval x))
  nlinarith only [he, hl]

theorem markov_brothers_unit_deriv_le {d : ℕ} {g : Polynomial ℝ} (hd : g.natDegree ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g.eval x| ≤ C) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |g.derivative.eval x| ≤ 4*(d : ℝ)^2*C := by
  intro x hx
  have hdq := (markov_affine_degree g (1/2) (1/2)).trans hd
  have he := markov_brothers_deriv_le hdq hC
    (fun u hu => by
      have hmem : (1/2 : ℝ)*u+1/2 ∈ Set.Icc 0 1 := by constructor <;> linarith [hu.1,hu.2]
      simpa using hb _ hmem) (2*x-1) (by constructor <;> linarith [hx.1,hx.2])
  rw [markov_affine_derivative] at he
  have hx' : (1/2 : ℝ)*(2*x-1)+1/2 = x := by ring
  rw [hx', abs_mul] at he
  norm_num at he
  nlinarith only [he]

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
