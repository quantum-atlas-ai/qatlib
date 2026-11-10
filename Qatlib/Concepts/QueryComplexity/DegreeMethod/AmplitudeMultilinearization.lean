/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped Classical BigOperators

private noncomputable def clause19Multilinearize {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℂ) : MvPolynomial I ℂ :=
  ∑ d ∈ p.support, MvPolynomial.monomial (clampExponent d) (p.coeff d)

private theorem clause19_boolPow_clamp {I : Type} [Fintype I] [DecidableEq I] (x : I → ℂ)
    (d : I →₀ ℕ) (i : I) (h : x i = 0 ∨ x i = 1) :
    x i ^ (clampExponent d i) = x i ^ d i := by
  by_cases hd : d i = 0
  · simp [clampExponent_apply, hd]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hd
    cases h with
    | inl hx => simp [hx, clampExponent_apply, hk]
    | inr hx => simp [hx, clampExponent_apply, hk]

private theorem clause19Multilinearize_coeff_eq_zero {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℂ) (d : I →₀ ℕ) (hd : ∃ i : I, 2 ≤ d i) :
    (clause19Multilinearize p).coeff d = 0 := by
  classical
  rw [clause19Multilinearize, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro d' _
  rw [MvPolynomial.coeff_monomial]
  by_cases he : clampExponent d' = d
  · exfalso
    obtain ⟨i, hi⟩ := hd
    have hle : d i ≤ 1 := clampExponent_mul_le d' d he i
    omega
  · exact if_neg he

private theorem clause19Multilinearize_totalDegree_le {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℂ) : (clause19Multilinearize p).totalDegree ≤ p.totalDegree := by
  classical
  refine (MvPolynomial.totalDegree_finsetSum_le (s := p.support)
      (d := p.totalDegree) ?_).trans le_rfl
  intro d hd
  have h1 : (MvPolynomial.monomial (clampExponent d) (p.coeff d) :
      MvPolynomial I ℂ).totalDegree ≤ (clampExponent d).sum (fun _ e => e) :=
    MvPolynomial.totalDegree_monomial_le _ _
  have h2 : (clampExponent d).sum (fun _ e => e) = ∑ i, clampExponent d i :=
    Finsupp.sum_fintype _ _ (fun _ => rfl)
  have h3 : (∑ i, clampExponent d i) ≤ ∑ i, d i :=
    Finset.sum_le_sum fun i _ => clampExponent_le d i
  have h4 : d.sum (fun _ e => e) = ∑ i, d i := Finsupp.sum_fintype _ _ (fun _ => rfl)
  have h5 : d.sum (fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hd
  omega

private theorem clause19Multilinearize_eval {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℂ) (x : I → ℂ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    MvPolynomial.eval x (clause19Multilinearize p) = MvPolynomial.eval x p := by
  have hpow : ∀ (j : I →₀ ℕ), (∏ i, x i ^ (clampExponent j i)) = ∏ i, x i ^ (j i) :=
    fun j => Finset.prod_congr rfl fun i _ => clause19_boolPow_clamp x j i (hx i)
  rw [clause19Multilinearize]
  rw [MvPolynomial.eval_sum p.support
    (fun d => MvPolynomial.monomial (clampExponent d) (p.coeff d)) x]
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow, hpow]

theorem stageB_query_comparison_clause86 :
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
      (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
      (q : PolynomialWorkspace I W),
    ∃ p : MvPolynomial I ℂ,
      (∀ d : I →₀ ℕ, (∃ i : I, 2 ≤ d i) → p.coeff d = 0) ∧
        MvPolynomial.totalDegree p ≤ QueryCount C ∧
        ∀ f : I → Bool,
          MvPolynomial.eval (fun i => if f i then (1 : ℂ) else 0) p =
            Run (TensorGate (BitOracleOn f) 1) C ψ q := by
  intro I W _ _ _ _ C ψ q
  refine ⟨clause19Multilinearize (amplitudePolynomial C ψ q), ?_, ?_, ?_⟩
  · intro d hd
    exact clause19Multilinearize_coeff_eq_zero (amplitudePolynomial C ψ q) d hd
  · exact (clause19Multilinearize_totalDegree_le (amplitudePolynomial C ψ q)).trans
      (amplitude_polynomial_actual_query_degree C ψ q)
  · intro f
    have hx : ∀ i : I, (if f i then (1 : ℂ) else 0) = 0 ∨ (if f i then (1 : ℂ) else 0) = 1 := by
      intro i
      by_cases h : f i <;> simp [h]
    rw [clause19Multilinearize_eval (amplitudePolynomial C ψ q) _ hx]
    exact amplitude_polynomial_boolean_run_evaluation C ψ f q

end Qatlib.Concepts.QueryComplexity.DegreeMethod
