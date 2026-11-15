/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeMvPolynomial

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open Polynomial
open scoped Classical BigOperators

/-- Represents the product-bias expectation of a degree-bounded cube function by a polynomial of
degree at most `d`. -/
theorem cube_mu_expectation_polynomial {n d : ℕ} {f : (Fin n → Bool) → ℝ} (hd : CubeDegreeLE d f) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ d ∧ ∀ p : ℝ, P.eval p = cubeExpect n (muWeight p n) f := by
  obtain ⟨c,hc,hf⟩ := hd
  let q : Fin n → Polynomial ℝ := fun _ => Polynomial.X
  refine ⟨cubeExpectationPolynomial c q,
      cube_expectation_polynomial_degree_le c q hc (by intro i; simp [q]), ?_⟩
  intro p
  rw [cube_expectation_polynomial_eval c hf q p]
  simp only [q, Polynomial.eval_X]
  rfl

/-- Represents the product-bias variance by a polynomial of degree at most twice the function
degree on the unit interval. -/
theorem cube_mu_variance_polynomial {n d : ℕ} {f : (Fin n → Bool) → ℝ} (hd : CubeDegreeLE d f) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 2*d ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1, P.eval p = cubeVar n (muWeight p n) f := by
  obtain ⟨P,hP,hPe⟩ := cube_mu_expectation_polynomial hd
  obtain ⟨Q,hQ,hQe⟩ := cube_mu_expectation_polynomial (cube_degree_mul hd hd)
  have hm : (P*P).natDegree ≤ 2*d := (Polynomial.natDegree_mul_le).trans (by omega)
  refine ⟨Q-P*P, (Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) hm), ?_⟩
  intro p hp
  rw [Polynomial.eval_sub, Polynomial.eval_mul, hPe, hQe,
    cube_var_eq_second_moment_sub_sq n (muWeight_cubeWeight hp.1 hp.2 n)]
  simp only [pow_two]

/-- Represents each product-bias influence by a polynomial of degree at most twice the function
degree. -/
theorem cube_mu_influence_polynomial {n d : ℕ} {f : (Fin n → Bool) → ℝ} (hd : CubeDegreeLE d f)
    (i : Fin n) : ∃ P : Polynomial ℝ, P.natDegree ≤ 2*d ∧
      ∀ p : ℝ, P.eval p = cubeInf n (muWeight p n) f i := by
  have hdiff := cube_degree_sub hd (cube_degree_flip hd i)
  obtain ⟨P,hP,hPe⟩ := cube_mu_expectation_polynomial (cube_degree_mul hdiff hdiff)
  refine ⟨P, by omega, ?_⟩
  intro p
  simpa only [cubeInf, pow_two] using hPe p

/-- Bounds changes of a polynomial on the unit interval by four times its squared degree,
uniform bound, and input distance. -/
theorem cube_polynomial_bias_lipschitz {d : ℕ} {P : Polynomial ℝ} (hd : P.natDegree ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |P.eval x| ≤ C)
    {q r : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |P.eval q-P.eval r| ≤ 4*(d : ℝ)^2*C*|q-r| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (P.hasDerivAt x).differentiableAt)
    (fun x hx => by
      rw [(P.hasDerivAt x).deriv, Real.norm_eq_abs]
      exact markov_brothers_unit_deriv_le hd hC hb x hx)
    (convex_Icc (0 : ℝ) 1) hr hq
  simpa only [Real.norm_eq_abs] using h

/-- Bounds the change in product-measure variance by four times the squared degree and bias
distance. -/
theorem cube_mu_variance_bias_lipschitz {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f) {q r : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |cubeVar n (muWeight q n) f-cubeVar n (muWeight r n) f| ≤ 4*(d : ℝ)^2*|q-r| := by
  obtain ⟨P,hP,hPe⟩ := cube_mu_variance_polynomial hd
  have hbound (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : |P.eval p| ≤ 1/4 := by
    rw [hPe p hp, abs_of_nonneg (cubeVar_nonneg n (muWeight_cubeWeight hp.1 hp.2 n) f)]
    exact cubeVar_le_one_quarter n (muWeight_cubeWeight hp.1 hp.2 n) hb
  have h := cube_polynomial_bias_lipschitz hP (by norm_num) hbound hq hr
  rw [hPe q hq, hPe r hr] at h
  convert h using 1
  push_cast
  ring

/-- Bounds the change in product-measure influence by sixteen times the squared degree and bias
distance. -/
theorem cube_mu_influence_bias_lipschitz {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f) (i : Fin n) {q r : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |cubeInf n (muWeight q n) f i-cubeInf n (muWeight r n) f i| ≤ 16*(d : ℝ)^2*|q-r| := by
  obtain ⟨P,hP,hPe⟩ := cube_mu_influence_polynomial hd i
  have hpoint (x : Fin n → Bool) : (f x-f (cubeFlip x i))^2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sq_nonneg _
    · nlinarith [mul_nonneg (show 0 ≤ 1-(f x-f (cubeFlip x i)) by linarith [(hb x).2,(hb (cubeFlip x i)).1])
        (show 0 ≤ 1+(f x-f (cubeFlip x i)) by linarith [(hb x).1,(hb (cubeFlip x i)).2])]
  have hbound (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : |P.eval p| ≤ 1 := by
    rw [hPe p, abs_of_nonneg (cubeInf_nonneg n (muWeight_cubeWeight hp.1 hp.2 n) f i)]
    exact (cube_expect_range (muWeight_cubeWeight hp.1 hp.2 n) hpoint).2
  have h := cube_polynomial_bias_lipschitz hP (by norm_num) hbound hq hr
  rw [hPe q, hPe r] at h
  convert h using 1
  push_cast
  ring

end Qatlib.Concepts.ProbabilityCore.DistributionAA
