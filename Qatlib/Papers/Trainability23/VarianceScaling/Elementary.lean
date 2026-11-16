/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Qatlib.Papers.Trainability23.VarianceScaling.Elementary.SourceElementary
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-!
# Elementary source results

These finite probability identities and conditional estimates preserve closed
results from arXiv:2305.02881v2. They do not assert the missing full Haar-product
MMD variance identity or an unconditional trainability theorem.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.VarianceScaling.Elementary
open scoped BigOperators Matrix
namespace Qatlib.Papers.Trainability23.VarianceScaling.Elementary

/-

/-- The product of two finite laws, `(p × q) (a,b) = p a * q b`. This is the finite model of the
independent parameter blocks `α` and `β` in Lemma 4. -/
noncomputable def prodLaw {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) : FinDist (A × B) where
  prob z := p.prob z.1 * q.prob z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    have h : ∀ a, ∑ b : B, p.prob a * q.prob b = p.prob a := by
      intro a
      rw [← Finset.mul_sum, q.sum_one, mul_one]
    rw [Finset.sum_congr rfl (fun a _ => h a), p.sum_one]

/-- The expectation of a function of the product pair, written as the iterated expectation. -/
theorem prodLaw_expect {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) (f : A × B → ℝ) :
    (prodLaw p q).expect f = ∑ a, p.prob a * ∑ b, q.prob b * f (a, b) := by
  unfold FinDist.expect
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [prodLaw]
  ring

/-- The sum form of `prodLaw_expect`: the first moment as an explicit double sum. -/
theorem prodLaw_sum {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) (f : A × B → ℝ) :
    ∑ z : A × B, (prodLaw p q).prob z * f z
      = ∑ a, p.prob a * ∑ b, q.prob b * f (a, b) := by
  simpa only [FinDist.expect] using prodLaw_expect p q f
-/

/-- The second moment of a function of the product pair, written as the iterated second moment. -/
theorem prod_second {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) (f : A × B → ℝ) :
    ∑ z : A × B, (prodLaw p q).prob z * (f z) ^ 2
      = ∑ a, p.prob a * ∑ b, q.prob b * (f (a, b)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [prodLaw]
  ring

/-- Mean-square form of the finite variance: `Var = E[f²] - (E[f])²`. -/
theorem var_moments {X : Type*} [Fintype X] (p : FinDist X) (f : X → ℝ) :
    p.variance f = (∑ x, p.prob x * (f x) ^ 2) - (p.expect f) ^ 2 := by
  have hpt : ∀ x : X, p.prob x * (f x - p.expect f) ^ 2
      = p.prob x * (f x) ^ 2 - 2 * p.expect f * (p.prob x * f x)
        + (p.expect f) ^ 2 * p.prob x := fun x => by ring
  have h1 : ∑ x, 2 * p.expect f * (p.prob x * f x) = 2 * p.expect f * p.expect f := by
    rw [← Finset.mul_sum]
    rfl
  have h2 : ∑ x, (p.expect f) ^ 2 * p.prob x = (p.expect f) ^ 2 := by
    rw [← Finset.mul_sum, p.sum_one, mul_one]
  calc p.variance f
      = ∑ x, p.prob x * (f x - p.expect f) ^ 2 := rfl
    _ = ∑ x, (p.prob x * (f x) ^ 2 - 2 * p.expect f * (p.prob x * f x)
          + (p.expect f) ^ 2 * p.prob x) := Finset.sum_congr rfl fun x _ => hpt x
    _ = (∑ x, p.prob x * (f x) ^ 2) - 2 * p.expect f * p.expect f + (p.expect f) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
    _ = (∑ x, p.prob x * (f x) ^ 2) - (p.expect f) ^ 2 := by ring

/-- **Lemma 4, Eq. (354)**. For `f (α, β)` on independent finite blocks with product law,
`Var_{(α,β)} f = E_α [Var_β f] + Var_α [E_β f]`. -/
theorem total_variance {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) (f : A × B → ℝ) :
    (prodLaw p q).variance f
      = (∑ a, p.prob a * q.variance (fun b => f (a, b)))
        + p.variance (fun a => ∑ b, q.prob b * f (a, b)) := by
  have hsplit : ∑ a, p.prob a * ((∑ b, q.prob b * (f (a, b)) ^ 2)
        - (∑ b, q.prob b * f (a, b)) ^ 2)
      = (∑ a, p.prob a * ∑ b, q.prob b * (f (a, b)) ^ 2)
        - ∑ a, p.prob a * (∑ b, q.prob b * f (a, b)) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [var_moments, prod_second, prodLaw_sum, FinDist.expect]
  rw [hsplit]
  ring


end Qatlib.Papers.Trainability23.VarianceScaling.Elementary
