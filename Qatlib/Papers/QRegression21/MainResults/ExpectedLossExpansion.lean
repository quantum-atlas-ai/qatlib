/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Expected squared loss under a product sign law

`SourceModel` defines `lassoLoss` and `ridgeLoss` by the closed-form expressions of the fixed
source, and records in its module header that these closed forms equal the distributional
expectations `expectedLoss (lassoDist …)` and `expectedLoss (ridgeDist …)`. The paper files
`LassoExpectation` and `RidgeExpectation` discharge that bridge.

This module isolates the reusable part. For a product law over `Bool` coordinates with
coordinate values `xval`, the loss `(∑ j, θ j * xval (b j) - 1) ^ 2` decomposes into the squared
bias `(∑ j, θ j * E[xval]) - 1)` plus the variance contribution `∑ j, θ j^2 * Var_j(xval)`. The
decomposition needs only coordinate expectations and pairwise independence, both available from
the shared `independentSampleLaw` API.

Boundary: the decomposition is stated for finitely many `Bool` coordinates with a fixed target
`y = 1`; unbounded payoffs, dependent coordinates and other targets are not covered.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QRegression21.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.QRegression21.MainResults

/-! ## Linearity of the finite expectation -/

/-- The finite expectation is additive. -/
theorem FinDist.expect_add {X : Type*} [Fintype X] (p : FinDist X) (f g : X → ℝ) :
    p.expect (fun x => f x + g x) = p.expect f + p.expect g := by
  unfold FinDist.expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The finite expectation is subtractive. -/
theorem FinDist.expect_sub {X : Type*} [Fintype X] (p : FinDist X) (f g : X → ℝ) :
    p.expect (fun x => f x - g x) = p.expect f - p.expect g := by
  unfold FinDist.expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The finite expectation of a scalar multiple. -/
theorem FinDist.expect_const_mul {X : Type*} [Fintype X] (p : FinDist X) (c : ℝ)
    (f : X → ℝ) : p.expect (fun x => c * f x) = c * p.expect f := by
  unfold FinDist.expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The finite expectation of a finite sum of functions. -/
theorem FinDist.expect_finset_sum {X : Type*} [Fintype X] {ι : Type*} [DecidableEq ι]
    (p : FinDist X) (s : Finset ι) (f : ι → X → ℝ) :
    p.expect (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, p.expect (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [FinDist.expect]
  | cons a s ha ih =>
    have hfun : (fun x => ∑ i ∈ Finset.cons a s ha, f i x)
        = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x
      rw [Finset.sum_cons]
    rw [hfun, FinDist.expect_add, ih, Finset.sum_cons]

/-! ## Coordinate and pairwise expectations -/

/-- The expectation of a product of two coordinate functions under the product law factors, for
distinct coordinates. -/
theorem independentSampleLaw_expect_coord_mul {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) {j k : Fin n} (hjk : j ≠ k) (f g : X → ℝ) :
    (independentSampleLaw p).expect (fun ω => f (ω j) * g (ω k))
      = (p j).expect f * (p k).expect g := by
  classical
  set F : Fin n → X → ℝ := fun i x => if i = j then f x else if i = k then g x else 1 with hF
  have hjk' : k ≠ j := Ne.symm hjk
  have hval : ∀ c : Fin n, c ≠ j → c ≠ k → ∀ x : X, F c x = 1 := by
    intro c hcj hck x
    simp only [hF]
    rw [ite_eq_right hcj, ite_eq_right hck]
  have hfun : ∀ ω : Fin n → X, ∏ i, F i (ω i) = f (ω j) * g (ω k) := by
    intro ω
    rw [Finset.prod_eq_mul_of_mem j k (Finset.mem_univ j) (Finset.mem_univ k) hjk]
    · show (if j = j then f (ω j) else if j = k then g (ω j) else 1)
          * (if k = j then f (ω k) else if k = k then g (ω k) else 1) = f (ω j) * g (ω k)
      rw [ite_eq_left rfl, ite_eq_right hjk', ite_eq_left rfl]
    · intro c _ hc
      obtain ⟨hcj, hck⟩ := hc
      exact hval c hcj hck (ω c)
  rw [show (independentSampleLaw p).expect (fun ω => f (ω j) * g (ω k))
      = (independentSampleLaw p).expect (fun ω => ∏ i, F i (ω i)) from
    congrArg _ (funext fun ω => (hfun ω).symm), independentSampleLaw_expect_prod p F]
  rw [Finset.prod_eq_mul_of_mem j k (Finset.mem_univ j) (Finset.mem_univ k) hjk]
  · show (∑ x, (p j).prob x * (if j = j then f x else if j = k then g x else 1))
        * (∑ x, (p k).prob x * (if k = j then f x else if k = k then g x else 1))
      = (p j).expect f * (p k).expect g
    have h1 : (∑ x, (p j).prob x * (if j = j then f x else if j = k then g x else 1))
        = ∑ x, (p j).prob x * f x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [ite_eq_left rfl]
    have h2 : (∑ x, (p k).prob x * (if k = j then f x else if k = k then g x else 1))
        = ∑ x, (p k).prob x * g x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [ite_eq_right hjk', ite_eq_left rfl]
    rw [h1, h2]
    rfl
  · intro c _ hc
    obtain ⟨hcj, hck⟩ := hc
    show (∑ x, (p c).prob x * F c x) = 1
    rw [show (∑ x, (p c).prob x * F c x) = ∑ x, (p c).prob x from
      Finset.sum_congr rfl fun x _ => by rw [hval c hcj hck x, mul_one]]
    exact (p c).sum_one

/-! ## The variance decomposition -/

/-- Splitting a doubly indexed sum along its diagonal. -/
theorem sum_ite_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ℝ) (B : ι → ι → ℝ) :
    (∑ j, ∑ k, (if j = k then A j else B j k))
      = (∑ j, ∑ k, B j k) + ∑ j, (A j - B j j) := by
  classical
  have hinner : ∀ j, (∑ k, (if j = k then A j else B j k))
      = (∑ k, B j k) + (A j - B j j) := by
    intro j
    have hpt : ∀ k : ι, (if j = k then A j else B j k)
        = B j k + (if j = k then A j - B j j else 0) := by
      intro k
      by_cases hkj : j = k
      · subst hkj
        simp
      · simp [hkj]
    rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_add_distrib]

/-- The expected squared loss of a linear score under a product sign law equals the squared bias
plus the variance-weighted squared coefficients. -/
theorem expect_sq_sub_one_eq {d : ℕ} (p : Fin d → FinDist Bool) (xval : Bool → ℝ)
    (θ : Fin d → ℝ) :
    (independentSampleLaw p).expect (fun b => ((∑ j, θ j * xval (b j)) - 1) ^ 2)
      = ((∑ j, θ j * (p j).expect xval) - 1) ^ 2
        + ∑ j, θ j ^ 2 *
            ((p j).expect (fun b => xval b ^ 2) - ((p j).expect xval) ^ 2) := by
  classical
  let μ : Fin d → ℝ := fun j => (p j).expect xval
  let s : Fin d → ℝ := fun j => (p j).expect (fun b => xval b ^ 2)
  have hcross : ∀ j k : Fin d,
      (independentSampleLaw p).expect (fun b => (θ j * xval (b j)) * (θ k * xval (b k)))
        = if j = k then θ j ^ 2 * s j else θ j * θ k * (μ j * μ k) := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      have hfun : (fun b : Fin d → Bool => (θ j * xval (b j)) * (θ j * xval (b j)))
          = fun b => θ j ^ 2 * (xval (b j) ^ 2) := by
        funext b
        ring
      rw [hfun, FinDist.expect_const_mul]
      rw [show (independentSampleLaw p).expect (fun b => xval (b j) ^ 2)
          = (p j).expect (fun b => xval b ^ 2) from
        independentSampleLaw_expect_coord p j (fun b => xval b ^ 2)]
      simp [s]
    · have hfun : (fun b : Fin d → Bool => (θ j * xval (b j)) * (θ k * xval (b k)))
          = fun b => (θ j * θ k) * (xval (b j) * xval (b k)) := by
        funext b
        ring
      rw [hfun, FinDist.expect_const_mul,
        independentSampleLaw_expect_coord_mul p hjk xval xval]
      simp [μ, hjk]
  have hexp : ∀ b : Fin d → Bool, ((∑ j, θ j * xval (b j)) - 1) ^ 2
      = (∑ j, ∑ k, (θ j * xval (b j)) * (θ k * xval (b k)))
        - 2 * (∑ j, θ j * xval (b j)) + 1 := by
    intro b
    have h : ((∑ j, θ j * xval (b j)) - 1) ^ 2
        = (∑ j, θ j * xval (b j)) * (∑ k, θ k * xval (b k))
          - 2 * (∑ j, θ j * xval (b j)) + 1 := by
      ring
    rw [h, Finset.sum_mul_sum]
  have hA : (independentSampleLaw p).expect
      (fun b => ∑ j, ∑ k, (θ j * xval (b j)) * (θ k * xval (b k)))
      = ∑ j, ∑ k, (if j = k then θ j ^ 2 * s j else θ j * θ k * (μ j * μ k)) := by
    rw [FinDist.expect_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [FinDist.expect_finset_sum]
    exact Finset.sum_congr rfl fun k _ => hcross j k
  have hS : (independentSampleLaw p).expect (fun b => ∑ j, θ j * xval (b j))
      = ∑ j, θ j * μ j := by
    rw [FinDist.expect_finset_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show (independentSampleLaw p).expect (fun b => θ j * xval (b j))
          = (p j).expect (fun b => θ j * xval b) from
        independentSampleLaw_expect_coord p j (fun b => θ j * xval b),
        FinDist.expect_const_mul]
  have hB : (∑ j, ∑ k, θ j * θ k * (μ j * μ k)) = (∑ j, θ j * μ j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hsplit : (independentSampleLaw p).expect
      (fun b => (∑ j, ∑ k, (θ j * xval (b j)) * (θ k * xval (b k)))
        - 2 * (∑ j, θ j * xval (b j)) + 1)
      = (independentSampleLaw p).expect
          (fun b => ∑ j, ∑ k, (θ j * xval (b j)) * (θ k * xval (b k)))
        - 2 * (independentSampleLaw p).expect (fun b => ∑ j, θ j * xval (b j)) + 1 := by
    rw [FinDist.expect_add, FinDist.expect_sub, FinDist.expect_const_mul, FinDist.expect_const]
  calc (independentSampleLaw p).expect (fun b => ((∑ j, θ j * xval (b j)) - 1) ^ 2)
      = (independentSampleLaw p).expect
          (fun b => (∑ j, ∑ k, (θ j * xval (b j)) * (θ k * xval (b k)))
            - 2 * (∑ j, θ j * xval (b j)) + 1) := congrArg _ (funext hexp)
    _ = (independentSampleLaw p).expect
          (fun b => ∑ j, ∑ k, (θ j * xval (b j)) * (θ k * xval (b k)))
        - 2 * (independentSampleLaw p).expect (fun b => ∑ j, θ j * xval (b j)) + 1 := hsplit
    _ = (∑ j, ∑ k, (if j = k then θ j ^ 2 * s j else θ j * θ k * (μ j * μ k)))
          - 2 * (∑ j, θ j * μ j) + 1 := by rw [hA, hS]
    _ = ((∑ j, θ j * μ j) - 1) ^ 2 + ∑ j, θ j ^ 2 * (s j - μ j ^ 2) := by
        rw [sum_ite_diag (fun j => θ j ^ 2 * s j) (fun j k => θ j * θ k * (μ j * μ k)), hB]
        have hsub : (∑ j, (θ j ^ 2 * s j - θ j * θ j * (μ j * μ j)))
            = ∑ j, θ j ^ 2 * (s j - μ j ^ 2) :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [hsub]
        ring
    _ = ((∑ j, θ j * (p j).expect xval) - 1) ^ 2
          + ∑ j, θ j ^ 2 *
              ((p j).expect (fun b => xval b ^ 2) - ((p j).expect xval) ^ 2) := rfl

/-! ## Bernoulli sign moments -/

/-- The Bernoulli sign has expectation `2 q - 1`. -/
theorem bernoulli_expect_sgn (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (bernoulli q h0 h1).expect sgnBool = 2 * q - 1 := by
  rw [FinDist.expect, Fintype.sum_bool]
  simp [bernoulli, sgnBool]
  ring

/-- The squared Bernoulli sign has expectation one. -/
theorem bernoulli_expect_sgn_sq (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (bernoulli q h0 h1).expect (fun b => sgnBool b ^ 2) = 1 := by
  rw [FinDist.expect, Fintype.sum_bool]
  simp [bernoulli, sgnBool]

/-- A scaled Bernoulli sign has expectation `c * (2 q - 1)`. -/
theorem bernoulli_expect_scale (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (c : ℝ) :
    (bernoulli q h0 h1).expect (fun b => c * sgnBool b) = c * (2 * q - 1) := by
  rw [FinDist.expect, Fintype.sum_bool]
  simp [bernoulli, sgnBool]
  ring

/-- The square of a scaled Bernoulli sign has expectation `c ^ 2`. -/
theorem bernoulli_expect_scale_sq (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (c : ℝ) :
    (bernoulli q h0 h1).expect (fun b => (c * sgnBool b) ^ 2) = c ^ 2 := by
  rw [FinDist.expect, Fintype.sum_bool]
  simp [bernoulli, sgnBool]
  ring

end Qatlib.Papers.QRegression21.MainResults
