/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Independent weighted finite estimators

The product distribution `independentSampleLaw` supports independent observations with different
finite laws. The weighted estimator `weightedSampleSum` has explicit expectation and variance
formulas, leading to a Chebyshev bound. These finite statistical tools support the Monte Carlo
mean-estimation framework of [Montanaro2015].

## Main statements

* `independent_weighted_expectation`: the estimator mean is the weighted sum of component means.
* `independent_weighted_variance`: the estimator variance is the sum of squared weights times
  component variances.
* `independent_weighted_chebyshev`: the explicit variance gives a finite tail bound.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The finite product distribution whose record mass is the product of the coordinate
distribution masses. -/
def independentSampleLaw {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) : FinDist (Fin n → X) where
  prob ω := ∏ i, (p i).prob (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (p i).nonneg _
  sum_one := by
    have hswap : (∑ ω : Fin n → X, ∏ i, (p i).prob (ω i))
        = ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset X)),
            ∏ i, (p i).prob (ω i) :=
      Finset.sum_congr rfl fun ω _ => rfl
    rw [hswap, ← Finset.prod_univ_sum]
    exact Finset.prod_eq_one fun i _ => (p i).sum_one

/-- The sum of the coordinate payoffs multiplied by their respective real weights. -/
def weightedSampleSum {n : ℕ} {X : Type} (w : Fin n → ℝ) (f : Fin n → X → ℝ)
    (ω : Fin n → X) : ℝ := ∑ i, w i * f i (ω i)

/-- The expectation of a product of coordinate payoffs factors into the product of their finite
weighted sums. -/
theorem independentSampleLaw_expect_prod {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) (f : Fin n → X → ℝ) :
    (independentSampleLaw p).expect (fun ω => ∏ i, f i (ω i))
      = ∏ i, (∑ x, (p i).prob x * f i x) := by
  have habs : ∀ ω : Fin n → X,
      (independentSampleLaw p).prob ω * ∏ k, f k (ω k)
        = ∏ k, ((p k).prob (ω k) * f k (ω k)) := by
    intro ω
    show (∏ i, (p i).prob (ω i)) * ∏ k, f k (ω k) = _
    rw [← Finset.prod_mul_distrib]
  calc (independentSampleLaw p).expect (fun ω => ∏ i, f i (ω i))
      = ∑ ω : Fin n → X, ∏ k, ((p k).prob (ω k) * f k (ω k)) :=
        Finset.sum_congr rfl fun ω _ => habs ω
    _ = ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset X)),
          ∏ k, ((p k).prob (ω k) * f k (ω k)) :=
        Finset.sum_congr rfl fun ω _ => rfl
    _ = ∏ k : Fin n, (∑ x, (p k).prob x * f k x) :=
        (Finset.prod_univ_sum
          (t := fun _ : Fin n => (Finset.univ : Finset X))
          (f := fun k x => (p k).prob x * f k x)).symm

/-- The independent record law has product masses and factors expectations of arbitrary products
of coordinate payoffs. -/
theorem independent_sample_product_law {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) (ω : Fin n → X) :
    (independentSampleLaw p).prob ω = ∏ i, (p i).prob (ω i) ∧
      (∀ f : Fin n → X → ℝ, (independentSampleLaw p).expect (fun ω => ∏ i, f i (ω i))
        = ∏ i, (p i).expect (f i)) :=
  ⟨rfl, fun f => independentSampleLaw_expect_prod p f⟩

/-- The expectation of a constant under a finite probability distribution equals that constant. -/
theorem FinDist.expect_const {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (c : ℝ) : p.expect (fun _ => c) = c := by
  show ∑ x, p.prob x * c = c
  rw [← Finset.sum_mul, p.sum_one, one_mul]

/-- A payoff depending on one observation has expectation equal to its expectation under that
coordinate's law. -/
theorem independentSampleLaw_expect_coord {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) (k : Fin n) (h : X → ℝ) :
    (independentSampleLaw p).expect (fun ω => h (ω k)) = (p k).expect h := by
  have hsplit : ∀ ω : Fin n → X, h (ω k) = ∏ j, (if j = k then h (ω j) else 1) := by
    intro ω
    rw [Finset.prod_eq_single k]
    · rw [ite_eq_left rfl]
    · intro j _ hjk
      simp only [hjk, ite_false]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  calc (independentSampleLaw p).expect (fun ω => h (ω k))
      = (independentSampleLaw p).expect (fun ω => ∏ j, (if j = k then h (ω j) else 1)) :=
        congrArg _ (funext hsplit)
    _ = ∏ j, (∑ x, (p j).prob x * (if j = k then h x else 1)) :=
        independentSampleLaw_expect_prod p (fun j x => if j = k then h x else 1)
    _ = (p k).expect h := by
        rw [Finset.prod_eq_single k]
        · simp only [ite_true]
          rfl
        · intro j _ hjk
          simp only [hjk, ite_false, mul_one]
          exact (p j).sum_one
        · intro hcon
          exact absurd (Finset.mem_univ k) hcon

/-- The expectation of the weighted sample sum equals the sum of the weights times the component
expectations. -/
theorem independent_weighted_expectation {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) (w : Fin n → ℝ) (f : Fin n → X → ℝ) :
    (independentSampleLaw p).expect (weightedSampleSum w f)
      = ∑ i, w i * (p i).expect (f i) := by
  calc (independentSampleLaw p).expect (weightedSampleSum w f)
      = ∑ ω : Fin n → X, (independentSampleLaw p).prob ω * ∑ i, w i * f i (ω i) := rfl
    _ = ∑ ω : Fin n → X, ∑ i, (independentSampleLaw p).prob ω * (w i * f i (ω i)) :=
        Finset.sum_congr rfl fun ω _ =>
          Finset.mul_sum Finset.univ (fun i => w i * f i (ω i)) _
    _ = ∑ i, ∑ ω : Fin n → X, (independentSampleLaw p).prob ω * (w i * f i (ω i)) :=
        Finset.sum_comm
    _ = ∑ i, w i * ∑ ω : Fin n → X, (independentSampleLaw p).prob ω * f i (ω i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ = ∑ i, w i * (p i).expect (f i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (∑ ω : Fin n → X, (independentSampleLaw p).prob ω * f i (ω i))
            = (p i).expect (f i) from independentSampleLaw_expect_coord p i (f i)]

/-- The variance of the independent weighted sample sum equals the sum of squared weights times
the component variances. -/
theorem independent_weighted_variance {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) (w : Fin n → ℝ) (f : Fin n → X → ℝ) :
    (independentSampleLaw p).variance (weightedSampleSum w f)
      = ∑ i, (w i)^2 * (p i).variance (f i) := by
  set μ : Fin n → ℝ := fun i => (p i).expect (f i) with hμ
  have hmean : (independentSampleLaw p).expect (weightedSampleSum w f) = ∑ i, w i * μ i :=
    independent_weighted_expectation p w f
  have hcenter : ∀ ω : Fin n → X,
      weightedSampleSum w f ω - ∑ i, w i * μ i = ∑ i, w i * (f i (ω i) - μ i) := by
    intro ω
    show (∑ i, w i * f i (ω i)) - ∑ i, w i * μ i = _
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : ∀ ω : Fin n → X,
      (weightedSampleSum w f ω - ∑ i, w i * μ i) ^ 2
        = ∑ i, ∑ j, (w i * (f i (ω i) - μ i)) * (w j * (f j (ω j) - μ j)) := by
    intro ω
    rw [hcenter ω, sq, Finset.sum_mul_sum]

  have hterm : ∀ i j : Fin n,
      (independentSampleLaw p).expect
          (fun ω => (w i * (f i (ω i) - μ i)) * (w j * (f j (ω j) - μ j)))
        = w i * w j * (if i = j then (p i).variance (f i) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      have h1 : (independentSampleLaw p).expect
            (fun ω => (w i * (f i (ω i) - μ i)) * (w i * (f i (ω i) - μ i)))
          = (w i)^2 * (independentSampleLaw p).expect (fun ω => (f i (ω i) - μ i)^2) := by
        show ∑ ω, (independentSampleLaw p).prob ω *
              ((w i * (f i (ω i) - μ i)) * (w i * (f i (ω i) - μ i)))
            = (w i)^2 * ∑ ω, (independentSampleLaw p).prob ω * (f i (ω i) - μ i)^2
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
      rw [h1, independentSampleLaw_expect_coord p i (fun x => (f i x - μ i)^2)]
      rw [hμ]
      show (w i)^2 * (p i).variance (f i) = w i * w i * (p i).variance (f i)
      ring
    · rw [ite_eq_right hij]
      have hprod : ∀ ω : Fin n → X,
          ∏ m, (if m = i ∨ m = j then f m (ω m) - μ m else 1)
            = (f i (ω i) - μ i) * (f j (ω j) - μ j) := by
        intro ω
        rw [← Finset.prod_subset (Finset.subset_univ (insert i {j}))
          (fun m _ hm => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rw [ite_eq_right (fun hor => by tauto)]),
          Finset.prod_insert (Finset.notMem_singleton.mpr hij), Finset.prod_singleton]
        simp only [true_or, or_true, ite_true]
      have hz : ∏ m, (∑ x, (p m).prob x * (if m = i ∨ m = j then f m x - μ m else 1))
          = 0 := by
        have hz0 : (∑ x, (p i).prob x * (if i = i ∨ i = j then f i x - μ i else 1))
            = 0 := by
          simp only [eq_self, true_or, ite_true]
          rw [hμ]
          exact Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_sub_mean (p i) (f i)
        exact Finset.prod_eq_zero (Finset.mem_univ i) hz0
      have hfact : (independentSampleLaw p).expect
            (fun ω => ∏ m, (if m = i ∨ m = j then f m (ω m) - μ m else 1))
          = 0 := by
        calc (independentSampleLaw p).expect
              (fun ω => ∏ m, (if m = i ∨ m = j then f m (ω m) - μ m else 1))
            = ∏ m, (∑ x, (p m).prob x * (if m = i ∨ m = j then f m x - μ m else 1)) :=
              independentSampleLaw_expect_prod p
                (fun m x => if m = i ∨ m = j then f m x - μ m else 1)
          _ = 0 := hz
      calc (independentSampleLaw p).expect
            (fun ω => (w i * (f i (ω i) - μ i)) * (w j * (f j (ω j) - μ j)))
          = w i * w j * (independentSampleLaw p).expect
              (fun ω => ∏ m, (if m = i ∨ m = j then f m (ω m) - μ m else 1)) := by
            show ∑ ω, (independentSampleLaw p).prob ω *
                  ((w i * (f i (ω i) - μ i)) * (w j * (f j (ω j) - μ j)))
                = w i * w j * ∑ ω, (independentSampleLaw p).prob ω *
                    (∏ m, (if m = i ∨ m = j then f m (ω m) - μ m else 1))
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun ω _ => by rw [hprod ω]; ring
        _ = w i * w j * 0 := by rw [hfact]

  have hexpand : (independentSampleLaw p).variance (weightedSampleSum w f)
      = ∑ i, ∑ j, w i * w j * (if i = j then (p i).variance (f i) else 0) := by
    calc (independentSampleLaw p).variance (weightedSampleSum w f)
        = ∑ ω : Fin n → X, (independentSampleLaw p).prob ω *
            (weightedSampleSum w f ω - ∑ i, w i * μ i)^2 := by
          show (independentSampleLaw p).expect
              (fun ω => (weightedSampleSum w f ω -
                (independentSampleLaw p).expect (weightedSampleSum w f))^2) = _
          rw [hmean]
          rfl
      _ = ∑ ω : Fin n → X, (independentSampleLaw p).prob ω *
            (∑ i, ∑ j, (w i * (f i (ω i) - μ i)) * (w j * (f j (ω j) - μ j))) :=
          Finset.sum_congr rfl fun ω _ => by rw [hsq ω]
      _ = ∑ ω : Fin n → X, ∑ i, ∑ j, (independentSampleLaw p).prob ω *
            ((w i * (f i (ω i) - μ i)) * (w j * (f j (ω j) - μ j))) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, ∑ ω : Fin n → X, (independentSampleLaw p).prob ω *
            ((w i * (f i (ω i) - μ i)) * (w j * (f j (ω j) - μ j))) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, w i * w j * (if i = j then (p i).variance (f i) else 0) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
  rw [hexpand]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsumj : (∑ j, w i * w j * (if i = j then (p i).variance (f i) else 0))
      = w i * w i * (p i).variance (f i) := by
    have h1 : ∀ j : Fin n, w i * w j * (if i = j then (p i).variance (f i) else 0)
        = if i = j then w i * w i * (p i).variance (f i) else 0 := by
      intro j
      by_cases h : i = j
      · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i)]
  rw [hsumj]
  ring

/-- For positive `ε`, the probability that the weighted sample sum deviates from its mean by
more than `ε` is at most the summed weighted variances divided by ε². -/
theorem independent_weighted_chebyshev {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) (w : Fin n → ℝ) (f : Fin n → X → ℝ) (ε : ℝ) (hε : 0 < ε) :
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |weightedSampleSum w f ω - ∑ i, w i*(p i).expect (f i)|), (independentSampleLaw p).prob ω) ≤ (∑ i, (w i)^2*(p i).variance (f i))/ε^2 := by
  set M := ∑ i, w i * (p i).expect (f i) with hM
  have hnn : ∀ ω : Fin n → X, 0 ≤ (independentSampleLaw p).prob ω :=
    fun ω => (independentSampleLaw p).nonneg ω
  have hpoint : ∀ ω : Fin n → X, ε < |weightedSampleSum w f ω - M| →
      (independentSampleLaw p).prob ω
        ≤ (independentSampleLaw p).prob ω * (weightedSampleSum w f ω - M)^2 / ε^2 := by
    intro ω hlt
    have hd : ε^2 ≤ (weightedSampleSum w f ω - M)^2 := by
      nlinarith [hlt, abs_nonneg (weightedSampleSum w f ω - M),
        sq_abs (weightedSampleSum w f ω - M)]
    calc (independentSampleLaw p).prob ω = (independentSampleLaw p).prob ω * 1 := by ring
      _ ≤ (independentSampleLaw p).prob ω * ((weightedSampleSum w f ω - M)^2 / ε^2) := by
          refine mul_le_mul_of_nonneg_left ?_ (hnn ω)
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < ε^2), one_mul]
          exact hd
      _ = (independentSampleLaw p).prob ω * (weightedSampleSum w f ω - M)^2 / ε^2 := by ring
  have htotal : (∑ ω : Fin n → X,
        (independentSampleLaw p).prob ω * (weightedSampleSum w f ω - M)^2)
      = ∑ i, (w i)^2 * (p i).variance (f i) := by
    have hm : (independentSampleLaw p).expect (weightedSampleSum w f) = M :=
      independent_weighted_expectation p w f
    have hvar : (independentSampleLaw p).variance (weightedSampleSum w f)
        = ∑ ω : Fin n → X,
            (independentSampleLaw p).prob ω * (weightedSampleSum w f ω - M)^2 := by
      show (independentSampleLaw p).expect
          (fun ω => (weightedSampleSum w f ω -
            (independentSampleLaw p).expect (weightedSampleSum w f))^2) = _
      rw [hm]
      rfl
    rw [← hvar]
    exact independent_weighted_variance p w f
  calc (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |weightedSampleSum w f ω - M|),
        (independentSampleLaw p).prob ω)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |weightedSampleSum w f ω - M|),
          (independentSampleLaw p).prob ω * (weightedSampleSum w f ω - M)^2 / ε^2 := by
        refine Finset.sum_le_sum fun ω hω => ?_
        exact hpoint ω (Finset.mem_filter.mp hω).2
    _ = (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |weightedSampleSum w f ω - M|),
          (independentSampleLaw p).prob ω * (weightedSampleSum w f ω - M)^2) / ε^2 :=
        (Finset.sum_div (Finset.univ.filter (fun ω => ε < |weightedSampleSum w f ω - M|))
          (fun ω => (independentSampleLaw p).prob ω * (weightedSampleSum w f ω - M)^2) _).symm
    _ ≤ (∑ ω : Fin n → X,
          (independentSampleLaw p).prob ω * (weightedSampleSum w f ω - M)^2) / ε^2 := by
        refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => mul_nonneg (hnn ω) (sq_nonneg _))
    _ = (∑ i, (w i)^2 * (p i).variance (f i)) / ε^2 := by rw [htotal]

end Qatlib.Concepts.MonteCarloMean.FinDistBounds
