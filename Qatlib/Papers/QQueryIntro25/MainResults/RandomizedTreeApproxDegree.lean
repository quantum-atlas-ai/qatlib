/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
public import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonDefs
public import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeMvPolynomial
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-!
# Randomized decision trees and the approximate degree

Proposition 20 of [Hamoudi, 2025][Hamoudi2025QueryIntro] is the randomized half of the polynomial
method: if a probability distribution `prog` over Boolean decision trees answers a Boolean
function `f` correctly with probability at least `2 / 3` on every input, and every tree of
positive mass makes at most `T` queries, then `f` has an approximating real polynomial of total
degree at most `T`, so `approxDegree f ≤ T`.

The seed-averaged acceptance `x ↦ ∑' t, prog t · accept_t x` is a limit of finite convex
combinations of the acceptance indicators of the trees in the support. Every such indicator lies
in the linear span of the cube monomials of cardinality at most `T`, that span is finite
dimensional, and a finite-dimensional subspace of the product space of real functions on the cube
is closed. Hence the average lies in the span as well, and the `2 / 3` guarantee puts it within
`1 / 3` of `f` on every input.

## Main statements

* `treeAcceptReal`: the real acceptance indicator of a single tree.
* `averageAccept`: the seed-averaged real acceptance of a program.
* `cubeDegreeLE_treeAcceptReal`: a tree of maximum query count `d` has cube degree at most `d`.
* `mem_degreeBoundSubmodule_of_pmf`: bounded queries keep the average acceptance in the space of
  functions of cube degree at most `T`.
* `approxDegree_le_of_boundedSuccess`: the randomized degree bound of Proposition 20.

## Boundary

The bound is `approxDegree f ≤ T` for the support-uniform query bound `∀ t ∈ prog.support,
MaxQueries t ≤ T`; the expected-query model behind `randomizedComplexity` is not treated. Nothing
is claimed about the converse direction, and the sharper constant `2 T` for quantum algorithms in
`Qatlib.Concepts.QueryComplexity.DegreeMethod.boundedErrorApproxDegreeQueryLowerBound` is not
revisited. The `2 / 3` threshold is used exactly as stated: it leaves no slack in the `1 / 3`
approximation margin.

## References

* [Hamoudi, 2025][Hamoudi2025QueryIntro], Proposition 20.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal

namespace Qatlib.Papers.QQueryIntro25.MainResults.RandomizedTreeApproxDegree

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.ProbabilityCore.DistributionAA

variable {n : ℕ}

/-- The real acceptance indicator of a Boolean decision tree on a Boolean input. -/
noncomputable def treeAcceptReal (t : BoolQueryTree (Fin n) Bool) (x : Fin n → Bool) : ℝ :=
  if (BoolQueryTree.Run x t).1 then 1 else 0

/-- The real acceptance indicator is the evaluation of the tree's acceptance polynomial. -/
theorem treeAcceptReal_eq_eval (t : BoolQueryTree (Fin n) Bool) (x : Fin n → Bool) :
    treeAcceptReal t x
      = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (treeAcceptPolynomial t) := by
  rw [treeAcceptReal]
  have h := treeAcceptPolynomial_eval t x
  unfold oraclePoint at h
  exact h.symm

/-- The real acceptance indicator is nonnegative. -/
theorem treeAcceptReal_nonneg (t : BoolQueryTree (Fin n) Bool) (x : Fin n → Bool) :
    0 ≤ treeAcceptReal t x := by
  rw [treeAcceptReal]
  split <;> norm_num

/-- The real acceptance indicator is at most one. -/
theorem treeAcceptReal_le_one (t : BoolQueryTree (Fin n) Bool) (x : Fin n → Bool) :
    treeAcceptReal t x ≤ 1 := by
  rw [treeAcceptReal]
  split <;> norm_num

/-- The correctness indicator of the predicate "output equals `false`" is one minus the real
acceptance. -/
theorem indicator_false_eq_one_sub (t : BoolQueryTree (Fin n) Bool) (x : Fin n → Bool) :
    (if (BoolQueryTree.Run x t).1 = false then (1 : ℝ) else 0) = 1 - treeAcceptReal t x := by
  cases h : (BoolQueryTree.Run x t).1 <;> simp [treeAcceptReal, h]

/-- The correctness indicator of the predicate "output equals `true`" is the real acceptance. -/
theorem indicator_true_eq (t : BoolQueryTree (Fin n) Bool) (x : Fin n → Bool) :
    (if (BoolQueryTree.Run x t).1 = true then (1 : ℝ) else 0) = treeAcceptReal t x := by
  cases h : (BoolQueryTree.Run x t).1 <;> simp [treeAcceptReal, h]

/-- A tree whose maximum query count is `d` has acceptance indicator of cube degree at most
`d`. -/
theorem cubeDegreeLE_treeAcceptReal (t : BoolQueryTree (Fin n) Bool) :
    CubeDegreeLE (BoolQueryTree.MaxQueries t) (treeAcceptReal t) := by
  have h := cube_degree_of_mv_polynomial (treeAcceptPolynomial t)
    (treeAcceptPolynomial_totalDegree_le t)
  have he : (fun x : Fin n → Bool =>
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (treeAcceptPolynomial t))
      = treeAcceptReal t := by
    funext x
    exact (treeAcceptReal_eq_eval t x).symm
  rwa [he] at h

/-- An upper bound on the cube degree is monotone in the bound. -/
theorem cubeDegreeLE_mono {d d' : ℕ} (h : d ≤ d') {g : (Fin n → Bool) → ℝ}
    (hg : CubeDegreeLE d g) : CubeDegreeLE d' g := by
  obtain ⟨c, hc, hrep⟩ := hg
  exact ⟨c, fun S hS => hc S (lt_of_le_of_lt h hS), hrep⟩

/-- Multiplying a cube function by a real scalar preserves an upper bound on its cube degree. -/
theorem cubeDegreeLE_smul (c : ℝ) (d : ℕ) {g : (Fin n → Bool) → ℝ} (hg : CubeDegreeLE d g) :
    CubeDegreeLE d (c • g) := by
  obtain ⟨P, hP, hPe⟩ := cube_degree_to_mv_polynomial hg
  have hdeg : (MvPolynomial.C c * P).totalDegree ≤ d := by
    have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.C c) P
    rw [MvPolynomial.totalDegree_C, Nat.zero_add] at hmul
    exact hmul.trans hP
  have h := cube_degree_of_mv_polynomial (MvPolynomial.C c * P) hdeg
  have he : (fun x : Fin n → Bool =>
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (MvPolynomial.C c * P))
      = c • g := by
    funext x
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, hPe x, Pi.smul_apply, smul_eq_mul]
  rwa [he] at h

/-- The functions on the Boolean cube that are evaluations of polynomials of total degree at most
`T`. -/
def degreeBoundSubmodule (n T : ℕ) : Submodule ℝ ((Fin n → Bool) → ℝ) where
  carrier := {g | CubeDegreeLE T g}
  zero_mem' := ⟨fun _ => (0 : ℝ), fun _ _ => rfl, fun x => by simp⟩
  add_mem' := fun {f g} hf hg => cube_degree_add hf hg
  smul_mem' := fun c {g} hg => cubeDegreeLE_smul c T hg

/-- Every function of cube degree at most `T` is a finite combination of cube monomials. -/
theorem degreeBoundSubmodule_le_span (T : ℕ) :
    degreeBoundSubmodule n T ≤
      Submodule.span ℝ ((Finset.univ.image fun S : Finset (Fin n) =>
        fun x : Fin n → Bool => ∏ i ∈ S, (if x i then (1 : ℝ) else 0)) :
          Set ((Fin n → Bool) → ℝ)) := by
  intro g hg
  obtain ⟨c, _hc, hrep⟩ := hg
  have hsum : g = ∑ S : Finset (Fin n),
      c S • (fun x : Fin n → Bool => ∏ i ∈ S, (if x i then (1 : ℝ) else 0)) := by
    funext x
    rw [hrep x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  exact Submodule.sum_mem _ fun S _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (by
      simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨S, rfl⟩))

/-- The space of functions of cube degree at most `T` is finite dimensional. -/
instance finiteDimensional_degreeBound (T : ℕ) :
    FiniteDimensional ℝ (degreeBoundSubmodule n T) :=
  Submodule.finiteDimensional_of_le (degreeBoundSubmodule_le_span T)

/-- The space of functions of cube degree at most `T` is closed in the product space of real
functions on the cube. -/
theorem isClosed_degreeBound (T : ℕ) :
    IsClosed (degreeBoundSubmodule n T : Set ((Fin n → Bool) → ℝ)) :=
  Submodule.closed_of_finiteDimensional (degreeBoundSubmodule n T)

/-- The real masses of a program are summable. -/
theorem summable_progToReal (prog : PMF (BoolQueryTree (Fin n) Bool)) :
    Summable fun t => (prog t).toReal :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

/-- The real masses of a program sum to one. -/
theorem tsum_progToReal (prog : PMF (BoolQueryTree (Fin n) Bool)) :
    ∑' t, (prog t).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun t => prog.apply_ne_top t), PMF.tsum_coe,
    ENNReal.toReal_one]

/-- The seed-averaged real acceptance of a randomized tree program. -/
noncomputable def averageAccept (prog : PMF (BoolQueryTree (Fin n) Bool))
    (x : Fin n → Bool) : ℝ :=
  ∑' t, (prog t).toReal * treeAcceptReal t x

/-- The averaged acceptance terms at one input are summable. -/
theorem summable_averageTerms (prog : PMF (BoolQueryTree (Fin n) Bool)) (x : Fin n → Bool) :
    Summable fun t => (prog t).toReal * treeAcceptReal t x :=
  Summable.of_nonneg_of_le
    (fun t => mul_nonneg ENNReal.toReal_nonneg (treeAcceptReal_nonneg t x))
    (fun t => by
      have h1 := treeAcceptReal_le_one t x
      have h2 : (0 : ℝ) ≤ (prog t).toReal := ENNReal.toReal_nonneg
      nlinarith)
    (summable_progToReal prog)

/-- The averaged acceptance is nonnegative. -/
theorem averageAccept_nonneg (prog : PMF (BoolQueryTree (Fin n) Bool)) (x : Fin n → Bool) :
    0 ≤ averageAccept prog x :=
  tsum_nonneg fun t => mul_nonneg ENNReal.toReal_nonneg (treeAcceptReal_nonneg t x)

/-- The averaged acceptance is at most one. -/
theorem averageAccept_le_one (prog : PMF (BoolQueryTree (Fin n) Bool)) (x : Fin n → Bool) :
    averageAccept prog x ≤ 1 := by
  have hle : averageAccept prog x ≤ ∑' t, (prog t).toReal :=
    Summable.tsum_le_tsum
      (fun t => by
        have h1 := treeAcceptReal_le_one t x
        have h2 : (0 : ℝ) ≤ (prog t).toReal := ENNReal.toReal_nonneg
        nlinarith)
      (summable_averageTerms prog x) (summable_progToReal prog)
  rw [tsum_progToReal] at hle
  exact hle

/-- The real success probability of a program is the seed average of the real correctness
indicators. -/
theorem successProb_toReal_eq (prog : PMF (BoolQueryTree (Fin n) Bool)) (x : Fin n → Bool)
    (b : Bool) :
    (BoolQueryTree.SuccessProb prog x (fun o => o = b)).toReal
      = ∑' t, (prog t).toReal *
          (if (BoolQueryTree.Run x t).1 = b then (1 : ℝ) else 0) := by
  unfold BoolQueryTree.SuccessProb
  rw [ENNReal.tsum_toReal_eq
    (fun t => ENNReal.mul_ne_top (prog.apply_ne_top t) (by split_ifs <;> simp))]
  apply tsum_congr
  intro t
  rw [ENNReal.toReal_mul]
  congr 1
  split_ifs <;> simp

/-- The partial-tree sums converge to the averaged acceptance in the product space of real
functions on the cube. -/
theorem tendsto_partialSums (prog : PMF (BoolQueryTree (Fin n) Bool)) :
    Filter.Tendsto (fun s : Finset (BoolQueryTree (Fin n) Bool) =>
        ∑ t ∈ s, (prog t).toReal • treeAcceptReal t)
      (Filter.atTop : Filter (Finset (BoolQueryTree (Fin n) Bool)))
      (nhds (averageAccept prog)) := by
  rw [tendsto_pi_nhds]
  intro x
  have hc : Filter.Tendsto (fun s : Finset (BoolQueryTree (Fin n) Bool) =>
      ∑ t ∈ s, (prog t).toReal * treeAcceptReal t x) Filter.atTop
      (nhds (averageAccept prog x)) :=
    (summable_averageTerms prog x).hasSum
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc

/-- A single weighted tree stays inside the space of functions of cube degree at most `T`. -/
theorem smul_mem_degreeBound {T : ℕ} (prog : PMF (BoolQueryTree (Fin n) Bool))
    (hmax : ∀ t, prog t ≠ 0 → BoolQueryTree.MaxQueries t ≤ T)
    (t : BoolQueryTree (Fin n) Bool) :
    (prog t).toReal • treeAcceptReal t ∈ degreeBoundSubmodule n T := by
  by_cases hzero : prog t = 0
  · rw [hzero, ENNReal.toReal_zero, zero_smul]
    exact (degreeBoundSubmodule n T).zero_mem
  · exact cubeDegreeLE_smul (prog t).toReal T
      (cubeDegreeLE_mono (hmax t hzero) (cubeDegreeLE_treeAcceptReal t))

/-- The seed-averaged acceptance of a program whose support is bounded by `T` has cube degree at
most `T`. -/
theorem mem_degreeBoundSubmodule_of_pmf {T : ℕ} (prog : PMF (BoolQueryTree (Fin n) Bool))
    (hmax : ∀ t, prog t ≠ 0 → BoolQueryTree.MaxQueries t ≤ T) :
    averageAccept prog ∈ degreeBoundSubmodule n T :=
  (isClosed_degreeBound (n := n) T).mem_of_tendsto
    (b := (Filter.atTop : Filter (Finset (BoolQueryTree (Fin n) Bool))))
    (tendsto_partialSums prog)
    (Filter.Eventually.of_forall fun _ =>
      Submodule.sum_mem _ fun t _ => smul_mem_degreeBound prog hmax t)

/-- The seed-averaged acceptance of a successful bounded program is within `1 / 3` of the Boolean
function it decides. -/
theorem abs_averageAccept_le_sub (prog : PMF (BoolQueryTree (Fin n) Bool))
    {f : (Fin n → Bool) → Bool}
    (hsucc : ∀ x : Fin n → Bool,
      (2 / 3 : ℝ≥0∞) ≤ BoolQueryTree.SuccessProb prog x (fun o => o = f x)) :
    ∀ x : Fin n → Bool, |averageAccept prog x - (if f x then (1 : ℝ) else 0)| ≤ 1 / 3 := by
  intro x
  have htop : BoolQueryTree.SuccessProb prog x (fun o => o = f x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_lt_top.ne ?_
    unfold BoolQueryTree.SuccessProb
    refine le_trans (ENNReal.tsum_le_tsum (fun t => ?_)) (le_of_eq (PMF.tsum_coe prog))
    split_ifs <;> simp
  have h23 : (2 / 3 : ℝ)
      ≤ (BoolQueryTree.SuccessProb prog x (fun o => o = f x)).toReal := by
    have h := ENNReal.toReal_mono htop (hsucc x)
    simpa using h
  rcases hfx : f x with _ | _
  · have hpred : (fun o : Bool => o = f x) = fun o : Bool => o = false := by rw [hfx]
    have hval : (BoolQueryTree.SuccessProb prog x (fun o => o = f x)).toReal
        = 1 - averageAccept prog x := by
      rw [hpred, successProb_toReal_eq prog x false]
      calc ∑' t, (prog t).toReal *
            (if (BoolQueryTree.Run x t).1 = false then (1 : ℝ) else 0)
          = ∑' t, ((prog t).toReal - (prog t).toReal * treeAcceptReal t x) :=
            tsum_congr fun t => by
              rw [indicator_false_eq_one_sub]
              ring
        _ = (∑' t, (prog t).toReal) - ∑' t, (prog t).toReal * treeAcceptReal t x :=
            Summable.tsum_sub (summable_progToReal prog) (summable_averageTerms prog x)
        _ = 1 - averageAccept prog x := by rw [tsum_progToReal]; rfl
    rw [hval] at h23
    have hle : averageAccept prog x ≤ 1 / 3 := by linarith
    have hgoal : averageAccept prog x - (if false = true then (1 : ℝ) else 0)
        = averageAccept prog x := by norm_num
    rw [hgoal, abs_of_nonneg (averageAccept_nonneg prog x)]
    exact hle
  · have hpred : (fun o : Bool => o = f x) = fun o : Bool => o = true := by rw [hfx]
    have hval : (BoolQueryTree.SuccessProb prog x (fun o => o = f x)).toReal
        = averageAccept prog x := by
      rw [hpred, successProb_toReal_eq prog x true]
      simp only [averageAccept]
      apply tsum_congr
      intro t
      rw [indicator_true_eq]
    rw [hval] at h23
    have hle : averageAccept prog x ≤ 1 := averageAccept_le_one prog x
    have hgoal : averageAccept prog x - (if true = true then (1 : ℝ) else 0)
        = averageAccept prog x - 1 := by norm_num
    rw [hgoal, abs_of_nonpos (by linarith)]
    linarith

/-- The approximate degree of a Boolean function is the infimum of the total degrees of its
one-third approximating polynomials. -/
theorem approxDegree_def (f : (Fin n → Bool) → Bool) :
    approxDegree f = sInf ((fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) ''
      {p | ∀ g : Fin n → Bool, |boolEval p g - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3}) := rfl

/-- Proposition 20: a randomized decision tree of depth at most `T` that decides `f` with
probability at least `2 / 3` on every input gives `approxDegree f ≤ T`. -/
theorem approxDegree_le_of_boundedSuccess (f : (Fin n → Bool) → Bool)
    (prog : PMF (BoolQueryTree (Fin n) Bool)) (T : ℕ)
    (hsucc : ∀ x : Fin n → Bool,
      (2 / 3 : ℝ≥0∞) ≤ BoolQueryTree.SuccessProb prog x (fun o => o = f x))
    (hmax : ∀ t ∈ prog.support, BoolQueryTree.MaxQueries t ≤ T) :
    approxDegree f ≤ T := by
  have hmax' : ∀ t, prog t ≠ 0 → BoolQueryTree.MaxQueries t ≤ T :=
    fun t ht => hmax t ((PMF.mem_support_iff prog t).mpr ht)
  have hmem := mem_degreeBoundSubmodule_of_pmf prog hmax'
  obtain ⟨P, hP, hPe⟩ := cube_degree_to_mv_polynomial hmem
  have hle : approxDegree f ≤ P.totalDegree := by
    rw [approxDegree_def]
    refine Nat.sInf_le ⟨P, fun x => ?_, rfl⟩
    have hx := abs_averageAccept_le_sub prog hsucc x
    have heq : boolEval P x = averageAccept prog x := hPe x
    rwa [← heq] at hx
  exact hle.trans hP

end Qatlib.Papers.QQueryIntro25.MainResults.RandomizedTreeApproxDegree
