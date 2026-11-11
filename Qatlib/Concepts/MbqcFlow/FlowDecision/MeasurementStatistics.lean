/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatistics
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatisticsDefs

/-!
# Variance bounds for measurement U-statistics

Defines the kernel variance `kernelVarianceK` and the covariance `overlapCovarianceK` of two
coordinate selections from an independent sample. It proves an exact overlap expansion for the
variance of `povmUStatisticK`, a combinatorial variance bound, and a Chebyshev deviation bound.

The results specialize to repeated finite POVM measurements through `frontier1_povm`. The
measurement setting is described in [Watrous2018].

## Main statements

* `uStatistic_variance_overlap`: variance as a normalized sum of overlap covariances.
* `overlapCovarianceK_disjoint`: disjoint injective selections have zero covariance.
* `probEvent_uStatistic_le`: deviation bound from the kernel variance and overlap count.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatistics
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {O : Type} [Fintype O] [DecidableEq O]

/-- The product expectation of the kernel evaluated on the coordinate selections `t` and `s` of
an independent sample from `p`. -/
def overlapExpectK (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) : ℝ :=
  ∑ ω : Fin n → O, p.probOf ω * h (fun i => ω (t i)) * h (fun i => ω (s i))

/-- The variance of a real kernel on `k` independent outcomes drawn from `p`. -/
noncomputable def kernelVarianceK {k : ℕ} (p : FinDist O) (h : (Fin k → O) → ℝ) : ℝ :=
  ∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * (h y - kernelMeanK p h) ^ 2

/-- The product expectation for two coordinate selections minus the square of the independent
kernel mean. -/
noncomputable def overlapCovarianceK (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) : ℝ :=
  overlapExpectK p h t s - kernelMeanK p h ^ 2

/-- The combinatorial bound `k * k * n ^ (k - 1)` used to count coordinate selections
overlapping a fixed selection. -/
def overlapDegreeBound (n k : ℕ) : ℕ := k * k * n ^ (k - 1)

/-- The probabilities of all length-`n` independent sample tables sum to one. -/
theorem probOf_sum_one (p : FinDist O) (n : ℕ) :
    ∑ ω : Fin n → O, p.probOf ω = 1 := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf p n

/-- Every independent sample table has nonnegative probability. -/
theorem probOf_nonneg (p : FinDist O) {n : ℕ} (ω : Fin n → O) :
    0 ≤ p.probOf ω := Finset.prod_nonneg fun i _ => p.nonneg _

/-- Reading distinct coordinates from an independent sample preserves the kernel mean. -/
theorem read_expect (p : FinDist O) {n k : ℕ} (idx : Fin k → Fin n)
    (hidx : Function.Injective idx) (h : (Fin k → O) → ℝ) :
    ∑ ω : Fin n → O, p.probOf ω * h (fun i => ω (idx i)) = kernelMeanK p h :=
  povm_joint_expect p idx hidx h

/-- Reading distinct coordinates from an independent sample preserves the kernel variance. -/
theorem read_variance (p : FinDist O) {n k : ℕ} (idx : Fin k → Fin n)
    (hidx : Function.Injective idx) (h : (Fin k → O) → ℝ) :
    ∑ ω : Fin n → O, p.probOf ω * (h (fun i => ω (idx i)) - kernelMeanK p h) ^ 2
      = kernelVarianceK p h :=
  povm_joint_expect p idx hidx (fun y => (h y - kernelMeanK p h) ^ 2)

/-- The independent kernel variance is nonnegative. -/
theorem kernelVarianceK_nonneg {k : ℕ} (p : FinDist O) (h : (Fin k → O) → ℝ) :
    0 ≤ kernelVarianceK p h := by
  refine Finset.sum_nonneg fun y _ => ?_
  exact mul_nonneg (Finset.prod_nonneg fun i _ => p.nonneg _) (sq_nonneg _)

/-- For injective coordinate selections, the overlap covariance equals the expectation of the
product of the centered kernel values. -/
theorem overlapCovarianceK_eq (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) (ht : Function.Injective t) (hs : Function.Injective s) :
    overlapCovarianceK p h t s
      = ∑ ω : Fin n → O, p.probOf ω
          * (h (fun i => ω (t i)) - kernelMeanK p h)
          * (h (fun i => ω (s i)) - kernelMeanK p h) := by
  have h1 := read_expect p t ht h
  have h2 := read_expect p s hs h
  have h3 : ∑ ω : Fin n → O, p.probOf ω = 1 := probOf_sum_one p n
  have hrhs : ∑ ω : Fin n → O, p.probOf ω
          * (h (fun i => ω (t i)) - kernelMeanK p h)
          * (h (fun i => ω (s i)) - kernelMeanK p h)
      = (∑ ω : Fin n → O, p.probOf ω * h (fun i => ω (t i)) * h (fun i => ω (s i)))
        - kernelMeanK p h * (∑ ω : Fin n → O, p.probOf ω * h (fun i => ω (t i)))
        - kernelMeanK p h * (∑ ω : Fin n → O, p.probOf ω * h (fun i => ω (s i)))
        + kernelMeanK p h ^ 2 * (∑ ω : Fin n → O, p.probOf ω) := by
    have key : ∀ ω : Fin n → O,
        p.probOf ω * (h (fun i => ω (t i)) - kernelMeanK p h)
            * (h (fun i => ω (s i)) - kernelMeanK p h)
        = p.probOf ω * h (fun i => ω (t i)) * h (fun i => ω (s i))
          - kernelMeanK p h * (p.probOf ω * h (fun i => ω (t i)))
          - kernelMeanK p h * (p.probOf ω * h (fun i => ω (s i)))
          + kernelMeanK p h ^ 2 * p.probOf ω := fun ω => by ring
    simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  unfold overlapCovarianceK overlapExpectK
  rw [hrhs, h1, h2, h3]
  ring

/-- The equivalence of outcome tables obtained by precomposing with the inverse coordinate
permutation. -/
def precompEquiv {n : ℕ} (σ : Fin n ≃ Fin n) : (Fin n → O) ≃ (Fin n → O) where
  toFun ω := fun x => ω (σ.symm x)
  invFun ω := fun x => ω (σ x)
  left_inv ω := by funext x; simp
  right_inv ω := by funext x; simp

/-- A common permutation of both coordinate selections preserves their product expectation. -/
theorem overlapExpectK_transport (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (σ : Fin n ≃ Fin n) (t t' s s' : Fin k → Fin n)
    (ht : ∀ i, t' i = σ (t i)) (hs : ∀ i, s' i = σ (s i)) :
    overlapExpectK p h t s = overlapExpectK p h t' s' := by
  have ht' : ∀ i, σ.symm (t' i) = t i := fun i => by rw [ht i]; simp
  have hs' : ∀ i, σ.symm (s' i) = s i := fun i => by rw [hs i]; simp
  have hcoe : ∀ ω : Fin n → O, precompEquiv σ ω = fun x => ω (σ.symm x) := fun _ => rfl
  unfold overlapExpectK
  have hgo : ∀ ω : Fin n → O,
      p.probOf ω * h (fun i => ω (t i)) * h (fun i => ω (s i))
        = p.probOf (precompEquiv σ ω) * h (fun i => precompEquiv σ ω (t' i))
            * h (fun i => precompEquiv σ ω (s' i)) := by
    intro ω
    have hp : p.probOf (precompEquiv σ ω) = p.probOf ω := by
      rw [hcoe ω]
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf
      exact Equiv.prod_comp σ.symm (fun y => p.prob (ω y))
    rw [hp, hcoe ω]
    have hbeta : (fun i => (fun x => ω (σ.symm x)) (t' i)) = (fun i => ω (t i)) := by
      funext i
      simp only []
      rw [ht' i]
    have hbeta' : (fun i => (fun x => ω (σ.symm x)) (s' i)) = (fun i => ω (s i)) := by
      funext i
      simp only []
      rw [hs' i]
    simp only [hbeta, hbeta']
  exact Fintype.sum_equiv (precompEquiv σ)
    (fun ω => p.probOf ω * h (fun i => ω (t i)) * h (fun i => ω (s i)))
    (fun ω => p.probOf ω * h (fun i => ω (t' i)) * h (fun i => ω (s' i))) hgo

/-- A common permutation of both coordinate selections preserves their overlap covariance. -/
theorem overlapCovarianceK_transport (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (σ : Fin n ≃ Fin n) (t t' s s' : Fin k → Fin n)
    (ht : ∀ i, t' i = σ (t i)) (hs : ∀ i, s' i = σ (s i)) :
    overlapCovarianceK p h t s = overlapCovarianceK p h t' s' := by
  unfold overlapCovarianceK
  rw [overlapExpectK_transport p h σ t t' s s' ht hs]

/-- The overlap covariance of an injective selection with itself equals the kernel variance. -/
theorem overlapCovarianceK_self (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t : Fin k → Fin n) (ht : Function.Injective t) :
    overlapCovarianceK p h t t = kernelVarianceK p h := by
  have h1 : overlapExpectK p h t t
      = ∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * (h y * h y) := by
    have hassoc : ∀ ω : Fin n → O,
        p.probOf ω * h (fun i => ω (t i)) * h (fun i => ω (t i))
          = p.probOf ω * (h (fun i => ω (t i)) * h (fun i => ω (t i))) :=
      fun ω => mul_assoc _ _ _
    unfold overlapExpectK
    rw [Finset.sum_congr rfl fun ω _ => hassoc ω,
      povm_joint_expect p t ht (fun y => h y * h y)]
  have h2 : ∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * h y = kernelMeanK p h := rfl
  have h3 : ∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) = 1 := by
    simpa [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf] using
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf p k
  have hrhs : kernelVarianceK p h
      = (∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * (h y * h y))
        - kernelMeanK p h * (∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * h y)
        - kernelMeanK p h * (∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * h y)
        + kernelMeanK p h ^ 2 * (∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i))) := by
    have key : ∀ y : Fin k → O,
        (∏ i : Fin k, p.prob (y i)) * (h y - kernelMeanK p h) ^ 2
        = (∏ i : Fin k, p.prob (y i)) * (h y * h y)
          - kernelMeanK p h * ((∏ i : Fin k, p.prob (y i)) * h y)
          - kernelMeanK p h * ((∏ i : Fin k, p.prob (y i)) * h y)
          + kernelMeanK p h ^ 2 * (∏ i : Fin k, p.prob (y i)) := fun y => by ring
    unfold kernelVarianceK
    simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  calc overlapCovarianceK p h t t
      = overlapExpectK p h t t - kernelMeanK p h ^ 2 := rfl
    _ = ∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * (h y * h y)
          - kernelMeanK p h ^ 2 := by rw [h1]
    _ = kernelVarianceK p h := by rw [hrhs, h2, h3]; ring

/-- Reindexes an outcome table of length `k + k` by the sum of two copies of `Fin k`. -/
def readSumEquiv {k : ℕ} : (Fin (k + k) → O) ≃ ((Fin k ⊕ Fin k) → O) where
  toFun z := fun c => z (finSumFinEquiv c)
  invFun w := fun x => w (finSumFinEquiv.symm x)
  left_inv z := by funext x; simp
  right_inv w := by funext c; simp

/-- Splits a table indexed by `Fin k ⊕ Fin k` into its two component tables. -/
def sumTableEquiv {k : ℕ} : ((Fin k ⊕ Fin k) → O) ≃ ((Fin k → O) × (Fin k → O)) where
  toFun w := (fun i => w (Sum.inl i), fun i => w (Sum.inr i))
  invFun pr := Sum.elim pr.1 pr.2
  left_inv w := by funext c; rcases c with i | i <;> rfl
  right_inv pr := by
    rcases pr with ⟨a, b⟩
    rfl

/-- Disjoint injective coordinate selections have zero overlap covariance. -/
theorem overlapCovarianceK_disjoint (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) (ht : Function.Injective t) (hs : Function.Injective s)
    (hdis : ∀ i j : Fin k, t i ≠ s j) :
    overlapCovarianceK p h t s = 0 := by
  classical
  obtain ⟨u, hu⟩ : ∃ u : Fin (k + k) → Fin n,
      u = fun x => Sum.elim t s (finSumFinEquiv.symm x) := ⟨_, rfl⟩
  have hut : ∀ i : Fin k, u (Fin.castAdd k i) = t i := by
    intro i
    rw [hu]
    exact congrArg (Sum.elim t s) (finSumFinEquiv_symm_apply_castAdd i)
  have hus : ∀ i : Fin k, u (Fin.natAdd k i) = s i := by
    intro i
    rw [hu]
    exact congrArg (Sum.elim t s) (finSumFinEquiv_symm_apply_natAdd i)
  have hui : Function.Injective u := by
    intro a b hab
    have ha : u a = Sum.elim t s (finSumFinEquiv.symm a) := by rw [hu]
    have hb : u b = Sum.elim t s (finSumFinEquiv.symm b) := by rw [hu]
    rw [ha, hb] at hab
    rcases hc : finSumFinEquiv.symm a with ia | ib <;>
      rcases hc' : finSumFinEquiv.symm b with ja | jb <;>
      rw [hc, hc'] at hab <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · exact finSumFinEquiv.symm.injective
        (hc.trans ((congrArg Sum.inl (ht hab)).trans hc'.symm))
    · exact absurd hab (hdis ia jb)
    · exact absurd hab.symm (hdis ja ib)
    · exact finSumFinEquiv.symm.injective
        (hc.trans ((congrArg Sum.inr (hs hab)).trans hc'.symm))

  have hjoint : overlapExpectK p h t s
      = ∑ z : Fin (k + k) → O, (∏ x : Fin (k + k), p.prob (z x))
          * (h (fun i => z (Fin.castAdd k i)) * h (fun i => z (Fin.natAdd k i))) := by
    have he1 : ∀ ω : Fin n → O,
        (fun i => ω (u (Fin.castAdd k i))) = (fun i => ω (t i)) := by
      intro ω
      funext i
      rw [hut i]
    have he2 : ∀ ω : Fin n → O,
        (fun i => ω (u (Fin.natAdd k i))) = (fun i => ω (s i)) := by
      intro ω
      funext i
      rw [hus i]
    have hsub : ∀ ω : Fin n → O,
        p.probOf ω * h (fun i => ω (t i)) * h (fun i => ω (s i))
          = p.probOf ω * (h (fun i => ω (u (Fin.castAdd k i)))
              * h (fun i => ω (u (Fin.natAdd k i)))) := by
      intro ω
      rw [he1 ω, he2 ω]
      ring
    unfold overlapExpectK
    rw [Finset.sum_congr rfl fun ω _ => hsub ω]
    exact povm_joint_expect p u hui
      (fun z => h (fun i => z (Fin.castAdd k i)) * h (fun i => z (Fin.natAdd k i)))

  have hsplit : ∑ z : Fin (k + k) → O, (∏ x : Fin (k + k), p.prob (z x))
      * (h (fun i => z (Fin.castAdd k i)) * h (fun i => z (Fin.natAdd k i)))
      = (∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * h y)
        * (∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * h y) := by
    have hcoe : ∀ (z : Fin (k + k) → O) (c : Fin k ⊕ Fin k),
        readSumEquiv z c = z (finSumFinEquiv c) := fun _ _ => rfl
    have hgo : ∀ z : Fin (k + k) → O,
        (∏ x : Fin (k + k), p.prob (z x))
          * (h (fun i => z (Fin.castAdd k i)) * h (fun i => z (Fin.natAdd k i)))
        = (∏ c : Fin k ⊕ Fin k, p.prob (readSumEquiv z c))
            * (h (fun i => readSumEquiv z (Sum.inl i))
              * h (fun i => readSumEquiv z (Sum.inr i))) := by
      intro z
      have hprod : (∏ c : Fin k ⊕ Fin k, p.prob (readSumEquiv z c))
          = ∏ x : Fin (k + k), p.prob (z x) := by
        simp only [hcoe z]
        exact Equiv.prod_comp finSumFinEquiv (fun x => p.prob (z x))
      rw [hprod]
      have h1 : (fun i => readSumEquiv z (Sum.inl i))
          = (fun i => z (Fin.castAdd k i)) := funext fun i => rfl
      have h2 : (fun i => readSumEquiv z (Sum.inr i))
          = (fun i => z (Fin.natAdd k i)) := funext fun i => rfl
      rw [h1, h2]

    have hstep1 : ∑ z : Fin (k + k) → O, (∏ x : Fin (k + k), p.prob (z x))
        * (h (fun i => z (Fin.castAdd k i)) * h (fun i => z (Fin.natAdd k i)))
      = ∑ w : (Fin k ⊕ Fin k) → O, (∏ c : Fin k ⊕ Fin k, p.prob (w c))
          * (h (fun i => w (Sum.inl i)) * h (fun i => w (Sum.inr i))) :=
      Fintype.sum_equiv readSumEquiv
        (fun z => (∏ x : Fin (k + k), p.prob (z x))
          * (h (fun i => z (Fin.castAdd k i)) * h (fun i => z (Fin.natAdd k i))))
        (fun w => (∏ c : Fin k ⊕ Fin k, p.prob (w c))
          * (h (fun i => w (Sum.inl i)) * h (fun i => w (Sum.inr i)))) hgo
    rw [hstep1]
    have hprodSplit : ∀ w : (Fin k ⊕ Fin k) → O,
        (∏ c : Fin k ⊕ Fin k, p.prob (w c))
          = (∏ i : Fin k, p.prob (w (Sum.inl i))) * (∏ i : Fin k, p.prob (w (Sum.inr i))) :=
      fun w => Fintype.prod_sum_type _
    rw [Finset.sum_congr rfl fun w _ => by rw [hprodSplit w]]

    have hstep2 : ∑ w : (Fin k ⊕ Fin k) → O,
        ((∏ i : Fin k, p.prob (w (Sum.inl i))) * ∏ i : Fin k, p.prob (w (Sum.inr i)))
          * (h (fun i => w (Sum.inl i)) * h (fun i => w (Sum.inr i)))
      = ∑ pr : (Fin k → O) × (Fin k → O),
          ((∏ i : Fin k, p.prob (pr.1 i)) * ∏ i : Fin k, p.prob (pr.2 i))
            * (h pr.1 * h pr.2) :=
      Fintype.sum_equiv (sumTableEquiv (O := O))
        (fun w => ((∏ i : Fin k, p.prob (w (Sum.inl i))) * ∏ i : Fin k, p.prob (w (Sum.inr i)))
          * (h (fun i => w (Sum.inl i)) * h (fun i => w (Sum.inr i))))
        (fun pr => ((∏ i : Fin k, p.prob (pr.1 i)) * ∏ i : Fin k, p.prob (pr.2 i))
          * (h pr.1 * h pr.2))
        (fun w => rfl)
    rw [hstep2, Fintype.sum_prod_type]
    have hre : ∀ a : Fin k → O, ∀ b : Fin k → O,
        ((∏ i : Fin k, p.prob (a i)) * ∏ i : Fin k, p.prob (b i)) * (h a * h b)
          = ((∏ i : Fin k, p.prob (a i)) * h a) * ((∏ i : Fin k, p.prob (b i)) * h b) :=
      fun a b => by ring
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hre a b]
    rw [← Finset.sum_mul_sum]
  calc overlapCovarianceK p h t s
      = overlapExpectK p h t s - kernelMeanK p h ^ 2 := rfl
    _ = (∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * h y)
          * (∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * h y)
          - kernelMeanK p h ^ 2 := by rw [hjoint, hsplit]
    _ = 0 := by
          unfold kernelMeanK
          ring

/-- The expectation of the average of two squared centered kernel values equals the average of
their kernel variances. -/
theorem centered_half_sum (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) (ht : Function.Injective t) (hs : Function.Injective s) :
    (∑ ω : Fin n → O, p.probOf ω * (((h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
          + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2) / 2))
      = (kernelVarianceK p h + kernelVarianceK p h) / 2 := by
  have hVt := read_variance p t ht h
  have hVs := read_variance p s hs h
  have hmul : ∀ ω : Fin n → O,
      p.probOf ω * (((h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
            + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2) / 2)
        = (p.probOf ω * ((h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
            + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2)) / 2 := fun ω => by ring
  have hadd : ∀ ω : Fin n → O,
      p.probOf ω * ((h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
            + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2)
        = p.probOf ω * (h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
            + p.probOf ω * (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2 := fun ω => by ring
  rw [Finset.sum_congr rfl fun ω _ => hmul ω, ← Finset.sum_div,
    Finset.sum_congr rfl fun ω _ => hadd ω, Finset.sum_add_distrib, hVt, hVs]

/-- For injective selections, the overlap covariance is at most the kernel variance. -/
theorem overlapCovarianceK_le (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) (ht : Function.Injective t) (hs : Function.Injective s) :
    overlapCovarianceK p h t s ≤ kernelVarianceK p h := by
  rw [overlapCovarianceK_eq p h t s ht hs]
  have hpoint : ∀ ω : Fin n → O,
      p.probOf ω * (h (fun i => ω (t i)) - kernelMeanK p h)
          * (h (fun i => ω (s i)) - kernelMeanK p h)
        ≤ p.probOf ω * (((h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
            + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2) / 2) := by
    intro ω
    have h2 : 0 ≤ p.probOf ω := probOf_nonneg p ω
    have hkey : 2 * ((h (fun i => ω (t i)) - kernelMeanK p h)
          * (h (fun i => ω (s i)) - kernelMeanK p h))
        ≤ (h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
          + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2 := by
      nlinarith [sq_nonneg (h (fun i => ω (t i)) - kernelMeanK p h
          - (h (fun i => ω (s i)) - kernelMeanK p h))]
    nlinarith
  have hhalf : (kernelVarianceK p h + kernelVarianceK p h) / 2 = kernelVarianceK p h := by ring
  rw [← hhalf]
  exact le_trans (Finset.sum_le_sum fun ω _ => hpoint ω)
    (le_of_eq (centered_half_sum p h t s ht hs))

/-- For injective selections, the overlap covariance is at least the negative kernel variance. -/
theorem neg_overlapCovarianceK_le (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) (ht : Function.Injective t) (hs : Function.Injective s) :
    -kernelVarianceK p h ≤ overlapCovarianceK p h t s := by
  rw [overlapCovarianceK_eq p h t s ht hs]
  have hpoint : ∀ ω : Fin n → O,
      p.probOf ω * (-(h (fun i => ω (t i)) - kernelMeanK p h)
          * (h (fun i => ω (s i)) - kernelMeanK p h))
        ≤ p.probOf ω * (((h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
            + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2) / 2) := by
    intro ω
    have h2 : 0 ≤ p.probOf ω := probOf_nonneg p ω
    have hkey : 2 * (-(h (fun i => ω (t i)) - kernelMeanK p h)
          * (h (fun i => ω (s i)) - kernelMeanK p h))
        ≤ (h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
          + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2 := by
      nlinarith [sq_nonneg (h (fun i => ω (t i)) - kernelMeanK p h
          + (h (fun i => ω (s i)) - kernelMeanK p h))]
    nlinarith
  have hsumneg : ∑ ω : Fin n → O,
      p.probOf ω * (-(h (fun i => ω (t i)) - kernelMeanK p h)
        * (h (fun i => ω (s i)) - kernelMeanK p h))
      = -∑ ω : Fin n → O, p.probOf ω
          * (h (fun i => ω (t i)) - kernelMeanK p h)
          * (h (fun i => ω (s i)) - kernelMeanK p h) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  have hsum : (∑ ω : Fin n → O, p.probOf ω * (-(h (fun i => ω (t i)) - kernelMeanK p h)
        * (h (fun i => ω (s i)) - kernelMeanK p h)))
      ≤ (∑ ω : Fin n → O, p.probOf ω * (((h (fun i => ω (t i)) - kernelMeanK p h) ^ 2
          + (h (fun i => ω (s i)) - kernelMeanK p h) ^ 2) / 2)) :=
    Finset.sum_le_sum fun ω _ => hpoint ω
  rw [hsumneg] at hsum
  have hhalf : (kernelVarianceK p h + kernelVarianceK p h) / 2 = kernelVarianceK p h := by ring
  rw [centered_half_sum p h t s ht hs, hhalf] at hsum
  exact neg_le.mp hsum

/-- For injective selections, the absolute overlap covariance is bounded by the kernel variance. -/
theorem overlapCovarianceK_abs_le (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) (ht : Function.Injective t) (hs : Function.Injective s) :
    |overlapCovarianceK p h t s| ≤ kernelVarianceK p h :=
  abs_le.mpr ⟨neg_overlapCovarianceK_le p h t s ht hs,
    overlapCovarianceK_le p h t s ht hs⟩

/-- Summing a constant over injective coordinate selections multiplies it by `distinctTupleCount
n k`. -/
theorem sum_injective_const {n k : ℕ} (c : ℝ) :
    ∑ t : Fin k → Fin n, (if Function.Injective t then c else 0)
      = ((distinctTupleCount n k : ℕ) : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- When `distinctTupleCount n k` is nonzero, the U-statistic variance equals the sum of all
injective overlap covariances divided by the square of that count. -/
theorem uStatistic_variance_overlap (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (hN : (distinctTupleCount n k : ℕ) ≠ 0) :
    ∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ 2
      = (∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
          (if Function.Injective t ∧ Function.Injective s then
            overlapCovarianceK p h t s else 0))
        / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2 := by
  classical
  have hC : ((distinctTupleCount n k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN

  have hS2 : ∑ ω : Fin n → O, p.probOf ω
        * ((∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0))
            * (∑ s : Fin k → Fin n, (if Function.Injective s then h (fun i => ω (s i)) else 0)))
      = ∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
          (if Function.Injective t ∧ Function.Injective s then
            overlapExpectK p h t s else 0) := by
    have hmul : ∀ ω : Fin n → O,
        (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0))
            * (∑ s : Fin k → Fin n, (if Function.Injective s then h (fun i => ω (s i)) else 0))
        = ∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
            (if Function.Injective t ∧ Function.Injective s then
              h (fun i => ω (t i)) * h (fun i => ω (s i)) else 0) := by
      intro ω
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
      by_cases hts : Function.Injective t ∧ Function.Injective s
      · rw [if_pos hts, if_pos (hts.1), if_pos (hts.2)]
      · rw [if_neg hts]
        by_cases ht : Function.Injective t
        · rw [if_pos ht, if_neg (fun hc => hts ⟨ht, hc⟩)]
          ring
        · rw [if_neg ht]
          ring
    calc ∑ ω : Fin n → O, p.probOf ω
          * ((∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0))
            * (∑ s : Fin k → Fin n, (if Function.Injective s then h (fun i => ω (s i)) else 0)))
        = ∑ ω : Fin n → O, ∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
            p.probOf ω
              * (if Function.Injective t ∧ Function.Injective s then
                  h (fun i => ω (t i)) * h (fun i => ω (s i)) else 0) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [hmul ω, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
            ∑ ω : Fin n → O, p.probOf ω
              * (if Function.Injective t ∧ Function.Injective s then
                  h (fun i => ω (t i)) * h (fun i => ω (s i)) else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
            (if Function.Injective t ∧ Function.Injective s then
              overlapExpectK p h t s else 0) := by
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
          by_cases hts : Function.Injective t ∧ Function.Injective s
          · simp only [hts, and_true, if_true]
            unfold overlapExpectK
            exact Finset.sum_congr rfl fun ω _ => (mul_assoc _ _ _).symm
          · rw [if_neg hts]
            exact Finset.sum_eq_zero fun ω _ => by
              simp only [if_neg hts]
              ring
  have hSexp : ∑ ω : Fin n → O, p.probOf ω
        * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0))
      = ((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h :=
    povmUStatisticK_unbiased_scaled p h
  have hmass : ∑ ω : Fin n → O, p.probOf ω = 1 := probOf_sum_one p n

  have hterm : ∀ ω : Fin n → O,
      p.probOf ω * ((∑ t : Fin k → Fin n,
            (if Function.Injective t then h (fun i => ω (t i)) else 0))
          / ((distinctTupleCount n k : ℕ) : ℝ) - kernelMeanK p h) ^ 2
      = p.probOf ω * ((∑ t : Fin k → Fin n,
            (if Function.Injective t then h (fun i => ω (t i)) else 0))
            * (∑ s : Fin k → Fin n,
              (if Function.Injective s then h (fun i => ω (s i)) else 0)))
          / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2
        - 2 * kernelMeanK p h * (p.probOf ω
            * (∑ t : Fin k → Fin n,
              (if Function.Injective t then h (fun i => ω (t i)) else 0)))
          / ((distinctTupleCount n k : ℕ) : ℝ)
        + kernelMeanK p h ^ 2 * p.probOf ω := by
    intro ω
    field_simp
    ring
  have hsumA : ∑ ω : Fin n → O,
      (p.probOf ω * ((∑ t : Fin k → Fin n,
            (if Function.Injective t then h (fun i => ω (t i)) else 0))
            * (∑ s : Fin k → Fin n,
              (if Function.Injective s then h (fun i => ω (s i)) else 0))))
        / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2
      = (∑ ω : Fin n → O, p.probOf ω
          * ((∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0))
            * (∑ s : Fin k → Fin n,
              (if Function.Injective s then h (fun i => ω (s i)) else 0))))
        / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2 :=
    (Finset.sum_div Finset.univ
      (fun ω : Fin n → O => p.probOf ω
        * ((∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0))
          * (∑ s : Fin k → Fin n,
            (if Function.Injective s then h (fun i => ω (s i)) else 0))))
      (((distinctTupleCount n k : ℕ) : ℝ) ^ 2)).symm
  have hsumB : ∑ ω : Fin n → O,
      2 * kernelMeanK p h * (p.probOf ω
          * (∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0)))
        / ((distinctTupleCount n k : ℕ) : ℝ)
      = 2 * kernelMeanK p h * (((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h)
          / ((distinctTupleCount n k : ℕ) : ℝ) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, hSexp]
  have hsumC : ∑ ω : Fin n → O, kernelMeanK p h ^ 2 * p.probOf ω
      = kernelMeanK p h ^ 2 * 1 := by
    rw [← Finset.mul_sum, hmass]

  have hcount : ∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
      (if Function.Injective t ∧ Function.Injective s then kernelMeanK p h ^ 2 else 0)
      = ((distinctTupleCount n k : ℕ) : ℝ) ^ 2 * kernelMeanK p h ^ 2 := by
    have hsplit : ∀ t s : Fin k → Fin n,
        (if Function.Injective t ∧ Function.Injective s then kernelMeanK p h ^ 2 else 0)
        = (if Function.Injective t then
            (if Function.Injective s then kernelMeanK p h ^ 2 else 0) else 0) := by
      intro t s
      by_cases hts : Function.Injective t ∧ Function.Injective s
      · rw [if_pos hts, if_pos (hts.1), if_pos (hts.2)]
      · rw [if_neg hts]
        by_cases ht : Function.Injective t
        · rw [if_pos ht, if_neg (fun hc => hts ⟨ht, hc⟩)]
        · rw [if_neg ht]
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => hsplit t s]
    have hinner : ∀ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
        (if Function.Injective t then
          (if Function.Injective s then kernelMeanK p h ^ 2 else 0) else 0)
      = (if Function.Injective t then
          ((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h ^ 2 else 0) := by
      intro t
      by_cases ht : Function.Injective t
      · simp only [ht, if_true]
        exact sum_injective_const _
      · simp [ht]
    rw [Finset.sum_congr rfl fun t _ => hinner t, sum_injective_const]
    ring
  have htermwise : ∀ t s : Fin k → Fin n,
      (if Function.Injective t ∧ Function.Injective s then
        overlapCovarianceK p h t s else 0)
      = (if Function.Injective t ∧ Function.Injective s then
          overlapExpectK p h t s else 0)
        - (if Function.Injective t ∧ Function.Injective s then
          kernelMeanK p h ^ 2 else 0) := by
    intro t s
    by_cases hts : Function.Injective t ∧ Function.Injective s
    · rw [if_pos hts, if_pos hts, if_pos hts]
      unfold overlapCovarianceK
      ring
    · rw [if_neg hts, if_neg hts, if_neg hts]
      ring
  have hsub : (∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
      (if Function.Injective t ∧ Function.Injective s then
        overlapCovarianceK p h t s else 0))
      = (∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
          (if Function.Injective t ∧ Function.Injective s then
            overlapExpectK p h t s else 0))
        - ((distinctTupleCount n k : ℕ) : ℝ) ^ 2 * kernelMeanK p h ^ 2 := by
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => htermwise t s]
    simp only [Finset.sum_sub_distrib]
    rw [hcount]

  simp only [povmUStatisticK]
  calc ∑ ω : Fin n → O, p.probOf ω
          * ((∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0))
            / ((distinctTupleCount n k : ℕ) : ℝ) - kernelMeanK p h) ^ 2
      = ∑ ω : Fin n → O,
          ((p.probOf ω * ((∑ t : Fin k → Fin n,
              (if Function.Injective t then h (fun i => ω (t i)) else 0))
            * (∑ s : Fin k → Fin n,
              (if Function.Injective s then h (fun i => ω (s i)) else 0))))
            / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2
        - 2 * kernelMeanK p h * (p.probOf ω
            * (∑ t : Fin k → Fin n,
              (if Function.Injective t then h (fun i => ω (t i)) else 0)))
          / ((distinctTupleCount n k : ℕ) : ℝ)
        + kernelMeanK p h ^ 2 * p.probOf ω) := by
          exact Finset.sum_congr rfl fun ω _ => hterm ω
    _ = ((∑ ω : Fin n → O, p.probOf ω
            * ((∑ t : Fin k → Fin n, (if Function.Injective t then h (fun i => ω (t i)) else 0))
              * (∑ s : Fin k → Fin n,
                (if Function.Injective s then h (fun i => ω (s i)) else 0))))
          / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2)
        - 2 * kernelMeanK p h
            * (((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h)
          / ((distinctTupleCount n k : ℕ) : ℝ)
        + kernelMeanK p h ^ 2 * 1 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [hsumA, hsumB, hsumC]
    _ = ((∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
            (if Function.Injective t ∧ Function.Injective s then
              overlapExpectK p h t s else 0)))
          / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2
        - kernelMeanK p h ^ 2 := by
          rw [hS2]
          field_simp [hC]
          ring
    _ = ((∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
            (if Function.Injective t ∧ Function.Injective s then
              overlapCovarianceK p h t s else 0)))
          / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2 := by
          rw [hsub]
          field_simp [hC]

/-- Extends a table on the coordinates other than `i` by assigning the value `j` at `i`. -/
def coordFiberTable {k n : ℕ} (i : Fin k) (j : Fin n)
    (g : ∀ x : {x : Fin k // x ≠ i}, Fin n) : Fin k → Fin n :=
  fun x => if hx : x = i then j else g ⟨x, hx⟩

/-- Identifies tables with prescribed value `j` at coordinate `i` with tables on the remaining
coordinates. -/
def coordFiberEquiv {k n : ℕ} (i : Fin k) (j : Fin n) :
    {s : Fin k → Fin n // s i = j} ≃ (∀ x : {x : Fin k // x ≠ i}, Fin n) where
  toFun hs x := hs.1 x.1
  invFun g := ⟨coordFiberTable i j g, by rw [coordFiberTable]; exact dif_pos rfl⟩
  left_inv hs := by
    refine Subtype.ext (funext fun x => ?_)
    show coordFiberTable i j (fun x => hs.1 x.1) x = hs.1 x
    by_cases hx : x = i
    · subst hx
      rw [coordFiberTable, dif_pos rfl]
      exact hs.2.symm
    · rw [coordFiberTable, dif_neg hx]
  right_inv g := by
    funext x
    show coordFiberTable i j g x.1 = g x
    by_cases hx : (x : Fin k) = i
    · exact absurd hx x.2
    · rw [coordFiberTable, dif_neg hx]

/-- There are `n ^ (k - 1)` functions from `Fin k` to `Fin n` with a prescribed value at a
specified coordinate. -/
theorem coord_fiber_card {k n : ℕ} (i : Fin k) (j : Fin n) :
    Fintype.card {s : Fin k → Fin n // s i = j} = n ^ (k - 1) := by
  have h1 : Fintype.card {x : Fin k // x = i} = 1 := Fintype.card_subtype_eq i
  have h2 := Fintype.card_subtype_compl (fun x : Fin k => x = i)
  have h3 : Fintype.card {x : Fin k // x ≠ i}
      = Fintype.card {x : Fin k // ¬(x = i)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  have hcard : Fintype.card {x : Fin k // x ≠ i} = k - 1 := by
    rw [h3, h2, h1]
    simp
  calc Fintype.card {s : Fin k → Fin n // s i = j}
      = Fintype.card (∀ x : {x : Fin k // x ≠ i}, Fin n) :=
        Fintype.card_congr (coordFiberEquiv i j)
    _ = ∏ _x : {x : Fin k // x ≠ i}, Fintype.card (Fin n) := Fintype.card_pi
    _ = n ^ (k - 1) := by
        rw [Finset.prod_const]
        simp [hcard]

/-- The finite set of tables with a prescribed coordinate value has cardinality `n ^ (k - 1)`. -/
theorem coord_fiber_filter_card {k n : ℕ} (i : Fin k) (j : Fin n) :
    ((Finset.univ : Finset (Fin k → Fin n)).filter (fun s => s i = j)).card
      = n ^ (k - 1) := by
  have hbridge : Fintype.card {s : Fin k → Fin n // s i = j}
      = ((Finset.univ : Finset (Fin k → Fin n)).filter (fun s => s i = j)).card := by
    have e : {s : Fin k → Fin n // s i = j}
        ≃ {s : Fin k → Fin n // s ∈ Finset.univ.filter (fun s => s i = j)} :=
      Equiv.subtypeEquivRight (fun s => by simp [Finset.mem_filter])
    rw [Fintype.card_congr e, Fintype.card_coe]
  rw [← hbridge]
  exact coord_fiber_card i j

/-- At most `k * k * n ^ (k - 1)` injective selections share a coordinate value with a fixed
selection. -/
theorem overlap_index_card_le {n k : ℕ} (t : Fin k → Fin n) :
    ((Finset.univ : Finset (Fin k → Fin n)).filter
      (fun s => Function.Injective s ∧ ∃ i, ∃ j, s i = t j)).card
      ≤ k * k * n ^ (k - 1) := by
  classical
  set F : Fin k → Fin k → Finset (Fin k → Fin n) :=
    fun i j => ((Finset.univ : Finset (Fin k → Fin n))).filter (fun s => s i = t j) with hF
  have hsub : ((Finset.univ : Finset (Fin k → Fin n)).filter
      (fun s => Function.Injective s ∧ ∃ i, ∃ j, s i = t j))
    ⊆ Finset.biUnion Finset.univ (fun i : Fin k =>
        Finset.biUnion Finset.univ (fun j : Fin k => F i j)) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨-, i, j, hij⟩ := hs
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, ?_⟩
    refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, ?_⟩
    rw [hF]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ s, hij⟩
  have h1 : ((Finset.univ : Finset (Fin k → Fin n)).filter
      (fun s => Function.Injective s ∧ ∃ i, ∃ j, s i = t j)).card
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)),
          (Finset.biUnion Finset.univ (fun j : Fin k => F i j)).card :=
    (Finset.card_le_card hsub).trans
      (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin k)))
        (t := fun i : Fin k => Finset.biUnion Finset.univ (fun j : Fin k => F i j)))
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      (Finset.biUnion Finset.univ (fun j : Fin k => F i j)).card
      ≤ k * n ^ (k - 1) := by
    intro i _
    have hA := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin k)))
        (t := fun j : Fin k => F i j)
    have hsum : ∑ j ∈ (Finset.univ : Finset (Fin k)), (F i j).card = k * n ^ (k - 1) := by
      have hfib : ∀ j : Fin k, (F i j).card = n ^ (k - 1) :=
        fun j => coord_fiber_filter_card i (t j)
      rw [Finset.sum_congr rfl fun j _ => hfib j, Finset.sum_const, smul_eq_mul]
      simp [Fintype.card_fin]
    exact hA.trans (hsum.le)
  have hsum2 : ∑ i ∈ (Finset.univ : Finset (Fin k)), k * n ^ (k - 1) = k * k * n ^ (k - 1) := by
    rw [Finset.sum_const, smul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin]
    ring
  exact (h1.trans (Finset.sum_le_sum fun i hi => h2 i hi)).trans_eq hsum2

/-- For a nonzero distinct-tuple count, the U-statistic variance is bounded by the kernel
variance times the overlap degree bound divided by the tuple count. -/
theorem uStatistic_variance_le (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (hN : (distinctTupleCount n k : ℕ) ≠ 0) :
    ∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ 2
      ≤ kernelVarianceK p h * (overlapDegreeBound n k : ℝ)
          / ((distinctTupleCount n k : ℕ) : ℝ) := by
  classical
  have hV := kernelVarianceK_nonneg p h
  have hCpos : 0 < ((distinctTupleCount n k : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hC2pos : (0 : ℝ) < ((distinctTupleCount n k : ℕ) : ℝ) ^ 2 := by positivity

  have hsum : (∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
      (if Function.Injective t ∧ Function.Injective s then
        overlapCovarianceK p h t s else 0))
      ≤ ((distinctTupleCount n k : ℕ) : ℝ)
          * (kernelVarianceK p h * ((overlapDegreeBound n k : ℕ) : ℝ)) := by
    have hsplit : ∀ t s : Fin k → Fin n,
        (if Function.Injective t ∧ Function.Injective s then
          overlapCovarianceK p h t s else 0)
        = (if Function.Injective t then
            (if Function.Injective s then overlapCovarianceK p h t s else 0) else 0) := by
      intro t s
      by_cases hts : Function.Injective t ∧ Function.Injective s
      · rw [if_pos hts, if_pos (hts.1), if_pos (hts.2)]
      · rw [if_neg hts]
        by_cases ht : Function.Injective t
        · rw [if_pos ht, if_neg (fun hc => hts ⟨ht, hc⟩)]
        · rw [if_neg ht]
    have hinner : ∀ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
        (if Function.Injective t then
          (if Function.Injective s then overlapCovarianceK p h t s else 0) else 0)
      ≤ (if Function.Injective t then
          kernelVarianceK p h
            * ((((Finset.univ : Finset (Fin k → Fin n)).filter
                  (fun s => Function.Injective s ∧ ∃ i, ∃ j, s i = t j)).card : ℕ) : ℝ)
          else 0) := by
      intro t
      by_cases ht : Function.Injective t
      · simp only [ht, if_true]
        have hle : ∀ s : Fin k → Fin n,
            (if Function.Injective s then overlapCovarianceK p h t s else 0)
          ≤ (if Function.Injective s ∧ ∃ i, ∃ j, s i = t j
              then kernelVarianceK p h else 0) := by
          intro s
          by_cases hq : Function.Injective s ∧ ∃ i, ∃ j, s i = t j
          · rw [if_pos hq, if_pos hq.1]
            exact overlapCovarianceK_le p h t s ht hq.1
          · rw [if_neg hq]
            by_cases hs : Function.Injective s
            · rw [if_pos hs]
              simp only [not_and_or, not_exists] at hq
              have hdis : ∀ i j : Fin k, t i ≠ s j := by
                intro i j hcontra
                rcases hq with hns | hall
                · exact absurd hs hns
                · exact absurd hcontra.symm (hall j i)
              rw [overlapCovarianceK_disjoint p h t s ht hs hdis]
            · rw [if_neg hs]
        calc ∑ s : Fin k → Fin n,
            (if Function.Injective s then overlapCovarianceK p h t s else 0)
            ≤ ∑ s : Fin k → Fin n,
                (if Function.Injective s ∧ ∃ i, ∃ j, s i = t j
                  then kernelVarianceK p h else 0) := Finset.sum_le_sum fun s _ => hle s
          _ = kernelVarianceK p h
              * (((Finset.univ : Finset (Fin k → Fin n)).filter
                  (fun s => Function.Injective s ∧ ∃ i, ∃ j, s i = t j)).card : ℝ) := by
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
              ring
      · simp [ht]
    have houter : ∑ t : Fin k → Fin n,
        (if Function.Injective t then
          kernelVarianceK p h
            * ((((Finset.univ : Finset (Fin k → Fin n)).filter
                  (fun s => Function.Injective s ∧ ∃ i, ∃ j, s i = t j)).card : ℕ) : ℝ)
          else 0)
      ≤ ((distinctTupleCount n k : ℕ) : ℝ)
          * (kernelVarianceK p h * ((overlapDegreeBound n k : ℕ) : ℝ)) := by
      have hterm : ∀ t : Fin k → Fin n,
          (if Function.Injective t then
            kernelVarianceK p h
              * ((((Finset.univ : Finset (Fin k → Fin n)).filter
                    (fun s => Function.Injective s ∧ ∃ i, ∃ j, s i = t j)).card : ℕ) : ℝ)
            else 0)
        ≤ (if Function.Injective t then
            kernelVarianceK p h * ((overlapDegreeBound n k : ℕ) : ℝ) else 0) := by
        intro t
        by_cases ht : Function.Injective t
        · rw [if_pos ht, if_pos ht]
          refine mul_le_mul_of_nonneg_left ?_ hV
          exact_mod_cast overlap_index_card_le t
        · rw [if_neg ht, if_neg ht]
      calc ∑ t : Fin k → Fin n,
          (if Function.Injective t then
            kernelVarianceK p h
              * ((((Finset.univ : Finset (Fin k → Fin n)).filter
                    (fun s => Function.Injective s ∧ ∃ i, ∃ j, s i = t j)).card : ℕ) : ℝ)
            else 0)
          ≤ ∑ t : Fin k → Fin n,
              (if Function.Injective t then
                kernelVarianceK p h * ((overlapDegreeBound n k : ℕ) : ℝ) else 0) :=
              Finset.sum_le_sum fun t _ => hterm t
        _ = ((distinctTupleCount n k : ℕ) : ℝ)
            * (kernelVarianceK p h * ((overlapDegreeBound n k : ℕ) : ℝ)) :=
            sum_injective_const _
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => hsplit t s]
    exact (Finset.sum_le_sum fun t _ => hinner t).trans houter

  rw [uStatistic_variance_overlap p h hN, div_le_div_iff₀ hC2pos hCpos]
  calc (∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
          (if Function.Injective t ∧ Function.Injective s then
            overlapCovarianceK p h t s else 0))
        * ((distinctTupleCount n k : ℕ) : ℝ)
      ≤ (((distinctTupleCount n k : ℕ) : ℝ)
          * (kernelVarianceK p h * ((overlapDegreeBound n k : ℕ) : ℝ)))
          * ((distinctTupleCount n k : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsum hCpos.le
    _ = (kernelVarianceK p h * ((overlapDegreeBound n k : ℕ) : ℝ))
          * ((distinctTupleCount n k : ℕ) : ℝ) ^ 2 := by ring

/-- For a positive threshold, the probability of a strict absolute deviation from the mean is at
most the variance divided by the squared threshold. -/
theorem probEvent_le_variance {X : Type} [Fintype X] {n : ℕ} (p : FinDist X)
    (f : (Fin n → X) → ℝ) (μ : ℝ) (hμ : ∑ ω : Fin n → X, p.probOf ω * f ω = μ)
    (ε : ℝ) (hε : 0 < ε) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p (fun ω : Fin n → X => ε < |f ω - μ|)
      ≤ (∑ ω : Fin n → X, p.probOf ω * (f ω - μ) ^ 2) / ε ^ 2 := by
  classical
  have h2 : 0 < ε ^ 2 := by positivity
  have hsub : (Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|))
      ⊆ (Finset.univ : Finset (Fin n → X)) := Finset.filter_subset _ _
  have hpoint : ∀ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|),
      p.probOf ω ≤ p.probOf ω * (f ω - μ) ^ 2 / ε ^ 2 := by
    intro ω hω
    have hev : ε < |f ω - μ| := Finset.mem_filter.mp hω |>.2
    have h1 : ε ^ 2 < (f ω - μ) ^ 2 := by
      rw [← sq_abs (f ω - μ)]
      refine (sq_lt_sq (a := ε) (b := |f ω - μ|)).mpr ?_
      rw [abs_of_pos hε, abs_abs]
      exact hev
    have hle : (1 : ℝ) ≤ (f ω - μ) ^ 2 / ε ^ 2 := by
      rw [le_div_iff₀ h2, one_mul]
      exact le_of_lt h1
    calc p.probOf ω = p.probOf ω * 1 := by ring
      _ ≤ p.probOf ω * ((f ω - μ) ^ 2 / ε ^ 2) :=
          mul_le_mul_of_nonneg_left hle (probOf_nonneg p ω)
      _ = p.probOf ω * (f ω - μ) ^ 2 / ε ^ 2 := by ring
  have hsum1 : (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|), p.probOf ω)
      ≤ (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|),
          p.probOf ω * (f ω - μ) ^ 2) / ε ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun ω hω => hpoint ω hω
  have hsum2 : (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|),
      p.probOf ω * (f ω - μ) ^ 2)
      ≤ ∑ ω : Fin n → X, p.probOf ω * (f ω - μ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ =>
      mul_nonneg (probOf_nonneg p ω) (sq_nonneg _)
  have hdef : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p (fun ω : Fin n → X => ε < |f ω - μ|)
      = ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|), p.probOf ω :=
    rfl
  rw [hdef]
  calc ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|), p.probOf ω
      ≤ (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|),
          p.probOf ω * (f ω - μ) ^ 2) / ε ^ 2 := hsum1
    _ ≤ (∑ ω : Fin n → X, p.probOf ω * (f ω - μ) ^ 2) / ε ^ 2 :=
        div_le_div_of_nonneg_right hsum2 h2.le

/-- For a positive threshold and nonzero distinct-tuple count, the U-statistic deviation
probability is bounded by the kernel variance times the overlap degree bound divided by the
tuple count and squared threshold. -/
theorem probEvent_uStatistic_le (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (hN : (distinctTupleCount n k : ℕ) ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p
        (fun ω : Fin n → O => ε < |povmUStatisticK h ω - kernelMeanK p h|)
      ≤ kernelVarianceK p h * (overlapDegreeBound n k : ℝ)
          / (((distinctTupleCount n k : ℕ) : ℝ) * ε ^ 2) := by
  have hunb := povmUStatisticK_unbiased p h hN
  have hcheb := probEvent_le_variance p (povmUStatisticK h) (kernelMeanK p h) hunb ε hε
  have hvar := uStatistic_variance_le p h hN
  have h2 : 0 < ε ^ 2 := by positivity
  calc Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p
        (fun ω : Fin n → O => ε < |povmUStatisticK h ω - kernelMeanK p h|)
      ≤ (∑ ω : Fin n → O,
          p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ 2) / ε ^ 2 := hcheb
    _ ≤ (kernelVarianceK p h * (overlapDegreeBound n k : ℝ)
          / ((distinctTupleCount n k : ℕ) : ℝ)) / ε ^ 2 :=
        div_le_div_of_nonneg_right hvar h2.le
    _ = kernelVarianceK p h * (overlapDegreeBound n k : ℝ)
          / (((distinctTupleCount n k : ℕ) : ℝ) * ε ^ 2) := by
        ring

/-- Collects unbiasedness, the overlap variance formula, covariance identities, and variance and
deviation bounds for independent finite-sample U-statistics. -/
theorem frontier1 :
    ∀ {O : Type} [Fintype O] [DecidableEq O] (p : FinDist O) {n k : ℕ},
      (distinctTupleCount n k : ℕ) ≠ 0 → ∀ (h : (Fin k → O) → ℝ) (ε : ℝ), 0 < ε →
      (∑ ω : Fin n → O, p.probOf ω * povmUStatisticK h ω = kernelMeanK p h) ∧
      (∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ 2
        = (∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
            (if Function.Injective t ∧ Function.Injective s then
              overlapCovarianceK p h t s else 0))
          / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2) ∧
      (∀ t : Fin k → Fin n, Function.Injective t →
        overlapCovarianceK p h t t = kernelVarianceK p h) ∧
      (∀ t s : Fin k → Fin n, Function.Injective t → Function.Injective s →
        (∀ i j : Fin k, t i ≠ s j) → overlapCovarianceK p h t s = 0) ∧
      (∀ (σ : Fin n ≃ Fin n) (t t' s s' : Fin k → Fin n),
        (∀ i, t' i = σ (t i)) → (∀ i, s' i = σ (s i)) →
        overlapCovarianceK p h t s = overlapCovarianceK p h t' s') ∧
      (∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ 2
        ≤ kernelVarianceK p h * (overlapDegreeBound n k : ℝ)
            / ((distinctTupleCount n k : ℕ) : ℝ)) ∧
      (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p
          (fun ω : Fin n → O => ε < |povmUStatisticK h ω - kernelMeanK p h|)
        ≤ kernelVarianceK p h * (overlapDegreeBound n k : ℝ)
            / (((distinctTupleCount n k : ℕ) : ℝ) * ε ^ 2)) := by
  intro O _ _ p n k hN h ε hε
  exact ⟨povmUStatisticK_unbiased p h hN,
    uStatistic_variance_overlap p h hN,
    fun t ht => overlapCovarianceK_self p h t ht,
    fun t s ht hs hdis => overlapCovarianceK_disjoint p h t s ht hs hdis,
    fun σ t t' s s' ht hs => overlapCovarianceK_transport p h σ t t' s s' ht hs,
    uStatistic_variance_le p h hN,
    probEvent_uStatistic_le p h hN ε hε⟩

section Povm

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative

variable {D : ℕ}

/-- Specializes the U-statistic expectation, overlap covariance identities, variance expansion,
and variance and deviation bounds to repeated measurements of a density operator by a finite
POVM. -/
theorem frontier1_povm (E : FinitePOVM O D) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {n k : ℕ} (hN : (distinctTupleCount n k : ℕ) ≠ 0) (h : (Fin k → O) → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ((povmSampleLaw E ρ hρ).expect (fun ω : Fin n → O => povmUStatisticK h ω)
        = kernelMeanK (povmRecordLaw E ρ hρ) h) ∧
    ((povmSampleLaw E ρ hρ).expect
        (fun ω : Fin n → O =>
          (povmUStatisticK h ω - kernelMeanK (povmRecordLaw E ρ hρ) h) ^ 2)
      = (∑ t : Fin k → Fin n, ∑ s : Fin k → Fin n,
          (if Function.Injective t ∧ Function.Injective s then
            overlapCovarianceK (povmRecordLaw E ρ hρ) h t s else 0))
        / ((distinctTupleCount n k : ℕ) : ℝ) ^ 2) ∧
    (∀ t : Fin k → Fin n, Function.Injective t →
      overlapCovarianceK (povmRecordLaw E ρ hρ) h t t
        = kernelVarianceK (povmRecordLaw E ρ hρ) h) ∧
    (∀ t s : Fin k → Fin n, Function.Injective t → Function.Injective s →
      (∀ i j : Fin k, t i ≠ s j) →
      overlapCovarianceK (povmRecordLaw E ρ hρ) h t s = 0) ∧
    (∀ (σ : Fin n ≃ Fin n) (t t' s s' : Fin k → Fin n),
      (∀ i, t' i = σ (t i)) → (∀ i, s' i = σ (s i)) →
      overlapCovarianceK (povmRecordLaw E ρ hρ) h t s
        = overlapCovarianceK (povmRecordLaw E ρ hρ) h t' s') ∧
    ((povmSampleLaw E ρ hρ).expect
        (fun ω : Fin n → O =>
          (povmUStatisticK h ω - kernelMeanK (povmRecordLaw E ρ hρ) h) ^ 2)
      ≤ kernelVarianceK (povmRecordLaw E ρ hρ) h * (overlapDegreeBound n k : ℝ)
          / ((distinctTupleCount n k : ℕ) : ℝ)) ∧
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
        (fun ω : Fin n → O =>
          ε < |povmUStatisticK h ω - kernelMeanK (povmRecordLaw E ρ hρ) h|)
      ≤ kernelVarianceK (povmRecordLaw E ρ hρ) h * (overlapDegreeBound n k : ℝ)
          / (((distinctTupleCount n k : ℕ) : ℝ) * ε ^ 2)) := by
  have hb := frontier1 (povmRecordLaw E ρ hρ) hN h ε hε
  have hexpect : ∀ f : (Fin n → O) → ℝ,
      (povmSampleLaw E ρ hρ).expect f
        = ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * f ω := by
    intro f
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
    rfl
  rw [hexpect]
  exact hb

end Povm

end Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics
