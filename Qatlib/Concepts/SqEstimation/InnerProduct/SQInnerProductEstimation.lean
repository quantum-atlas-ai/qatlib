/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.SqEstimation.InnerProduct.FiniteSQAccess
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Complex inner-product estimation with sample-and-query access

`sqImportanceValue` is an unbiased complex importance estimator for `sqInnerTarget`, and
`sqMean` averages samples from a finite envelope distribution. `sqMedian` takes separate medians
of the real and imaginary block means, yielding a complex error bound from second-moment
control.

The counted implementations record access calls and implement deterministic selection through
groups of five. `sqSelect_rank_and_cost` proves the order-statistic specification and a linear
comparison bound used by `sqMedianCounted`. For background, see [ChiaEtAl2022].

## Main statements

* `finite_sq_actual_complex_importance_moments`: proves unbiasedness and a second-moment bound.
* `finite_sq_component_median_complex_guarantee`: bounds the probability of complex estimation
  error.
* `finite_sq_linear_median_and_actual_query_ledger`: relates counted estimators to their values
  and proves exact access counts and linear selection cost.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
open scoped Classical BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.SqEstimation.InnerProduct

/-- The finite complex inner product of `u` and `v`, conjugate-linear in `u`. -/
noncomputable def sqInnerTarget {X : Type} [Fintype X] (u v : X → ℂ) : ℂ := ∑ i, star (u i)*v i
/-- The importance-weighted contribution to the target inner product, scaled by the cached
envelope norm and set to zero at zero envelope entries. -/
noncomputable def sqImportanceValue {X : Type} [Fintype X] (a : FiniteSQInput X) (v : X → ℂ) (i : X) : ℂ :=
  if Complex.normSq (a.envelope i)=0 then 0 else
    (a.cachedEnvelopeSquaredNorm:ℂ)*star (a.target i)*v i/(Complex.normSq (a.envelope i):ℂ)
/-- The arithmetic mean of the importance contributions selected by the sample record. -/
noncomputable def sqMean {X : Type} [Fintype X] (a : FiniteSQInput X) (v : X → ℂ)
    {m : ℕ} (ω : Fin m → X) : ℂ := (∑ t, sqImportanceValue a v (ω t))/(m:ℂ)
/-- The complex estimator formed from separate medians of the real and imaginary parts of `2 * r
+ 1` block means. -/
noncomputable def sqMedian {X : Type} [Fintype X] (a : FiniteSQInput X) (v : X → ℂ)
    (m r : ℕ) (ω : Fin (2*r+1) → Fin m → X) : ℂ :=
  (sortedBlockMedian r (fun b => (sqMean a v (ω b)).re):ℂ)+
  (sortedBlockMedian r (fun b => (sqMean a v (ω b)).im):ℂ)*Complex.I

/-- The access-call categories used to record envelope norms, sampling operations, and matrix or
vector entry queries. -/
inductive SQCall where
  | envelopeNorm | sampleEnvelope | sampleRow | sampleColumn
  | targetEntry | envelopeEntry | otherEntry | leftVectorEntry | rightVectorEntry
  deriving DecidableEq
/-- Compute a block importance mean together with its list of sampling and entry-query calls. -/
noncomputable def sqMeanCounted {X : Type} [Fintype X] (a : FiniteSQInput X) (v : X → ℂ)
    {m : ℕ} (ω : Fin m → X) : ℂ × List SQCall :=
  let z := (List.ofFn (fun t : Fin m => t)).foldl (fun z t =>
    (z.1+sqImportanceValue a v (ω t),[.otherEntry,.envelopeEntry,.targetEntry,.sampleEnvelope]++z.2)) (0,[])
  (z.1/(m:ℂ),z.2.reverse)
/-- The access ledger for all block means, preceded by one envelope-norm query. -/
noncomputable def sqRunCalls {X : Type} [Fintype X] (a : FiniteSQInput X) (v : X → ℂ)
    (m r : ℕ) (ω : Fin (2*r+1) → Fin m → X) : List SQCall :=
  .envelopeNorm :: (List.ofFn (fun b => (sqMeanCounted a v (ω b)).2)).flatten

/-- Split a real list into successive groups of at most five, stopping when the fuel or input
list is exhausted. -/
def sqChunks5 : ℕ → List ℝ → List (List ℝ)
  | 0,_ => []
  | _+1,[] => []
  | k+1,x::xs => (x::xs).take 5 :: sqChunks5 k ((x::xs).drop 5)
/-- Partition a real list into reversed sublists below, equal to, and above a pivot, recording
the number of comparisons. -/
noncomputable def sqPartition (p : ℝ) (xs : List ℝ) : List ℝ × List ℝ × List ℝ × ℕ :=
  xs.foldl (fun z x => if x < p then (x::z.1,z.2.1,z.2.2.1,z.2.2.2+1) else
    if p < x then (z.1,z.2.1,x::z.2.2.1,z.2.2.2+2) else
      (z.1,x::z.2.1,z.2.2.1,z.2.2.2+2)) ([],[],[],0)
/-- Select a zero-based order statistic with a comparison count using recursive groups-of-five
pivots, with counted insertion sort as the fuel-zero or small-list fallback. -/
noncomputable def sqSelectFuel : ℕ → List ℝ → ℕ → ℝ × ℕ
  | 0,xs,k => let z := insertionSortCounted xs; (z.1.getD k 0,z.2)
  | f+1,xs,k =>
    if xs.length ≤ 1000 then let z := insertionSortCounted xs; (z.1.getD k 0,z.2) else
      let groups := (sqChunks5 xs.length xs).map insertionSortCounted
      let pivots := groups.map (fun z => z.1.getD (z.1.length/2) 0)
      let p := sqSelectFuel f pivots (pivots.length/2)
      let q := sqPartition p.1 xs
      let initial := (groups.map Prod.snd).sum+p.2+q.2.2.2
      if k < q.1.length then let z := sqSelectFuel f q.1 k; (z.1,initial+z.2) else
        if k < q.1.length+q.2.1.length then (p.1,initial) else
          let z := sqSelectFuel f q.2.2.1 (k-q.1.length-q.2.1.length)
          (z.1,initial+z.2)
/-- The counted order-statistic selector initialized with fuel equal to the list length. -/
noncomputable def sqSelect (xs : List ℝ) (k : ℕ) : ℝ × ℕ := sqSelectFuel xs.length xs k
/-- Compute the componentwise complex median using two counted order-statistic selections and
return their total comparison count. -/
noncomputable def sqMedianCounted {X : Type} [Fintype X] (a : FiniteSQInput X) (v : X → ℂ)
    (m r : ℕ) (ω : Fin (2*r+1) → Fin m → X) : ℂ × ℕ :=
  let x := sqSelect (List.ofFn (fun b => (sqMean a v (ω b)).re)) r
  let y := sqSelect (List.ofFn (fun b => (sqMean a v (ω b)).im)) r
  ((x.1:ℂ)+(y.1:ℂ)*Complex.I,x.2+y.2)
/-- The expected squared complex error of a block importance mean under independent envelope
samples. -/
noncomputable def sqMeanSquaredError {X : Type} [Fintype X] (a : FiniteSQInput X) (v : X → ℂ) (m : ℕ) : ℝ :=
  ∑ ω : Fin m → X, a.samples.probOf ω*Complex.normSq (sqMean a v ω-sqInnerTarget a.target v)
/-- The probability that the componentwise median estimator has complex norm error greater than
`ε`, under independent samples in all blocks. -/
noncomputable def sqBadMass {X : Type} [Fintype X] (a : FiniteSQInput X) (v : X → ℂ)
    (m r : ℕ) (ε : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → X =>
    ε < ‖sqMedian a v m r ω-sqInnerTarget a.target v‖), ∏ b, a.samples.probOf (ω b)

/-- Multiplying an importance contribution by its sampling probability recovers the
corresponding target inner-product summand. -/
theorem sqImportanceValue_weighted {X : Type} [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) (i : X) :
    (a.samples.prob i : ℂ) * sqImportanceValue a v i = star (a.target i) * v i := by
  by_cases hi : Complex.normSq (a.envelope i) = 0
  · have hu := (finite_sq_access_support_and_norm X a).2.2 i
      (Complex.normSq_eq_zero.mp hi)
    simp [sqImportanceValue, hi, hu]
  · have hw : (sqSquaredNorm a.envelope : ℂ) ≠ 0 := by
      exact_mod_cast a.envelope_pos.ne'
    have hi' : (Complex.normSq (a.envelope i) : ℂ) ≠ 0 := by exact_mod_cast hi
    rw [a.sample_spec, sqImportanceValue, if_neg hi, a.norm_spec]
    push_cast
    field_simp

/-- The probability-weighted squared importance contribution at a coordinate is bounded by the
envelope squared norm times the squared norm of the other vector entry. -/
theorem sqImportanceValue_secondMoment_le {X : Type} [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) (i : X) :
    a.samples.prob i * Complex.normSq (sqImportanceValue a v i) ≤
      sqSquaredNorm a.envelope * Complex.normSq (v i) := by
  by_cases hi : Complex.normSq (a.envelope i) = 0
  · simp only [sqImportanceValue, if_pos hi, Complex.normSq_zero, mul_zero]
    exact mul_nonneg a.envelope_pos.le (Complex.normSq_nonneg _)
  · have hp : 0 < Complex.normSq (a.envelope i) :=
      lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hi)
    rw [a.sample_spec, sqImportanceValue, if_neg hi, a.norm_spec]
    simp only [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.star_def, Complex.normSq_conj, ← pow_two]
    have heq : Complex.normSq (a.envelope i) / sqSquaredNorm a.envelope *
        (sqSquaredNorm a.envelope ^ 2 * Complex.normSq (a.target i) *
          Complex.normSq (v i) / Complex.normSq (a.envelope i) ^ 2) =
        sqSquaredNorm a.envelope * Complex.normSq (v i) *
          (Complex.normSq (a.target i) / Complex.normSq (a.envelope i)) := by
      field_simp
    rw [heq]
    exact mul_le_of_le_one_right
      (mul_nonneg a.envelope_pos.le (Complex.normSq_nonneg _))
      ((div_le_one hp).mpr (a.domination i))

/-- The importance estimator is unbiased for the complex target inner product, and its second
moment is bounded by the product of the envelope and other-vector squared norms. These are
the finite importance-sampling moment estimates associated with [Chia et al., Lemma
4.12][ChiaEtAl2022]. -/
theorem finite_sq_actual_complex_importance_moments (X : Type) [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) :
    (∑ i, (a.samples.prob i : ℂ) * sqImportanceValue a v i) = sqInnerTarget a.target v ∧
    (∑ i, a.samples.prob i * Complex.normSq (sqImportanceValue a v i)) ≤
      sqSquaredNorm a.envelope * sqSquaredNorm v := by
  refine ⟨Finset.sum_congr rfl (fun i _ => sqImportanceValue_weighted a v i), ?_⟩
  exact (Finset.sum_le_sum (fun i _ => sqImportanceValue_secondMoment_le a v i)).trans_eq
    (Finset.mul_sum _ _ _).symm

/-- The expected real and imaginary importance components equal the respective components of the
target inner product. -/
theorem sqImportanceValue_component_means {X : Type} [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) :
    a.samples.expect (fun i => (sqImportanceValue a v i).re) = (sqInnerTarget a.target v).re ∧
    a.samples.expect (fun i => (sqImportanceValue a v i).im) = (sqInnerTarget a.target v).im := by
  have h := (finite_sq_actual_complex_importance_moments X a v).1
  constructor
  · simpa [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Complex.mul_re] using!
      congrArg Complex.re h
  · simpa [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Complex.mul_im] using!
      congrArg Complex.im h

/-- The real and imaginary parts of the complex importance mean are the sample averages of the
respective importance components. -/
theorem sqMean_components {X : Type} [Fintype X] (a : FiniteSQInput X)
    (v : X → ℂ) {m : ℕ} (ω : Fin m → X) :
    (sqMean a v ω).re = Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (sqImportanceValue a v i).re) ω ∧
    (sqMean a v ω).im = Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (sqImportanceValue a v i).im) ω := by
  simp [sqMean, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg, ← Complex.ofReal_natCast]

/-- The variance of a real function on a finite distribution is its second moment minus the
square of its expectation. -/
theorem sq_real_variance_eq {X : Type} [Fintype X] (p : FinDist X) (f : X → ℝ) :
    p.variance f = p.expect (fun i => (f i)^2) - (p.expect f)^2 := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  simp_rw [show ∀ x : X, p.prob x * (f x - ∑ i, p.prob i * f i)^2 =
    p.prob x * (f x)^2 - 2 * (∑ i, p.prob i * f i) * (p.prob x * f x) +
      (∑ i, p.prob i * f i)^2 * p.prob x by intro x; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, p.sum_one]
  ring

/-- The sum of the real and imaginary importance-component variances is bounded by the product
of the envelope and other-vector squared norms. -/
theorem sqImportanceValue_component_variances_le {X : Type} [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) :
    a.samples.variance (fun i => (sqImportanceValue a v i).re) +
      a.samples.variance (fun i => (sqImportanceValue a v i).im) ≤
      sqSquaredNorm a.envelope * sqSquaredNorm v := by
  rw [sq_real_variance_eq, sq_real_variance_eq]
  have hraw : a.samples.expect (fun i => (sqImportanceValue a v i).re^2) +
      a.samples.expect (fun i => (sqImportanceValue a v i).im^2) =
      ∑ i, a.samples.prob i * Complex.normSq (sqImportanceValue a v i) := by
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.normSq_apply]
    ring
  have hbound := (finite_sq_actual_complex_importance_moments X a v).2
  have hr := sq_nonneg (a.samples.expect (fun i => (sqImportanceValue a v i).re))
  have hi := sq_nonneg (a.samples.expect (fun i => (sqImportanceValue a v i).im))
  linarith

/-- For a positive block size, the complex sample mean is unbiased and its mean squared error is
bounded by the product of the envelope and other-vector squared norms divided by the block
size. This supplies the block estimate used for [Chia et al., Lemma 4.12][ChiaEtAl2022]. -/
theorem finite_sq_same_record_mean_squared_error (X : Type) [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) (m : ℕ) (hm : 0 < m) :
    (∑ ω : Fin m → X, (a.samples.probOf ω : ℂ) * sqMean a v ω) =
        sqInnerTarget a.target v ∧
      sqMeanSquaredError a v m ≤ sqSquaredNorm a.envelope * sqSquaredNorm v / (m : ℝ) := by
  have hre := (sqImportanceValue_component_means a v).1
  have him := (sqImportanceValue_component_means a v).2
  have havgre := a.samples.expect_avg (fun i => (sqImportanceValue a v i).re) hm
  have havgim := a.samples.expect_avg (fun i => (sqImportanceValue a v i).im) hm
  have hvarre := a.samples.expect_avg_sub_sq (fun i => (sqImportanceValue a v i).re) hm
  have hvarim := a.samples.expect_avg_sub_sq (fun i => (sqImportanceValue a v i).im) hm
  constructor
  · apply Complex.ext
    · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, (sqMean_components a v _).1, hre] using! havgre.trans hre
    · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, (sqMean_components a v _).2, him] using! havgim.trans him
  · have heq : sqMeanSquaredError a v m =
        (a.samples.variance (fun i => (sqImportanceValue a v i).re) +
          a.samples.variance (fun i => (sqImportanceValue a v i).im)) / (m : ℝ) := by
      unfold sqMeanSquaredError
      simp_rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        (sqMean_components a v _).1, (sqMean_components a v _).2]
      simp_rw [← hre, ← him]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp_rw [← sq, hvarre, hvarim]
      rw [add_div]
    rw [heq]
    exact div_le_div_of_nonneg_right (sqImportanceValue_component_variances_le a v)
      (Nat.cast_nonneg m)

/-- Select the real or imaginary component of a complex number according to a Boolean flag. -/
def sqComponent (b : Bool) (z : ℂ) : ℝ := if b then z.im else z.re

/-- The uniformly weighted block construction for a chosen importance component equals that
component of each complex block mean. -/
theorem sq_component_weighted_block {X : Type} [Fintype X] [DecidableEq X]
    (a : FiniteSQInput X) (v : X → ℂ) (m r : ℕ) (z : Bool)
    (ω : Fin (2*r+1) → Fin m → X) :
    weightedBlock r m (fun _ _ => (1 : ℝ)/(m : ℝ))
      (fun _ _ i => sqComponent z (sqImportanceValue a v i)) ω =
        fun b => sqComponent z (sqMean a v (ω b)) := by
  funext b
  cases z <;> simp [weightedBlock, sqComponent,
    (sqMean_components a v _).1, (sqMean_components a v _).2,
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg, div_eq_mul_inv, ← Finset.mul_sum, mul_comm]

/-- If `m` and `ε` are positive and `m * ε²` is at least 64 times the product of the envelope
and other-vector squared norms, the complex median failure mass is at most `2 * 2^(2*r+1) *
(1/16)^(r+1)`. This is the componentwise median guarantee for the inner-product estimator of
[Chia et al., Lemma 4.12][ChiaEtAl2022]. -/
theorem finite_sq_component_median_complex_guarantee (X : Type) [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) (m r : ℕ) (ε : ℝ)
    (hm : 0 < m) (hε : 0 < ε)
    (hbudget : 64*sqSquaredNorm a.envelope*sqSquaredNorm v ≤ (m : ℝ)*ε^2) :
    sqBadMass a v m r ε ≤ 2*(2 : ℝ)^(2*r+1)*(1/16 : ℝ)^(r+1) := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let f : Bool → X → ℝ := fun z i => sqComponent z (sqImportanceValue a v i)
  let θ : Bool → ℝ := fun z => sqComponent z (sqInnerTarget a.target v)
  have hmeans : ∀ z, a.samples.expect (f z) = θ z := by
    intro z
    cases z
    · exact (sqImportanceValue_component_means a v).1
    · exact (sqImportanceValue_component_means a v).2
  have hvars : ∀ z, a.samples.variance (f z) ≤
      sqSquaredNorm a.envelope * sqSquaredNorm v := by
    have hsum := sqImportanceValue_component_variances_le a v
    have hre : 0 ≤ a.samples.variance (fun i => (sqImportanceValue a v i).re) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (a.samples.nonneg i) (sq_nonneg _)
    have him : 0 ≤ a.samples.variance (fun i => (sqImportanceValue a v i).im) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (a.samples.nonneg i) (sq_nonneg _)
    intro z
    cases z <;> dsimp [f, sqComponent] <;> linarith
  have hmean : ∀ (z : Bool) (j : Fin (2*r+1)),
      ∑ b : Fin m, (1 : ℝ)/(m : ℝ)*a.samples.expect (f z) = θ z := by
    intro z j
    rw [hmeans]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    field_simp
  have hvar : ∀ (z : Bool) (j : Fin (2*r+1)),
      ∑ b : Fin m, ((1 : ℝ)/(m : ℝ))^2 * a.samples.expect
        (fun i => (f z i - a.samples.expect (f z))^2) ≤ (ε/2)^2/16 := by
    intro z j
    change ∑ _ : Fin m, ((1 : ℝ)/(m : ℝ))^2 * a.samples.variance (f z) ≤ _
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    have heq : (m : ℝ)*((1 : ℝ)/(m : ℝ))^2*a.samples.variance (f z) =
        a.samples.variance (f z)/(m : ℝ) := by field_simp
    rw [← mul_assoc, heq]
    have hb : sqSquaredNorm a.envelope*sqSquaredNorm v/(m : ℝ) ≤ (ε/2)^2/16 := by
      apply (div_le_iff₀ hm').mpr
      nlinarith
    exact (div_le_div_of_nonneg_right (hvars z) hm'.le).trans hb
  have hmedian := heterogeneous_same_records_many_observables r m
    (fun _ _ => a.samples) (fun (_ : Bool) _ _ => (1 : ℝ)/(m : ℝ))
    (fun z _ _ i => f z i) θ (ε/2) (by linarith) hmean hvar
  simp only [Fintype.card_bool, Nat.cast_ofNat] at hmedian
  have hsub : (Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → X =>
      ε < ‖sqMedian a v m r ω-sqInnerTarget a.target v‖)) ⊆
      Finset.univ.filter (fun ω => ∃ z : Bool,
        ε/2 < |sortedBlockMedian r
          (weightedBlock r m (fun _ _ => (1 : ℝ)/(m : ℝ))
            (fun _ _ i => f z i) ω) - θ z|) := by
    intro ω hω
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hn
    have hn' : ∀ z : Bool, |sortedBlockMedian r
        (fun b => sqComponent z (sqMean a v (ω b))) - θ z| ≤ ε/2 := by
      intro z
      exact le_of_not_gt (fun hz => hn ⟨z, by
        simpa only [f, sq_component_weighted_block] using! hz⟩)
    have hre := hn' false
    have him := hn' true
    dsimp [θ, sqComponent] at hre him
    have hr2 : (sortedBlockMedian r (fun b => (sqMean a v (ω b)).re) -
        (sqInnerTarget a.target v).re)^2 ≤ (ε/2)^2 :=
      by
      simpa only [sq_abs] using! (sq_le_sq₀ (abs_nonneg _) (by linarith)).mpr hre
    have hi2 : (sortedBlockMedian r (fun b => (sqMean a v (ω b)).im) -
        (sqInnerTarget a.target v).im)^2 ≤ (ε/2)^2 := by
      simpa only [sq_abs] using! (sq_le_sq₀ (abs_nonneg _) (by linarith)).mpr him
    have heq : ‖sqMedian a v m r ω - sqInnerTarget a.target v‖^2 =
      (sortedBlockMedian r (fun b => (sqMean a v (ω b)).re) -
        (sqInnerTarget a.target v).re)^2 +
      (sortedBlockMedian r (fun b => (sqMean a v (ω b)).im) -
        (sqInnerTarget a.target v).im)^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [sqMedian, Complex.mul_re, Complex.mul_im, pow_two]
    have hbad := (Finset.mem_filter.mp hω).2
    nlinarith [norm_nonneg (sqMedian a v m r ω - sqInnerTarget a.target v)]
  have hlaw : ∀ ω : Fin (2*r+1) → Fin m → X,
      (blockRecordLaw r m (fun _ _ => a.samples)).prob ω =
        ∏ b, a.samples.probOf (ω b) := by
    intro ω
    rfl
  unfold sqBadMass
  calc _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ∃ z : Bool,
          ε/2 < |sortedBlockMedian r
            (weightedBlock r m (fun _ _ => (1 : ℝ)/(m : ℝ))
              (fun _ _ i => f z i) ω) - θ z|), ∏ b, a.samples.probOf (ω b) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ =>
          Finset.prod_nonneg fun b _ => Finset.prod_nonneg fun t _ => a.samples.nonneg _)
    _ ≤ _ := by
        simp only [hlaw, mul_assoc] at hmedian ⊢
        convert! hmedian using 1
        congr 1; ext; simp

/-- The value component of the counted summation fold is its initial value plus the sum of the
contributions. -/
private theorem sq_mean_fold_value {Y : Type} (f : Y → ℂ) (xs : List Y)
    (z : ℂ × List SQCall) :
    (xs.foldl (fun z t => (z.1 + f t,
      [.otherEntry,.envelopeEntry,.targetEntry,.sampleEnvelope] ++ z.2)) z).1 =
      z.1 + (xs.map f).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

/-- The call component of the summation fold prepends one fixed four-call list per input element
to the initial ledger. -/
private theorem sq_mean_fold_calls {Y : Type} (f : Y → ℂ) (xs : List Y)
    (z : ℂ × List SQCall) :
    (xs.foldl (fun z t => (z.1 + f t,
      [.otherEntry,.envelopeEntry,.targetEntry,.sampleEnvelope] ++ z.2)) z).2 =
      (List.replicate xs.length [.otherEntry,.envelopeEntry,.targetEntry,.sampleEnvelope]).flatten ++ z.2 := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, List.replicate_succ,
      List.flatten_cons, List.append_assoc]
    have hcomm : ∀ n : ℕ, ∀ l : List SQCall,
        (List.replicate n l).flatten ++ l = l ++ (List.replicate n l).flatten := by
      intro n l
      induction n with
      | zero => simp
      | succ n ih => simp [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]
    rw [← List.append_assoc, hcomm, List.append_assoc]

/-- The value returned by the counted block mean equals `sqMean` on the same sample record. -/
theorem sqMeanCounted_value {X : Type} [Fintype X] (a : FiniteSQInput X)
    (v : X → ℂ) {m : ℕ} (ω : Fin m → X) :
    (sqMeanCounted a v ω).1 = sqMean a v ω := by
  unfold sqMeanCounted sqMean
  (try dsimp only)
  rw [sq_mean_fold_value]
  simp [List.map_ofFn, List.sum_ofFn]

/-- Repeating and flattening a call list `n` times multiplies the count of each call category by
`n`. -/
private theorem sq_repeat_calls_count (l : List SQCall) (n : ℕ) (c : SQCall) :
    ((List.replicate n l).flatten).count c = n * l.count c := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.flatten_cons, List.count_append, ih, Nat.succ_mul, Nat.add_comm]

/-- Each call category in a counted block mean occurs `m` times its multiplicity in the
four-call contribution ledger. -/
theorem sqMeanCounted_calls_count {X : Type} [Fintype X] (a : FiniteSQInput X)
    (v : X → ℂ) {m : ℕ} (ω : Fin m → X) (c : SQCall) :
    (sqMeanCounted a v ω).2.count c =
      m * ([.otherEntry,.envelopeEntry,.targetEntry,.sampleEnvelope] : List SQCall).count c := by
  unfold sqMeanCounted
  rw [List.count_reverse, sq_mean_fold_calls]
  simp only [List.append_nil, sq_repeat_calls_count, List.length_ofFn]

/-- The count of a call category in a flattened family of ledgers is the sum of its counts in
the individual ledgers. -/
private theorem sq_count_flatten {Y : Type} (xs : List Y) (f : Y → List SQCall)
    (c : SQCall) : ((xs.map f).flatten).count c = (xs.map (fun x => (f x).count c)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.count_append, ih]

/-- The full access count is one envelope-norm query plus `m * (2 * r + 1)` copies of the
four-call contribution ledger. -/
theorem sqRunCalls_count {X : Type} [Fintype X] (a : FiniteSQInput X)
    (v : X → ℂ) (m r : ℕ) (ω : Fin (2*r+1) → Fin m → X) (c : SQCall) :
    (sqRunCalls a v m r ω).count c =
      (if c = .envelopeNorm then 1 else 0) +
        (2*r+1)*m*([.otherEntry,.envelopeEntry,.targetEntry,.sampleEnvelope] : List SQCall).count c := by
  unfold sqRunCalls
  have hfn : (List.ofFn (fun b : Fin (2*r+1) => (sqMeanCounted a v (ω b)).2)) =
      (List.ofFn (fun b : Fin (2*r+1) => b)).map (fun b => (sqMeanCounted a v (ω b)).2) := by
    rw [List.map_ofFn]
    rfl
  rw [List.count_cons, hfn, sq_count_flatten]
  rw [List.map_ofFn]
  simp only [Function.comp_apply, sqMeanCounted_calls_count, List.sum_ofFn,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  cases c <;> simp

/-- The zero-based order-statistic specification: the value occurs in the list, at most `k`
entries are strictly smaller, and more than `k` entries are at most the value. -/
def sqRank (xs : List ℝ) (k : ℕ) (v : ℝ) : Prop :=
  v ∈ xs ∧ xs.countP (fun x => decide (x < v)) ≤ k ∧
    k < xs.countP (fun x => decide (x ≤ v))

/-- For predicates ordered by implication on a list, the number of entries satisfying the first
predicate is bounded by the number satisfying the second. -/
private theorem sq_count_mono (xs : List ℝ) (P Q : ℝ → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ x ∈ xs, P x → Q x) :
    xs.countP (fun x => decide (P x)) ≤ xs.countP (fun x => decide (Q x)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.countP_cons]
    by_cases hp : P x <;> by_cases hq : Q x <;> simp_all; omega

/-- The entry at a valid zero-based index in a nondecreasing real list satisfies `sqRank` at
that index. -/
private theorem sq_sorted_rank (xs : List ℝ) (hs : xs.SortedLE)
    (k : ℕ) (hk : k < xs.length) : sqRank xs k (xs.getD k 0) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp (List.sortedLE_iff_pairwise.mp hs)
    cases k with
    | zero =>
      simp only [List.getD_cons_zero]
      have hz : xs.countP (fun y => decide (y < x)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro y hy
        simp only [Bool.not_eq_true, decide_eq_false_iff_not]
        exact not_lt_of_ge (hx y hy)
      simp [sqRank, hz]
    | succ k =>
      have hk' : k < xs.length := by simpa using! hk
      have hr := ih (List.sortedLE_iff_pairwise.mpr ht) k hk'
      have hrl := hr.2.1
      have hru := hr.2.2
      have hxv : x ≤ xs.getD k 0 := hx _ hr.1
      simp only [List.getD_cons_succ]
      refine ⟨List.mem_cons_of_mem _ hr.1, ?_, ?_⟩
      · simp only [List.countP_cons]
        split <;> omega
      · simp only [List.countP_cons, decide_eq_true hxv, if_true]
        omega

/-- Selecting a valid entry from the counted insertion-sort output gives the corresponding order
statistic of the original list. -/
theorem sq_insertion_rank (xs : List ℝ) (k : ℕ) (hk : k < xs.length) :
    sqRank xs k ((insertionSortCounted xs).1.getD k 0) := by
  have hp := insertionSortCounted_perm xs
  have h := sq_sorted_rank (insertionSortCounted xs).1 (insertionSortCounted_sorted xs)
    k (by simpa only [insertionSortCounted_length] using! hk)
  exact ⟨hp.mem_iff.mp h.1,
    (hp.countP_eq _).symm ▸ h.2.1, (hp.countP_eq _).symm ▸ h.2.2⟩

/-- Two values satisfying the same order-statistic specification for a real list and index are
equal. -/
theorem sqRank_unique {xs : List ℝ} {k : ℕ} {u v : ℝ}
    (hu : sqRank xs k u) (hv : sqRank xs k v) : u = v := by
  apply le_antisymm
  · by_contra h
    have hc := sq_count_mono xs (fun x => x ≤ v) (fun x => x < u)
      (fun x _ hx => lt_of_le_of_lt hx (lt_of_not_ge h))
    try dsimp only at hc
    have h1 := hu.2.1
    have h2 := hv.2.2
    omega
  · by_contra h
    have hc := sq_count_mono xs (fun x => x ≤ u) (fun x => x < v)
      (fun x _ hx => lt_of_le_of_lt hx (lt_of_not_ge h))
    try dsimp only at hc
    have h1 := hv.2.1
    have h2 := hu.2.2
    omega

/-- With fuel at least the list length, the groups of five reconstruct the list and are nonempty
with length at most five. Their number satisfies the stated ceiling bounds and is no greater
than the input length. -/
theorem sqChunks5_properties (fuel : ℕ) (xs : List ℝ) (hf : xs.length ≤ fuel) :
    (sqChunks5 fuel xs).flatten = xs ∧
    (∀ g ∈ sqChunks5 fuel xs, 0 < g.length ∧ g.length ≤ 5) ∧
    xs.length ≤ 5*(sqChunks5 fuel xs).length ∧
    5*(sqChunks5 fuel xs).length ≤ xs.length+4 ∧
    (sqChunks5 fuel xs).length ≤ xs.length := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    simp [sqChunks5]
  | succ fuel ih =>
    cases xs with
    | nil => simp [sqChunks5]
    | cons x xs =>
      have hd : ((x::xs).drop 5).length ≤ fuel := by simp only [List.length_drop]; omega
      have ht := ih ((x::xs).drop 5) hd
      simp only [sqChunks5, List.flatten_cons, ht.1, List.take_append_drop]
      refine ⟨True.intro, ?_, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · simp only [List.length_take, List.length_cons]
          constructor <;> omega
        · exact ht.2.1 g hg
      · have h := ht.2.2.1
        simp only [List.length_cons, List.length_drop] at h ⊢
        omega
      · by_cases hsmall : (x::xs).length ≤ 5
        · have hd0 : (x::xs).drop 5 = [] := List.drop_eq_nil_iff.mpr hsmall
          have hnil : sqChunks5 fuel [] = [] := by cases fuel <;> rfl
          simp only [hd0, hnil, List.length_nil, List.length_cons]
          omega
        · have h := ht.2.2.2.1
          simp only [List.length_cons, List.length_drop] at h ⊢
          omega
      · have h := ht.2.2.2.2
        simp only [List.length_cons, List.length_drop] at h ⊢
        omega

/-- The entry at index half the list length after counted insertion sort, using zero as the
default for an empty list. -/
noncomputable def sqGroupMedian (xs : List ℝ) : ℝ :=
  (insertionSortCounted xs).1.getD (xs.length/2) 0

/-- The list of group medians obtained by splitting the input into groups of at most five. -/
noncomputable def sqPivots (xs : List ℝ) : List ℝ :=
  (sqChunks5 xs.length xs).map sqGroupMedian

/-- For a nonempty list, its group median satisfies the order-statistic specification at index
half its length. -/
theorem sqGroupMedian_rank (xs : List ℝ) (hx : 0 < xs.length) :
    sqRank xs (xs.length/2) (sqGroupMedian xs) :=
  sq_insertion_rank xs (xs.length/2) (by omega)

/-- Every group median in the pivot list is an entry of the original list. -/
theorem sqPivots_mem {xs : List ℝ} {p : ℝ} (hp : p ∈ sqPivots xs) : p ∈ xs := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
  have hprops := sqChunks5_properties xs.length xs (le_refl _)
  have hm := (sqGroupMedian_rank g (hprops.2.1 g hg).1).1
  rw [← hprops.1]
  exact List.mem_flatten.mpr ⟨g, hg, hm⟩

/-- The pivot list has one entry for each group in the groups-of-five partition. -/
theorem sqPivots_length (xs : List ℝ) : (sqPivots xs).length = (sqChunks5 xs.length xs).length := by
  simp [sqPivots]

/-- The numbers of entries strictly below a pivot and at least the pivot sum to the list length. -/
private theorem sq_count_lt_ge (xs : List ℝ) (p : ℝ) :
    xs.countP (fun x => decide (x < p)) + xs.countP (fun x => decide (p ≤ x)) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases hx : x < p
    · simp [hx, not_le_of_gt hx]; omega
    · simp [hx, le_of_not_gt hx]; omega

/-- The numbers of entries at most a pivot and strictly above the pivot sum to the list length. -/
private theorem sq_count_le_gt (xs : List ℝ) (p : ℝ) :
    xs.countP (fun x => decide (x ≤ p)) + xs.countP (fun x => decide (p < x)) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases hx : x ≤ p
    · simp [hx, not_lt_of_ge hx]; omega
    · simp [hx, lt_of_not_ge hx]; omega

/-- The partition fold prepends the reversed filtered sublists to the initial partitions and
adds at most two comparisons per input entry. -/
private theorem sq_partition_fold (p : ℝ) (xs : List ℝ)
    (z : List ℝ × List ℝ × List ℝ × ℕ) :
    let q := xs.foldl (fun z x => if x < p then (x::z.1,z.2.1,z.2.2.1,z.2.2.2+1) else
      if p < x then (z.1,z.2.1,x::z.2.2.1,z.2.2.2+2) else
        (z.1,x::z.2.1,z.2.2.1,z.2.2.2+2)) z
    q.1 = (xs.filter (fun x => decide (x < p))).reverse ++ z.1 ∧
    q.2.1 = (xs.filter (fun x => decide (x = p))).reverse ++ z.2.1 ∧
    q.2.2.1 = (xs.filter (fun x => decide (p < x))).reverse ++ z.2.2.1 ∧
    q.2.2.2 ≤ z.2.2.2 + 2*xs.length := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hlt : x < p
    · simp only [if_pos hlt]
      have h := ih (x::z.1,z.2.1,z.2.2.1,z.2.2.2+1)
      have hn : ¬p < x := not_lt_of_ge hlt.le
      have hne : x ≠ p := hlt.ne
      simp only [List.filter_cons, decide_eq_true hlt, decide_eq_false hn,
        decide_eq_false hne, if_true, Bool.false_eq_true, if_false,
        List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons] at h ⊢
      exact ⟨h.1, h.2.1, h.2.2.1, by omega⟩
    · simp only [if_neg hlt]
      by_cases hgt : p < x
      · simp only [if_pos hgt]
        have h := ih (z.1,z.2.1,x::z.2.2.1,z.2.2.2+2)
        have hne : x ≠ p := Ne.symm hgt.ne
        simp only [List.filter_cons, decide_eq_false hlt, decide_eq_true hgt,
          decide_eq_false hne, if_true, Bool.false_eq_true, if_false,
          List.reverse_cons, List.append_assoc, List.singleton_append,
          List.length_cons] at h ⊢
        exact ⟨h.1, h.2.1, h.2.2.1, by omega⟩
      · simp only [if_neg hgt]
        have heq : x = p := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
        have h := ih (z.1,x::z.2.1,z.2.2.1,z.2.2.2+2)
        simp only [List.filter_cons, decide_eq_false hlt, decide_eq_false hgt,
          decide_eq_true heq, if_true, Bool.false_eq_true, if_false,
          List.reverse_cons, List.append_assoc, List.singleton_append,
          List.length_cons] at h ⊢
        exact ⟨h.1, h.2.1, h.2.2.1, by omega⟩

/-- The three partitions are the reversed filters below, equal to, and above the pivot, and the
comparison count is at most twice the input length. -/
theorem sqPartition_filters (p : ℝ) (xs : List ℝ) :
    (sqPartition p xs).1 = (xs.filter (fun x => decide (x < p))).reverse ∧
    (sqPartition p xs).2.1 = (xs.filter (fun x => decide (x = p))).reverse ∧
    (sqPartition p xs).2.2.1 = (xs.filter (fun x => decide (p < x))).reverse ∧
    (sqPartition p xs).2.2.2 ≤ 2*xs.length := by
  simpa [sqPartition] using! sq_partition_fold p xs ([],[],[],0)

/-- An order statistic of the reversed sublist below a pivot is the same-index order statistic
of the whole list. -/
private theorem sq_rank_left {xs : List ℝ} {p v : ℝ} {k : ℕ}
    (hr : sqRank (xs.filter (fun x => decide (x < p))).reverse k v) : sqRank xs k v := by
  have hm := List.mem_filter.mp (List.mem_reverse.mp hr.1)
  have hpv : v < p := of_decide_eq_true hm.2
  have hc1 : ((xs.filter (fun x => decide (x < p))).reverse).countP
      (fun x => decide (x < v)) = xs.countP (fun x => decide (x < v)) := by
    rw [List.countP_reverse, List.countP_filter]
    apply List.countP_congr
    intro x _
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, lt_trans h hpv⟩⟩
  have hc2 : ((xs.filter (fun x => decide (x < p))).reverse).countP
      (fun x => decide (x ≤ v)) = xs.countP (fun x => decide (x ≤ v)) := by
    rw [List.countP_reverse, List.countP_filter]
    apply List.countP_congr
    intro x _
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, lt_of_le_of_lt h hpv⟩⟩
  exact ⟨hm.1, hc1 ▸ hr.2.1, hc2 ▸ hr.2.2⟩

/-- For a value above the pivot, its strict and non-strict lower counts split into entries at
most the pivot and the corresponding counts in the upper partition. -/
private theorem sq_right_counts (xs : List ℝ) (p v : ℝ) (hv : p < v) :
    xs.countP (fun x => decide (x < v)) = xs.countP (fun x => decide (x ≤ p)) +
      (xs.filter (fun x => decide (p < x))).countP (fun x => decide (x < v)) ∧
    xs.countP (fun x => decide (x ≤ v)) = xs.countP (fun x => decide (x ≤ p)) +
      (xs.filter (fun x => decide (p < x))).countP (fun x => decide (x ≤ v)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x ≤ p
    · have hxv := lt_of_le_of_lt hx hv
      simp [hx, hxv, hxv.le, not_lt_of_ge hx, ih]
      omega
    · have hpx := lt_of_not_ge hx
      by_cases hxv : x < v <;> by_cases hxve : x ≤ v <;>
        simp [hx, hpx, hxv, hxve, ih] <;> omega

/-- An order statistic of the reversed upper partition lifts to the full list after adding the
number of entries at most the pivot to its index. -/
private theorem sq_rank_right {xs : List ℝ} {p v : ℝ} {k : ℕ}
    (hk : xs.countP (fun x => decide (x ≤ p)) ≤ k)
    (hr : sqRank (xs.filter (fun x => decide (p < x))).reverse
      (k-xs.countP (fun x => decide (x ≤ p))) v) : sqRank xs k v := by
  have hm := List.mem_filter.mp (List.mem_reverse.mp hr.1)
  have hpv : p < v := of_decide_eq_true hm.2
  have hc := sq_right_counts xs p v hpv
  have hrl := hr.2.1
  have hru := hr.2.2
  rw [List.countP_reverse] at hrl hru
  exact ⟨hm.1, by omega, by omega⟩

/-- The number of entries below a pivot plus the number equal to it is the number at most the
pivot. -/
private theorem sq_count_lt_eq_le (xs : List ℝ) (p : ℝ) :
    xs.countP (fun x => decide (x < p)) + xs.countP (fun x => decide (x = p)) =
      xs.countP (fun x => decide (x ≤ p)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases lt_trichotomy x p with hx | hx | hx
    · simp only [List.countP_cons, decide_eq_true hx, decide_eq_false hx.ne,
        decide_eq_true hx.le, if_true, Bool.false_eq_true, if_false]
      omega
    · subst x
      simp only [List.countP_cons, lt_self_iff_false, decide_false, decide_true,
        le_refl, if_true, Bool.false_eq_true, if_false]
      omega
    · have hn := not_lt_of_ge hx.le
      have hne := Ne.symm hx.ne
      have hnle := not_le_of_gt hx
      simp only [List.countP_cons, decide_eq_false hn, decide_eq_false hne,
        decide_eq_false hnle, Bool.false_eq_true, if_false]
      exact ih

/-- The partition lengths recover the strict and non-strict lower counts, and the three lengths
sum to the input length. -/
private theorem sq_partition_lengths (xs : List ℝ) (p : ℝ) :
    (sqPartition p xs).1.length = xs.countP (fun x => decide (x < p)) ∧
    (sqPartition p xs).1.length + (sqPartition p xs).2.1.length =
      xs.countP (fun x => decide (x ≤ p)) ∧
    (sqPartition p xs).1.length + (sqPartition p xs).2.1.length +
      (sqPartition p xs).2.2.1.length = xs.length := by
  have hf := sqPartition_filters p xs
  rw [hf.1, hf.2.1, hf.2.2.1]
  simp only [List.length_reverse, ← List.countP_eq_length_filter]
  have heq := sq_count_lt_eq_le xs p
  exact ⟨True.intro, heq, by rw [heq]; exact sq_count_le_gt xs p⟩

/-- For any fuel and valid index, the value returned by the counted selector satisfies the
requested order-statistic specification. -/
theorem sqSelectFuel_rank (fuel : ℕ) (xs : List ℝ) (k : ℕ) (hk : k < xs.length) :
    sqRank xs k (sqSelectFuel fuel xs k).1 := by
  induction fuel generalizing xs k with
  | zero => exact sq_insertion_rank xs k hk
  | succ fuel ih =>
    by_cases hs : xs.length ≤ 1000
    · simpa only [sqSelectFuel, if_pos hs] using! sq_insertion_rank xs k hk
    · have hprops := sqChunks5_properties xs.length xs (le_refl _)
      have hg : 0 < (sqPivots xs).length := by
        rw [sqPivots_length]
        have h := hprops.2.2.1
        omega
      have hp := ih (sqPivots xs) ((sqPivots xs).length/2) (by omega)
      let p := (sqSelectFuel fuel (sqPivots xs) ((sqPivots xs).length/2)).1
      have hpm : p ∈ xs := sqPivots_mem hp.1
      have hlen := sq_partition_lengths xs p
      have hf := sqPartition_filters p xs
      have hpiv : ((sqChunks5 xs.length xs).map insertionSortCounted).map
          (fun z => z.1.getD (z.1.length/2) 0) = sqPivots xs := by
        rw [List.map_map]
        unfold sqPivots
        apply List.map_congr_left
        intro g _
        simp [sqGroupMedian, insertionSortCounted_length]
      rw [sqSelectFuel, if_neg hs]
      simp only [hpiv]
      split_ifs with hl he
      · change k < (sqPartition p xs).1.length at hl
        change sqRank xs k (sqSelectFuel fuel (sqPartition p xs).1 k).1
        apply sq_rank_left (p := p)
        rw [← hf.1]
        exact ih (sqPartition p xs).1 k hl
      · change ¬k < (sqPartition p xs).1.length at hl
        change k < (sqPartition p xs).1.length+(sqPartition p xs).2.1.length at he
        change sqRank xs k p
        refine ⟨hpm, ?_, ?_⟩
        · rw [← hlen.1]; omega
        · rw [← hlen.2.1]; exact he
      · change ¬k < (sqPartition p xs).1.length at hl
        change ¬k < (sqPartition p xs).1.length+(sqPartition p xs).2.1.length at he
        change sqRank xs k (sqSelectFuel fuel (sqPartition p xs).2.2.1
          (k-(sqPartition p xs).1.length-(sqPartition p xs).2.1.length)).1
        have hsum := hlen.2.2
        have hoff := hlen.2.1
        have hr := ih (sqPartition p xs).2.2.1
          (k-(sqPartition p xs).1.length-(sqPartition p xs).2.1.length) (by omega)
        have hshift : k-(sqPartition p xs).1.length-(sqPartition p xs).2.1.length =
            k-xs.countP (fun x => decide (x ≤ p)) := by omega
        apply sq_rank_right (p := p) (by omega)
        rw [← hf.2.2.1, ← hshift]
        exact hr

/-- A nonempty group has at least `length / 2 + 1` entries at most its median and at least
`length - length / 2` entries at least its median. -/
private theorem sq_group_sides (g : List ℝ) (hg : 0 < g.length) :
    g.length/2+1 ≤ g.countP (fun x => decide (x ≤ sqGroupMedian g)) ∧
    g.length-g.length/2 ≤ g.countP (fun x => decide (sqGroupMedian g ≤ x)) := by
  have hr := sqGroupMedian_rank g hg
  have hc := sq_count_lt_ge g (sqGroupMedian g)
  have hrl := hr.2.1
  have hru := hr.2.2
  exact ⟨by omega, by omega⟩

/-- For groups of five, three times the count of medians on either closed side of a pivot is
bounded by the original count on that side plus two. -/
private theorem sq_chunks_discard (fuel : ℕ) (xs : List ℝ) (hf : xs.length ≤ fuel) (p : ℝ) :
    3*((sqChunks5 fuel xs).map sqGroupMedian).countP (fun v => decide (v ≤ p)) ≤
      xs.countP (fun x => decide (x ≤ p))+2 ∧
    3*((sqChunks5 fuel xs).map sqGroupMedian).countP (fun v => decide (p ≤ v)) ≤
      xs.countP (fun x => decide (p ≤ x))+2 := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    simp [sqChunks5]
  | succ fuel ih =>
    cases xs with
    | nil => simp [sqChunks5]
    | cons x xs =>
      simp only [List.length_cons] at hf
      let g := (x::xs).take 5
      let tail := (x::xs).drop 5
      have hg : 0 < g.length := by simp only [g, List.length_take, List.length_cons]; omega
      have htlen : tail.length ≤ fuel := by
        simp only [tail, List.length_drop, List.length_cons]; omega
      have hsides := sq_group_sides g hg
      have htakeL : g.countP (fun x => decide (x ≤ p)) ≤ (x::xs).countP (fun x => decide (x ≤ p)) :=
        List.Sublist.countP_le (List.take_sublist _ _)
      have htakeR : g.countP (fun x => decide (p ≤ x)) ≤ (x::xs).countP (fun x => decide (p ≤ x)) :=
        List.Sublist.countP_le (List.take_sublist _ _)
      simp only [List.countP_cons] at htakeL htakeR
      simp only [sqChunks5, List.map_cons, List.countP_cons]
      change 3*(((sqChunks5 fuel tail).map sqGroupMedian).countP (fun v => decide (v ≤ p)) +
          (if decide (sqGroupMedian g ≤ p) then 1 else 0)) ≤
          _ ∧
        3*(((sqChunks5 fuel tail).map sqGroupMedian).countP (fun v => decide (p ≤ v)) +
          (if decide (p ≤ sqGroupMedian g) then 1 else 0)) ≤
          _
      by_cases hsmall : (x::xs).length ≤ 5
      · have ht : tail = [] := List.drop_eq_nil_iff.mpr hsmall
        have hnil : sqChunks5 fuel [] = [] := by cases fuel <;> rfl
        simp only [ht, hnil, List.map_nil, List.countP_nil, zero_add]
        constructor
        · by_cases hm : sqGroupMedian g ≤ p
          · have hc := sq_count_mono g (fun y => y ≤ sqGroupMedian g) (fun y => y ≤ p)
              (fun y _ hy => hy.trans hm)
            try dsimp only at hc
            simp only [decide_eq_true hm, if_true]
            have h := hsides.1
            omega
          · simp [hm]
        · by_cases hm : p ≤ sqGroupMedian g
          · have hc := sq_count_mono g (fun y => sqGroupMedian g ≤ y) (fun y => p ≤ y)
              (fun y _ hy => hm.trans hy)
            try dsimp only at hc
            simp only [decide_eq_true hm, if_true]
            have h := hsides.2
            have hgl : 0 < g.length-g.length/2 := by omega
            omega
          · simp [hm]
      · have hgl : g.length = 5 := by simp only [g, List.length_take]; omega
        have ht := ih tail htlen
        have hL : (x::xs).countP (fun y => decide (y ≤ p)) =
            g.countP (fun y => decide (y ≤ p)) + tail.countP (fun y => decide (y ≤ p)) := by
          rw [← List.countP_append, List.take_append_drop]
        have hR : (x::xs).countP (fun y => decide (p ≤ y)) =
            g.countP (fun y => decide (p ≤ y)) + tail.countP (fun y => decide (p ≤ y)) := by
          rw [← List.countP_append, List.take_append_drop]
        simp only [List.countP_cons] at hL hR
        constructor
        · have htail := ht.1
          by_cases hm : sqGroupMedian g ≤ p
          · have hc := sq_count_mono g (fun y => y ≤ sqGroupMedian g) (fun y => y ≤ p)
              (fun y _ hy => hy.trans hm)
            try dsimp only at hc
            simp only [decide_eq_true hm, if_true]
            have h := hsides.1
            rw [hgl] at h
            omega
          · simp only [decide_eq_false hm, Bool.false_eq_true, if_false]
            omega
        · have htail := ht.2
          by_cases hm : p ≤ sqGroupMedian g
          · have hc := sq_count_mono g (fun y => sqGroupMedian g ≤ y) (fun y => p ≤ y)
              (fun y _ hy => hm.trans hy)
            try dsimp only at hc
            simp only [decide_eq_true hm, if_true]
            have h := hsides.2
            rw [hgl] at h
            omega
          · simp only [decide_eq_false hm, Bool.false_eq_true, if_false]
            omega

/-- A median of the group medians bounds the combined pivot-list and either strict partition
size by the stated inequality `10 * size ≤ 9 * xs.length + 70`. -/
private theorem sq_partition_shrink (xs : List ℝ) (p : ℝ)
    (hr : sqRank (sqPivots xs) ((sqPivots xs).length/2) p) :
    10*((sqPivots xs).length + (sqPartition p xs).1.length) ≤ 9*xs.length+70 ∧
    10*((sqPivots xs).length + (sqPartition p xs).2.2.1.length) ≤ 9*xs.length+70 := by
  have hprops := sqChunks5_properties xs.length xs (le_refl _)
  have hng : xs.length ≤ 5*(sqPivots xs).length := by
    simpa only [sqPivots_length] using! hprops.2.2.1
  have hc := sq_chunks_discard xs.length xs (le_refl _) p
  change 3*(sqPivots xs).countP (fun v => decide (v ≤ p)) ≤ _ ∧
    3*(sqPivots xs).countP (fun v => decide (p ≤ v)) ≤ _ at hc
  have hpl := hr.2.1
  have hpu := hr.2.2
  have hpg := sq_count_lt_ge (sqPivots xs) p
  have hxsge := sq_count_lt_ge xs p
  have hlen := sq_partition_lengths xs p
  have hcl := hc.1
  have hcr := hc.2
  have hl := hlen.1
  have hoff := hlen.2.1
  have hsum := hlen.2.2
  constructor <;> omega

/-- Sorting groups of at most five by counted insertion sort costs at most 25 comparisons per
group in total. -/
private theorem sq_groups_sort_cost (gs : List (List ℝ))
    (hg : ∀ g ∈ gs, g.length ≤ 5) :
    ((gs.map insertionSortCounted).map Prod.snd).sum ≤ 25*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hlen := hg g (by simp)
    have hcost := insertionSortCounted_cost_le g
    have htail := ih (fun g hg' => hg g (by simp [hg']))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- With fuel at least the input length and a valid index, the counted selector uses at most
10000 times the input length comparisons. -/
theorem sqSelectFuel_cost (fuel : ℕ) (xs : List ℝ) (k : ℕ)
    (hf : xs.length ≤ fuel) (hk : k < xs.length) :
    (sqSelectFuel fuel xs k).2 ≤ 10000*xs.length := by
  induction fuel generalizing xs k with
  | zero => omega
  | succ fuel ih =>
    by_cases hs : xs.length ≤ 1000
    · rw [sqSelectFuel, if_pos hs]
      have hcost := insertionSortCounted_cost_le xs
      (try dsimp only)
      nlinarith
    · have hprops := sqChunks5_properties xs.length xs (le_refl _)
      have hg : 0 < (sqPivots xs).length := by
        rw [sqPivots_length]
        have h := hprops.2.2.1
        omega
      have hgl : (sqPivots xs).length ≤ fuel := by
        rw [sqPivots_length]
        have h := hprops.2.2.2.1
        omega
      have hkm : (sqPivots xs).length/2 < (sqPivots xs).length := by omega
      have hpcost := ih (sqPivots xs) ((sqPivots xs).length/2) hgl hkm
      have hprank := sqSelectFuel_rank fuel (sqPivots xs) ((sqPivots xs).length/2) hkm
      let p := (sqSelectFuel fuel (sqPivots xs) ((sqPivots xs).length/2)).1
      have hshrink := sq_partition_shrink xs p hprank
      have hsort := sq_groups_sort_cost (sqChunks5 xs.length xs)
        (fun g hg' => (hprops.2.1 g hg').2)
      have hglen : (sqPivots xs).length ≤ xs.length := by
        simpa only [sqPivots_length] using! hprops.2.2.2.2
      have hsort' : ((List.map insertionSortCounted (sqChunks5 xs.length xs)).map Prod.snd).sum ≤
          25*xs.length := by
        rw [sqPivots_length] at hglen
        omega
      have hpart := (sqPartition_filters p xs).2.2.2
      have hlshrink := hshrink.1
      have hrshrink := hshrink.2
      have hlcost : ∀ k, k < (sqPartition p xs).1.length →
          (sqSelectFuel fuel (sqPartition p xs).1 k).2 ≤ 10000*(sqPartition p xs).1.length := by
        intro j hj
        apply ih _ j (by omega) hj
      have hrcost : ∀ k, k < (sqPartition p xs).2.2.1.length →
          (sqSelectFuel fuel (sqPartition p xs).2.2.1 k).2 ≤ 10000*(sqPartition p xs).2.2.1.length := by
        intro j hj
        apply ih _ j (by omega) hj
      have hpiv : ((sqChunks5 xs.length xs).map insertionSortCounted).map
          (fun z => z.1.getD (z.1.length/2) 0) = sqPivots xs := by
        rw [List.map_map]
        unfold sqPivots
        apply List.map_congr_left
        intro g _
        simp [sqGroupMedian, insertionSortCounted_length]
      rw [sqSelectFuel, if_neg hs]
      simp only [hpiv]
      split_ifs with hl he
      · change k < (sqPartition p xs).1.length at hl
        have hchild := hlcost k hl
        change _ + _ + (sqPartition p xs).2.2.2 +
          (sqSelectFuel fuel (sqPartition p xs).1 k).2 ≤ _
        omega
      · change _ + _ + (sqPartition p xs).2.2.2 ≤ _
        omega
      · change ¬k < (sqPartition p xs).1.length at hl
        change ¬k < (sqPartition p xs).1.length+(sqPartition p xs).2.1.length at he
        have hlen := (sq_partition_lengths xs p).2.2
        have hchild :=
            hrcost (k-(sqPartition p xs).1.length-(sqPartition p xs).2.1.length) (by omega)
        change _ + _ + (sqPartition p xs).2.2.2 +
          (sqSelectFuel fuel (sqPartition p xs).2.2.1
            (k-(sqPartition p xs).1.length-(sqPartition p xs).2.1.length)).2 ≤ _
        omega

/-- At a valid index, `sqSelect` returns the requested order statistic and uses at most 10000
comparisons per input element. -/
theorem sqSelect_rank_and_cost (xs : List ℝ) (k : ℕ) (hk : k < xs.length) :
    sqRank xs k (sqSelect xs k).1 ∧ (sqSelect xs k).2 ≤ 10000*xs.length :=
  ⟨sqSelectFuel_rank xs.length xs k hk, sqSelectFuel_cost xs.length xs k (le_refl _) hk⟩

/-- Selecting index `r` from the list of `2 * r + 1` values returns their sorted block median. -/
theorem sqSelect_ofFn_median (r : ℕ) (v : Fin (2*r+1) → ℝ) :
    (sqSelect (List.ofFn v) r).1 = sortedBlockMedian r v := by
  apply sqRank_unique (sqSelect_rank_and_cost _ r (by simp; omega)).1
    (sq_insertion_rank _ r (by simp; omega))

/-- The counted means and median equal their mathematical estimators, with one envelope-norm
query and `(2*r+1)*m` calls of each contribution category. The componentwise median costs at
most `20000*(2*r+1)` comparisons, and the general selector satisfies its rank specification
and linear bound; these implement the estimator of [Chia et al., Lemma 4.12][ChiaEtAl2022]. -/
theorem finite_sq_linear_median_and_actual_query_ledger (X : Type) [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) (m r : ℕ)
    (ω : Fin (2*r+1) → Fin m → X) :
    (∀ b, (sqMeanCounted a v (ω b)).1 = sqMean a v (ω b)) ∧
    (sqRunCalls a v m r ω).count .envelopeNorm = 1 ∧
    (sqRunCalls a v m r ω).count .sampleEnvelope = (2*r+1)*m ∧
    (sqRunCalls a v m r ω).count .targetEntry = (2*r+1)*m ∧
    (sqRunCalls a v m r ω).count .envelopeEntry = (2*r+1)*m ∧
    (sqRunCalls a v m r ω).count .otherEntry = (2*r+1)*m ∧
    (sqMedianCounted a v m r ω).1 = sqMedian a v m r ω ∧
    (sqMedianCounted a v m r ω).2 ≤ 20000*(2*r+1) ∧
    (∀ (xs : List ℝ) (k : ℕ), k < xs.length →
      (sqSelect xs k).1 ∈ xs ∧
      xs.countP (fun x => decide (x < (sqSelect xs k).1)) ≤ k ∧
      k < xs.countP (fun x => decide (x ≤ (sqSelect xs k).1)) ∧
      (sqSelect xs k).2 ≤ 10000*xs.length) := by
  refine ⟨fun b => sqMeanCounted_value a v (ω b), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sqRunCalls_count]
  · simp [sqRunCalls_count]
  · simp [sqRunCalls_count]
  · simp [sqRunCalls_count]
  · simp [sqRunCalls_count]
  · simp only [sqMedianCounted, sqMedian, sqSelect_ofFn_median]
  · have hre := (sqSelect_rank_and_cost (List.ofFn (fun b => (sqMean a v (ω b)).re)) r
      (by simp; omega)).2
    have him := (sqSelect_rank_and_cost (List.ofFn (fun b => (sqMean a v (ω b)).im)) r
      (by simp; omega)).2
    simp only [List.length_ofFn] at hre him
    change _ + _ ≤ _
    omega
  · intro xs k hk
    have h := sqSelect_rank_and_cost xs k hk
    exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩

end Qatlib.Concepts.SqEstimation.InnerProduct
