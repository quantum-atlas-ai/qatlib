/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SqEstimation.HierarchicalSQ.NativeCoefficientChoice
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Hierarchical sample-and-query closure

This module constructs prepared coefficient mixtures, outer-product sampling, and hierarchical
row-then-column sampling for linear combinations of matrices. It formalizes envelope domination,
actual sampling laws, and resource accounting associated with the sample-and-query closure
results in [ChiaEtAl2022].

`closurePrepare` caches weighted coefficient data with operation counters. The bounded and
unbounded matrix samplers then combine row and conditional column draws, with explicit timeout
probabilities and expected resource bounds.

## Main statements

* `native_sq_preparation_and_point_query_ledger`: proves preparation and point-query accounting.
* `native_sq_outer_product_access`: factors outer-product norms and sampling probabilities.
* `native_sq_hierarchical_matrix_lcu_actual_access`: collects envelope bounds, sampling laws,
  timeout estimates, and expected costs for matrix linear combinations.

## References

* [Chia et al., 2022, Lemmas 3.8–3.9][ChiaEtAl2022]
-/

set_option autoImplicit false
open Matrix
open scoped Classical BigOperators ENNReal ComplexOrder
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.SqEstimation.HierarchicalSQ

/-- Cached mixture preparation data containing weights in list and array form, their maximum and
sum, and counts of norm queries and coefficient, comparison, and addition operations. -/
structure ClosurePreparation where
  reverseWeights : List ℝ
  weights : Array ℝ
  maxWeight : ℝ
  sumWeight : ℝ
  normQueries : ℕ
  coefficientOperations : ℕ
  maxComparisons : ℕ
  sumAdditions : ℕ
/-- Prepare the weights `Complex.normSq (coeff t) * W t`, their maximum with initial value zero,
their sum, and one count of each recorded operation per coefficient. -/
noncomputable def closurePrepare {τ : ℕ} (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) : ClosurePreparation :=
  let z : ClosurePreparation := (List.ofFn (fun t : Fin τ => t)).foldl (fun z t =>
    let w := Complex.normSq (coeff t)*W t
    ⟨w::z.reverseWeights,z.weights,max z.maxWeight w,z.sumWeight+w,z.normQueries+1,
      z.coefficientOperations+1,z.maxComparisons+1,z.sumAdditions+1⟩) ⟨[],#[],0,0,0,0,0,0⟩
  {z with weights := z.reverseWeights.reverse.toArray}
/-- Read a prepared weight at index `t`, returning zero if the array index is out of bounds. -/
noncomputable def closurePreparedWeight {τ : ℕ} (z : ClosurePreparation) (t : Fin τ) : ℝ :=
  z.weights.getD t.val 0
/-- The bounded coefficient-choice run using cached weights and their maximum, returning the
initial configuration when the cached maximum is zero. -/
noncomputable def closureChoicePreparedRun {τ : ℕ} (rand : ClosureNativeRandom)
    (z : ClosurePreparation) (T : ℕ) : CostedLaw (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration Unit (Fin τ)) :=
  if z.maxWeight=0 then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inr ()) else
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor (closureChoiceNext rand (closurePreparedWeight z) z.maxWeight) T (.inr ())
/-- The unbounded coefficient-choice law using the cached weights and maximum. -/
noncomputable def closureChoicePreparedUnbounded {τ : ℕ} (rand : ClosureNativeRandom)
    (z : ClosurePreparation) : PMF (Option (Fin τ × ℕ)) :=
  generalUnboundedLaw (closureChoiceNext rand (closurePreparedWeight z) z.maxWeight) (.inr ())

/-- Draw from the native distribution at a coefficient selected by the bounded prepared run,
recording failure or an output together with its costs. -/
noncomputable def closureDrawPrepared {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (z : ClosurePreparation) (T : ℕ) (native : Fin τ → FinDist X) :
    PMF (ClosureDrawResult X) :=
  PMF.bind (closureChoicePreparedRun rand z T) (fun a => match a.1 with
    | .inr _ => PMF.pure (none,a.2,0,0)
    | .inl t => (closurePMF (native t)).map (fun x => (some x,a.2,1,0)))
/-- Draw from a native distribution after an unbounded prepared coefficient choice, recording
the chosen value and resource counts. -/
noncomputable def closureDrawPreparedUnbounded {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (z : ClosurePreparation) (native : Fin τ → FinDist X) :
    PMF (ClosureDrawResult X) :=
  PMF.bind (closureChoicePreparedUnbounded rand z) (fun a => match a with
    | none => PMF.pure (none,0,0,0)
    | some (t,k) => (closurePMF (native t)).map (fun x => (some x,k,1,0)))

/-- The coefficient mixture weights `Complex.normSq (coeff t) * W t`. -/
noncomputable def closureWeights {τ : ℕ} (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) : Fin τ → ℝ :=
  fun t => Complex.normSq (coeff t)*W t
/-- The product law obtained by drawing independently from finite distributions `p` and `q`. -/
noncomputable def closureOuterSample {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (p : FinDist X) (q : FinDist Y) : PMF (X × Y) :=
  (closurePMF p).bind (fun x => (closurePMF q).map (fun y => (x,y)))
/-- The outer-product function `(x, y) ↦ u x * star (v y)`. -/
noncomputable def closureOuter {X Y : Type} (u : X → ℂ) (v : Y → ℂ) : X × Y → ℂ :=
  fun p => u p.1*star (v p.2)

/-- The sum of squared entry norms in row `i` of a matrix. -/
noncomputable def closureRowSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) : ℝ :=
  ∑ j, Complex.normSq (A i j)
/-- The squared Frobenius norm expressed as the sum of `closureRowSq` over all rows. -/
noncomputable def closureFrobSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
    ∑ i, closureRowSq A i
/-- The matrix linear combination with entries `∑ t, coeff t * A t i j`. -/
noncomputable def closureMatrixTarget {τ m n : ℕ} (coeff : Fin τ → ℂ)
    (A : Fin τ → Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => ∑ t, coeff t*A t i j
/-- The squared envelope value `τ * ∑ t, Complex.normSq (coeff t * A t i j)` at an entry. -/
noncomputable def closureMatrixEnvelopeSq {τ m n : ℕ} (coeff : Fin τ → ℂ)
    (A : Fin τ → Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) : ℝ :=
  (τ:ℝ)*∑ t, Complex.normSq (coeff t*A t i j)
/-- The coefficient weights `Complex.normSq (coeff t) * R t i` for conditional sampling in row
`i`. -/
noncomputable def closureRowWeights {τ m : ℕ} (coeff : Fin τ → ℂ)
    (R : Fin τ → Fin m → ℝ) (i : Fin m) : Fin τ → ℝ :=
  fun t => Complex.normSq (coeff t)*R t i
/-- The bounded hierarchical matrix draw that first samples a row, prepares its conditional
weights, and samples a column, recording the combined costs. -/
noncomputable def closureMatrixDraw {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n))
    (Trow Tcol : ℕ) : PMF (ClosureDrawResult (Fin m × Fin n)) :=
  let globalCache := closurePrepare coeff W
  PMF.bind (closureDrawPrepared rand globalCache Trow rows) (fun z => match z.1 with
    | none => PMF.pure (none,z.2.1,z.2.2.1,z.2.2.2)
    | some i =>
      let rowCache := closurePrepare coeff (fun t => R t i)
      (closureDrawPrepared rand rowCache Tcol (fun t => cols t i)).map
      (fun y => (y.1.map (fun j => (i,j)),z.2.1+y.2.1,z.2.2.1+y.2.2.1,z.2.2.2+y.2.2.2+rowCache.normQueries)))
/-- The unbounded hierarchical matrix draw using prepared global and conditional row weights and
recording combined resource counts. -/
noncomputable def closureMatrixUnboundedDraw {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n)) :
    PMF (ClosureDrawResult (Fin m × Fin n)) :=
  let globalCache := closurePrepare coeff W
  PMF.bind (closureDrawPreparedUnbounded rand globalCache rows) (fun z => match z.1 with
    | none => PMF.pure (none,z.2.1,z.2.2.1,z.2.2.2)
    | some i =>
      let rowCache := closurePrepare coeff (fun t => R t i)
      (closureDrawPreparedUnbounded rand rowCache (fun t => cols t i)).map
      (fun y => (y.1.map (fun j => (i,j)),z.2.1+y.2.1,z.2.2.1+y.2.2.1,z.2.2.2+y.2.2.2+rowCache.normQueries)))
/-- The real probability that the bounded hierarchical matrix draw returns the entry `(i, j)`. -/
noncomputable def closureMatrixMass {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n))
    (Trow Tcol : ℕ) (i : Fin m) (j : Fin n) : ℝ :=
  (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixDraw rand coeff W R rows cols Trow Tcol)
    (fun z => z.1=some (i,j))).toReal

/-- Compute an entry of the matrix linear combination while counting one read per source matrix. -/
noncomputable def closureMatrixQuery {τ m n : ℕ} (coeff : Fin τ → ℂ)
    (A : Fin τ → Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) : ℂ × ℕ :=
  (List.ofFn (fun t : Fin τ => t)).foldl (fun z t => (z.1+coeff t*A t i j,z.2+1)) (0,0)
/-- Compute the nonnegative square root of the entry's squared envelope, cast to `ℂ`, while
counting source reads. -/
noncomputable def closureMatrixEnvelopeQuery {τ m n : ℕ} (coeff : Fin τ → ℂ)
    (A : Fin τ → Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) : ℂ × ℕ :=
  let z := (List.ofFn (fun t : Fin τ => t)).foldl
    (fun z t => (z.1+Complex.normSq (coeff t*A t i j),z.2+1)) ((0:ℝ),0)
  ((Real.sqrt ((τ:ℝ)*z.1):ℂ),z.2)

/-- Expand the preparation fold into the reversed weight list, maximum and sum updates, and
operation counts increased by the list length. -/
private theorem closure_prepare_fold {Y : Type} (f : Y → ℝ) (xs : List Y)
    (z : ClosurePreparation) :
    xs.foldl (fun z t => let w := f t
      ⟨w::z.reverseWeights,z.weights,max z.maxWeight w,z.sumWeight+w,z.normQueries+1,
        z.coefficientOperations+1,z.maxComparisons+1,z.sumAdditions+1⟩) z =
      ⟨(xs.map f).reverse++z.reverseWeights,z.weights,(xs.map f).foldl max z.maxWeight,
        z.sumWeight+(xs.map f).sum,z.normQueries+xs.length,z.coefficientOperations+xs.length,
        z.maxComparisons+xs.length,z.sumAdditions+xs.length⟩ := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp [List.reverse_cons, List.append_assoc, add_assoc, Nat.add_comm]

/-- A counted additive fold returns the initial value plus the mapped list sum and increases the
read count by the list length. -/
private theorem closure_sum_counted_fold {Y V : Type} [AddCommMonoid V]
    (f : Y → V) (xs : List Y) (v : V) (reads : ℕ) :
    xs.foldl (fun z t => (z.1+f t,z.2+1)) (v,reads) = (v+(xs.map f).sum,reads+xs.length) := by
  induction xs generalizing v reads with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, add_assoc, Nat.add_comm]

/-- Preparation stores the coefficient weights, their maximum and sum, and exactly `τ` of each
recorded operation; target and envelope point queries return their specified values with `τ`
source reads. This gives the preparation and query ledger associated with [Chia et al.,
Lemma 3.9][ChiaEtAl2022]. -/
theorem native_sq_preparation_and_point_query_ledger (τ : ℕ)
    (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) :
    (closurePrepare coeff W).reverseWeights.reverse = List.ofFn (closureWeights coeff W) ∧
    (closurePrepare coeff W).weights.toList = List.ofFn (closureWeights coeff W) ∧
    (closurePrepare coeff W).maxWeight = closureMax (closureWeights coeff W) ∧
    (closurePrepare coeff W).sumWeight = closureSum (closureWeights coeff W) ∧
    (closurePrepare coeff W).normQueries = τ ∧ (closurePrepare coeff W).coefficientOperations = τ ∧
    (closurePrepare coeff W).maxComparisons = τ ∧ (closurePrepare coeff W).sumAdditions = τ ∧
    (∀ (m n : ℕ) (A : Fin τ → Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n),
      (closureMatrixQuery coeff A i j).1 = closureMatrixTarget coeff A i j ∧
      (closureMatrixQuery coeff A i j).2 = τ ∧
      (closureMatrixEnvelopeQuery coeff A i j).1 = (Real.sqrt (closureMatrixEnvelopeSq coeff A i j) : ℂ) ∧
      (closureMatrixEnvelopeQuery coeff A i j).2 = τ) := by
  have hmap : (List.ofFn (fun t : Fin τ => t)).map (fun t => Complex.normSq (coeff t)*W t) =
      List.ofFn (closureWeights coeff W) := by rw [List.map_ofFn]; rfl
  have hprep : closurePrepare coeff W =
      ⟨(List.ofFn (closureWeights coeff W)).reverse,(List.ofFn (closureWeights coeff W)).toArray,
        closureMax (closureWeights coeff W),closureSum (closureWeights coeff W),τ,τ,τ,τ⟩ := by
    unfold closurePrepare
    rw [closure_prepare_fold, hmap]
    simp [closureMax, closureSum, List.sum_ofFn]
  rw [hprep]
  refine ⟨by simp, by simp, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro m n A i j
  simp [closureMatrixQuery, closureMatrixEnvelopeQuery, closure_sum_counted_fold,
    List.map_ofFn, List.sum_ofFn, closureMatrixTarget, closureMatrixEnvelopeSq]

/-- The squared norm of the outer-product function is the product of the squared norms of its
factors. -/
theorem closureOuter_normSq {X Y : Type} [Fintype X] [Fintype Y] (u : X → ℂ) (v : Y → ℂ) :
    closureNormSq (closureOuter u v) = closureNormSq u*closureNormSq v := by
  simp only [closureNormSq, closureOuter, Fintype.sum_prod_type, Complex.normSq_mul,
    Complex.star_def, Complex.normSq_conj]
  rw [Finset.sum_mul_sum]

/-- The finite sum of squared complex norms `closureNormSq u` is nonnegative. -/
theorem closureNormSq_nonneg {X : Type} [Fintype X] (u : X → ℂ) :
    0 ≤ closureNormSq u := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The mass of an outer-product sample at `(i, j)` is the product of the two marginal PMF
masses. -/
private theorem closureOuterSample_apply {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (p : FinDist X) (q : FinDist Y) (i : X) (j : Y) :
    closureOuterSample p q (i,j) = closurePMF p i*closurePMF q j := by
  simp [closureOuterSample, PMF.bind_apply, PMF.map_apply, tsum_fintype, ite_and]

/-- Under positive envelope norms and the stated domination and sampling assumptions, outer
products have factored squared norms, factored oversampling ratios when target norms are
positive, entrywise domination, and the normalized product sampling law. This is the
outer-product access construction of [Chia et al., Lemma 3.8][ChiaEtAl2022]. -/
theorem native_sq_outer_product_access (m n : ℕ) (u a : Fin m → ℂ) (v b : Fin n → ℂ)
    (p : FinDist (Fin m)) (q : FinDist (Fin n))
    (ha : 0 < closureNormSq a) (hb : 0 < closureNormSq b)
    (hp : ∀ i, Complex.normSq (u i) ≤ Complex.normSq (a i) ∧
      p.prob i = Complex.normSq (a i)/closureNormSq a)
    (hq : ∀ j, Complex.normSq (v j) ≤ Complex.normSq (b j) ∧
      q.prob j = Complex.normSq (b j)/closureNormSq b) :
    closureNormSq (closureOuter a b) = closureNormSq a*closureNormSq b ∧
    closureNormSq (closureOuter u v) = closureNormSq u*closureNormSq v ∧
    (0 < closureNormSq u → 0 < closureNormSq v →
      closureNormSq (closureOuter a b)/closureNormSq (closureOuter u v) =
        (closureNormSq a/closureNormSq u)*(closureNormSq b/closureNormSq v) ∧
      1 ≤ closureNormSq (closureOuter a b)/closureNormSq (closureOuter u v)) ∧
    (∀ i j, Complex.normSq (closureOuter u v (i,j)) ≤ Complex.normSq (closureOuter a b (i,j))) ∧
    (∀ i j, (closureOuterSample p q (i,j)).toReal =
      Complex.normSq (closureOuter a b (i,j))/(closureNormSq a*closureNormSq b)) := by
  have hnu : closureNormSq u ≤ closureNormSq a := Finset.sum_le_sum fun i _ => (hp i).1
  have hnv : closureNormSq v ≤ closureNormSq b := Finset.sum_le_sum fun j _ => (hq j).1
  refine ⟨closureOuter_normSq a b, closureOuter_normSq u v, ?_, ?_, ?_⟩
  · intro hu hv
    rw [closureOuter_normSq, closureOuter_normSq]
    refine ⟨by field_simp, (one_le_div (mul_pos hu hv)).mpr ?_⟩
    exact mul_le_mul hnu hnv (closureNormSq_nonneg v) ha.le
  · intro i j
    simp only [closureOuter, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
    exact mul_le_mul (hp i).1 (hq j).1 (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  · intro i j
    rw [closureOuterSample_apply, ENNReal.toReal_mul, closurePMF_toReal, closurePMF_toReal,
      (hp i).2, (hq j).2]
    simp only [closureOuter, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
    rw [div_mul_div_comm]

/-- The squared norm of a finite complex sum is at most the cardinality of the index type times
the sum of squared norms. -/
theorem closure_complex_sum_bound {X : Type} [Fintype X] (f : X → ℂ) :
    Complex.normSq (∑ x, f x) ≤ (Fintype.card X : ℝ)*∑ x, Complex.normSq (f x) := by
  have hn := norm_sum_le (s := Finset.univ) f
  have hsq : ‖∑ x, f x‖^2 ≤ (∑ x, ‖f x‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr hn
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset X)
    (fun _ => (1 : ℝ)) (fun x => ‖f x‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    mul_one, ← Complex.normSq_eq_norm_sq] at hcs hsq
  exact hsq.trans hcs

/-- Reading the weights produced by `closurePrepare` recovers `closureWeights coeff W`. -/
theorem closurePreparedWeight_prepare {τ : ℕ} (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) :
    closurePreparedWeight (closurePrepare coeff W) = closureWeights coeff W := by
  funext t
  unfold closurePreparedWeight
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    (native_sq_preparation_and_point_query_ledger τ coeff W).2.1,
    List.getElem?_ofFn]
  simp [t.isLt]

/-- Bounded coefficient choice with prepared data agrees with direct choice using the
coefficient weights. -/
theorem closureChoicePreparedRun_prepare {τ : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) (T : ℕ) :
    closureChoicePreparedRun rand (closurePrepare coeff W) T =
      closureChoiceRun rand (closureWeights coeff W) T := by
  simp only [closureChoicePreparedRun, closureChoiceRun,
    (native_sq_preparation_and_point_query_ledger τ coeff W).2.2.1,
    closurePreparedWeight_prepare]

/-- Unbounded coefficient choice with prepared data agrees with direct unbounded choice using
the coefficient weights. -/
theorem closureChoicePreparedUnbounded_prepare {τ : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) :
    closureChoicePreparedUnbounded rand (closurePrepare coeff W) =
      closureChoiceUnbounded rand (closureWeights coeff W) := by
  simp only [closureChoicePreparedUnbounded, closureChoiceUnbounded,
    (native_sq_preparation_and_point_query_ledger τ coeff W).2.2.1,
    closurePreparedWeight_prepare]

/-- The bounded prepared draw agrees with the direct draw using the coefficient weights. -/
theorem closureDrawPrepared_prepare {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (coeff : Fin τ → ℂ) (W : Fin τ → ℝ)
    (T : ℕ) (native : Fin τ → FinDist X) :
    closureDrawPrepared rand (closurePrepare coeff W) T native =
      closureDraw rand (closureWeights coeff W) T native := by
  rw [closureDrawPrepared, closureChoicePreparedRun_prepare]
  rfl

/-- The unbounded prepared draw agrees with the direct unbounded draw using the coefficient
weights. -/
theorem closureDrawPreparedUnbounded_prepare {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (coeff : Fin τ → ℂ) (W : Fin τ → ℝ)
    (native : Fin τ → FinDist X) :
    closureDrawPreparedUnbounded rand (closurePrepare coeff W) native =
      closureUnboundedDraw rand (closureWeights coeff W) native := by
  rw [closureDrawPreparedUnbounded, closureChoicePreparedUnbounded_prepare]
  rfl

/-- Entrywise domination of each source matrix by its envelope implies domination of the linear
combination's squared entry norms by `closureMatrixEnvelopeSq`. -/
theorem closureMatrixTarget_bound {τ m n : ℕ} (coeff : Fin τ → ℂ)
    (A env : Fin τ → Matrix (Fin m) (Fin n) ℂ)
    (hdom : ∀ t i j, Complex.normSq (A t i j) ≤ Complex.normSq (env t i j)) :
    ∀ i j, Complex.normSq (closureMatrixTarget coeff A i j) ≤ closureMatrixEnvelopeSq coeff env i j := by
  intro i j
  have h := closure_complex_sum_bound (fun t => coeff t*A t i j)
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg τ)
  apply Finset.sum_le_sum
  intro t _
  simp only [Complex.normSq_mul]
  exact mul_le_mul_of_nonneg_left (hdom t i j) (Complex.normSq_nonneg _)

/-- The sum of all squared envelope entries equals `τ` times the sum of the coefficient-weighted
source squared Frobenius norms. -/
theorem closureMatrixEnvelope_sum {τ m n : ℕ} (coeff : Fin τ → ℂ)
    (env : Fin τ → Matrix (Fin m) (Fin n) ℂ) :
    (∑ i, ∑ j, closureMatrixEnvelopeSq coeff env i j) =
      (τ : ℝ)*closureSum (closureWeights coeff (fun t => closureFrobSq (env t))) := by
  unfold closureMatrixEnvelopeSq
  simp_rw [← Finset.mul_sum]
  congr 1
  calc (∑ i, ∑ j, ∑ t, Complex.normSq (coeff t*env t i j)) =
        ∑ t, ∑ i, ∑ j, Complex.normSq (coeff t*env t i j) := by
          conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
    _ = _ := by
          simp only [closureSum, closureWeights, closureFrobSq, closureRowSq, Complex.normSq_mul]
          simp_rw [← Finset.mul_sum]

/-- Compose a row draw with its conditional column draw, propagating failure and adding both
cost records and the row query charge. -/
noncomputable def closureMatrixCompose {m n : ℕ}
    (rowRun : PMF (ClosureDrawResult (Fin m)))
    (columnRuns : Fin m → PMF (ClosureDrawResult (Fin n))) (rowQueries : Fin m → ℕ) :
    PMF (ClosureDrawResult (Fin m × Fin n)) :=
  rowRun.bind (fun z => match z.1 with
    | none => PMF.pure (none,z.2.1,z.2.2.1,z.2.2.2)
    | some i => (columnRuns i).map (fun y =>
      (y.1.map (fun j => (i,j)),z.2.1+y.2.1,z.2.2.1+y.2.2.1,z.2.2.2+y.2.2.2+rowQueries i)))

/-- The probability that the composed draw returns `(i, j)` factors as the probability of row
`i` times the conditional probability of column `j`. -/
theorem closureMatrixCompose_event {m n : ℕ} (rowRun : PMF (ClosureDrawResult (Fin m)))
    (columnRuns : Fin m → PMF (ClosureDrawResult (Fin n))) (rowQueries : Fin m → ℕ) (i : Fin m) (j : Fin n) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixCompose rowRun columnRuns rowQueries) (fun z => z.1 = some (i,j)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event rowRun (fun z => z.1 = some i)*Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (columnRuns i) (fun z => z.1 = some j) := by
  let after : ClosureDrawResult (Fin m) → PMF (ClosureDrawResult (Fin m × Fin n)) :=
    fun z => match z.1 with
    | none => PMF.pure (none,z.2.1,z.2.2.1,z.2.2.2)
    | some k => (columnRuns k).map (fun y =>
      (y.1.map (fun l => (k,l)),z.2.1+y.2.1,z.2.2.1+y.2.2.1,z.2.2.2+y.2.2.2+rowQueries k))
  let mass :=
      fun k : Fin m => if k = i then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (columnRuns k) (fun z => z.1 = some j) else 0
  have haf : ∀ z, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (after z) (fun z : ClosureDrawResult (Fin m × Fin n) => z.1 = some (i,j)) =
      ∑ k, if z.1 = some k then mass k else 0 := by
    intro z
    cases hz : z.1 with
    | none => simp [after, hz, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    | some k =>
      simp only [after, hz]
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
      by_cases hk : k = i
      · subst k
        have hiff : ∀ y : ClosureDrawResult (Fin n),
            y.1.map (fun l => (i,l)) = some (i,j) ↔ y.1 = some j := by
          intro y
          by_cases hy : y.1 = none <;> simp [hy]
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hiff]
        simp [mass]
      · have he : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (columnRuns k)
          (fun y => y.1.map (fun l => (k,l)) = some (i,j)) = 0 := by
          apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_zero
          intro y
          cases y.1 <;> simp [hk]
        rw [he]
        simp [mass, hk]
  have h := closure_record_mixture_event rowRun (fun z => z.1) after
    (fun z : ClosureDrawResult (Fin m × Fin n) => z.1 = some (i,j)) mass haf
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rowRun.bind after) _ = _
  rw [h]
  simp [mass, mul_ite]

/-- The bounded prepared matrix sampler equals composition of the direct row and conditional
column samplers, charging `τ` row queries. -/
theorem closureMatrixDraw_prepare {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n)) (Trow Tcol : ℕ) :
    closureMatrixDraw rand coeff W R rows cols Trow Tcol =
      closureMatrixCompose (closureDraw rand (closureWeights coeff W) Trow rows)
        (fun i => closureDraw rand (closureRowWeights coeff R i) Tcol (fun t => cols t i)) (fun _ => τ) := by
  unfold closureMatrixDraw closureMatrixCompose
  simp only [closureDrawPrepared_prepare]
  congr 1
  funext z
  cases z.1 with
  | none => rfl
  | some i =>
    (try dsimp only)
    rw [(native_sq_preparation_and_point_query_ledger τ coeff (fun t => R t i)).2.2.2.2.1]
    rfl

/-- The unbounded prepared matrix sampler equals composition of the direct unbounded row and
conditional column samplers, charging `τ` row queries. -/
theorem closureMatrixUnboundedDraw_prepare {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n)) :
    closureMatrixUnboundedDraw rand coeff W R rows cols =
      closureMatrixCompose (closureUnboundedDraw rand (closureWeights coeff W) rows)
        (fun i => closureUnboundedDraw rand (closureRowWeights coeff R i) (fun t => cols t i)) (fun _ => τ) := by
  unfold closureMatrixUnboundedDraw closureMatrixCompose
  simp only [closureDrawPreparedUnbounded_prepare]
  congr 1
  funext z
  cases z.1 with
  | none => rfl
  | some i =>
    (try dsimp only)
    rw [(native_sq_preparation_and_point_query_ledger τ coeff (fun t => R t i)).2.2.2.2.1]
    rfl

/-- The source assumptions specifying positive envelope squared Frobenius norms, row squared
norms, entrywise domination, and normalized row and nonzero-row column sampling laws. -/
private def ClosureMatrixSourceSpec {τ m n : ℕ}
    (A env : Fin τ → Matrix (Fin m) (Fin n) ℂ) (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n)) : Prop :=
  ∀ t, 0 < W t ∧ W t = closureFrobSq (env t) ∧ (∀ i, R t i = closureRowSq (env t) i) ∧
    (∀ i j, Complex.normSq (A t i j) ≤ Complex.normSq (env t i j)) ∧
    (∀ i, (rows t).prob i = closureRowSq (env t) i/W t) ∧
    (∀ i j, 0 < closureRowSq (env t) i →
      (cols t i).prob j = Complex.normSq (env t i j)/closureRowSq (env t) i)

/-- Every specified source row squared norm is nonnegative. -/
private theorem closure_source_row_nonneg {τ m n : ℕ}
    {A env : Fin τ → Matrix (Fin m) (Fin n) ℂ} {W : Fin τ → ℝ} {R : Fin τ → Fin m → ℝ}
    {rows : Fin τ → FinDist (Fin m)} {cols : Fin τ → Fin m → FinDist (Fin n)}
    (h : ClosureMatrixSourceSpec A env W R rows cols) (t : Fin τ) (i : Fin m) : 0 ≤ R t i := by
  rw [(h t).2.2.1 i]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Nonnegative source weights give nonnegative coefficient mixture weights. -/
private theorem closure_weights_nonneg {τ : ℕ} (coeff : Fin τ → ℂ) (W : Fin τ → ℝ)
    (h : ∀ t, 0 ≤ W t) (t : Fin τ) : 0 ≤ closureWeights coeff W t :=
  mul_nonneg (Complex.normSq_nonneg _) (h t)

/-- Under the source specification, the mixture-weighted row probability equals the total
coefficient-weighted squared norm of that row. -/
private theorem closure_source_weighted_rows {τ m n : ℕ}
    (coeff : Fin τ → ℂ) {A env : Fin τ → Matrix (Fin m) (Fin n) ℂ}
    {W : Fin τ → ℝ} {R : Fin τ → Fin m → ℝ}
    {rows : Fin τ → FinDist (Fin m)} {cols : Fin τ → Fin m → FinDist (Fin n)}
    (h : ClosureMatrixSourceSpec A env W R rows cols) (i : Fin m) :
    (∑ t, closureWeights coeff W t*(rows t).prob i) = closureSum (closureRowWeights coeff R i) := by
  unfold closureSum
  apply Finset.sum_congr rfl
  intro t _
  rw [(h t).2.2.2.2.1 i, ← (h t).2.2.1 i]
  unfold closureWeights closureRowWeights
  field_simp [(h t).1.ne']

/-- If a row has zero squared norm, every entry in that row has zero squared norm. -/
private theorem closure_row_zero_entry {m n : ℕ} (env : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin m) (j : Fin n) (h : closureRowSq env i = 0) : Complex.normSq (env i j) = 0 := by
  have hle : Complex.normSq (env i j) ≤ closureRowSq env i :=
    Finset.single_le_sum (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  exact le_antisymm (h ▸ hle) (Complex.normSq_nonneg _)

/-- Under the source specification, the mixture-weighted conditional column probability equals
the sum of coefficient-weighted envelope squared entry norms. -/
private theorem closure_source_weighted_columns {τ m n : ℕ}
    (coeff : Fin τ → ℂ) {A env : Fin τ → Matrix (Fin m) (Fin n) ℂ}
    {W : Fin τ → ℝ} {R : Fin τ → Fin m → ℝ}
    {rows : Fin τ → FinDist (Fin m)} {cols : Fin τ → Fin m → FinDist (Fin n)}
    (h : ClosureMatrixSourceSpec A env W R rows cols) (i : Fin m) (j : Fin n) :
    (∑ t, closureRowWeights coeff R i t*(cols t i).prob j) =
      ∑ t, Complex.normSq (coeff t*env t i j) := by
  apply Finset.sum_congr rfl
  intro t _
  by_cases hz : R t i = 0
  · have hn : Complex.normSq (env t i j) = 0 := closure_row_zero_entry _ i j
      (by rw [← (h t).2.2.1 i, hz])
    simp [closureRowWeights, hz, Complex.normSq_mul, hn]
  · have hp : 0 < R t i := lt_of_le_of_ne (closure_source_row_nonneg h t i) (Ne.symm hz)
    rw [(h t).2.2.2.2.2 i j (by rw [← (h t).2.2.1 i]; exact hp), ← (h t).2.2.1 i]
    simp only [closureRowWeights, Complex.normSq_mul]
    field_simp [hz]

/-- A nonnegative finite weight family with zero sum vanishes at every index. -/
private theorem closure_weight_sum_zero {τ : ℕ} (q : Fin τ → ℝ)
    (hn : ∀ t, 0 ≤ q t) (hs : closureSum q = 0) : ∀ t, q t = 0 := by
  intro t
  have hle : q t ≤ closureSum q := Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ t)
  exact le_antisymm (hs ▸ hle) (hn t)

/-- With the source specification and positive total mixture weight, the bounded matrix output
mass equals the normalized squared envelope multiplied by the row and conditional column
success factors. -/
private theorem closure_matrix_finite_mass {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (A env : Fin τ → Matrix (Fin m) (Fin n) ℂ)
    (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n))
    (Trow Tcol : ℕ) (h : ClosureMatrixSourceSpec A env W R rows cols)
    (hs : 0 < closureSum (closureWeights coeff W)) (i : Fin m) (j : Fin n) :
    closureMatrixMass rand coeff W R rows cols Trow Tcol i j =
      closureSuccess (closureWeights coeff W) Trow*closureSuccess (closureRowWeights coeff R i) Tcol*
        closureMatrixEnvelopeSq coeff env i j/((τ : ℝ)*closureSum (closureWeights coeff W)) := by
  have hq := closure_weights_nonneg coeff W (fun t => (h t).1.le)
  have hqi : ∀ t, 0 ≤ closureRowWeights coeff R i t :=
    fun t => mul_nonneg (Complex.normSq_nonneg _) (closure_source_row_nonneg h t i)
  have hg : closureDrawMass rand (closureWeights coeff W) Trow rows i =
      closureSuccess (closureWeights coeff W) Trow/closureSum (closureWeights coeff W)*
        closureSum (closureRowWeights coeff R i) := by
    rw [closureDrawMass_formula rand _ Trow rows hq hs, closure_source_weighted_rows coeff h i]
  rw [closureMatrixMass, closureMatrixDraw_prepare, closureMatrixCompose_event, ENNReal.toReal_mul]
  change closureDrawMass rand (closureWeights coeff W) Trow rows i*
    closureDrawMass rand (closureRowWeights coeff R i) Tcol (fun t => cols t i) j = _
  rw [hg]
  by_cases hz : closureSum (closureRowWeights coeff R i) = 0
  · have hzero := closure_weight_sum_zero _ hqi hz
    have he : (∑ t, Complex.normSq (coeff t*env t i j)) = 0 := by
      rw [← closure_source_weighted_columns coeff h i j]
      simp [hzero]
    simp only [hz, closureMatrixEnvelopeSq, he, mul_zero, zero_mul, zero_div]
  · have hpos : 0 < closureSum (closureRowWeights coeff R i) :=
      lt_of_le_of_ne (Finset.sum_nonneg fun t _ => hqi t) (Ne.symm hz)
    rw [closureDrawMass_formula rand _ Tcol (fun t => cols t i) hqi hpos,
      closure_source_weighted_columns coeff h i j]
    have hτ : 0 < τ := (closure_positive_rate _ hq hs).2.1
    have hτr : (τ : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hτ
    unfold closureMatrixEnvelopeSq
    field_simp [hz, hs.ne', hτr]

/-- With the source specification and positive total mixture weight, the unbounded matrix
sampler's entry probability is its squared envelope divided by `τ` times the total mixture
weight. -/
private theorem closure_matrix_unbounded_mass {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (A env : Fin τ → Matrix (Fin m) (Fin n) ℂ)
    (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n))
    (h : ClosureMatrixSourceSpec A env W R rows cols)
    (hs : 0 < closureSum (closureWeights coeff W)) (i : Fin m) (j : Fin n) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => z.1 = some (i,j))).toReal =
      closureMatrixEnvelopeSq coeff env i j/((τ : ℝ)*closureSum (closureWeights coeff W)) := by
  have hq := closure_weights_nonneg coeff W (fun t => (h t).1.le)
  have hqi : ∀ t, 0 ≤ closureRowWeights coeff R i t :=
    fun t => mul_nonneg (Complex.normSq_nonneg _) (closure_source_row_nonneg h t i)
  have hg : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureUnboundedDraw rand (closureWeights coeff W) rows)
      (fun z => z.1 = some i)).toReal =
      (1/closureSum (closureWeights coeff W))*closureSum (closureRowWeights coeff R i) := by
    rw [closureUnboundedDrawMass_formula rand _ rows hq hs, closure_source_weighted_rows coeff h i]
  rw [closureMatrixUnboundedDraw_prepare, closureMatrixCompose_event, ENNReal.toReal_mul, hg]
  by_cases hz : closureSum (closureRowWeights coeff R i) = 0
  · have hzero := closure_weight_sum_zero _ hqi hz
    have he : (∑ t, Complex.normSq (coeff t*env t i j)) = 0 := by
      rw [← closure_source_weighted_columns coeff h i j]
      simp [hzero]
    simp only [hz, closureMatrixEnvelopeSq, he, mul_zero, zero_mul, zero_div]
  · have hpos : 0 < closureSum (closureRowWeights coeff R i) :=
      lt_of_le_of_ne (Finset.sum_nonneg fun t _ => hqi t) (Ne.symm hz)
    rw [closureUnboundedDrawMass_formula rand _ (fun t => cols t i) hqi hpos,
      closure_source_weighted_columns coeff h i j]
    have hτ : 0 < τ := (closure_positive_rate _ hq hs).2.1
    have hτr : (τ : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hτ
    unfold closureMatrixEnvelopeSq
    field_simp [hz, hs.ne', hτr]

/-- A pointwise inequality on the support of a PMF gives the corresponding inequality of
extended nonnegative expectations. -/
private theorem closure_expectation_support_le {Ω : Type} (p : PMF Ω) (f g : Ω → ℝ≥0∞)
    (h : ∀ z ∈ p.support, f z ≤ g z) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p f ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p g := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : p z = 0
  · simp [hz]
  · exact mul_le_mul' (le_refl _) (h z ((PMF.mem_support_iff p z).mp hz))

/-- Functions agreeing on the support of a PMF have equal extended nonnegative expectations. -/
private theorem closure_expectation_support_eq {Ω : Type} (p : PMF Ω) (f g : Ω → ℝ≥0∞)
    (h : ∀ z ∈ p.support, f z = g z) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p f = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p g :=
  le_antisymm (closure_expectation_support_le p f g (fun z hz => (h z hz).le))
    (closure_expectation_support_le p g f (fun z hz => (h z hz).ge))

/-- A supported draw result returning `some x` implies that the event of returning `some x` has
positive real probability. -/
private theorem closure_support_event_pos {X : Type} (p : PMF (ClosureDrawResult X))
    (z : ClosureDrawResult X) (hz : z ∈ p.support) (x : X) (hx : z.1 = some x) :
    0 < (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = some x)).toReal := by
  have hmap : some x ∈ (p.map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨z,hz,hx⟩
  have hnon : (p.map Prod.fst) (some x) ≠ 0 := (PMF.mem_support_iff _ _).mpr hmap
  have heq :=
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map p Prod.fst
      (fun o : Option X => o = some x)
  rw [GeneralExecution.event_point_mass] at heq
  have he : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = some x) ≠ 0 := by
    simpa only [heq] using hnon
  exact ENNReal.toReal_pos he
      (ne_of_lt (lt_of_le_of_lt (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _) ENNReal.one_lt_top))

/-- For an additive price function, the expected cost of composed row and column draws equals
the expected row cost plus the row-averaged expected column cost and query charge, with zero
additional charge after row failure. -/
theorem closureMatrixCompose_expectation {m n : ℕ} (rowRun : PMF (ClosureDrawResult (Fin m)))
    (columnRuns : Fin m → PMF (ClosureDrawResult (Fin n))) (rowQueries : Fin m → ℕ)
    (price : ℕ × ℕ × ℕ → ℝ≥0∞) (hadd : ∀ c d, price (c+d) = price c+price d) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixCompose rowRun columnRuns rowQueries) (fun z => price z.2) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation rowRun (fun z => price z.2) +
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation rowRun (fun z => match z.1 with
        | none => 0
        | some i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (columnRuns i) (fun y => price y.2) + price (0,0,rowQueries i)) := by
  rw [closureMatrixCompose, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind,
      ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro z
  cases hz : z.1 with
  | none => simp
  | some i =>
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    have hpoint : ∀ y : ClosureDrawResult (Fin n),
        price (z.2.1+y.2.1,z.2.2.1+y.2.2.1,z.2.2.2+y.2.2.2+rowQueries i) =
          price z.2+price y.2+price (0,0,rowQueries i) := by
      intro y
      change price (z.2+y.2+(0,0,rowQueries i)) = _
      rw [hadd, hadd]
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hpoint]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
    rw [add_assoc]

/-- If failure has zero probability, charging a constant `c` on successful draws and zero on
failure has expectation `c`. -/
theorem closure_expectation_some_const {X : Type} (p : PMF (ClosureDrawResult X))
    (hnone : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = none) = 0) (c : ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => match z.1 with | none => 0 | some _ => c) = c := by
  have hpart : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = none) +
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => match z.1 with | none => 0 | some _ => (1 : ℝ≥0∞)) = 1 := by
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
    calc _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun _ => 1) := by
          apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
          intro z
          cases hz : z.1 <;> simp [hz]
      _ = 1 := by simp
  rw [hnone, zero_add] at hpart
  have heq : (fun z : ClosureDrawResult X => match z.1 with | none => 0 | some _ => c) =
      fun z => c*(match z.1 with | none => 0 | some _ => (1 : ℝ≥0∞)) := by
    funext z
    cases z.1 <;> simp
  rw [heq, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul, hpart,
      mul_one]

/-- The failure probability of a composed matrix draw equals row failure probability plus the
row-averaged conditional column failure probability. -/
theorem closureMatrixCompose_none {m n : ℕ} (rowRun : PMF (ClosureDrawResult (Fin m)))
    (columnRuns : Fin m → PMF (ClosureDrawResult (Fin n))) (rowQueries : Fin m → ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixCompose rowRun columnRuns rowQueries) (fun z => z.1 = none) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event rowRun (fun z => z.1 = none) +
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation rowRun (fun z => match z.1 with
        | none => 0 | some i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (columnRuns i) (fun z => z.1 = none)) := by
  unfold closureMatrixCompose Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind,
      ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro z
  cases hz : z.1 with
  | none => simp [hz]
  | some i =>
    simp only [hz, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
        Option.some_ne_none, if_false, zero_add]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro y
    by_cases hy : y.1 = none <;> simp [hy]

/-- Under the source specification and positive total mixture weight, the unbounded row
probability is the row's total coefficient weight divided by the global coefficient weight. -/
private theorem closure_source_unbounded_row_mass {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) {A env : Fin τ → Matrix (Fin m) (Fin n) ℂ}
    {W : Fin τ → ℝ} {R : Fin τ → Fin m → ℝ}
    {rows : Fin τ → FinDist (Fin m)} {cols : Fin τ → Fin m → FinDist (Fin n)}
    (h : ClosureMatrixSourceSpec A env W R rows cols) (hs : 0 < closureSum (closureWeights coeff W)) (i : Fin m) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureUnboundedDraw rand (closureWeights coeff W) rows) (fun z => z.1 = some i)).toReal =
      closureSum (closureRowWeights coeff R i)/closureSum (closureWeights coeff W) := by
  rw [closureUnboundedDrawMass_formula rand _ rows (closure_weights_nonneg coeff W (fun t => (h t).1.le)) hs,
    closure_source_weighted_rows coeff h i]
  ring

/-- Under the source specification and the stated proportional row mass formula, a supported
result returning row `i` implies that its total conditional row weight is positive. -/
private theorem closure_source_reachable_row {τ m n : ℕ}
    (coeff : Fin τ → ℂ) {A env : Fin τ → Matrix (Fin m) (Fin n) ℂ}
    {W : Fin τ → ℝ} {R : Fin τ → Fin m → ℝ}
    {rows : Fin τ → FinDist (Fin m)} {cols : Fin τ → Fin m → FinDist (Fin n)}
    (h : ClosureMatrixSourceSpec A env W R rows cols)
    (p : PMF (ClosureDrawResult (Fin m))) (κ : ℝ)
    (hmass : ∀ i, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = some i)).toReal =
      κ*closureSum (closureRowWeights coeff R i))
    (z : ClosureDrawResult (Fin m)) (hz : z ∈ p.support) (i : Fin m) (hi : z.1 = some i) :
    0 < closureSum (closureRowWeights coeff R i) := by
  have hp := closure_support_event_pos p z hz i hi
  rw [hmass i] at hp
  have hnn : 0 ≤ closureSum (closureRowWeights coeff R i) := Finset.sum_nonneg fun t _ =>
    mul_nonneg (Complex.normSq_nonneg _) (closure_source_row_nonneg h t i)
  by_contra hn
  have heq : closureSum (closureRowWeights coeff R i) = 0 := by linarith
  rw [heq, mul_zero] at hp
  exact (lt_irrefl 0) hp

/-- Under the source specification and positive total mixture weight, the unbounded hierarchical
matrix sampler has zero failure probability. -/
private theorem closure_matrix_unbounded_none {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (A env : Fin τ → Matrix (Fin m) (Fin n) ℂ)
    (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n))
    (h : ClosureMatrixSourceSpec A env W R rows cols) (hs : 0 < closureSum (closureWeights coeff W)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixUnboundedDraw rand coeff W R rows cols) (fun z => z.1 = none) = 0 := by
  have hq := closure_weights_nonneg coeff W (fun t => (h t).1.le)
  let p := closureUnboundedDraw rand (closureWeights coeff W) rows
  have hnone :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = none) = 0 :=
      closureUnboundedDraw_none rand _ rows hq hs
  have hmass : ∀ i, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = some i)).toReal =
      (1/closureSum (closureWeights coeff W))*closureSum (closureRowWeights coeff R i) := by
    intro i
    rw [closure_source_unbounded_row_mass rand coeff h hs i]
    ring
  rw [closureMatrixUnboundedDraw_prepare, closureMatrixCompose_none, hnone, zero_add]
  calc _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun _ => 0) := by
        apply closure_expectation_support_eq
        intro z hz
        cases hi : z.1 with
        | none => rfl
        | some i =>
          have hpos := closure_source_reachable_row coeff h p _ hmass z hz i hi
          exact closureUnboundedDraw_none rand _ (fun t => cols t i)
            (fun t => mul_nonneg (Complex.normSq_nonneg _) (closure_source_row_nonneg h t i)) hpos
    _ = 0 := by simp

/-- Under the source specification and positive total mixture weight, the unbounded sampler has
expected attempts at most `2 * τ`, random calls at most `4 * τ`, native sample count exactly
two, and row query count exactly `τ`. -/
private theorem closure_matrix_unbounded_prices {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (A env : Fin τ → Matrix (Fin m) (Fin n) ℂ)
    (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n))
    (h : ClosureMatrixSourceSpec A env W R rows cols) (hs : 0 < closureSum (closureWeights coeff W)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (z.2.1 : ℝ≥0∞)) ≤ (2*τ : ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (closureDrawRandomCalls z : ℝ≥0∞)) ≤ (4*τ : ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (z.2.2.1 : ℝ≥0∞)) = 2 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (z.2.2.2 : ℝ≥0∞)) = (τ : ℝ≥0∞) := by
  have hq := closure_weights_nonneg coeff W (fun t => (h t).1.le)
  let p := closureUnboundedDraw rand (closureWeights coeff W) rows
  let cp := fun i => closureUnboundedDraw rand (closureRowWeights coeff R i) (fun t => cols t i)
  have hnone :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = none) = 0 :=
      closureUnboundedDraw_none rand _ rows hq hs
  have hmass : ∀ i, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = some i)).toReal =
      (1/closureSum (closureWeights coeff W))*closureSum (closureRowWeights coeff R i) := by
    intro i
    rw [closure_source_unbounded_row_mass rand coeff h hs i]
    ring
  have hrowpos := fun z hz i hi => closure_source_reachable_row coeff h p _ hmass z hz i hi
  have hprice : ∀ i, 0 < closureSum (closureRowWeights coeff R i) →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (cp i) (fun z => (z.2.1 : ℝ≥0∞)) ≤ (τ : ℝ≥0∞) := by
    intro i hpos
    rw [closureUnboundedDraw_attempts]
    exact (native_coefficient_choice_joint_halt_and_cost τ rand _ 0
      (fun t => mul_nonneg (Complex.normSq_nonneg _) (closure_source_row_nonneg h t i)) hpos).2.2.2.2.2.2.2.1
  have hglobal : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => (z.2.1 : ℝ≥0∞)) ≤ (τ : ℝ≥0∞) := by
    rw [closureUnboundedDraw_attempts]
    exact (native_coefficient_choice_joint_halt_and_cost τ rand _ 0 hq hs).2.2.2.2.2.2.2.1
  have hbound : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => match z.1 with
      | none => 0 | some i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (cp i) (fun y => (y.2.1 : ℝ≥0∞))) ≤ (τ : ℝ≥0∞) := by
    apply (closure_expectation_support_le p _ (fun _ => (τ : ℝ≥0∞)) ?_).trans_eq
        (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const _ _)
    intro z hz
    cases hi : z.1 with
    | none => exact bot_le
    | some i => exact hprice i (hrowpos z hz i hi)
  have hattempt : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (z.2.1 : ℝ≥0∞)) ≤ (2*τ : ℕ) := by
    rw [closureMatrixUnboundedDraw_prepare]
    have heq := closureMatrixCompose_expectation p cp (fun _ => τ)
      (fun c : ℕ × ℕ × ℕ => (c.1 : ℝ≥0∞)) (by intro c d; simp [Nat.cast_add])
    simp only [Nat.cast_zero, add_zero] at heq
    rw [heq]
    exact (add_le_add hglobal hbound).trans_eq (by simp [two_mul])
  refine ⟨hattempt, ?_, ?_, ?_⟩
  · have heq : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
        (fun z => (closureDrawRandomCalls z : ℝ≥0∞)) =
        2*Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
          (fun z => (z.2.1 : ℝ≥0∞)) := by
      rw [← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro z
      simp [closureDrawRandomCalls, Nat.cast_mul]
    rw [heq]
    exact (mul_le_mul' (le_refl 2) hattempt).trans_eq (by norm_num [Nat.cast_mul]; ring)
  · rw [closureMatrixUnboundedDraw_prepare]
    have heq := closureMatrixCompose_expectation p cp (fun _ => τ)
      (fun c : ℕ × ℕ × ℕ => (c.2.1 : ℝ≥0∞)) (by intro c d; simp [Nat.cast_add])
    simp only [Nat.cast_zero, add_zero] at heq
    rw [heq, closureUnboundedDraw_native_calls rand _ rows hq hs]
    have hselected : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => match z.1 with
        | none => 0 | some i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (cp i) (fun y => (y.2.2.1 : ℝ≥0∞))) = 1 := by
      calc _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => match z.1 with | none => 0 | some _ => 1) := by
            apply closure_expectation_support_eq
            intro z hz
            cases hi : z.1 with
            | none => rfl
            | some i =>
                exact closureUnboundedDraw_native_calls rand _ (fun t => cols t i)
                  (fun t => mul_nonneg (Complex.normSq_nonneg _) (closure_source_row_nonneg h t i)) (hrowpos z hz i hi)
        _ = 1 := by
          convert closure_expectation_some_const p hnone 1 using 1
          apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
          intro z
          cases z.1 <;> simp
    rw [hselected]
    norm_num
  · rw [closureMatrixUnboundedDraw_prepare]
    have heq := closureMatrixCompose_expectation p cp (fun _ => τ)
      (fun c : ℕ × ℕ × ℕ => (c.2.2 : ℝ≥0∞)) (by intro c d; simp [Nat.cast_add])
    rw [heq, closureUnboundedDraw_norm_queries, zero_add]
    have hselected : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => match z.1 with
        | none => 0 | some i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (cp i) (fun y => (y.2.2.2 : ℝ≥0∞)) + (τ : ℝ≥0∞)) =
        (τ : ℝ≥0∞) := by
      simp only [cp, closureUnboundedDraw_norm_queries]
      simp only [zero_add]
      convert closure_expectation_some_const p hnone (τ : ℝ≥0∞) using 1
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro z
      cases z.1 <;> simp
    exact hselected

/-- Under the source specification and positive total mixture weight, bounded hierarchical
sampling fails with real probability at most `Real.exp (-Trow / τ) + Real.exp (-Tcol / τ)`. -/
private theorem closure_matrix_timeout_bound {τ m n : ℕ} (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (A env : Fin τ → Matrix (Fin m) (Fin n) ℂ)
    (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n))
    (Trow Tcol : ℕ) (h : ClosureMatrixSourceSpec A env W R rows cols)
    (hs : 0 < closureSum (closureWeights coeff W)) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixDraw rand coeff W R rows cols Trow Tcol)
      (fun z => z.1 = none)).toReal ≤
        Real.exp (-(Trow : ℝ)/(τ : ℝ))+Real.exp (-(Tcol : ℝ)/(τ : ℝ)) := by
  have hq := closure_weights_nonneg coeff W (fun t => (h t).1.le)
  let p := closureDraw rand (closureWeights coeff W) Trow rows
  let cp := fun i => closureDraw rand (closureRowWeights coeff R i) Tcol (fun t => cols t i)
  let er := Real.exp (-(Trow : ℝ)/(τ : ℝ))
  let ec := Real.exp (-(Tcol : ℝ)/(τ : ℝ))
  have hmass : ∀ i, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = some i)).toReal =
      (closureSuccess (closureWeights coeff W) Trow/closureSum (closureWeights coeff W))*
        closureSum (closureRowWeights coeff R i) := by
    intro i
    exact (closureDrawMass_formula rand _ Trow rows hq hs i).trans
      (by rw [closure_source_weighted_rows coeff h i])
  have hglobal : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = none)).toReal ≤ er := by
    rw [closureDraw_none, (native_coefficient_choice_joint_halt_and_cost τ rand _ Trow hq hs).1]
    exact (native_coefficient_choice_joint_halt_and_cost τ rand _ Trow hq hs).2.2.2.1
  have hlocal : ∀ i, 0 < closureSum (closureRowWeights coeff R i) →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (cp i) (fun z => z.1 = none) ≤ ENNReal.ofReal ec := by
    intro i hpos
    have hcstep := native_coefficient_choice_joint_halt_and_cost τ rand (closureRowWeights coeff R i) Tcol
      (fun t => mul_nonneg (Complex.normSq_nonneg _) (closure_source_row_nonneg h t i)) hpos
    have hc : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (cp i) (fun z => z.1 = none)).toReal ≤ ec := by
      rw [closureDraw_none, hcstep.1]
      exact hcstep.2.2.2.1
    calc _ = ENNReal.ofReal ((Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (cp i) (fun z => z.1 = none)).toReal) :=
          (ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _) ENNReal.one_lt_top))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hc
  have hselected : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun z => match z.1 with
      | none => 0 | some i => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (cp i) (fun z => z.1 = none)) ≤ ENNReal.ofReal ec := by
    apply (closure_expectation_support_le p _ (fun _ => ENNReal.ofReal ec) ?_).trans_eq
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const _ _)
    intro z hz
    cases hi : z.1 with
    | none => exact bot_le
    | some i => exact hlocal i (closure_source_reachable_row coeff h p _ hmass z hz i hi)
  have hg : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = none) ≤ ENNReal.ofReal er := by
    calc _ = ENNReal.ofReal ((Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 = none)).toReal) :=
          (ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _) ENNReal.one_lt_top))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hglobal
  have hbound : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixDraw rand coeff W R rows cols Trow Tcol)
      (fun z => z.1 = none) ≤ ENNReal.ofReal (er+ec) := by
    rw [closureMatrixDraw_prepare, closureMatrixCompose_none,
        ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    exact add_le_add hg hselected
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  have hnon : 0 ≤ er+ec := by dsimp [er,ec]; positivity
  rw [ENNReal.toReal_ofReal hnon] at hreal
  exact hreal

/-- Under the source sampling and envelope assumptions with positive total mixture weight,
hierarchical matrix sampling has the stated envelope domination and normalization, exact
bounded and unbounded entry laws, and exponential timeout bound. The unbounded sampler has
zero failure probability, expected attempts at most `2 * τ`, random calls at most `4 * τ`,
native sample count two, and row query count `τ`, as formalized for [Chia et al., Lemma
3.9][ChiaEtAl2022]. -/
theorem native_sq_hierarchical_matrix_lcu_actual_access (τ m n : ℕ) (rand : ClosureNativeRandom)
    (coeff : Fin τ → ℂ) (A env : Fin τ → Matrix (Fin m) (Fin n) ℂ)
    (W : Fin τ → ℝ) (R : Fin τ → Fin m → ℝ)
    (rows : Fin τ → FinDist (Fin m)) (cols : Fin τ → Fin m → FinDist (Fin n)) (Trow Tcol : ℕ)
    (h : ∀ t, 0 < W t ∧ W t = closureFrobSq (env t) ∧ (∀ i, R t i = closureRowSq (env t) i) ∧
      (∀ i j, Complex.normSq (A t i j) ≤ Complex.normSq (env t i j)) ∧
      (∀ i, (rows t).prob i = closureRowSq (env t) i/W t) ∧
      (∀ i j, 0 < closureRowSq (env t) i →
        (cols t i).prob j = Complex.normSq (env t i j)/closureRowSq (env t) i))
    (hs : 0 < closureSum (closureWeights coeff W)) :
    (∀ i j, Complex.normSq (closureMatrixTarget coeff A i j) ≤ closureMatrixEnvelopeSq coeff env i j) ∧
    (∑ i, ∑ j, closureMatrixEnvelopeSq coeff env i j) = (τ : ℝ)*closureSum (closureWeights coeff W) ∧
    (0 < closureFrobSq (closureMatrixTarget coeff A) →
      1 ≤ ((τ : ℝ)*closureSum (closureWeights coeff W))/closureFrobSq (closureMatrixTarget coeff A)) ∧
    (∀ i j, closureMatrixMass rand coeff W R rows cols Trow Tcol i j =
      closureSuccess (closureWeights coeff W) Trow*closureSuccess (closureRowWeights coeff R i) Tcol*
        closureMatrixEnvelopeSq coeff env i j/((τ : ℝ)*closureSum (closureWeights coeff W))) ∧
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixDraw rand coeff W R rows cols Trow Tcol) (fun z => z.1 = none)).toReal ≤
      Real.exp (-(Trow : ℝ)/(τ : ℝ))+Real.exp (-(Tcol : ℝ)/(τ : ℝ)) ∧
    (∀ i j, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => z.1 = some (i,j))).toReal =
        closureMatrixEnvelopeSq coeff env i j/((τ : ℝ)*closureSum (closureWeights coeff W))) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureMatrixUnboundedDraw rand coeff W R rows cols) (fun z => z.1 = none) = 0 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (z.2.1 : ℝ≥0∞)) ≤ (2*τ : ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (closureDrawRandomCalls z : ℝ≥0∞)) ≤ (4*τ : ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (z.2.2.1 : ℝ≥0∞)) = 2 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureMatrixUnboundedDraw rand coeff W R rows cols)
      (fun z => (z.2.2.2 : ℝ≥0∞)) = (τ : ℝ≥0∞) := by
  have hdom := closureMatrixTarget_bound coeff A env (fun t => (h t).2.2.2.1)
  have hsum : (∑ i, ∑ j, closureMatrixEnvelopeSq coeff env i j) =
      (τ : ℝ)*closureSum (closureWeights coeff W) := by
    rw [closureMatrixEnvelope_sum]
    congr 2
    funext t
    simp only [closureWeights]
    rw [(h t).2.1]
  have hcost := closure_matrix_unbounded_prices rand coeff A env W R rows cols h hs
  refine ⟨hdom, hsum, ?_, closure_matrix_finite_mass rand coeff A env W R rows cols Trow Tcol h hs,
    closure_matrix_timeout_bound rand coeff A env W R rows cols Trow Tcol h hs,
    closure_matrix_unbounded_mass rand coeff A env W R rows cols h hs,
    closure_matrix_unbounded_none rand coeff A env W R rows cols h hs,
    hcost.1, hcost.2.1, hcost.2.2.1, hcost.2.2.2⟩
  intro htarget
  apply (one_le_div htarget).mpr
  rw [← hsum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hdom i j

end Qatlib.Concepts.SqEstimation.HierarchicalSQ
