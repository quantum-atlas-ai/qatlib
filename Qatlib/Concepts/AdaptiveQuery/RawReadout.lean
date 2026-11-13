/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveQuery.RawProcess.ObservedRawProcess
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Report testers and query-degree readout blocks

This module groups raw process rows by report labels and proves positivity, completeness, and
probability formulas for the resulting testers. `observedRawReportDistribution` turns
normalized, well-formed unitary-query execution into a finite report distribution.

For homogeneous symbolic queries, testers and normalizers have no entries between distinct query
degrees. Their pairings decompose into positive degree blocks, each measuring the mass of traces
with the corresponding query count. For background, see [BealsEtAl2001].

## Main statements

* `rawReportTester_sum`: The sum of all report testers equals the full Gram matrix of `L`.
* `observedRawReportDistribution_pairing`: For homogeneous degree-one queries, the probability
  of a report equals its raw report tester pairing with the tensor vector.
* `observedRawTester_degree_pairing`: For homogeneous degree-one queries, the degree-`q` event
  tester pairing equals the mass of selected traces with exactly `q.val` queries.
* `observedRawNormalizer_sum_degree_complete`: For homogeneous degree-one queries evaluating to
  a unitary, a well-formed circuit and normalized input give degree-block normalizer pairings
  whose sum is one.

## References

* [Beals et al., 2001][BealsEtAl2001]
* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.AdaptiveQuery.RawReadout

open Matrix
open scoped ComplexOrder

section Reports

variable {A B J : Type*} [Fintype A] [Fintype B] [Fintype J] [DecidableEq J]

/-- The Gram tester retaining precisely the rows of `L` whose report label is `j`. -/
noncomputable def rawReportTester (L : Matrix A B ℂ) (label : A → J) (j : J) :
    Matrix B B ℂ := rawProcessTester L (fun a => decide (label a = j))

omit [Fintype J] in

/-- Every report tester is positive semidefinite. -/
theorem rawReportTester_posSemidef (L : Matrix A B ℂ) (label : A → J) (j : J) :
    (rawReportTester L label j).PosSemidef := rawProcessTester_posSemidef _ _

omit [Fintype B] in

/-- The sum of all report testers equals the full Gram matrix of `L`. -/
theorem rawReportTester_sum (L : Matrix A B ℂ) (label : A → J) :
    ∑ j, rawReportTester L label j = L.conjTranspose * L := by
  classical
  ext u v
  simp only [rawReportTester, rawProcessTester, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [rawProcessEventMatrix, eq_comm]

omit [Fintype B] [Fintype J] in

/-- A report label unused by every row has zero report tester. -/
theorem rawReportTester_unused (L : Matrix A B ℂ) (label : A → J) (j : J)
    (hj : ∀ a, label a ≠ j) : rawReportTester L label j = 0 := by
  ext u v
  simp [rawReportTester, rawProcessTester, Matrix.mul_apply, Matrix.conjTranspose_apply,
    rawProcessEventMatrix, hj]

/-- The real quadratic pairing with `M` equals the real part of the trace of `M *
Matrix.vecMulVec v (star v)`. -/
theorem rawProcessPairing_eq_trace (M : Matrix B B ℂ) (v : B → ℂ) :
    rawProcessPairing M v = (Matrix.trace (M * Matrix.vecMulVec v (star v))).re := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  rfl

end Reports

section Degrees

variable {A σ : Type*} [Fintype A] [Fintype σ] {N : ℕ}

/-- The submatrix of process coefficients restricted to columns of the fixed degree `q`. -/
noncomputable def rawFixedDegreeMatrix (L : Matrix A (RawProcessIndex σ N) ℂ)
    (q : Fin (N + 1)) : Matrix A (Fin q.val → σ) ℂ := fun a w => L a ⟨q,w⟩

/-- The diagonal block of a process-indexed matrix corresponding to monomial degree `q`. -/
noncomputable def rawDegreeBlock (T : Matrix (RawProcessIndex σ N) (RawProcessIndex σ N) ℂ)
    (q : Fin (N + 1)) : Matrix (Fin q.val → σ) (Fin q.val → σ) ℂ :=
  T.submatrix (fun w => ⟨q,w⟩) (fun w => ⟨q,w⟩)

/-- The product of variable values indexed by a word of length `q.val`. -/
noncomputable def rawTensorPower (x : σ → ℂ) (q : Fin (N + 1))
    (w : Fin q.val → σ) : ℂ := ∏ j, x (w j)

omit [Fintype σ] in

/-- The degree-`q` block of a full Gram matrix equals the Gram matrix of the degree-`q`
coefficient restriction. -/
theorem rawDegreeBlock_gram (L : Matrix A (RawProcessIndex σ N) ℂ) (q : Fin (N + 1)) :
    rawDegreeBlock (L.conjTranspose * L) q =
      (rawFixedDegreeMatrix L q).conjTranspose * rawFixedDegreeMatrix L q := by
  ext u v
  rfl

omit [Fintype σ] in

/-- Taking a degree block of an event tester gives the event tester of the fixed-degree
coefficient matrix. -/
theorem rawDegreeBlock_tester (L : Matrix A (RawProcessIndex σ N) ℂ)
    (e : A → Bool) (q : Fin (N + 1)) :
    rawDegreeBlock (rawProcessTester L e) q =
      rawProcessTester (rawFixedDegreeMatrix L q) e := by
  ext u v
  rfl

/-- Every diagonal degree block of an event tester is positive semidefinite. -/
theorem rawDegreeBlock_tester_posSemidef (L : Matrix A (RawProcessIndex σ N) ℂ)
    (e : A → Bool) (q : Fin (N + 1)) :
    (rawDegreeBlock (rawProcessTester L e) q).PosSemidef := by
  rw [rawDegreeBlock_tester]
  exact rawProcessTester_posSemidef _ _

omit [Fintype σ] in

/-- If each row of `L` is supported on one degree, its event testers have zero entries between
distinct degrees. -/
theorem rawProcessTester_cross_degree (L : Matrix A (RawProcessIndex σ N) ℂ)
    (degree : A → ℕ)
    (hL : ∀ a w, w.1.val ≠ degree a → L a w = 0)
    (e : A → Bool) (u v : RawProcessIndex σ N) (huv : u.1 ≠ v.1) :
    rawProcessTester L e u v = 0 := by
  classical
  unfold rawProcessTester
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases hu : u.1.val = degree a
  · have hv : v.1.val ≠ degree a := fun hv => huv (Fin.ext (hu.trans hv.symm))
    simp [rawProcessEventMatrix, hL a v hv]
  · simp [rawProcessEventMatrix, hL a u hu]

omit [Fintype A] in

/-- For a row supported at degree `q`, evaluation against the full tensor vector equals
evaluation of the degree restriction against `rawTensorPower x q`. -/
theorem rawFixedDegreeMatrix_evaluate (L : Matrix A (RawProcessIndex σ N) ℂ)
    (q : Fin (N + 1)) (a : A)
    (hL : ∀ w, w.1 ≠ q → L a w = 0) (x : σ → ℂ) :
    (L *ᵥ rawTensorVector x) a = (rawFixedDegreeMatrix L q *ᵥ rawTensorPower x q) a := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single q]
  · rfl
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro w _
    rw [hL ⟨r,w⟩ hr, zero_mul]
  · simp

/-- A matrix with zero entries between distinct degrees pairs with the full tensor vector as the
sum of its degree-block pairings. -/
theorem rawProcessPairing_sum_degree
    (T : Matrix (RawProcessIndex σ N) (RawProcessIndex σ N) ℂ)
    (hT : ∀ u v, u.1 ≠ v.1 → T u v = 0) (x : σ → ℂ) :
    rawProcessPairing T (rawTensorVector x) =
      ∑ q, rawProcessPairing (rawDegreeBlock T q) (rawTensorPower x q) := by
  classical
  unfold rawProcessPairing
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [Finset.sum_eq_single q]
  · rfl
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro v _
    rw [hT ⟨q,u⟩ ⟨r,v⟩ (Ne.symm hr), zero_mul]
  · simp

/-- When each coefficient row has its assigned degree, a degree block of the event tester pairs
to the sum of squared evaluated amplitudes selected by both the event and that degree. -/
theorem rawDegreeBlock_tester_pairing (L : Matrix A (RawProcessIndex σ N) ℂ)
    (degree : A → ℕ) (hL : ∀ a w, w.1.val ≠ degree a → L a w = 0)
    (e : A → Bool) (q : Fin (N + 1)) (x : σ → ℂ) :
    rawProcessPairing (rawDegreeBlock (rawProcessTester L e) q) (rawTensorPower x q) =
      ∑ a, if e a && decide (degree a = q.val) then ‖(L *ᵥ rawTensorVector x) a‖ ^ 2 else 0 := by
  classical
  rw [rawDegreeBlock_tester, rawProcessTester_pairing]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : degree a = q.val
  · have he := rawFixedDegreeMatrix_evaluate L q a (fun w hw => hL a w
        (fun h => hw (Fin.ext (h.trans ha)))) x
    simp only [ha, decide_true, Bool.and_true]
    rw [he]
  · have hz : (rawFixedDegreeMatrix L q *ᵥ rawTensorPower x q) a = 0 := by
      simp only [Matrix.mulVec, dotProduct, rawFixedDegreeMatrix]
      apply Finset.sum_eq_zero
      intro w _
      rw [hL a ⟨q,w⟩ (Ne.symm ha), zero_mul]
    simp [ha, hz]

end Degrees

section ObservedReports

variable {I σ J : Type*} [Fintype I] [DecidableEq I] [Fintype σ] [DecidableEq σ]
  [Fintype J] [DecidableEq J]

/-- The observed raw tester selecting symbolic leaves with report label `j`. -/
noncomputable def observedRawReportTester (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (label : ObservedRawIndex Q P → J) (j : J) :=
  observedRawTester Q P ψ (fun i => decide (label i = j))

omit [Fintype J] in

/-- Every observed raw report tester is positive semidefinite. -/
theorem observedRawReportTester_posSemidef (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (label : ObservedRawIndex Q P → J) (j : J) :
    (observedRawReportTester Q P ψ label j).PosSemidef := observedRawTester_posSemidef _ _ _ _

omit [Fintype J] in

/-- The observed raw normalizer minus any report tester is positive semidefinite. -/
theorem observedRawReportTester_le_normalizer (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (label : ObservedRawIndex Q P → J) (j : J) :
    (observedRawNormalizer Q P ψ - observedRawReportTester Q P ψ label j).PosSemidef :=
  observedRawTester_le_normalizer _ _ _ _

omit [Fintype σ] in

/-- The observed raw report testers sum to the observed raw normalizer. -/
theorem observedRawReportTester_sum (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (label : ObservedRawIndex Q P → J) :
    ∑ j, observedRawReportTester Q P ψ label j = observedRawNormalizer Q P ψ :=
  rawReportTester_sum (observedRawProcessMatrix Q P ψ) (fun a => label a.1)

omit [Fintype J] in

/-- For homogeneous degree-one queries, a report tester pairs with the tensor vector to the
total evaluated mass of leaves carrying that report. -/
theorem observedRawReportTester_pairing (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) (label : ObservedRawIndex Q P → J) (j : J) :
    rawProcessPairing (observedRawReportTester Q P ψ label j) (rawTensorVector x) =
      ∑ i, if label i = j then branchMass ((observedRawLeaf Q P i).toTrace x ψ).state else 0 := by
  simpa [observedRawReportTester] using
    observedRawTester_pairing Q hQ x P ψ (fun i => decide (label i = j))

/-- The finite report distribution obtained by grouping branch masses of a normalized,
well-formed execution with a unitary evaluated query by their report labels. -/
noncomputable def observedRawReportDistribution (Q : Matrix I I (MvPolynomial σ ℂ))
    (x : σ → ℂ) (P : ObservedCircuit I) (ψ : QState I)
    (label : ObservedRawIndex Q P → J)
    (hO : rawEvaluateMatrix x Q ∈ Matrix.unitaryGroup I ℂ)
    (hP : observedWellFormed P) (hψ : Normalized ψ) : FinDist J where
  prob j := ∑ i, if label i = j then branchMass ((observedRawLeaf Q P i).toTrace x ψ).state else 0
  nonneg j := Finset.sum_nonneg (fun i _ => by
    split_ifs
    · exact branchMass_nonneg _
    · exact le_rfl)
  sum_one := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have h := observedTraces_mass_eq_one _ hO P hP hψ
    rw [observedTraces_eq_raw_ofFn] at h
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using h

/-- For homogeneous degree-one queries, the probability of a report equals its raw report tester
pairing with the tensor vector. -/
theorem observedRawReportDistribution_pairing (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) (label : ObservedRawIndex Q P → J)
    (hO : rawEvaluateMatrix x Q ∈ Matrix.unitaryGroup I ℂ)
    (hP : observedWellFormed P) (hψ : Normalized ψ) (j : J) :
    (observedRawReportDistribution Q x P ψ label hO hP hψ).prob j =
      rawProcessPairing (observedRawReportTester Q P ψ label j) (rawTensorVector x) :=
  (observedRawReportTester_pairing Q hQ x P ψ label j).symm

omit [Fintype σ] in

/-- For homogeneous degree-one queries, an observed raw event tester has zero entries between
different monomial degrees. -/
theorem observedRawTester_cross_degree (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (P : ObservedCircuit I) (ψ : QState I)
    (e : ObservedRawIndex Q P → Bool)
    (u v : RawProcessIndex σ (observedQueryBudget P)) (huv : u.1 ≠ v.1) :
    observedRawTester Q P ψ e u v = 0 :=
  rawProcessTester_cross_degree _ (fun a => (observedRawLeaf Q P a.1).queries)
    (observedRawProcessMatrix_degree Q hQ P ψ) _ u v huv

omit [Fintype σ] in

/-- For homogeneous degree-one queries, the observed raw normalizer has zero entries between
different monomial degrees. -/
theorem observedRawNormalizer_cross_degree (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (P : ObservedCircuit I) (ψ : QState I)
    (u v : RawProcessIndex σ (observedQueryBudget P)) (huv : u.1 ≠ v.1) :
    observedRawNormalizer Q P ψ u v = 0 := by
  simpa [observedRawTester, rawProcessTester, rawProcessEventMatrix, observedRawNormalizer] using!
    observedRawTester_cross_degree Q hQ P ψ (fun _ => true) u v huv

/-- For homogeneous degree-one queries, the observed raw event tester pairing is the sum of its
fixed-degree block pairings. -/
theorem observedRawTester_sum_degree (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) (e : ObservedRawIndex Q P → Bool) :
    rawProcessPairing (observedRawTester Q P ψ e) (rawTensorVector x) =
      ∑ q, rawProcessPairing (rawDegreeBlock (observedRawTester Q P ψ e) q)
        (rawTensorPower x q) :=
  rawProcessPairing_sum_degree _ (observedRawTester_cross_degree Q hQ P ψ e) x

/-- Every fixed-degree diagonal block of an observed raw event tester is positive semidefinite. -/
theorem observedRawTester_degree_posSemidef (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (e : ObservedRawIndex Q P → Bool)
    (q : Fin (observedQueryBudget P + 1)) :
    (rawDegreeBlock (observedRawTester Q P ψ e) q).PosSemidef :=
  rawDegreeBlock_tester_posSemidef _ _ _

/-- For homogeneous degree-one queries, the degree-`q` event tester pairing equals the mass of
selected traces with exactly `q.val` queries. -/
theorem observedRawTester_degree_pairing (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) (e : ObservedRawIndex Q P → Bool)
    (q : Fin (observedQueryBudget P + 1)) :
    rawProcessPairing (rawDegreeBlock (observedRawTester Q P ψ e) q) (rawTensorPower x q) =
      ∑ i, if e i && decide ((observedRawLeaf Q P i).queries = q.val)
        then branchMass ((observedRawLeaf Q P i).toTrace x ψ).state else 0 := by
  rw [observedRawTester, rawDegreeBlock_tester_pairing _
    (fun a => (observedRawLeaf Q P a.1).queries) (observedRawProcessMatrix_degree Q hQ P ψ)]
  rw [observedRawProcessMatrix_evaluate Q hQ, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [branchMass, MeasureProb, BornProb]

/-- For homogeneous degree-one queries, the degree-`q` normalizer pairing equals the total mass
of traces with exactly `q.val` queries. -/
theorem observedRawNormalizer_degree_pairing (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) (q : Fin (observedQueryBudget P + 1)) :
    rawProcessPairing (rawDegreeBlock (observedRawNormalizer Q P ψ) q) (rawTensorPower x q) =
      ∑ i, if (observedRawLeaf Q P i).queries = q.val
        then branchMass ((observedRawLeaf Q P i).toTrace x ψ).state else 0 := by
  simpa [observedRawTester, rawProcessTester, rawProcessEventMatrix, observedRawNormalizer] using!
    observedRawTester_degree_pairing Q hQ x P ψ (fun _ => true) q

/-- For homogeneous degree-one queries evaluating to a unitary, a well-formed circuit and
normalized input give degree-block normalizer pairings whose sum is one. -/
theorem observedRawNormalizer_sum_degree_complete (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (hO : rawEvaluateMatrix x Q ∈ Matrix.unitaryGroup I ℂ)
    (P : ObservedCircuit I) (hP : observedWellFormed P) (ψ : QState I) (hψ : Normalized ψ) :
    (∑ q, rawProcessPairing (rawDegreeBlock (observedRawNormalizer Q P ψ) q)
      (rawTensorPower x q)) = 1 := by
  rw [← rawProcessPairing_sum_degree _ (observedRawNormalizer_cross_degree Q hQ P ψ) x]
  exact observedRawNormalizer_complete Q hQ x hO P hP ψ hψ

end ObservedReports

end Qatlib.Concepts.AdaptiveQuery.RawReadout
