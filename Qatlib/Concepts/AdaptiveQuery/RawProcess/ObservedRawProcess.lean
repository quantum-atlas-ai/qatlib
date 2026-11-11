/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveQuery.RawProcess.ObservedCircuitLaws
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Polynomial process matrices for observed query circuits

This module expands observed circuits into polynomial operator leaves while retaining outcome
histories and resource counts. When query entries are homogeneous of degree one, each leaf
amplitude is homogeneous of its query count, and `observedRawProcessMatrix` evaluates on
`rawTensorVector` to the branch amplitudes.

Gram matrices encode branch events and total mass through `observedRawTester` and
`observedRawNormalizer`. The forward-query specialization treats an oracle acting on a data
register with an untouched workspace. For background, see [BealsEtAl2001].

## Main statements

* `observedRawLeaves`: Expand an observed circuit into its list of symbolic terminal leaves
  using polynomial query matrix `Q` and constant known gates and projectors.
* `observedRawProcessMatrix_evaluate`: With homogeneous degree-one query entries, the raw
  process matrix applied to the tensor vector gives every evaluated branch amplitude.
* `observedRawTester_acceptance`: With degree-one query entries, the raw tester selecting
  accepted leaves pairs with the tensor vector to the observed acceptance mass.
* `forwardObservedRawNormalizer_complete`: For a unitary oracle, well-formed observed circuit,
  and normalized input, the forward raw normalizer pairs with the tensor vector of oracle
  entries to one.

## References

* [Beals et al., 2001][BealsEtAl2001]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdaptiveQuery.RawProcess

open Matrix
open scoped ComplexOrder

variable {I σ : Type*} [Fintype I] [DecidableEq I] [DecidableEq σ]

/-- A symbolic terminal branch stores its polynomial operator, acceptance flag, query and gate
counts, measurement count, and outcome history. -/
structure ObservedRawLeaf (I σ : Type*) where
  operator : Matrix I I (MvPolynomial σ ℂ)
  accepted : Bool
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  outcomes : List (ℕ × ℕ)

/-- Prepend a symbolic operator and resource increments to a raw leaf, multiplying its operator
on the right and prefixing the outcome history. -/
noncomputable def ObservedRawLeaf.prepend (G : Matrix I I (MvPolynomial σ ℂ))
    (q g m : ℕ) (os : List (ℕ × ℕ)) (leaf : ObservedRawLeaf I σ) :
    ObservedRawLeaf I σ :=
  ⟨leaf.operator * G, leaf.accepted, leaf.queries + q, leaf.gates + g,
    leaf.measurements + m, os ++ leaf.outcomes⟩

/-- Embed a known complex matrix as a matrix of constant multivariate polynomials. -/
noncomputable def rawKnownMatrix (G : Matrix I I ℂ) :
    Matrix I I (MvPolynomial σ ℂ) := G.map MvPolynomial.C

/-- Evaluate each polynomial entry of a symbolic matrix at the variable assignment `x`. -/
noncomputable def rawEvaluateMatrix (x : σ → ℂ)
    (G : Matrix I I (MvPolynomial σ ℂ)) : Matrix I I ℂ :=
  G.map (MvPolynomial.eval x)

omit [Fintype I] [DecidableEq I] [DecidableEq σ] in

/-- Evaluating a matrix of constant polynomials recovers the original complex matrix. -/
@[simp] theorem rawEvaluateMatrix_known (x : σ → ℂ) (G : Matrix I I ℂ) :
    rawEvaluateMatrix x (rawKnownMatrix G) = G := by
  ext i j
  simp [rawEvaluateMatrix, rawKnownMatrix]

omit [DecidableEq I] [DecidableEq σ] in

/-- Polynomial matrix evaluation preserves matrix multiplication. -/
@[simp] theorem rawEvaluateMatrix_mul (x : σ → ℂ)
    (A B : Matrix I I (MvPolynomial σ ℂ)) :
    rawEvaluateMatrix x (A * B) = rawEvaluateMatrix x A * rawEvaluateMatrix x B := by
  ext i j
  simp [rawEvaluateMatrix, Matrix.mul_apply, map_sum, map_mul]

/-- Evaluate a raw leaf operator on an input state and retain its acceptance flag, resource
counts, and outcome history as a branch trace. -/
noncomputable def ObservedRawLeaf.toTrace (x : σ → ℂ) (ψ : QState I)
    (leaf : ObservedRawLeaf I σ) : BranchTrace I :=
  ⟨ApplyGate (rawEvaluateMatrix x leaf.operator) ψ, leaf.accepted, leaf.queries,
    leaf.gates, leaf.measurements, leaf.outcomes⟩

/-- Expand an observed circuit into its list of symbolic terminal leaves using polynomial query
matrix `Q` and constant known gates and projectors. -/
noncomputable def observedRawLeaves (Q : Matrix I I (MvPolynomial σ ℂ)) :
    ObservedCircuit I → List (ObservedRawLeaf I σ)
  | .halt a => [⟨1, a, 0, 0, 0, []⟩]
  | .step (.gate G) P =>
      (observedRawLeaves Q P).map (.prepend (rawKnownMatrix G) 0 1 0 [])
  | .step .query P => (observedRawLeaves Q P).map (.prepend Q 1 0 0 [])
  | .measure n label next =>
      (List.ofFn (fun o : Fin n => (observedRawLeaves Q (next o)).map
        (.prepend (rawKnownMatrix (Projector (Finset.univ.filter (fun i => label i = o))))
          0 0 1 [(n, o.val)]))).flatten
  | .project P onFalse onTrue =>
      (observedRawLeaves Q onFalse).map
        (.prepend (rawKnownMatrix (1 - P)) 0 0 1 [(2, 0)]) ++
      (observedRawLeaves Q onTrue).map
        (.prepend (rawKnownMatrix P) 0 0 1 [(2, 1)])

omit [DecidableEq σ] in

/-- Observed execution with the evaluated query matrix equals the list of evaluated symbolic
leaves. -/
theorem observedTraces_eq_rawLeaves (Q : Matrix I I (MvPolynomial σ ℂ))
    (x : σ → ℂ) (P : ObservedCircuit I) (ψ : QState I) :
    observedTraces (rawEvaluateMatrix x Q) P ψ =
      (observedRawLeaves Q P).map (ObservedRawLeaf.toTrace x ψ) := by
  induction P generalizing ψ with
  | halt a =>
      simp [observedTraces, observedRawLeaves, ObservedRawLeaf.toTrace,
        rawEvaluateMatrix, applyGate_one]
  | step s P ih =>
      cases s <;>
        simp [observedTraces, observedRawLeaves, ih, List.map_map, Function.comp_def,
          ObservedRawLeaf.toTrace, ObservedRawLeaf.prepend, applyGate_mul]
  | measure n label next ih =>
      simp [observedTraces, observedRawLeaves, ih, List.map_flatten, List.map_ofFn,
        List.map_map, Function.comp_def, ObservedRawLeaf.toTrace,
        ObservedRawLeaf.prepend, Collapse, applyGate_mul]
  | project A P R ihP ihR =>
      simp [observedTraces, observedRawLeaves, ihP, ihR, List.map_append,
        List.map_map, Function.comp_def, ObservedRawLeaf.toTrace,
        ObservedRawLeaf.prepend, ProjectiveBranch, applyGate_mul]

omit [Fintype I] [DecidableEq I] [DecidableEq σ] in

/-- Every entry of a known constant polynomial matrix is homogeneous of degree zero. -/
private theorem rawKnownMatrix_homogeneous (G : Matrix I I ℂ) (i j : I) :
    (rawKnownMatrix (σ := σ) G i j).IsHomogeneous 0 :=
  MvPolynomial.isHomogeneous_C _ _

omit [DecidableEq I] [DecidableEq σ] in

/-- Multiplying matrices with entries homogeneous of degrees `a` and `b` gives entries
homogeneous of degree `a + b`. -/
private theorem rawMatrix_mul_homogeneous
    (A B : Matrix I I (MvPolynomial σ ℂ)) (a b : ℕ)
    (hA : ∀ i j, (A i j).IsHomogeneous a)
    (hB : ∀ i j, (B i j).IsHomogeneous b) (i j : I) :
    ((A * B) i j).IsHomogeneous (a + b) := by
  exact MvPolynomial.IsHomogeneous.sum Finset.univ _ _
    (fun k _ => (hA i k).mul (hB k j))

omit [DecidableEq σ] in

/-- If every query entry is homogeneous of degree one, each raw leaf operator entry is
homogeneous of its leaf query count. -/
theorem observedRawLeaves_homogeneous (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (P : ObservedCircuit I) :
    ∀ leaf ∈ observedRawLeaves Q P, ∀ i j,
      (leaf.operator i j).IsHomogeneous leaf.queries := by
  induction P with
  | halt a =>
      intro leaf hl i j
      simp only [observedRawLeaves, List.mem_singleton] at hl
      subst leaf
      by_cases hij : i = j <;>
        simp [Matrix.one_apply, hij, MvPolynomial.isHomogeneous_one,
          MvPolynomial.isHomogeneous_zero]
  | step s P ih =>
      cases s with
      | gate G =>
          intro leaf hl i j
          obtain ⟨l, hlmem, rfl⟩ := List.mem_map.mp hl
          exact rawMatrix_mul_homogeneous _ _ _ _ (ih l hlmem)
            (rawKnownMatrix_homogeneous G) i j
      | query =>
          intro leaf hl i j
          obtain ⟨l, hlmem, rfl⟩ := List.mem_map.mp hl
          exact rawMatrix_mul_homogeneous _ _ _ _ (ih l hlmem) hQ i j
  | measure n label next ih =>
      intro leaf hl i j
      obtain ⟨ls, hls, hl⟩ := List.mem_flatten.mp hl
      obtain ⟨o, rfl⟩ := List.mem_ofFn.mp hls
      obtain ⟨l, hlmem, rfl⟩ := List.mem_map.mp hl
      exact rawMatrix_mul_homogeneous _ _ _ _ (ih o l hlmem)
        (rawKnownMatrix_homogeneous _) i j
  | project A P R ihP ihR =>
      intro leaf hl i j
      rcases List.mem_append.mp hl with hl | hl
      · obtain ⟨l, hlmem, rfl⟩ := List.mem_map.mp hl
        exact rawMatrix_mul_homogeneous _ _ _ _ (ihP l hlmem)
          (rawKnownMatrix_homogeneous _) i j
      · obtain ⟨l, hlmem, rfl⟩ := List.mem_map.mp hl
        exact rawMatrix_mul_homogeneous _ _ _ _ (ihR l hlmem)
          (rawKnownMatrix_homogeneous _) i j

/-- The symbolic forward query on a data register and workspace, with one variable for each
data-matrix entry and the identity on the workspace. -/
noncomputable def rawLiftedQuery {D W : Type*} [DecidableEq W] :
    Matrix (D × W) (D × W) (MvPolynomial (D × D) ℂ) :=
  fun a b => MvPolynomial.X (a.1, b.1) * MvPolynomial.C (if a.2 = b.2 then 1 else 0)

/-- Every entry of the symbolic lifted query is homogeneous of degree one. -/
theorem rawLiftedQuery_homogeneous {D W : Type*} [DecidableEq D] [DecidableEq W]
    (i j : D × W) :
    (rawLiftedQuery i j).IsHomogeneous 1 := by
  simpa only [add_zero] using!
    (MvPolynomial.isHomogeneous_X ℂ (i.1, j.1)).mul
      (MvPolynomial.isHomogeneous_C (D × D) (if i.2 = j.2 then 1 else 0 : ℂ))

/-- Substituting the entries of `U` into the symbolic lifted query gives `TensorGate U 1`. -/
theorem rawLiftedQuery_evaluate {D W : Type*} [Fintype D] [DecidableEq D]
    [Fintype W] [DecidableEq W] (U : Matrix D D ℂ) :
    rawEvaluateMatrix (fun a : D × D => U a.1 a.2)
      (rawLiftedQuery (D := D) (W := W)) = TensorGate U (1 : Matrix W W ℂ) := by
  ext i j
  simp [rawEvaluateMatrix, rawLiftedQuery, TensorGate,
    Matrix.one_apply, apply_ite (MvPolynomial.eval _)]

/-- An index consisting of a degree at most `N` and an ordered list of that many polynomial
variables. -/
abbrev RawProcessIndex (σ : Type*) (N : ℕ) :=
  (q : Fin (N + 1)) × (Fin q.val → σ)

/-- The product of the assigned variable values in an ordered monomial index, including the
empty product at degree zero. -/
noncomputable def rawTensorVector {N : ℕ} (x : σ → ℂ)
    (w : RawProcessIndex σ N) : ℂ := ∏ j, x (w.2 j)

omit [DecidableEq σ] in

/-- The length of the list representing a finitely supported exponent multiset equals its total
degree. -/
private theorem rawExponent_length (m : σ →₀ ℕ) :
    m.toMultiset.toList.length = m.degree := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  rfl

/-- Encode an exponent multiset as an ordered monomial index when its degree is at most `N`,
returning `none` otherwise. -/
noncomputable def rawExponentIndex (N : ℕ) (m : σ →₀ ℕ) :
    Option (RawProcessIndex σ N) :=
  if h : m.toMultiset.toList.length ≤ N then
    some ⟨⟨m.toMultiset.toList.length, Nat.lt_succ_iff.mpr h⟩,
      fun j => m.toMultiset.toList[j.val]⟩
  else none

omit [DecidableEq σ] in

/-- The product over the ordered exponent list equals the product of variable values raised to
their multiplicities. -/
private theorem rawExponent_product (m : σ →₀ ℕ) (x : σ → ℂ) :
    (∏ j : Fin m.toMultiset.toList.length, x m.toMultiset.toList[j.val]) =
      m.prod (fun a n => x a ^ n) := by
  classical
  rw [Fin.prod_univ_fun_getElem, Multiset.prod_map_toList,
    Finsupp.toMultiset_map, Finsupp.prod_toMultiset]
  exact Finsupp.prod_mapDomain_index (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)

omit [DecidableEq σ] in

/-- An exponent of degree at most `N` has an encoded index of the same degree whose
tensor-vector value equals its monomial evaluation. -/
private theorem rawExponentIndex_spec (N : ℕ) (m : σ →₀ ℕ)
    (hm : m.degree ≤ N) (x : σ → ℂ) :
    ∃ w, rawExponentIndex N m = some w ∧
      rawTensorVector x w = m.prod (fun a n => x a ^ n) ∧ w.1.val = m.degree := by
  have hl : m.toMultiset.toList.length ≤ N := (rawExponent_length m).trans_le hm
  refine ⟨⟨⟨_, Nat.lt_succ_iff.mpr hl⟩, fun j => m.toMultiset.toList[j.val]⟩,
    ?_, rawExponent_product m x, rawExponent_length m⟩
  simp only [rawExponentIndex, dif_pos hl]

section Coefficients

variable {A : Type*} [Fintype A] [Fintype σ]

/-- The coefficient matrix expressing a family of polynomials in the ordered monomial indices of
degrees at most `N`. -/
noncomputable def rawPolynomialCoefficients (N : ℕ) (p : A → MvPolynomial σ ℂ) :
    Matrix A (RawProcessIndex σ N) ℂ :=
  fun a w => ∑ m ∈ (p a).support,
    if rawExponentIndex N m = some w then (p a).coeff m else 0

omit [Fintype A] in

/-- For polynomials supported in degrees at most `N`, multiplying the coefficient matrix by the
tensor vector gives their evaluations. -/
theorem rawPolynomialCoefficients_evaluate (N : ℕ) (p : A → MvPolynomial σ ℂ)
    (hp : ∀ a m, m ∈ (p a).support → m.degree ≤ N) (x : σ → ℂ) :
    rawPolynomialCoefficients N p *ᵥ rawTensorVector x =
      fun a => MvPolynomial.eval x (p a) := by
  classical
  funext a
  simp only [Matrix.mulVec, dotProduct, rawPolynomialCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨w, hw, hprod, _⟩ := rawExponentIndex_spec N m (hp a m hm) x
  simp only [hw, Option.some.injEq]
  rw [Finset.sum_eq_single w]
  · simp only [ite_true, hprod, Finsupp.prod]
  · intro v _ hv
    simp [hv.symm]
  · simp

omit [Fintype A] [Fintype σ] in

/-- For a homogeneous polynomial family, the coefficient matrix vanishes at indices whose
degrees differ from the corresponding polynomial degree. -/
theorem rawPolynomialCoefficients_degree (N : ℕ) (p : A → MvPolynomial σ ℂ)
    (q : A → ℕ) (hp : ∀ a, (p a).IsHomogeneous (q a))
    (a : A) (w : RawProcessIndex σ N) (hw : w.1.val ≠ q a) :
    rawPolynomialCoefficients N p a w = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro m hm
  by_cases he : rawExponentIndex N m = some w
  · have hdeg : m.degree = q a := by
      simpa only [Finsupp.degree_eq_weight_one] using!
        (hp a) (MvPolynomial.mem_support_iff.mp hm)
    have hlen : w.1.val = m.degree := by
      unfold rawExponentIndex at he
      split_ifs at he with h
      · cases Option.some.inj he
        exact rawExponent_length m
    exact (hw (hlen.trans hdeg)).elim
  · simp [he]

end Coefficients

/-- The finite index type of the symbolic leaves of an observed circuit. -/
abbrev ObservedRawIndex (Q : Matrix I I (MvPolynomial σ ℂ)) (P : ObservedCircuit I) :=
  Fin (observedRawLeaves Q P).length

/-- The symbolic leaf selected by a finite index into `observedRawLeaves`. -/
noncomputable def observedRawLeaf (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (i : ObservedRawIndex Q P) : ObservedRawLeaf I σ :=
  (observedRawLeaves Q P).get i

omit [DecidableEq σ] in

/-- The observed trace list is the finite indexed list of evaluated raw leaves. -/
theorem observedTraces_eq_raw_ofFn (Q : Matrix I I (MvPolynomial σ ℂ))
    (x : σ → ℂ) (P : ObservedCircuit I) (ψ : QState I) :
    observedTraces (rawEvaluateMatrix x Q) P ψ =
      List.ofFn (fun i => (observedRawLeaf Q P i).toTrace x ψ) := by
  rw [observedTraces_eq_rawLeaves]
  simpa only [observedRawLeaf, List.ofFn_get] using!
    (List.map_ofFn (f := (observedRawLeaves Q P).get)
      (g := ObservedRawLeaf.toTrace x ψ))

omit [DecidableEq σ] in

/-- The query count of every indexed raw leaf is bounded by the circuit query budget. -/
theorem observedRawLeaf_queries_le (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (i : ObservedRawIndex Q P) :
    (observedRawLeaf Q P i).queries ≤ observedQueryBudget P := by
  let x : σ → ℂ := fun _ => 0
  have ht : (observedRawLeaf Q P i).toTrace x 0 ∈
      observedTraces (rawEvaluateMatrix x Q) P 0 := by
    rw [observedTraces_eq_rawLeaves]
    exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
  exact queries_le_observedQueryBudget _ P 0 ht

/-- The polynomial amplitude at a selected raw leaf and output coordinate for the fixed input
state. -/
noncomputable def observedRawAmplitude (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (a : ObservedRawIndex Q P × I) :
    MvPolynomial σ ℂ :=
  ∑ j, (observedRawLeaf Q P a.1).operator a.2 j * MvPolynomial.C (ψ j)

omit [DecidableEq σ] in

/-- Evaluating a raw amplitude polynomial gives the corresponding coordinate of the evaluated
branch state. -/
theorem observedRawAmplitude_evaluate (Q : Matrix I I (MvPolynomial σ ℂ))
    (x : σ → ℂ) (P : ObservedCircuit I) (ψ : QState I)
    (a : ObservedRawIndex Q P × I) :
    MvPolynomial.eval x (observedRawAmplitude Q P ψ a) =
      ((observedRawLeaf Q P a.1).toTrace x ψ).state a.2 := by
  simp [observedRawAmplitude, ObservedRawLeaf.toTrace, ApplyGate,
    rawEvaluateMatrix, Matrix.mulVec, dotProduct, map_sum, map_mul]

omit [DecidableEq σ] in

/-- With degree-one query entries, every raw amplitude polynomial is homogeneous of the query
count of its leaf. -/
theorem observedRawAmplitude_homogeneous (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (P : ObservedCircuit I) (ψ : QState I)
    (a : ObservedRawIndex Q P × I) :
    (observedRawAmplitude Q P ψ a).IsHomogeneous
      (observedRawLeaf Q P a.1).queries := by
  apply MvPolynomial.IsHomogeneous.sum Finset.univ
  intro j _
  simpa only [add_zero] using!
    (observedRawLeaves_homogeneous Q hQ P _ (List.get_mem _ _) a.2 j).mul
      (MvPolynomial.isHomogeneous_C σ (ψ j))

section Process

variable [Fintype σ]

/-- The coefficient matrix of all raw branch amplitudes in monomial indices up to the circuit
query budget. -/
noncomputable def observedRawProcessMatrix (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) :
    Matrix (ObservedRawIndex Q P × I) (RawProcessIndex σ (observedQueryBudget P)) ℂ :=
  rawPolynomialCoefficients (observedQueryBudget P) (observedRawAmplitude Q P ψ)

/-- With homogeneous degree-one query entries, the raw process matrix applied to the tensor
vector gives every evaluated branch amplitude. -/
theorem observedRawProcessMatrix_evaluate (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) :
    observedRawProcessMatrix Q P ψ *ᵥ rawTensorVector x =
      fun a => ((observedRawLeaf Q P a.1).toTrace x ψ).state a.2 := by
  have hp (a : ObservedRawIndex Q P × I) (m : σ →₀ ℕ)
      (hm : m ∈ (observedRawAmplitude Q P ψ a).support) : m.degree ≤ observedQueryBudget P := by
    have he : m.degree = (observedRawLeaf Q P a.1).queries := by
      simpa only [Finsupp.degree_eq_weight_one] using!
        observedRawAmplitude_homogeneous Q hQ P ψ a (MvPolynomial.mem_support_iff.mp hm)
    exact he.trans_le (observedRawLeaf_queries_le Q P a.1)
  exact (rawPolynomialCoefficients_evaluate _ _ hp x).trans
    (funext (observedRawAmplitude_evaluate Q x P ψ))

omit [Fintype σ] in

/-- A raw process matrix entry vanishes when its monomial degree differs from the query count of
the associated leaf. -/
theorem observedRawProcessMatrix_degree (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (P : ObservedCircuit I) (ψ : QState I)
    (a : ObservedRawIndex Q P × I) (w : RawProcessIndex σ (observedQueryBudget P))
    (hw : w.1.val ≠ (observedRawLeaf Q P a.1).queries) :
    observedRawProcessMatrix Q P ψ a w = 0 :=
  rawPolynomialCoefficients_degree _ _ _ (observedRawAmplitude_homogeneous Q hQ P ψ) a w hw

end Process

section Gram

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The real quadratic pairing of a complex matrix with a vector, given by the real part of `v†
M v`. -/
noncomputable def rawProcessPairing (M : Matrix B B ℂ) (v : B → ℂ) : ℝ :=
  (star v ⬝ᵥ (M *ᵥ v)).re

/-- The quadratic pairing with the Gram matrix `L.conjTranspose * L` equals the sum of squared
coordinate norms of `L *ᵥ v`. -/
theorem rawProcessPairing_gram (L : Matrix A B ℂ) (v : B → ℂ) :
    rawProcessPairing (L.conjTranspose * L) v = ∑ a, ‖(L *ᵥ v) a‖ ^ 2 := by
  unfold rawProcessPairing
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- The matrix obtained from `L` by keeping rows satisfying the Boolean event and replacing all
other rows by zero. -/
noncomputable def rawProcessEventMatrix (L : Matrix A B ℂ) (e : A → Bool) : Matrix A B ℂ :=
  fun a b => if e a then L a b else 0

/-- The Gram matrix of the rows selected by a Boolean event. -/
noncomputable def rawProcessTester (L : Matrix A B ℂ) (e : A → Bool) : Matrix B B ℂ :=
  (rawProcessEventMatrix L e).conjTranspose * rawProcessEventMatrix L e

/-- A raw process tester is positive semidefinite. -/
theorem rawProcessTester_posSemidef (L : Matrix A B ℂ) (e : A → Bool) :
    (rawProcessTester L e).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype B] in

/-- The testers of an event and its complement sum to the full Gram matrix. -/
theorem rawProcessTester_add_complement (L : Matrix A B ℂ) (e : A → Bool) :
    rawProcessTester L e + rawProcessTester L (fun a => !(e a)) = L.conjTranspose * L := by
  ext i j
  simp only [rawProcessTester, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, rawProcessEventMatrix, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rcases Bool.eq_false_or_eq_true (e a) with h | h <;> simp [h]

/-- The full Gram matrix minus an event tester is positive semidefinite. -/
theorem rawProcessTester_le_normalizer (L : Matrix A B ℂ) (e : A → Bool) :
    (L.conjTranspose * L - rawProcessTester L e).PosSemidef := by
  rw [← rawProcessTester_add_complement L e, add_sub_cancel_left]
  exact rawProcessTester_posSemidef _ _

/-- Pairing an event tester with a vector gives the sum of the selected squared coordinate norms
of `L *ᵥ v`. -/
theorem rawProcessTester_pairing (L : Matrix A B ℂ) (e : A → Bool) (v : B → ℂ) :
    rawProcessPairing (rawProcessTester L e) v =
      ∑ a, if e a then ‖(L *ᵥ v) a‖ ^ 2 else 0 := by
  rw [rawProcessTester, rawProcessPairing_gram]
  apply Finset.sum_congr rfl
  intro a _
  rcases Bool.eq_false_or_eq_true (e a) with h | h <;>
    simp [rawProcessEventMatrix, Matrix.mulVec, dotProduct, h]

end Gram

section Born

variable [Fintype σ]

/-- The Gram tester selecting all output coordinates of the raw leaves satisfying the branch
event. -/
noncomputable def observedRawTester (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (e : ObservedRawIndex Q P → Bool) :
    Matrix (RawProcessIndex σ (observedQueryBudget P))
      (RawProcessIndex σ (observedQueryBudget P)) ℂ :=
  rawProcessTester (observedRawProcessMatrix Q P ψ) (fun a => e a.1)

/-- The full Gram matrix of the observed raw process matrix, encoding total branch mass. -/
noncomputable def observedRawNormalizer (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) :
    Matrix (RawProcessIndex σ (observedQueryBudget P))
      (RawProcessIndex σ (observedQueryBudget P)) ℂ :=
  (observedRawProcessMatrix Q P ψ).conjTranspose * observedRawProcessMatrix Q P ψ

/-- Every observed raw event tester is positive semidefinite. -/
theorem observedRawTester_posSemidef (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (e : ObservedRawIndex Q P → Bool) :
    (observedRawTester Q P ψ e).PosSemidef := rawProcessTester_posSemidef _ _

/-- The observed raw normalizer is positive semidefinite. -/
theorem observedRawNormalizer_posSemidef (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) :
    (observedRawNormalizer Q P ψ).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _

/-- The observed raw normalizer minus any observed raw event tester is positive semidefinite. -/
theorem observedRawTester_le_normalizer (Q : Matrix I I (MvPolynomial σ ℂ))
    (P : ObservedCircuit I) (ψ : QState I) (e : ObservedRawIndex Q P → Bool) :
    (observedRawNormalizer Q P ψ - observedRawTester Q P ψ e).PosSemidef :=
  rawProcessTester_le_normalizer _ _

/-- With degree-one query entries, pairing an observed raw tester with the tensor vector gives
the sum of the selected evaluated branch masses. -/
theorem observedRawTester_pairing (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) (e : ObservedRawIndex Q P → Bool) :
    rawProcessPairing (observedRawTester Q P ψ e) (rawTensorVector x) =
      ∑ i, if e i then branchMass ((observedRawLeaf Q P i).toTrace x ψ).state else 0 := by
  rw [observedRawTester, rawProcessTester_pairing, observedRawProcessMatrix_evaluate Q hQ]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rcases Bool.eq_false_or_eq_true (e i) with h | h <;>
    simp [h, branchMass, MeasureProb, BornProb]

/-- With degree-one query entries, pairing the raw normalizer with the tensor vector gives the
total observed terminal branch mass. -/
theorem observedRawNormalizer_pairing (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) :
    rawProcessPairing (observedRawNormalizer Q P ψ) (rawTensorVector x) =
      ((observedTraces (rawEvaluateMatrix x Q) P ψ).map
        (fun t => branchMass t.state)).sum := by
  rw [observedRawNormalizer, rawProcessPairing_gram,
    observedRawProcessMatrix_evaluate Q hQ, observedTraces_eq_raw_ofFn]
  simp [Fintype.sum_prod_type, List.map_ofFn, List.sum_ofFn,
    branchMass, MeasureProb, BornProb]

/-- For a unitary evaluated query, a well-formed observed circuit, and a normalized input, the
raw normalizer pairs with the tensor vector to one. -/
theorem observedRawNormalizer_complete (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (hO : rawEvaluateMatrix x Q ∈ Matrix.unitaryGroup I ℂ)
    (P : ObservedCircuit I) (hP : observedWellFormed P)
    (ψ : QState I) (hψ : Normalized ψ) :
    rawProcessPairing (observedRawNormalizer Q P ψ) (rawTensorVector x) = 1 := by
  rw [observedRawNormalizer_pairing Q hQ]
  exact observedTraces_mass_eq_one _ hO P hP hψ

/-- With degree-one query entries, the raw tester selecting accepted leaves pairs with the
tensor vector to the observed acceptance mass. -/
theorem observedRawTester_acceptance (Q : Matrix I I (MvPolynomial σ ℂ))
    (hQ : ∀ i j, (Q i j).IsHomogeneous 1) (x : σ → ℂ)
    (P : ObservedCircuit I) (ψ : QState I) :
    rawProcessPairing (observedRawTester Q P ψ
      (fun i => (observedRawLeaf Q P i).accepted)) (rawTensorVector x) =
      observedAcceptance (rawEvaluateMatrix x Q) P ψ := by
  rw [observedRawTester_pairing Q hQ, ← observedEventMass_accepted,
    observedEventMass, observedTraces_eq_raw_ofFn]
  simp only [List.map_ofFn, List.sum_ofFn, ObservedRawLeaf.toTrace, Function.comp_def]

end Born

section ForwardWorkspace

variable {D W : Type*} [Fintype D] [DecidableEq D] [Fintype W] [DecidableEq W]

/-- The raw process matrix for forward queries acting on the data register and leaving the
workspace unchanged. -/
noncomputable abbrev forwardObservedProcessMatrix (P : ObservedCircuit (D × W))
    (ψ : QState (D × W)) :=
  observedRawProcessMatrix (rawLiftedQuery (D := D) (W := W)) P ψ

/-- Applying the forward process matrix to the tensor vector of oracle entries gives all
evaluated branch amplitudes. -/
theorem forwardObservedProcessMatrix_evaluate (P : ObservedCircuit (D × W))
    (ψ : QState (D × W)) (U : Matrix D D ℂ) :
    forwardObservedProcessMatrix P ψ *ᵥ rawTensorVector (fun a : D × D => U a.1 a.2) =
      fun a => ((observedRawLeaf rawLiftedQuery P a.1).toTrace
        (fun b : D × D => U b.1 b.2) ψ).state a.2 :=
  observedRawProcessMatrix_evaluate _ rawLiftedQuery_homogeneous _ P ψ

/-- Observed traces of a forward oracle acting with the workspace identity equal the indexed
evaluated symbolic leaves. -/
theorem forwardObservedTraces_raw (P : ObservedCircuit (D × W))
    (ψ : QState (D × W)) (U : Matrix D D ℂ) :
    observedTraces (TensorGate U (1 : Matrix W W ℂ)) P ψ =
      List.ofFn (fun i => (observedRawLeaf rawLiftedQuery P i).toTrace
        (fun b : D × D => U b.1 b.2) ψ) := by
  rw [← rawLiftedQuery_evaluate U]
  exact observedTraces_eq_raw_ofFn _ _ P ψ

/-- The forward process matrix reconstructs every observed branch state together with its
acceptance flag, resource counts, and outcome history. -/
theorem forwardObservedTraces_eq_process (P : ObservedCircuit (D × W))
    (ψ : QState (D × W)) (U : Matrix D D ℂ) :
    observedTraces (TensorGate U (1 : Matrix W W ℂ)) P ψ =
      List.ofFn (fun i =>
        { state := fun j => (forwardObservedProcessMatrix P ψ *ᵥ
            rawTensorVector (fun a : D × D => U a.1 a.2)) (i, j)
          accepted := (observedRawLeaf rawLiftedQuery P i).accepted
          queries := (observedRawLeaf rawLiftedQuery P i).queries
          gates := (observedRawLeaf rawLiftedQuery P i).gates
          measurements := (observedRawLeaf rawLiftedQuery P i).measurements
          outcomes := (observedRawLeaf rawLiftedQuery P i).outcomes } :
          ObservedRawIndex (rawLiftedQuery (D := D) (W := W)) P → BranchTrace (D × W)) := by
  rw [forwardObservedTraces_raw, forwardObservedProcessMatrix_evaluate]
  rfl

/-- The forward raw tester selecting accepted leaves pairs with the tensor vector of oracle
entries to the observed acceptance mass. -/
theorem forwardObservedRawTester_acceptance (P : ObservedCircuit (D × W))
    (ψ : QState (D × W)) (U : Matrix D D ℂ) :
    rawProcessPairing (observedRawTester rawLiftedQuery P ψ
      (fun i => (observedRawLeaf rawLiftedQuery P i).accepted))
      (rawTensorVector (fun a : D × D => U a.1 a.2)) =
      observedAcceptance (TensorGate U (1 : Matrix W W ℂ)) P ψ := by
  rw [← rawLiftedQuery_evaluate U]
  exact observedRawTester_acceptance _ rawLiftedQuery_homogeneous _ P ψ

/-- For a unitary oracle, well-formed observed circuit, and normalized input, the forward raw
normalizer pairs with the tensor vector of oracle entries to one. -/
theorem forwardObservedRawNormalizer_complete (P : ObservedCircuit (D × W))
    (hP : observedWellFormed P) (ψ : QState (D × W)) (hψ : Normalized ψ)
    (U : Matrix D D ℂ) (hU : U ∈ Matrix.unitaryGroup D ℂ) :
    rawProcessPairing (observedRawNormalizer rawLiftedQuery P ψ)
      (rawTensorVector (fun a : D × D => U a.1 a.2)) = 1 := by
  apply observedRawNormalizer_complete _ rawLiftedQuery_homogeneous _ _ P hP ψ hψ
  rw [rawLiftedQuery_evaluate]
  exact tensorGate_unitary hU (Submonoid.one_mem _)

end ForwardWorkspace

end Qatlib.Concepts.AdaptiveQuery.RawProcess
