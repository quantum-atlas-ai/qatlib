/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import QuantumInfo.ForMathlib.Isometry

/-!
# Composition on disjoint workspaces

This module proves that operator branches on disjoint tensor factors commute and records the
resources of sequential and stacked clean-operation words. The actual width trails determine
auxiliary-space peaks: sequential composition takes a maximum, while stacking is bounded by the
sum and attains it when peaks coincide.

The module also proves trace-norm contraction for successive auxiliary-register releases and
cancellation of joint allocation followed by release, including arbitrary reference registers.
These use the tensor-product channel formalism of [Watrous2018].

## Main statements

* `frontier1`: combines disjoint branch commutation, resource counts, live-space bounds, and
  release guarantees.
* `lcu_select_consumer`: gives exact counts and peaks for two query-phase words.
* `stopping_joint_consumer`: combines measured stopping traces with a disjoint clean word.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportLiveWire
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.DisjointWorkspaceComposition
open Matrix
open Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease
open scoped Classical ComplexOrder BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- Lift an operator to the left factor of a tensor product and flatten the product index. -/
def tensorLiftL {a b : ℕ} (M : Operator a) : Operator (a*b) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (TensorGate M (1 : Operator b))

/-- Lift an operator to the right factor of a tensor product and flatten the product index. -/
def tensorLiftR {a b : ℕ} (N : Operator b) : Operator (a*b) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (TensorGate (1 : Operator a) N)

/-- Multiplying the left lift of `M` by the right lift of `N` gives their tensor product under
the flattened indexing. -/
theorem liftL_mul_liftR {a b : ℕ} (M : Operator a) (N : Operator b) :
    tensorLiftL M * tensorLiftR N =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (TensorGate M N) := by
  have h : tensorLiftL M * tensorLiftR N =
      (TensorGate M (1 : Operator b) * TensorGate (1 : Operator a) N).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm :=
    Matrix.submatrix_mul_equiv _ _ _ _ _
  rw [h, tensorGate_mul, Matrix.mul_one, Matrix.one_mul]
  rfl

/-- Multiplying the right lift of `N` by the left lift of `M` gives the same flattened tensor
product. -/
theorem liftR_mul_liftL {a b : ℕ} (M : Operator a) (N : Operator b) :
    tensorLiftR N * tensorLiftL M =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (TensorGate M N) := by
  have h : tensorLiftR N * tensorLiftL M =
      (TensorGate (1 : Operator a) N * TensorGate M (1 : Operator b)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm :=
    Matrix.submatrix_mul_equiv _ _ _ _ _
  rw [h, tensorGate_mul, Matrix.one_mul, Matrix.mul_one]
  rfl

/-- Operators lifted to disjoint tensor factors commute. -/
theorem lift_commute {a b : ℕ} (M : Operator a) (N : Operator b) :
    tensorLiftL M * tensorLiftR N = tensorLiftR N * tensorLiftL M :=
  (liftL_mul_liftR M N).trans (liftR_mul_liftL M N).symm

/-- Conjugation branches acting on disjoint tensor factors commute on every joint operator. -/
theorem cp_output_commute_state {a b : ℕ} (M : Operator a) (N : Operator b)
    (ρ : Operator (a*b)) :
    conjBranch (tensorLiftL M) (conjBranch (tensorLiftR N) ρ)
      = conjBranch (tensorLiftR N) (conjBranch (tensorLiftL M) ρ) := by
  have h1 : conjBranch (tensorLiftL M) (conjBranch (tensorLiftR N) ρ)
      = conjBranch (tensorLiftL M * tensorLiftR N) ρ :=
    congrArg (fun T : Operator (a*b) →ₗ[ℂ] Operator (a*b) => T ρ)
      (conjBranch_comp (tensorLiftL M) (tensorLiftR N))
  have h2 : conjBranch (tensorLiftR N) (conjBranch (tensorLiftL M) ρ)
      = conjBranch (tensorLiftR N * tensorLiftL M) ρ :=
    congrArg (fun T : Operator (a*b) →ₗ[ℂ] Operator (a*b) => T ρ)
      (conjBranch_comp (tensorLiftR N) (tensorLiftL M))
  rw [h1, h2, lift_commute]

/-- Swapping both product indices of a tensor-product operator exchanges its two factors. -/
theorem joint_output_swap {a b : ℕ} (M : Operator a) (N : Operator b) :
    (TensorGate M N).submatrix (Equiv.prodComm (Fin a) (Fin b)).symm
      (Equiv.prodComm (Fin a) (Fin b)).symm = TensorGate N M := by
  ext p q
  simp only [Matrix.submatrix_apply, TensorGate, Matrix.kroneckerMap_apply]
  exact mul_comm _ _

/-- The list of auxiliary-qubit widths obtained by applying the base-two ceiling logarithm to
the word's register widths. -/
def liveTrailOf {n : ℕ} (w : List (CleanOp n)) : List ℕ :=
  (wordWidths w).map (Nat.clog 2)

/-- The maximum auxiliary-qubit width along a clean-operation word. -/
def peakAuxOf {n : ℕ} (w : List (CleanOp n)) : ℕ :=
  maxTrail (liveTrailOf w)

/-- The maximum of a natural-number trail is its right fold by `Nat.max` starting at zero. -/
theorem maxTrail_eq_foldr (l : List ℕ) : maxTrail l = l.foldr Nat.max 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [maxTrail, List.foldr_cons, ih]

/-- The executed word trace has the syntactic width trail and auxiliary-space maximum prescribed
by the word. -/
theorem liveTrailOf_is_actual {n : ℕ} (U : Operator (2^n)) (w : List (CleanOp n))
    (ρ : Operator ((2^n)*1)) :
    (wordTrace U w ρ).widths = wordWidths w ∧
    (wordTrace U w ρ).peakAux = peakAuxOf w := by
  refine ⟨rfl, ?_⟩
  simp only [MeasuredTrace.peakAux, wordTrace, liveTrailOf, peakAuxOf, maxTrail_eq_foldr]

/-- A clean word has peak auxiliary space zero when it contains no phase operations and one
otherwise. -/
theorem peakAuxOf_eq {n : ℕ} (w : List (CleanOp n)) :
    peakAuxOf w = if wordPhases w = 0 then 0 else 1 := by
  simp only [peakAuxOf, liveTrailOf, maxTrail_eq_foldr]
  exact wordWidths_peak w

/-- The maximum of the empty trail is zero. -/
theorem maxTrail_nil : maxTrail ([] : List ℕ) = 0 := rfl

/-- The maximum of a nonempty trail is the maximum of its head and tail maximum. -/
theorem maxTrail_cons (a : ℕ) (l : List ℕ) : maxTrail (a :: l) = max a (maxTrail l) := rfl

/-- Every member of a trail is at most the trail's maximum. -/
theorem mem_le_maxTrail {l : List ℕ} (x : ℕ) (hx : x ∈ l) : x ≤ maxTrail l := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
      rcases List.mem_cons.mp hx with h | h
      · simp only [h, maxTrail_cons]
        exact Nat.le_max_left _ _
      · exact le_trans (ih h) (Nat.le_max_right _ _)

/-- A uniform upper bound on every trail member bounds the trail's maximum. -/
theorem maxTrail_le_of_forall {l : List ℕ} {m : ℕ} (h : ∀ x ∈ l, x ≤ m) : maxTrail l ≤ m := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
      exact Nat.max_le.mpr ⟨h a (by simp), ih (fun x hx => h x (by simp [hx]))⟩

/-- Natural-number list indexing with zero returned outside the list. -/
def nthNat : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, k+1 => nthNat l k

/-- Indexing an empty natural-number list returns zero. -/
theorem nthNat_nil (k : ℕ) : nthNat [] k = 0 := by cases k <;> rfl

/-- Index zero of a nonempty natural-number list returns its head. -/
theorem nthNat_zero (a : ℕ) (l : List ℕ) : nthNat (a :: l) 0 = a := rfl

/-- Indexing a nonempty list at a successor reduces to indexing its tail. -/
theorem nthNat_succ (a : ℕ) (l : List ℕ) (k : ℕ) : nthNat (a :: l) (k+1) = nthNat l k := rfl

/-- An in-range value returned by `nthNat` belongs to the list. -/
theorem nthNat_lt_mem {l : List ℕ} {k : ℕ} (hk : k < l.length) : nthNat l k ∈ l := by
  induction l generalizing k with
  | nil => simp only [List.length_nil] at hk; exact absurd hk (Nat.not_lt_zero k)
  | cons a l ih =>
      match k with
      | 0 => simp [nthNat_zero]
      | k+1 => exact List.mem_cons_of_mem a (ih (Nat.lt_of_succ_lt_succ hk))

/-- Mapping addition by zero over a list preserves its `nthNat` values. -/
theorem nthNat_map_add_zero (l : List ℕ) (k : ℕ) :
    nthNat (l.map (fun x => x + 0)) k = nthNat l k + 0 := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons a l ih =>
      cases k with
      | zero => rfl
      | succ k => simp only [List.map_cons, nthNat_succ, ih k]

/-- The sequential live-space trail formed by concatenating the two component trails. -/
def seqLiveTrail {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) : List ℕ :=
  liveTrailOf w₁ ++ liveTrailOf w₂

/-- The sequential live-space maximum is the maximum of the two component auxiliary-space peaks. -/
theorem seq_peak {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    maxTrail (seqLiveTrail w₁ w₂) = max (peakAuxOf w₁) (peakAuxOf w₂) := by
  simp only [seqLiveTrail, peakAuxOf, maxTrail_append]

/-- The pointwise sum of two trails, treating missing entries in the shorter trail as zero. -/
def stackTrail : List ℕ → List ℕ → List ℕ
  | [], l => l.map (fun x => x + 0)
  | l, [] => l.map (fun x => x + 0)
  | a :: l₁, b :: l₂ => (a + b) :: stackTrail l₁ l₂

/-- Stacking an empty left trail maps addition by zero over the right trail. -/
theorem stackTrail_nil_left (l : List ℕ) : stackTrail [] l = l.map (fun x => x + 0) := rfl

/-- Stacking a nonempty trail with an empty right trail preserves its head and maps addition by
zero over its tail. -/
theorem stackTrail_nil_right (a : ℕ) (l : List ℕ) :
    stackTrail (a :: l) [] = (a + 0) :: l.map (fun x => x + 0) := rfl

/-- Stacking two nonempty trails adds their heads and recursively stacks their tails. -/
theorem stackTrail_cons (a b : ℕ) (l₁ l₂ : List ℕ) :
    stackTrail (a :: l₁) (b :: l₂) = (a + b) :: stackTrail l₁ l₂ := rfl

/-- Mapping addition by zero preserves a trail's maximum. -/
theorem maxTrail_map_add_zero (l : List ℕ) :
    maxTrail (l.map (fun x => x + 0)) = maxTrail l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, maxTrail_cons, ih]; omega

/-- The length of a stacked trail is the maximum of the component lengths. -/
theorem stackTrail_length (l₁ l₂ : List ℕ) :
    (stackTrail l₁ l₂).length = max l₁.length l₂.length := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => simp [stackTrail_nil_left]
      | cons b l₂ => simp [stackTrail_nil_left]
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp [stackTrail_nil_right]
      | cons b l₂ =>
          simp only [stackTrail_cons, List.length_cons, ih l₂]
          omega

/-- Every zero-padded entry of a stacked trail is the sum of the corresponding component
entries. -/
theorem nthNat_stackTrail (l₁ l₂ : List ℕ) (k : ℕ) :
    nthNat (stackTrail l₁ l₂) k = nthNat l₁ k + nthNat l₂ k := by
  induction l₁ generalizing l₂ k with
  | nil =>
      cases l₂ with
      | nil => cases k <;> rfl
      | cons b l₂ =>
          cases k with
          | zero => simp [stackTrail_nil_left, nthNat_zero, nthNat_nil]
          | succ k => simp [stackTrail_nil_left, nthNat_succ, nthNat_nil, add_zero]
  | cons a l₁ ih =>
      cases l₂ with
      | nil =>
          cases k with
          | zero => simp [stackTrail_nil_right, nthNat_zero, nthNat_nil]
          | succ k => simp [stackTrail_nil_right, nthNat_succ, nthNat_nil, add_zero]
      | cons b l₂ =>
          cases k with
          | zero => rfl
          | succ k => simp only [stackTrail_cons, nthNat_succ, ih l₂ k]

/-- At an index in both component trails, the sum of their entries belongs to the stacked trail. -/
theorem nthNat_stackTrail_mem {l₁ l₂ : List ℕ} {k : ℕ} (h1 : k < l₁.length)
    (h2 : k < l₂.length) : nthNat l₁ k + nthNat l₂ k ∈ stackTrail l₁ l₂ := by
  have hlen : k < (stackTrail l₁ l₂).length := by
    rw [stackTrail_length]
    omega
  rw [← nthNat_stackTrail l₁ l₂ k]
  exact nthNat_lt_mem hlen

/-- Stacking two natural-number trails is symmetric. -/
theorem stackTrail_swap (l₁ l₂ : List ℕ) : stackTrail l₁ l₂ = stackTrail l₂ l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons b l₂ => simp [stackTrail_nil_left, stackTrail_nil_right]
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp [stackTrail_nil_left, stackTrail_nil_right]
      | cons b l₂ =>
          simp only [stackTrail_cons, ih l₂, Nat.add_comm a b]

/-- The peak of a stacked trail is at most the sum of the two component peaks. -/
theorem stack_peak_le (l₁ l₂ : List ℕ) :
    maxTrail (stackTrail l₁ l₂) ≤ maxTrail l₁ + maxTrail l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      have h1 : maxTrail (stackTrail [] l₂) = maxTrail l₂ := by
        rw [stackTrail_nil_left, maxTrail_map_add_zero]
      rw [h1, maxTrail_nil]
      omega
  | cons a l₁ ih =>
      cases l₂ with
      | nil =>
          have h1 : maxTrail (stackTrail (a :: l₁) []) = maxTrail (a :: l₁) := by
            rw [stackTrail_nil_right, maxTrail_cons, maxTrail_cons, maxTrail_map_add_zero]
            omega
          rw [h1, maxTrail_nil]
          omega
      | cons b l₂ =>
          have hA : maxTrail (a :: l₁) = max a (maxTrail l₁) := maxTrail_cons a l₁
          have hB : maxTrail (b :: l₂) = max b (maxTrail l₂) := maxTrail_cons b l₂
          have hS : maxTrail (stackTrail (a :: l₁) (b :: l₂))
              = max (a + b) (maxTrail (stackTrail l₁ l₂)) := by
            rw [stackTrail_cons, maxTrail_cons]
          have htail := ih l₂
          rw [hS]
          omega

/-- If both component peaks occur at the same valid index, the stacked peak equals their sum. -/
theorem stack_peak_eq_of_cooccur (l₁ l₂ : List ℕ) (k : ℕ)
    (h1 : k < l₁.length) (h2 : k < l₂.length)
    (e1 : nthNat l₁ k = maxTrail l₁) (e2 : nthNat l₂ k = maxTrail l₂) :
    maxTrail (stackTrail l₁ l₂) = maxTrail l₁ + maxTrail l₂ := by
  refine le_antisymm (stack_peak_le l₁ l₂) ?_
  have hmem : nthNat l₁ k + nthNat l₂ k ∈ stackTrail l₁ l₂ :=
    nthNat_stackTrail_mem h1 h2
  rw [e1, e2] at hmem
  exact mem_le_maxTrail _ hmem

/-- The joint sequential resource record, adding operation costs and using the maximum component
auxiliary-space peak. -/
def jointSeqResources {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    ResourceCost :=
  ⟨wordQueries w₁ + wordQueries w₂,
   wordGates w₁ + wordGates w₂,
   wordGates w₁ + wordGates w₂,
   (wordQueries w₁ + wordGates w₁ + 2*wordPhases w₁)
     + (wordQueries w₂ + wordGates w₂ + 2*wordPhases w₂),
   n₁ + n₂ + max (peakAuxOf w₁) (peakAuxOf w₂),
   0, 0⟩

/-- The joint stacked resource record, adding operation costs and the two component
auxiliary-space peaks. -/
def jointStackResources {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    ResourceCost :=
  ⟨wordQueries w₁ + wordQueries w₂,
   wordGates w₁ + wordGates w₂,
   wordGates w₁ + wordGates w₂,
   (wordQueries w₁ + wordGates w₁ + 2*wordPhases w₁)
     + (wordQueries w₂ + wordGates w₂ + 2*wordPhases w₂),
   n₁ + n₂ + (peakAuxOf w₁ + peakAuxOf w₂),
   0, 0⟩

/-- The sequential joint query, macro-gate, basic-gate, and depth counts are sums of the
corresponding actual trace counts. -/
theorem jointSeq_resources_from_actual {n₁ n₂ : ℕ}
    (U₁ : Operator (2^n₁)) (U₂ : Operator (2^n₂))
    (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂))
    (ρ₁ : Operator ((2^n₁)*1)) (ρ₂ : Operator ((2^n₂)*1)) :
    (jointSeqResources w₁ w₂).queries
      = ((wordTrace U₁ w₁ ρ₁).resources n₁).queries
        + ((wordTrace U₂ w₂ ρ₂).resources n₂).queries ∧
    (jointSeqResources w₁ w₂).macroGates
      = ((wordTrace U₁ w₁ ρ₁).resources n₁).macroGates
        + ((wordTrace U₂ w₂ ρ₂).resources n₂).macroGates ∧
    (jointSeqResources w₁ w₂).basicGates
      = ((wordTrace U₁ w₁ ρ₁).resources n₁).basicGates
        + ((wordTrace U₂ w₂ ρ₂).resources n₂).basicGates ∧
    (jointSeqResources w₁ w₂).depth
      = ((wordTrace U₁ w₁ ρ₁).resources n₁).depth
        + ((wordTrace U₂ w₂ ρ₂).resources n₂).depth := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  have hw1 : (wordTrace U₁ w₁ ρ₁).resources n₁ = wordResources n₁ w₁ :=
    wordTrace_resources U₁ w₁ ρ₁
  have hw2 : (wordTrace U₂ w₂ ρ₂).resources n₂ = wordResources n₂ w₂ :=
    wordTrace_resources U₂ w₂ ρ₂
  rw [hw1, hw2]
  rfl

/-- The sequential resource record is unchanged when its two component words are exchanged. -/
theorem jointSeq_exchange {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    jointSeqResources w₁ w₂ = jointSeqResources w₂ w₁ := by
  ext <;> simp only [jointSeqResources] <;> omega

/-- The stacked resource record is unchanged when its two component words are exchanged. -/
theorem jointStack_exchange {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    jointStackResources w₁ w₂ = jointStackResources w₂ w₁ := by
  ext <;> simp only [jointStackResources] <;> omega

/-- The sequential peak-space field equals the two data-register sizes plus the maximum of the
concatenated live trail. -/
theorem jointSeq_peakSpace_trail {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    (jointSeqResources w₁ w₂).peakSpace = n₁ + n₂ + maxTrail (seqLiveTrail w₁ w₂) := by
  simp only [jointSeqResources, seq_peak]

/-- The sequential joint peak space is at most the stacked joint peak space. -/
theorem seq_peakSpace_le_stack {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    (jointSeqResources w₁ w₂).peakSpace ≤ (jointStackResources w₁ w₂).peakSpace := by
  simp only [jointSeqResources, jointStackResources]
  omega

section ReferenceError

open Classical

variable {α β : Type} [Fintype α] [Fintype β]

/-- A finite sum with a left equality indicator selects the indicated function value. -/
private theorem sum_ite_left_eq (F : α → ℂ) (t : α) :
    ∑ i, (if i = t then (1 : ℂ) else 0) * F i = F t := by
  simp [Finset.sum_ite_eq']

/-- A finite sum with a right equality indicator selects the indicated function value. -/
private theorem sum_ite_right_eq (F : α → ℂ) (t : α) :
    ∑ i, F i * (if i = t then (1 : ℂ) else 0) = F t := by
  simp [Finset.sum_ite_eq]

/-- The complex indicator of a proposition is fixed by complex conjugation. -/
private theorem star_indicator (c : Prop) [Decidable c] :
    star (if c then (1 : ℂ) else 0) = if c then 1 else 0 := by
  by_cases h : c <;> simp [h]

/-- The rectangular permutation matrix representing an equivalence of finite index types. -/
private def equivRows (e : α ≃ β) : Matrix β α ℂ :=
  fun i j => if j = e.symm i then 1 else 0

/-- Left multiplication by the equivalence matrix reindexes the rows of a matrix. -/
private theorem equivRows_left_mul (e : α ≃ β) (A : Matrix α α ℂ) (i : β) (k : α) :
    (equivRows e * A) i k = A (e.symm i) k := by
  rw [Matrix.mul_apply]
  simp only [equivRows]
  exact sum_ite_left_eq (fun j => A j k) (e.symm i)

/-- Conjugation by the equivalence matrix reindexes both indices of a matrix. -/
private theorem equivRows_conj_mul (e : α ≃ β) (A : Matrix α α ℂ) (i k : β) :
    (equivRows e * A * (equivRows e).conjTranspose) i k = A (e.symm i) (e.symm k) := by
  have houter : (equivRows e * A * (equivRows e).conjTranspose) i k
      = ∑ l : α, (equivRows e * A) i l * ((equivRows e).conjTranspose) l k := by
    rw [Matrix.mul_apply]
  have hinner : ∀ l : α, (equivRows e * A) i l = A (e.symm i) l := equivRows_left_mul e A i
  rw [houter]
  simp only [hinner, Matrix.conjTranspose_apply, equivRows, star_indicator]
  exact sum_ite_right_eq (fun l => A (e.symm i) l) (e.symm k)

/-- The matrix representing an equivalence of finite index types is an isometry. -/
private theorem equivRows_isometry (e : α ≃ β) : (equivRows e).Isometry := by
  ext j j'
  by_cases hjj : j = j'
  · subst hjj
    have hcond : ∀ i : β, (j = e.symm i) = (i = e j) := by
      intro i
      apply propext
      constructor
      · intro h
        rw [h]
        exact (e.apply_symm_apply i).symm
      · intro h
        rw [h]
        exact (e.symm_apply_apply j).symm
    have hterm : ∀ i : β,
        ((if i = e j then (1 : ℂ) else 0) * (if i = e j then (1 : ℂ) else 0))
          = (if i = e j then (1 : ℂ) else 0) := by
      intro i; by_cases h : i = e j <;> simp [h]
    simp only [Matrix.conjTranspose_apply, equivRows, star_indicator, Matrix.mul_apply,
      Matrix.one_apply, hcond]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  · have hzero : ∀ i : β,
        ((if j = e.symm i then (1 : ℂ) else 0)
          * (if j' = e.symm i then (1 : ℂ) else 0)) = 0 := by
      intro i
      by_cases h1 : j = e.symm i
      · have h2 : j' ≠ e.symm i := fun hh => hjj (h1.trans hh.symm)
        simp [h1, h2]
      · simp [h1]
    simp only [Matrix.conjTranspose_apply, equivRows, star_indicator, Matrix.mul_apply,
      Matrix.one_apply, hzero, Finset.sum_const_zero, hjj, if_false]

/-- Reindexing a square matrix by an equivalence preserves its trace norm. -/
theorem traceNorm_reindex (e : α ≃ β) (A : Matrix α α ℂ) :
    (Matrix.reindex e e A).traceNorm = A.traceNorm := by
  have hconj : equivRows e * A * (equivRows e).conjTranspose = Matrix.reindex e e A := by
    ext i k
    rw [Matrix.reindex_apply]
    exact equivRows_conj_mul e A i k
  rw [← hconj, Matrix.mul_assoc,
    traceNorm_isometry_left (equivRows_isometry e),
    traceNorm_isometry_right (equivRows_isometry e)]

/-- Reindexing a Hermitian matrix by an equivalence preserves Hermiticity. -/
theorem isHermitian_reindex (e : α ≃ β) (A : Matrix α α ℂ) (hA : A.IsHermitian) :
    (Matrix.reindex e e A).IsHermitian :=
  hA.submatrix _

/-- Reindexing by an equivalence and then its inverse returns the original matrix. -/
private theorem reindex_symm_cancel (e : α ≃ β) (M : Matrix α α ℂ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e M) = M := by
  ext i j
  simp [Matrix.reindex_apply]

/-- Reindexing by an inverse equivalence and then the equivalence returns the original matrix. -/
private theorem reindex_symm_cancel' (e : α ≃ β) (N : Matrix β β ℂ) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm N) = N := by
  ext i j
  simp [Matrix.reindex_apply]

end ReferenceError

/-- The property that a complex-linear map commutes with conjugate transpose. -/
def StarPreserving {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Prop :=
  ∀ Y, (T Y).conjTranspose = T Y.conjTranspose

/-- The release branch commutes with conjugate transpose. -/
theorem release_branch_starPreserving (d : ℕ) : StarPreserving ((release d).branch 0) := by
  intro Y
  simp only [release_branch, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The allocation branch commutes with conjugate transpose. -/
theorem allocate_branch_starPreserving (d : ℕ) : StarPreserving ((allocate d).branch 0) := by
  intro Y
  simp only [allocate_branch, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

/-- Amplifying a conjugate-transpose-preserving map by an identity reference maps Hermitian
matrices to Hermitian matrices. -/
theorem channelAmplification_hermitian {D E r : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (hT : StarPreserving T) {X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ}
    (hX : X.IsHermitian) : (ChannelAmplification T r X).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro u v
  have h1 : Matrix.conjTranspose (fun i j => X (v.1, i) (u.1, j))
      = fun i j => X (u.1, i) (v.1, j) := by
    ext i j
    simp only [Matrix.conjTranspose_apply]
    exact hX.apply (u.1, i) (v.1, j)
  have h2 := hT (fun i j => X (v.1, i) (u.1, j))
  simp only [ChannelAmplification]
  rw [show star (T (fun i j => X (v.1, i) (u.1, j)) v.2 u.2)
      = Matrix.conjTranspose (T (fun i j => X (v.1, i) (u.1, j))) u.2 v.2 from rfl,
    h2, h1]

/-- Amplified release after amplified allocation returns the original joint operator. -/
theorem channelAmplification_release_allocate (d r : ℕ)
    (Y : Matrix (Fin r × Fin (d*1)) (Fin r × Fin (d*1)) ℂ) :
    ChannelAmplification ((release d).branch 0) r
      (ChannelAmplification ((allocate d).branch 0) r Y) = Y := by
  ext x y
  simp only [ChannelAmplification]
  rw [release_clean d (fun i j => Y (x.1, i) (y.1, j))]

section TwoFactorRelease

/-- The register equivalence combining the reference and left system indices while retaining the
right system index. -/
def flatRight (r a b : ℕ) : Fin r × (Fin a × Fin b) ≃ Fin (r*a) × Fin b :=
  (Equiv.prodAssoc (Fin r) (Fin a) (Fin b)).symm.trans
    ((finProdFinEquiv (m := r) (n := a)).prodCongr (Equiv.refl (Fin b)))

/-- The register equivalence combining the reference and right system indices while retaining
the left system index. -/
def flatLeft (r a b : ℕ) : Fin r × (Fin a × Fin b) ≃ Fin (r*b) × Fin a :=
  ((Equiv.prodCongr (Equiv.refl (Fin r)) (Equiv.prodComm (Fin a) (Fin b))).trans
    (Equiv.prodAssoc (Fin r) (Fin b) (Fin a)).symm).trans
    ((finProdFinEquiv (m := r) (n := b)).prodCongr (Equiv.refl (Fin a)))

/-- Release the auxiliary register of the second system while preserving the first system and
the reference. -/
def releaseSecond (d₁ d₂ r : ℕ)
    (X : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ) :
    Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*1))) (Fin r × (Fin (d₁*2) × Fin (d₂*1))) ℂ :=
  (ChannelAmplification ((release d₂).branch 0) (r*(d₁*2))
    (Matrix.reindex (flatRight r (d₁*2) (d₂*2)) (flatRight r (d₁*2) (d₂*2)) X)).reindex
    (flatRight r (d₁*2) (d₂*1)).symm (flatRight r (d₁*2) (d₂*1)).symm

/-- Release the auxiliary register of the first system after the second system's auxiliary
register has been released. -/
def releaseFirst (d₁ d₂ r : ℕ)
    (Y : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*1))) (Fin r × (Fin (d₁*2) × Fin (d₂*1))) ℂ) :
    Matrix (Fin r × (Fin (d₁*1) × Fin (d₂*1))) (Fin r × (Fin (d₁*1) × Fin (d₂*1))) ℂ :=
  (ChannelAmplification ((release d₁).branch 0) (r*(d₂*1))
    (Matrix.reindex (flatLeft r (d₁*2) (d₂*1)) (flatLeft r (d₁*2) (d₂*1)) Y)).reindex
    (flatLeft r (d₁*1) (d₂*1)).symm (flatLeft r (d₁*1) (d₂*1)).symm

/-- Allocate the auxiliary registers of both systems while retaining the reference register. -/
def jointAllocate (d₁ d₂ r : ℕ)
    (ρ : Matrix (Fin r × (Fin (d₁*1) × Fin (d₂*1))) (Fin r × (Fin (d₁*1) × Fin (d₂*1))) ℂ) :
    Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ :=
  (ChannelAmplification ((allocate d₂).branch 0) (r*(d₁*2))
    (Matrix.reindex (flatRight r (d₁*2) (d₂*1)) (flatRight r (d₁*2) (d₂*1))
      ((ChannelAmplification ((allocate d₁).branch 0) (r*(d₂*1))
        (Matrix.reindex (flatLeft r (d₁*1) (d₂*1)) (flatLeft r (d₁*1) (d₂*1)) ρ)).reindex
        (flatLeft r (d₁*2) (d₂*1)).symm (flatLeft r (d₁*2) (d₂*1)).symm))).reindex
    (flatRight r (d₁*2) (d₂*2)).symm (flatRight r (d₁*2) (d₂*2)).symm

/-- Releasing the second system's auxiliary register preserves Hermiticity. -/
theorem releaseSecond_hermitian (d₁ d₂ r : ℕ)
    (X : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ)
    (hX : X.IsHermitian) : (releaseSecond d₁ d₂ r X).IsHermitian :=
  isHermitian_reindex _ _ (channelAmplification_hermitian _ (release_branch_starPreserving d₂)
    (isHermitian_reindex _ _ hX))

/-- Releasing the first system's auxiliary register preserves Hermiticity. -/
theorem releaseFirst_hermitian (d₁ d₂ r : ℕ)
    (Y : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*1))) (Fin r × (Fin (d₁*2) × Fin (d₂*1))) ℂ)
    (hY : Y.IsHermitian) : (releaseFirst d₁ d₂ r Y).IsHermitian :=
  isHermitian_reindex _ _ (channelAmplification_hermitian _ (release_branch_starPreserving d₁)
    (isHermitian_reindex _ _ hY))

/-- Releasing the second system's auxiliary register does not increase the trace norm of a
Hermitian operator. -/
theorem releaseSecond_traceNorm (d₁ d₂ r : ℕ)
    (X : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ)
    (hX : X.IsHermitian) : (releaseSecond d₁ d₂ r X).traceNorm ≤ X.traceNorm := by
  have h1 := release_reference_error d₂ (r*(d₁*2)) _
    (isHermitian_reindex (flatRight r (d₁*2) (d₂*2)) _ hX)
  rw [traceNorm_reindex] at h1
  unfold releaseSecond
  rw [traceNorm_reindex]
  exact h1

/-- Releasing the first system's auxiliary register does not increase the trace norm of a
Hermitian operator. -/
theorem releaseFirst_traceNorm (d₁ d₂ r : ℕ)
    (Y : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*1))) (Fin r × (Fin (d₁*2) × Fin (d₂*1))) ℂ)
    (hY : Y.IsHermitian) : (releaseFirst d₁ d₂ r Y).traceNorm ≤ Y.traceNorm := by
  have h1 := release_reference_error d₁ (r*(d₂*1)) _
    (isHermitian_reindex (flatLeft r (d₁*2) (d₂*1)) _ hY)
  rw [traceNorm_reindex] at h1
  unfold releaseFirst
  rw [traceNorm_reindex]
  exact h1

/-- Successively releasing both auxiliary registers does not increase the trace norm of a
Hermitian operator. -/
theorem release_stepwise_traceNorm (d₁ d₂ r : ℕ)
    (X : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ)
    (hX : X.IsHermitian) :
    (releaseFirst d₁ d₂ r (releaseSecond d₁ d₂ r X)).traceNorm ≤ X.traceNorm :=
  (releaseFirst_traceNorm d₁ d₂ r _ (releaseSecond_hermitian d₁ d₂ r X hX)).trans
    (releaseSecond_traceNorm d₁ d₂ r X hX)

/-- Allocating both auxiliary registers and then releasing them successively returns the
original joint operator. -/
theorem release_stepwise_clean (d₁ d₂ r : ℕ)
    (ρ : Matrix (Fin r × (Fin (d₁*1) × Fin (d₂*1))) (Fin r × (Fin (d₁*1) × Fin (d₂*1))) ℂ) :
    releaseFirst d₁ d₂ r (releaseSecond d₁ d₂ r (jointAllocate d₁ d₂ r ρ)) = ρ := by
  have hstep2 : releaseSecond d₁ d₂ r (jointAllocate d₁ d₂ r ρ)
      = (ChannelAmplification ((allocate d₁).branch 0) (r*(d₂*1))
          (Matrix.reindex (flatLeft r (d₁*1) (d₂*1)) (flatLeft r (d₁*1) (d₂*1)) ρ)).reindex
        (flatLeft r (d₁*2) (d₂*1)).symm (flatLeft r (d₁*2) (d₂*1)).symm := by
    unfold releaseSecond jointAllocate
    rw [reindex_symm_cancel', channelAmplification_release_allocate, reindex_symm_cancel]
  rw [hstep2]
  unfold releaseFirst
  rw [reindex_symm_cancel', channelAmplification_release_allocate, reindex_symm_cancel]

end TwoFactorRelease

/-- Disjoint clean-word branches commute, their sequential resources follow the stated sum and
peak rules, and stacked live-space peaks obey the additive bound. Sequential releases are
trace-norm contractive on Hermitian operators and undo joint allocation with any reference. -/
theorem frontier1 {n₁ n₂ : ℕ} (U₁ : Operator (2^n₁)) (U₂ : Operator (2^n₂))
    (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂))
    (ρ : Operator ((2^n₁*1)*(2^n₂*1))) (ρ₁ : Operator ((2^n₁)*1)) (ρ₂ : Operator ((2^n₂)*1)) :
    conjBranch (tensorLiftL (wordMatrix U₁ w₁))
        (conjBranch (tensorLiftR (wordMatrix U₂ w₂)) ρ)
      = conjBranch (tensorLiftR (wordMatrix U₂ w₂))
        (conjBranch (tensorLiftL (wordMatrix U₁ w₁)) ρ) ∧
    (jointSeqResources w₁ w₂).queries
      = ((wordTrace U₁ w₁ ρ₁).resources n₁).queries
        + ((wordTrace U₂ w₂ ρ₂).resources n₂).queries ∧
    (jointSeqResources w₁ w₂).macroGates
      = ((wordTrace U₁ w₁ ρ₁).resources n₁).macroGates
        + ((wordTrace U₂ w₂ ρ₂).resources n₂).macroGates ∧
    (jointSeqResources w₁ w₂).peakSpace = n₁ + n₂ + maxTrail (seqLiveTrail w₁ w₂) ∧
    maxTrail (stackTrail (liveTrailOf w₁) (liveTrailOf w₂)) ≤ peakAuxOf w₁ + peakAuxOf w₂ ∧
    ∀ (r : ℕ)
      (X : Matrix (Fin r × (Fin ((2^n₁)*2) × Fin ((2^n₂)*2)))
        (Fin r × (Fin ((2^n₁)*2) × Fin ((2^n₂)*2))) ℂ),
      X.IsHermitian →
      (releaseFirst (2^n₁) (2^n₂) r (releaseSecond (2^n₁) (2^n₂) r X)).traceNorm ≤ X.traceNorm ∧
      ∀ (Y : Matrix (Fin r × (Fin ((2^n₁)*1) × Fin ((2^n₂)*1)))
        (Fin r × (Fin ((2^n₁)*1) × Fin ((2^n₂)*1))) ℂ),
        releaseFirst (2^n₁) (2^n₂) r (releaseSecond (2^n₁) (2^n₂) r
          (jointAllocate (2^n₁) (2^n₂) r Y)) = Y :=
  ⟨cp_output_commute_state _ _ ρ,
    (jointSeq_resources_from_actual U₁ U₂ w₁ w₂ ρ₁ ρ₂).1,
    (jointSeq_resources_from_actual U₁ U₂ w₁ w₂ ρ₁ ρ₂).2.1,
    jointSeq_peakSpace_trail w₁ w₂,
    stack_peak_le _ _,
    fun r X hX => ⟨release_stepwise_traceNorm _ _ r X hX,
      fun Y => release_stepwise_clean _ _ r Y⟩⟩

/-- The two-operation word consisting of an oracle query followed by a phase operation at `i`. -/
def lcuWord {n : ℕ} (i : Fin n) : List (CleanOp n) := [CleanOp.query, CleanOp.phase i]

/-- The query-phase word has one query, four gates, and one phase operation. -/
theorem lcuWord_counts {n : ℕ} (i : Fin n) :
    wordQueries (lcuWord i) = 1 ∧ wordGates (lcuWord i) = 4 ∧ wordPhases (lcuWord i) = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The query-phase word has peak auxiliary space one. -/
theorem lcuWord_peak {n : ℕ} (i : Fin n) : peakAuxOf (lcuWord i) = 1 := by
  rw [peakAuxOf_eq]
  simp [lcuWord, wordPhases]

/-- The query-phase word has live auxiliary-space trail `[0, 0, 1, 1, 1, 1, 1, 0]`. -/
theorem liveTrailOf_lcuWord {n : ℕ} (i : Fin n) :
    liveTrailOf (lcuWord i) = [0, 0, 1, 1, 1, 1, 1, 0] := by
  have h1 : Nat.clog 2 1 = 0 := by decide
  have h2 : Nat.clog 2 2 = 1 := by decide
  simp only [liveTrailOf, lcuWord, wordWidths, List.map_cons, List.map_append,
    List.map_replicate, List.cons_append, h1, h2]
  decide

/-- Two disjoint query-phase words have commuting output branches, two total queries, and eight
macro gates. Their sequential and stacked auxiliary-space contributions are one and two,
respectively. -/
theorem lcu_select_consumer {n₁ n₂ : ℕ} (i : Fin n₁) (j : Fin n₂)
    (U₁ : Operator (2^n₁)) (U₂ : Operator (2^n₂))
    (ρ : Operator ((2^n₁*1)*(2^n₂*1))) :
    conjBranch (tensorLiftL (wordMatrix U₁ (lcuWord i)))
        (conjBranch (tensorLiftR (wordMatrix U₂ (lcuWord j))) ρ)
      = conjBranch (tensorLiftR (wordMatrix U₂ (lcuWord j)))
        (conjBranch (tensorLiftL (wordMatrix U₁ (lcuWord i))) ρ) ∧
    (jointSeqResources (lcuWord i) (lcuWord j)).queries = 2 ∧
    (jointSeqResources (lcuWord i) (lcuWord j)).macroGates = 8 ∧
    (jointSeqResources (lcuWord i) (lcuWord j)).peakSpace = n₁ + n₂ + 1 ∧
    (jointStackResources (lcuWord i) (lcuWord j)).peakSpace = n₁ + n₂ + 2 ∧
    maxTrail (stackTrail (liveTrailOf (lcuWord i)) (liveTrailOf (lcuWord j))) = 2 := by
  refine ⟨cp_output_commute_state _ _ ρ, rfl, rfl, ?_, rfl, ?_⟩
  · simp only [jointSeqResources, lcuWord_peak]
    simp
  · exact stack_peak_eq_of_cooccur _ _ 2
      (by rw [liveTrailOf_lcuWord]; decide) (by rw [liveTrailOf_lcuWord]; decide)
      (by rw [liveTrailOf_lcuWord]; rfl) (by rw [liveTrailOf_lcuWord]; rfl)

/-- The joint sequential resource record for a measured stopping trace and a clean-operation
word. -/
def stopJointResources (n₁ n₂ : ℕ) (t₁ : MeasuredTrace (2^n₁)) (w₂ : List (CleanOp n₂)) :
    ResourceCost :=
  ⟨t₁.native.queries + wordQueries w₂,
   t₁.gates + wordGates w₂,
   t₁.gates + wordGates w₂,
   (t₁.native.queries + t₁.gates + t₁.instruments)
     + (wordQueries w₂ + wordGates w₂ + 2*wordPhases w₂),
   n₁ + n₂ + max t₁.peakAux (peakAuxOf w₂),
   0, 0⟩

/-- The measured stopping construction has `h + 1` traces and exactly the stated rejected trace.
Combining a trace with a clean word adds query counts and takes the maximum auxiliary peak,
with rejected-branch query count `h + wordQueries w₂`. -/
theorem stopping_joint_consumer {n₁ n₂ : ℕ} (i : Fin n₁) (h : ℕ)
    (U₁ : Operator (2^n₁)) (U₂ : Operator (2^n₂)) (w₂ : List (CleanOp n₂))
    (ρ₁ : Operator ((2^n₁)*1)) (ρ₂ : Operator ((2^n₂)*1)) :
    (stopMeasured U₁ i h ρ₁).length = h + 1 ∧
    (stopMeasured U₁ i h ρ₁).filter (fun t => !t.native.accepted) = [rejectedTrace U₁ i h ρ₁] ∧
    (∀ t₁ ∈ stopMeasured U₁ i h ρ₁,
      (stopJointResources n₁ n₂ t₁ w₂).queries
        = (t₁.resources n₁).queries + ((wordTrace U₂ w₂ ρ₂).resources n₂).queries ∧
      (stopJointResources n₁ n₂ t₁ w₂).peakSpace
        = n₁ + n₂ + max t₁.peakAux (peakAuxOf w₂)) ∧
    (stopJointResources n₁ n₂ (rejectedTrace U₁ i h ρ₁) w₂).queries
      = h + wordQueries w₂ := by
  refine ⟨stopMeasured_length U₁ i h ρ₁, stopMeasured_rejected U₁ i h ρ₁, ?_, ?_⟩
  · intro t₁ _
    exact ⟨rfl, rfl⟩
  · calc (stopJointResources n₁ n₂ (rejectedTrace U₁ i h ρ₁) w₂).queries
        = (rejectedTrace U₁ i h ρ₁).native.queries + wordQueries w₂ := rfl
      _ = h + wordQueries w₂ := by rw [rejectedTrace_native U₁ i h ρ₁]

end
