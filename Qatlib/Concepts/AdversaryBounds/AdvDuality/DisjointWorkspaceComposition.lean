/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import QuantumInfo.ForMathlib.Isometry
set_option warningAsError false
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
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

def tensorLiftL {a b : ℕ} (M : Operator a) : Operator (a*b) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (TensorGate M (1 : Operator b))

def tensorLiftR {a b : ℕ} (N : Operator b) : Operator (a*b) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (TensorGate (1 : Operator a) N)

theorem liftL_mul_liftR {a b : ℕ} (M : Operator a) (N : Operator b) :
    tensorLiftL M * tensorLiftR N =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (TensorGate M N) := by
  have h : tensorLiftL M * tensorLiftR N =
      (TensorGate M (1 : Operator b) * TensorGate (1 : Operator a) N).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm :=
    Matrix.submatrix_mul_equiv _ _ _ _ _
  rw [h, tensorGate_mul, Matrix.mul_one, Matrix.one_mul]
  rfl

theorem liftR_mul_liftL {a b : ℕ} (M : Operator a) (N : Operator b) :
    tensorLiftR N * tensorLiftL M =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (TensorGate M N) := by
  have h : tensorLiftR N * tensorLiftL M =
      (TensorGate (1 : Operator a) N * TensorGate M (1 : Operator b)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm :=
    Matrix.submatrix_mul_equiv _ _ _ _ _
  rw [h, tensorGate_mul, Matrix.one_mul, Matrix.mul_one]
  rfl

theorem lift_commute {a b : ℕ} (M : Operator a) (N : Operator b) :
    tensorLiftL M * tensorLiftR N = tensorLiftR N * tensorLiftL M :=
  (liftL_mul_liftR M N).trans (liftR_mul_liftL M N).symm

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

theorem joint_output_swap {a b : ℕ} (M : Operator a) (N : Operator b) :
    (TensorGate M N).submatrix (Equiv.prodComm (Fin a) (Fin b)).symm
      (Equiv.prodComm (Fin a) (Fin b)).symm = TensorGate N M := by
  ext p q
  simp only [Matrix.submatrix_apply, TensorGate, Matrix.kroneckerMap_apply]
  exact mul_comm _ _

def liveTrailOf {n : ℕ} (w : List (CleanOp n)) : List ℕ :=
  (wordWidths w).map (Nat.clog 2)

def peakAuxOf {n : ℕ} (w : List (CleanOp n)) : ℕ :=
  maxTrail (liveTrailOf w)

theorem maxTrail_eq_foldr (l : List ℕ) : maxTrail l = l.foldr Nat.max 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [maxTrail, List.foldr_cons, ih]

theorem liveTrailOf_is_actual {n : ℕ} (U : Operator (2^n)) (w : List (CleanOp n))
    (ρ : Operator ((2^n)*1)) :
    (wordTrace U w ρ).widths = wordWidths w ∧
    (wordTrace U w ρ).peakAux = peakAuxOf w := by
  refine ⟨rfl, ?_⟩
  simp only [MeasuredTrace.peakAux, wordTrace, liveTrailOf, peakAuxOf, maxTrail_eq_foldr]

theorem peakAuxOf_eq {n : ℕ} (w : List (CleanOp n)) :
    peakAuxOf w = if wordPhases w = 0 then 0 else 1 := by
  simp only [peakAuxOf, liveTrailOf, maxTrail_eq_foldr]
  exact wordWidths_peak w

theorem maxTrail_nil : maxTrail ([] : List ℕ) = 0 := rfl

theorem maxTrail_cons (a : ℕ) (l : List ℕ) : maxTrail (a :: l) = max a (maxTrail l) := rfl

theorem mem_le_maxTrail {l : List ℕ} (x : ℕ) (hx : x ∈ l) : x ≤ maxTrail l := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
      rcases List.mem_cons.mp hx with h | h
      · simp only [h, maxTrail_cons]
        exact Nat.le_max_left _ _
      · exact le_trans (ih h) (Nat.le_max_right _ _)

theorem maxTrail_le_of_forall {l : List ℕ} {m : ℕ} (h : ∀ x ∈ l, x ≤ m) : maxTrail l ≤ m := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
      exact Nat.max_le.mpr ⟨h a (by simp), ih (fun x hx => h x (by simp [hx]))⟩

def nthNat : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, k+1 => nthNat l k

theorem nthNat_nil (k : ℕ) : nthNat [] k = 0 := by cases k <;> rfl

theorem nthNat_zero (a : ℕ) (l : List ℕ) : nthNat (a :: l) 0 = a := rfl

theorem nthNat_succ (a : ℕ) (l : List ℕ) (k : ℕ) : nthNat (a :: l) (k+1) = nthNat l k := rfl

theorem nthNat_lt_mem {l : List ℕ} {k : ℕ} (hk : k < l.length) : nthNat l k ∈ l := by
  induction l generalizing k with
  | nil => simp only [List.length_nil] at hk; exact absurd hk (Nat.not_lt_zero k)
  | cons a l ih =>
      match k with
      | 0 => simp [nthNat_zero]
      | k+1 => exact List.mem_cons_of_mem a (ih (Nat.lt_of_succ_lt_succ hk))

theorem nthNat_map_add_zero (l : List ℕ) (k : ℕ) :
    nthNat (l.map (fun x => x + 0)) k = nthNat l k + 0 := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons a l ih =>
      cases k with
      | zero => rfl
      | succ k => simp only [List.map_cons, nthNat_succ, ih k]

def seqLiveTrail {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) : List ℕ :=
  liveTrailOf w₁ ++ liveTrailOf w₂

theorem seq_peak {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    maxTrail (seqLiveTrail w₁ w₂) = max (peakAuxOf w₁) (peakAuxOf w₂) := by
  simp only [seqLiveTrail, peakAuxOf, maxTrail_append]

def stackTrail : List ℕ → List ℕ → List ℕ
  | [], l => l.map (fun x => x + 0)
  | l, [] => l.map (fun x => x + 0)
  | a :: l₁, b :: l₂ => (a + b) :: stackTrail l₁ l₂

theorem stackTrail_nil_left (l : List ℕ) : stackTrail [] l = l.map (fun x => x + 0) := rfl

theorem stackTrail_nil_right (a : ℕ) (l : List ℕ) :
    stackTrail (a :: l) [] = (a + 0) :: l.map (fun x => x + 0) := rfl

theorem stackTrail_cons (a b : ℕ) (l₁ l₂ : List ℕ) :
    stackTrail (a :: l₁) (b :: l₂) = (a + b) :: stackTrail l₁ l₂ := rfl

theorem maxTrail_map_add_zero (l : List ℕ) :
    maxTrail (l.map (fun x => x + 0)) = maxTrail l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, maxTrail_cons, ih]; omega

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

theorem nthNat_stackTrail_mem {l₁ l₂ : List ℕ} {k : ℕ} (h1 : k < l₁.length)
    (h2 : k < l₂.length) : nthNat l₁ k + nthNat l₂ k ∈ stackTrail l₁ l₂ := by
  have hlen : k < (stackTrail l₁ l₂).length := by
    rw [stackTrail_length]
    omega
  rw [← nthNat_stackTrail l₁ l₂ k]
  exact nthNat_lt_mem hlen

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

theorem stack_peak_eq_of_cooccur (l₁ l₂ : List ℕ) (k : ℕ)
    (h1 : k < l₁.length) (h2 : k < l₂.length)
    (e1 : nthNat l₁ k = maxTrail l₁) (e2 : nthNat l₂ k = maxTrail l₂) :
    maxTrail (stackTrail l₁ l₂) = maxTrail l₁ + maxTrail l₂ := by
  refine le_antisymm (stack_peak_le l₁ l₂) ?_
  have hmem : nthNat l₁ k + nthNat l₂ k ∈ stackTrail l₁ l₂ :=
    nthNat_stackTrail_mem h1 h2
  rw [e1, e2] at hmem
  exact mem_le_maxTrail _ hmem

def jointSeqResources {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    ResourceCost :=
  ⟨wordQueries w₁ + wordQueries w₂,
   wordGates w₁ + wordGates w₂,
   wordGates w₁ + wordGates w₂,
   (wordQueries w₁ + wordGates w₁ + 2*wordPhases w₁)
     + (wordQueries w₂ + wordGates w₂ + 2*wordPhases w₂),
   n₁ + n₂ + max (peakAuxOf w₁) (peakAuxOf w₂),
   0, 0⟩

def jointStackResources {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    ResourceCost :=
  ⟨wordQueries w₁ + wordQueries w₂,
   wordGates w₁ + wordGates w₂,
   wordGates w₁ + wordGates w₂,
   (wordQueries w₁ + wordGates w₁ + 2*wordPhases w₁)
     + (wordQueries w₂ + wordGates w₂ + 2*wordPhases w₂),
   n₁ + n₂ + (peakAuxOf w₁ + peakAuxOf w₂),
   0, 0⟩

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

theorem jointSeq_exchange {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    jointSeqResources w₁ w₂ = jointSeqResources w₂ w₁ := by
  ext <;> simp only [jointSeqResources] <;> omega

theorem jointStack_exchange {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    jointStackResources w₁ w₂ = jointStackResources w₂ w₁ := by
  ext <;> simp only [jointStackResources] <;> omega

theorem jointSeq_peakSpace_trail {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    (jointSeqResources w₁ w₂).peakSpace = n₁ + n₂ + maxTrail (seqLiveTrail w₁ w₂) := by
  simp only [jointSeqResources, seq_peak]

theorem seq_peakSpace_le_stack {n₁ n₂ : ℕ} (w₁ : List (CleanOp n₁)) (w₂ : List (CleanOp n₂)) :
    (jointSeqResources w₁ w₂).peakSpace ≤ (jointStackResources w₁ w₂).peakSpace := by
  simp only [jointSeqResources, jointStackResources]
  omega

section ReferenceError

open Classical

variable {α β : Type} [Fintype α] [Fintype β]

private theorem sum_ite_left_eq (F : α → ℂ) (t : α) :
    ∑ i, (if i = t then (1 : ℂ) else 0) * F i = F t := by
  simp [Finset.sum_ite_eq']

private theorem sum_ite_right_eq (F : α → ℂ) (t : α) :
    ∑ i, F i * (if i = t then (1 : ℂ) else 0) = F t := by
  simp [Finset.sum_ite_eq]

private theorem star_indicator (c : Prop) [Decidable c] :
    star (if c then (1 : ℂ) else 0) = if c then 1 else 0 := by
  by_cases h : c <;> simp [h]

private def equivRows (e : α ≃ β) : Matrix β α ℂ :=
  fun i j => if j = e.symm i then 1 else 0

private theorem equivRows_left_mul (e : α ≃ β) (A : Matrix α α ℂ) (i : β) (k : α) :
    (equivRows e * A) i k = A (e.symm i) k := by
  rw [Matrix.mul_apply]
  simp only [equivRows]
  exact sum_ite_left_eq (fun j => A j k) (e.symm i)

private theorem equivRows_conj_mul (e : α ≃ β) (A : Matrix α α ℂ) (i k : β) :
    (equivRows e * A * (equivRows e).conjTranspose) i k = A (e.symm i) (e.symm k) := by
  have houter : (equivRows e * A * (equivRows e).conjTranspose) i k
      = ∑ l : α, (equivRows e * A) i l * ((equivRows e).conjTranspose) l k := by
    rw [Matrix.mul_apply]
  have hinner : ∀ l : α, (equivRows e * A) i l = A (e.symm i) l := equivRows_left_mul e A i
  rw [houter]
  simp only [hinner, Matrix.conjTranspose_apply, equivRows, star_indicator]
  exact sum_ite_right_eq (fun l => A (e.symm i) l) (e.symm k)

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

theorem traceNorm_reindex (e : α ≃ β) (A : Matrix α α ℂ) :
    (Matrix.reindex e e A).traceNorm = A.traceNorm := by
  have hconj : equivRows e * A * (equivRows e).conjTranspose = Matrix.reindex e e A := by
    ext i k
    rw [Matrix.reindex_apply]
    exact equivRows_conj_mul e A i k
  rw [← hconj, Matrix.mul_assoc,
    traceNorm_isometry_left (equivRows_isometry e),
    traceNorm_isometry_right (equivRows_isometry e)]

theorem isHermitian_reindex (e : α ≃ β) (A : Matrix α α ℂ) (hA : A.IsHermitian) :
    (Matrix.reindex e e A).IsHermitian :=
  hA.submatrix _

private theorem reindex_symm_cancel (e : α ≃ β) (M : Matrix α α ℂ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e M) = M := by
  ext i j
  simp [Matrix.reindex_apply]

private theorem reindex_symm_cancel' (e : α ≃ β) (N : Matrix β β ℂ) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm N) = N := by
  ext i j
  simp [Matrix.reindex_apply]

end ReferenceError

def StarPreserving {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Prop :=
  ∀ Y, (T Y).conjTranspose = T Y.conjTranspose

theorem release_branch_starPreserving (d : ℕ) : StarPreserving ((release d).branch 0) := by
  intro Y
  simp only [release_branch, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem allocate_branch_starPreserving (d : ℕ) : StarPreserving ((allocate d).branch 0) := by
  intro Y
  simp only [allocate_branch, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

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

theorem channelAmplification_release_allocate (d r : ℕ)
    (Y : Matrix (Fin r × Fin (d*1)) (Fin r × Fin (d*1)) ℂ) :
    ChannelAmplification ((release d).branch 0) r
      (ChannelAmplification ((allocate d).branch 0) r Y) = Y := by
  ext x y
  simp only [ChannelAmplification]
  rw [release_clean d (fun i j => Y (x.1, i) (y.1, j))]

section TwoFactorRelease

def flatRight (r a b : ℕ) : Fin r × (Fin a × Fin b) ≃ Fin (r*a) × Fin b :=
  (Equiv.prodAssoc (Fin r) (Fin a) (Fin b)).symm.trans
    ((finProdFinEquiv (m := r) (n := a)).prodCongr (Equiv.refl (Fin b)))

def flatLeft (r a b : ℕ) : Fin r × (Fin a × Fin b) ≃ Fin (r*b) × Fin a :=
  ((Equiv.prodCongr (Equiv.refl (Fin r)) (Equiv.prodComm (Fin a) (Fin b))).trans
    (Equiv.prodAssoc (Fin r) (Fin b) (Fin a)).symm).trans
    ((finProdFinEquiv (m := r) (n := b)).prodCongr (Equiv.refl (Fin a)))

def releaseSecond (d₁ d₂ r : ℕ)
    (X : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ) :
    Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*1))) (Fin r × (Fin (d₁*2) × Fin (d₂*1))) ℂ :=
  (ChannelAmplification ((release d₂).branch 0) (r*(d₁*2))
    (Matrix.reindex (flatRight r (d₁*2) (d₂*2)) (flatRight r (d₁*2) (d₂*2)) X)).reindex
    (flatRight r (d₁*2) (d₂*1)).symm (flatRight r (d₁*2) (d₂*1)).symm

def releaseFirst (d₁ d₂ r : ℕ)
    (Y : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*1))) (Fin r × (Fin (d₁*2) × Fin (d₂*1))) ℂ) :
    Matrix (Fin r × (Fin (d₁*1) × Fin (d₂*1))) (Fin r × (Fin (d₁*1) × Fin (d₂*1))) ℂ :=
  (ChannelAmplification ((release d₁).branch 0) (r*(d₂*1))
    (Matrix.reindex (flatLeft r (d₁*2) (d₂*1)) (flatLeft r (d₁*2) (d₂*1)) Y)).reindex
    (flatLeft r (d₁*1) (d₂*1)).symm (flatLeft r (d₁*1) (d₂*1)).symm

def jointAllocate (d₁ d₂ r : ℕ)
    (ρ : Matrix (Fin r × (Fin (d₁*1) × Fin (d₂*1))) (Fin r × (Fin (d₁*1) × Fin (d₂*1))) ℂ) :
    Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ :=
  (ChannelAmplification ((allocate d₂).branch 0) (r*(d₁*2))
    (Matrix.reindex (flatRight r (d₁*2) (d₂*1)) (flatRight r (d₁*2) (d₂*1))
      ((ChannelAmplification ((allocate d₁).branch 0) (r*(d₂*1))
        (Matrix.reindex (flatLeft r (d₁*1) (d₂*1)) (flatLeft r (d₁*1) (d₂*1)) ρ)).reindex
        (flatLeft r (d₁*2) (d₂*1)).symm (flatLeft r (d₁*2) (d₂*1)).symm))).reindex
    (flatRight r (d₁*2) (d₂*2)).symm (flatRight r (d₁*2) (d₂*2)).symm

theorem releaseSecond_hermitian (d₁ d₂ r : ℕ)
    (X : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ)
    (hX : X.IsHermitian) : (releaseSecond d₁ d₂ r X).IsHermitian :=
  isHermitian_reindex _ _ (channelAmplification_hermitian _ (release_branch_starPreserving d₂)
    (isHermitian_reindex _ _ hX))

theorem releaseFirst_hermitian (d₁ d₂ r : ℕ)
    (Y : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*1))) (Fin r × (Fin (d₁*2) × Fin (d₂*1))) ℂ)
    (hY : Y.IsHermitian) : (releaseFirst d₁ d₂ r Y).IsHermitian :=
  isHermitian_reindex _ _ (channelAmplification_hermitian _ (release_branch_starPreserving d₁)
    (isHermitian_reindex _ _ hY))

theorem releaseSecond_traceNorm (d₁ d₂ r : ℕ)
    (X : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ)
    (hX : X.IsHermitian) : (releaseSecond d₁ d₂ r X).traceNorm ≤ X.traceNorm := by
  have h1 := release_reference_error d₂ (r*(d₁*2)) _
    (isHermitian_reindex (flatRight r (d₁*2) (d₂*2)) _ hX)
  rw [traceNorm_reindex] at h1
  unfold releaseSecond
  rw [traceNorm_reindex]
  exact h1

theorem releaseFirst_traceNorm (d₁ d₂ r : ℕ)
    (Y : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*1))) (Fin r × (Fin (d₁*2) × Fin (d₂*1))) ℂ)
    (hY : Y.IsHermitian) : (releaseFirst d₁ d₂ r Y).traceNorm ≤ Y.traceNorm := by
  have h1 := release_reference_error d₁ (r*(d₂*1)) _
    (isHermitian_reindex (flatLeft r (d₁*2) (d₂*1)) _ hY)
  rw [traceNorm_reindex] at h1
  unfold releaseFirst
  rw [traceNorm_reindex]
  exact h1

theorem release_stepwise_traceNorm (d₁ d₂ r : ℕ)
    (X : Matrix (Fin r × (Fin (d₁*2) × Fin (d₂*2))) (Fin r × (Fin (d₁*2) × Fin (d₂*2))) ℂ)
    (hX : X.IsHermitian) :
    (releaseFirst d₁ d₂ r (releaseSecond d₁ d₂ r X)).traceNorm ≤ X.traceNorm :=
  (releaseFirst_traceNorm d₁ d₂ r _ (releaseSecond_hermitian d₁ d₂ r X hX)).trans
    (releaseSecond_traceNorm d₁ d₂ r X hX)

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

def lcuWord {n : ℕ} (i : Fin n) : List (CleanOp n) := [CleanOp.query, CleanOp.phase i]

theorem lcuWord_counts {n : ℕ} (i : Fin n) :
    wordQueries (lcuWord i) = 1 ∧ wordGates (lcuWord i) = 4 ∧ wordPhases (lcuWord i) = 1 :=
  ⟨rfl, rfl, rfl⟩

theorem lcuWord_peak {n : ℕ} (i : Fin n) : peakAuxOf (lcuWord i) = 1 := by
  rw [peakAuxOf_eq]
  simp [lcuWord, wordPhases]

theorem liveTrailOf_lcuWord {n : ℕ} (i : Fin n) :
    liveTrailOf (lcuWord i) = [0, 0, 1, 1, 1, 1, 1, 0] := by
  have h1 : Nat.clog 2 1 = 0 := by decide
  have h2 : Nat.clog 2 2 = 1 := by decide
  simp only [liveTrailOf, lcuWord, wordWidths, List.map_cons, List.map_append,
    List.map_replicate, List.cons_append, h1, h2]
  decide

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

def stopJointResources (n₁ n₂ : ℕ) (t₁ : MeasuredTrace (2^n₁)) (w₂ : List (CleanOp n₂)) :
    ResourceCost :=
  ⟨t₁.native.queries + wordQueries w₂,
   t₁.gates + wordGates w₂,
   t₁.gates + wordGates w₂,
   (t₁.native.queries + t₁.gates + t₁.instruments)
     + (wordQueries w₂ + wordGates w₂ + 2*wordPhases w₂),
   n₁ + n₂ + max t₁.peakAux (peakAuxOf w₂),
   0, 0⟩

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
