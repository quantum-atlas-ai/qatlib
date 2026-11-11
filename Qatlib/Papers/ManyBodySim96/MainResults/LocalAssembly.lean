/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodySim96.MainResults.FirstOrderSelection
import Qatlib.Papers.ManyBodySim96.MainResults.LocalEvolution
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegistersDefs

/-!
# Lifting and compiling local product formulas

`partitionLift` extends an operator by the identity on a complementary register. This module
proves its algebraic and norm properties and transports product-formula words through a fixed
partition. It also assembles supplied reflection-gate implementations into a legal circuit with
the product-formula matrix and an explicit gate bound.

The mathematical setting is that of [Wiesner1996].

## Main statements

* `partitionLift_norm`: Lifting an operator by the identity on a nonempty complementary register
  preserves its operator norm.
* `first_order_common_partition`: Local Hermitian terms with a common nonnegative norm bound
  retain those bounds under their supplied partitions, and the selected first-order formula
  satisfies the stated unitarity, length, operator-error, and observable-error bounds.
* `compiled_first_order_word`: Exact legal local implementations of length at most `C` assemble
  into a legal, query-free reflection program realizing the first-order product formula with at
  most `M * r * C` gates.

## References

* [Wiesner, 1996][Wiesner1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open scoped BigOperators Matrix.Norms.L2Operator Kronecker

namespace Qatlib.Papers.ManyBodySim96.MainResults

/-- Lifting to a partitioned register preserves matrix multiplication. -/
theorem partitionLift_mul {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (U V : Matrix A A ℂ) :
    partitionLift e (U * V) = partitionLift e U * partitionLift e V := by
  change Matrix.reindexAlgEquiv ℂ ℂ e.symm ((U * V) ⊗ₖ (1 : Matrix B B ℂ)) =
    Matrix.reindexAlgEquiv ℂ ℂ e.symm (U ⊗ₖ (1 : Matrix B B ℂ)) *
      Matrix.reindexAlgEquiv ℂ ℂ e.symm (V ⊗ₖ (1 : Matrix B B ℂ))
  rw [← map_mul]
  congr 1
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

/-- Lifting the identity matrix gives the identity on the full register. -/
theorem partitionLift_one {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) :
    partitionLift e (1 : Matrix A A ℂ) = 1 := by
  change Matrix.reindexAlgEquiv ℂ ℂ e.symm
    ((1 : Matrix A A ℂ) ⊗ₖ (1 : Matrix B B ℂ)) = 1
  rw [Matrix.one_kronecker_one, map_one]

/-- Lifting to a partitioned register commutes with conjugate transpose. -/
theorem partitionLift_conjTranspose {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (U : Matrix A A ℂ) :
    (partitionLift e U)ᴴ = partitionLift e Uᴴ := by
  simp only [partitionLift]
  rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- Lifting a Hermitian matrix preserves Hermiticity. -/
theorem partitionLift_isHermitian {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) {U : Matrix A A ℂ} (hU : U.IsHermitian) :
    (partitionLift e U).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [partitionLift_conjTranspose, hU.eq]

/-- Lifting an operator by the identity on a nonempty complementary register preserves its
operator norm. -/
theorem partitionLift_norm {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
    (e : S ≃ A × B) (U : Matrix A A ℂ) :
    ‖partitionLift e U‖ = ‖U‖ := by
  have h : partitionLift e U = relabelGate e.symm (U ⊗ₖ (1 : Matrix B B ℂ)) := rfl
  rw [h, l2_norm_relabelGate, l2_norm_kronecker, l2_norm_one_eq, mul_one]

/-- Lifting commutes with the left fold that multiplies each successive word matrix on the left
of the accumulator. -/
private theorem partitionLift_foldl {D a : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (e : Fin D ≃ Fin (2 ^ a) × B) (xs : List (Operator (2 ^ a) × ℕ))
    (X : Operator (2 ^ a)) :
    partitionLift e (xs.foldl (fun U x => x.1 * U) X) =
      (xs.map (fun p => (partitionLift e p.1, p.2))).foldl
        (fun U x => x.1 * U) (partitionLift e X) := by
  induction xs generalizing X with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, partitionLift_mul]

/-- Lifting the interpretation of a tagged matrix word equals interpreting the word after
lifting each matrix. -/
theorem partitionLift_pfInterpret {D a : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (e : Fin D ≃ Fin (2 ^ a) × B) (xs : List (Operator (2 ^ a) × ℕ)) :
    partitionLift e (pfInterpret xs) =
      pfInterpret (xs.map (fun p => (partitionLift e p.1, p.2))) := by
  unfold pfInterpret
  rw [partitionLift_foldl, partitionLift_one]

/-- The product-formula word of a lifted Hamiltonian family is obtained by lifting every matrix
in the original word. -/
theorem partitionLift_pfFamilyWord {D a : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (e : Fin D ≃ Fin (2 ^ a) × B) {M : ℕ} (H : Fin M → Operator (2 ^ a))
    (t : ℝ) (r : ℕ) :
    pfFamilyWord (fun j => partitionLift e (H j)) t r =
      (pfFamilyWord H t r).map (fun p => (partitionLift e p.1, p.2)) := by
  unfold pfFamilyWord
  rw [List.map_flatten, List.map_replicate, List.map_ofFn]
  congr 1
  congr 1
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [evolution_partitionLift]

/-- The product formula for a lifted Hamiltonian family is the lift of the original product
formula. -/
theorem partitionLift_pfFamily {D a : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (e : Fin D ≃ Fin (2 ^ a) × B) {M : ℕ} (H : Fin M → Operator (2 ^ a))
    (t : ℝ) (r : ℕ) :
    pfFamily (fun j => partitionLift e (H j)) t r =
      partitionLift e (pfFamily H t r) := by
  unfold pfFamily
  rw [partitionLift_pfFamilyWord, partitionLift_pfInterpret]

/-- Lifting to a partitioned register preserves matrix addition. -/
theorem partitionLift_add {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (U V : Matrix A A ℂ) :
    partitionLift e (U + V) = partitionLift e U + partitionLift e V := by
  change Matrix.reindexAlgEquiv ℂ ℂ e.symm ((U + V) ⊗ₖ (1 : Matrix B B ℂ)) =
    Matrix.reindexAlgEquiv ℂ ℂ e.symm (U ⊗ₖ (1 : Matrix B B ℂ)) +
      Matrix.reindexAlgEquiv ℂ ℂ e.symm (V ⊗ₖ (1 : Matrix B B ℂ))
  rw [← map_add]
  congr 1
  rw [Matrix.add_kronecker]

/-- The sum of a finite family of lifted matrices is the lift of their sum. -/
theorem partitionLift_sum {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) {M : ℕ} (H : Fin M → Matrix A A ℂ) :
    (∑ j, partitionLift e (H j)) = partitionLift e (∑ j, H j) := by
  have hzero : partitionLift e (0 : Matrix A A ℂ) = 0 := by
    simp [partitionLift]
  induction (Finset.univ : Finset (Fin M)) using Finset.induction with
  | empty => simp [hzero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, partitionLift_add, ih]

/-- Local Hermitian terms with a common nonnegative norm bound retain those bounds under their
supplied partitions, and the selected first-order formula satisfies the stated unitarity,
length, operator-error, and observable-error bounds. [Wiesner1996] -/
theorem first_order_common_partition {D a M : ℕ} (B : Type*) [Fintype B]
    [DecidableEq B] [Nonempty B] (e : Fin M → Fin D ≃ Fin (2 ^ a) × B)
    (H : Fin M → Operator (2 ^ a)) (b T ε : ℝ) (O : Operator D)
    (hb : 0 ≤ b) (hε : 0 < ε) (hH : ∀ j, (H j).IsHermitian)
    (hbound : ∀ j, ‖H j‖ ≤ b) :
    let HL : Fin M → Operator D := fun j => partitionLift (e j) (H j)
    let r := sourceFirstSegments M b T ε
    0 < r ∧ (∀ j, (HL j).IsHermitian) ∧ (∀ j, ‖HL j‖ ≤ b) ∧
      (pfFamilyWord HL (-T) r).length = M * r ∧
      pfFamily HL (-T) r ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ‖pfFamily HL (-T) r - HamiltonianEvolution (∑ j, HL j) (-T)‖ ≤ ε ∧
      ‖(pfFamily HL (-T) r)ᴴ * O * pfFamily HL (-T) r -
        (HamiltonianEvolution (∑ j, HL j) (-T))ᴴ * O *
          HamiltonianEvolution (∑ j, HL j) (-T)‖ ≤ 2 * ‖O‖ * ε := by
  (try dsimp only)
  have hHL : ∀ j, ((fun j => partitionLift (e j) (H j)) j : Operator D).IsHermitian :=
    fun j => partitionLift_isHermitian (e j) (hH j)
  have hbd : ∀ j, ‖partitionLift (e j) (H j)‖ ≤ b := by
    intro j
    rw [partitionLift_norm]
    exact hbound j
  obtain ⟨hr, hlen, hu, herr, hobs⟩ :=
    source_first_order_selected (fun j => partitionLift (e j) (H j)) b T ε O hb hε hHL hbd
  refine ⟨hr, hHL, hbd, hlen, hu, ?_, hobs⟩
  have hpos : NormedSpace.exp ((Complex.I * (T : ℂ)) •
      ∑ j : Fin M, partitionLift (e j) (H j)) =
      HamiltonianEvolution (∑ j, partitionLift (e j) (H j)) (-T) :=
    source_positive_evolution _ T
  rw [← hpos]
  exact herr

/-- The matrix of flattened reflection-program blocks is their successive left-multiplication
fold starting from the identity. -/
theorem reflectionProgramMatrix_flatten {b : ℕ}
    (blocks : List (List (ReflectionGate b))) :
    reflectionProgramMatrix blocks.flatten =
      blocks.foldl (fun U blk => reflectionProgramMatrix blk * U) 1 := by
  have h : ∀ U : Matrix (Reg b) (Reg b) ℂ,
      blocks.foldl (fun U blk => reflectionProgramMatrix blk * U) U =
        reflectionProgramMatrix blocks.flatten * U := by
    induction blocks with
    | nil => intro U; simp [reflectionProgramMatrix]
    | cons blk blocks ih =>
      intro U
      rw [List.flatten_cons, List.foldl_cons, ih, reflectionProgramMatrix_append,
        mul_assoc]
  simpa using! (h 1).symm

/-- Replacing each label by a reflection program realizing its Hamiltonian evolution makes the
evolution fold equal the relabeled matrix of the flattened program times the initial
accumulator. -/
theorem relabel_flatten_fold {b M : ℕ}
    (H : Fin M → Operator (2 ^ b)) (s : ℝ)
    (ws : Fin M → List (ReflectionGate b))
    (hreal : ∀ j, relabelGate (bitVecEquiv b) (reflectionProgramMatrix (ws j)) =
      HamiltonianEvolution (H j) s) :
    ∀ (word : List (Fin M)) (U : Matrix (Fin (2 ^ b)) (Fin (2 ^ b)) ℂ),
      word.foldl (fun V j => HamiltonianEvolution (H j) s * V) U =
        relabelGate (bitVecEquiv b)
          (reflectionProgramMatrix (((word.map ws).flatten))) * U := by
  intro word
  induction word with
  | nil =>
    intro U
    simp [reflectionProgramMatrix,
        Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one]
  | cons j word ih =>
    intro U
    simp only [List.map_cons, List.flatten_cons, List.foldl_cons]
    rw [reflectionProgramMatrix_append,
      Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,
      hreal j, ih, mul_assoc]

/-- The concatenation of `r` copies of the ordered list of all `M` term labels. -/
def segmentLabels (M r : ℕ) : List (Fin M) :=
  (List.replicate r (List.ofFn (fun j : Fin M => j))).flatten

/-- The first-order product formula equals the fold of term evolutions at time `T / r` along the
repeated segment labels. -/
theorem pfFamily_eq_segmentFold {D M r : ℕ} (H : Fin M → Operator D) (T : ℝ) :
    pfFamily H T r =
      (segmentLabels M r).foldl (fun U j => HamiltonianEvolution (H j) (T / r) * U) 1 := by
  have hlist : pfFamilyWord H T r =
      (segmentLabels M r).map
        (fun j => (HamiltonianEvolution (H j) (T / r), j.val)) := by
    unfold pfFamilyWord segmentLabels
    simp only [List.map_flatten, List.map_replicate, List.map_ofFn, Function.comp_def]
  unfold pfFamily pfInterpret
  rw [hlist, List.foldl_map]

/-- Substituting a program of length at most `C` for each label gives a flattened program of
length at most the label-list length times `C`. -/
private theorem length_flatten_map_le {b M : ℕ} (ws : Fin M → List (ReflectionGate b))
    (C : ℕ) (hlen : ∀ j, (ws j).length ≤ C) :
    ∀ word : List (Fin M), ((word.map ws).flatten).length ≤ word.length * C := by
  intro word
  induction word with
  | nil => simp
  | cons j word ih =>
    rw [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have h1 := hlen j
    have h2 : (word.length + 1) * C = C + word.length * C := by ring
    omega

/-- Exact legal local implementations of length at most `C` assemble into a legal, query-free
reflection program realizing the first-order product formula with at most `M * r * C` gates.
[Wiesner1996] -/
theorem compiled_first_order_word {b M r : ℕ} (H : Fin M → Operator (2 ^ b)) (s : ℝ)
    (ws : Fin M → List (ReflectionGate b)) (C : ℕ)
    (hreal : ∀ j, relabelGate (bitVecEquiv b) (reflectionProgramMatrix (ws j)) =
      HamiltonianEvolution (H j) (s / r))
    (hlegal : ∀ j, reflectionLegal (ws j)) (hlen : ∀ j, (ws j).length ≤ C) :
    ∃ gs : List (ReflectionGate b),
      reflectionLegal gs ∧ gs.length ≤ M * r * C ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      relabelGate (bitVecEquiv b) (reflectionProgramMatrix gs) = pfFamily H s r := by
  classical
  let word := segmentLabels M r
  let gs : List (ReflectionGate b) := (word.map ws).flatten
  have hlen_word : word.length = M * r := by
    simp [word, segmentLabels, List.length_flatten, List.length_ofFn, Nat.mul_comm]
  have hlen_gs : gs.length ≤ M * r * C := by
    have hl := length_flatten_map_le ws C hlen word
    rwa [hlen_word] at hl
  have hlegal_gs : reflectionLegal gs := by
    intro g hg
    obtain ⟨blk, hblk, hmem⟩ := List.mem_flatten.mp hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hblk
    exact hlegal j g hmem
  have hmat : relabelGate (bitVecEquiv b) (reflectionProgramMatrix gs) = pfFamily H s r := by
    rw [pfFamily_eq_segmentFold]
    simpa using! (relabel_flatten_fold H (s / r) ws hreal word 1).symm
  refine ⟨gs, hlegal_gs, hlen_gs, ?_, ?_, hmat⟩
  · exact gateCount_reflectionCompile gs
  · exact queryCount_reflectionCompile gs

end Qatlib.Papers.ManyBodySim96.MainResults
