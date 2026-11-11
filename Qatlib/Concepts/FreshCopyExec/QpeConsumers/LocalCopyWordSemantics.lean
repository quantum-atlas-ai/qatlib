/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl
import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyLayout

/-!
# Local controlled-swap word semantics

This module proves legality, exact lengths, and matrix semantics for the local controlled-swap
words. `localCopyPairLift` separates data-copy pairs, while `localCopyPhaseLift` isolates the
control and parity wires.

The Bell basis diagonalizes register swap into a parity sign, and the compute word accumulates
that parity without changing the control bit. These circuit identities use the elementary gate
and tensor conventions described in [NielsenChuang2010].

## Main statements

* `local_controlled_swap_actual_gate_table_and_inverse`: packages legality, unitarity, support,
  and the `36 * n + 7` gate count.
* `local_bell_basis_register_swap_parity`: diagonalizes register swap in the local Bell basis.
* `localCopyComputeAndParity_sign`: identifies the computed parity sign for clean auxiliary
  wires.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators
set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers

/-- The data wire and fresh-copy wire at the same position are distinct. -/
private theorem localCopyData_ne_fresh (n : ℕ) (i : Fin n) :
    localCopyDataWire n i ≠ localCopyFreshWire n i := by
  intro h
  have := congrArg Fin.val h
  dsimp [localCopyDataWire, localCopyFreshWire] at this
  omega

/-- The data wire and auxiliary AND wire at the same position are distinct. -/
private theorem localCopyData_ne_and (n : ℕ) (i : Fin n) :
    localCopyDataWire n i ≠ localCopyAndWire n i := by
  intro h
  have := congrArg Fin.val h
  dsimp [localCopyDataWire, localCopyAndWire] at this
  omega

/-- The fresh-copy wire and auxiliary AND wire at the same position are distinct. -/
private theorem localCopyFresh_ne_and (n : ℕ) (i : Fin n) :
    localCopyFreshWire n i ≠ localCopyAndWire n i := by
  intro h
  have := congrArg Fin.val h
  dsimp [localCopyFreshWire, localCopyAndWire] at this
  omega

/-- Every auxiliary AND wire is distinct from the parity wire. -/
private theorem localCopyAnd_ne_parity (n : ℕ) (i : Fin n) :
    localCopyAndWire n i ≠ localCopyParityWire n := by
  intro h
  have := congrArg Fin.val h
  dsimp [localCopyAndWire, localCopyParityWire] at this
  omega

/-- The control wire is distinct from the parity wire. -/
private theorem localCopyControl_ne_parity (n : ℕ) :
    localCopyControlWire n ≠ localCopyParityWire n := by
  intro h
  have := congrArg Fin.val h
  dsimp [localCopyControlWire, localCopyParityWire] at this
  omega

/-- Concatenating two legal reflection-gate words gives a legal word. -/
private theorem reflectionLegal_append' {n : ℕ} {a b : List (ReflectionGate n)}
    (ha : reflectionLegal a) (hb : reflectionLegal b) : reflectionLegal (a ++ b) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact ha g h
  · exact hb g h

/-- The local Bell-basis word consists of legal reflection gates. -/
theorem localCopyBellSteps_legal (n : ℕ) : reflectionLegal (localCopyBellSteps n) := by
  intro g hg
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact hadamard_unitary
  · exact localCopyData_ne_fresh n i

/-- The local AND-and-parity computation word consists of legal reflection gates. -/
theorem localCopyComputeAndParity_legal (n : ℕ) :
    reflectionLegal (localCopyComputeAndParity n) := by
  intro g hg
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hg
  rcases List.mem_append.mp hi with hi | hi
  · exact toffoliLocalSteps_legal _ _ _ (localCopyData_ne_fresh n i)
      (localCopyData_ne_and n i) (localCopyFresh_ne_and n i) g hi
  · have he : g = .inr (localCopyAndWire n i, localCopyParityWire n) :=
      List.mem_singleton.mp hi
    subst g
    exact localCopyAnd_ne_parity n i

/-- Embedding a known qubit-control step into the local copy layout gives a legal reflection
gate. -/
theorem localCopyControlStep_legal (n : ℕ) (g : KnownQubitControlStep) :
    reflectionGateLegal (localCopyControlStep n g) := by
  cases g with
  | single b p => exact knownQubitUnitary_unitary p
  | cnot => exact localCopyControl_ne_parity n

/-- The local controlled-swap word consists of legal reflection gates for every angle. -/
theorem localControlledSwapSteps_legal (n : ℕ) (θ : ℝ) :
    reflectionLegal (localControlledSwapSteps n θ) := by
  have hp : reflectionLegal (localCopyControlledPhaseSteps n θ) := by
    intro g hg
    obtain ⟨g', _, rfl⟩ := List.mem_map.mp hg
    exact localCopyControlStep_legal n g'
  have hr : reflectionLegal [.inl (localCopyControlWire n, Rz (-θ))] := by
    intro g hg
    have he := List.mem_singleton.mp hg
    subst g
    exact rz_unitary (-θ)
  exact reflectionLegal_append'
    (reflectionLegal_append'
      (reflectionLegal_append'
        (reflectionLegal_append'
          (reflectionLegal_append' (reflectionAdjoint_legal _ (localCopyBellSteps_legal n))
            (localCopyComputeAndParity_legal n)) hp)
          (reflectionAdjoint_legal _ (localCopyComputeAndParity_legal n)))
        (localCopyBellSteps_legal n)) hr

/-- Flattening lists of constant length `k` multiplies the outer list length by `k`. -/
private theorem length_flatMap_const {α β : Type*} (xs : List α) (f : α → List β)
    (k : ℕ) (h : ∀ a, (f a).length = k) : (xs.flatMap f).length = xs.length*k := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.flatMap_cons, h, ih, Nat.add_mul, Nat.add_comm]

/-- The local Bell-basis word has length `2 * n`. -/
theorem localCopyBellSteps_length (n : ℕ) : (localCopyBellSteps n).length = 2*n := by
  unfold localCopyBellSteps
  rw [length_flatMap_const _ _ 2 (fun _ => rfl)]
  simp [Nat.mul_comm]

/-- The local AND-and-parity computation word has length `16 * n`. -/
theorem localCopyComputeAndParity_length (n : ℕ) :
    (localCopyComputeAndParity n).length = 16*n := by
  unfold localCopyComputeAndParity
  rw [length_flatMap_const _ _ 16 (by intro i; simp [toffoliLocalSteps_length])]
  simp [Nat.mul_comm]

/-- The local controlled-swap word has length `36 * n + 7`. -/
theorem localControlledSwapSteps_length (n : ℕ) (θ : ℝ) :
    (localControlledSwapSteps n θ).length = 36*n+7 := by
  simp only [localControlledSwapSteps, List.length_append, reflectionAdjoint_length,
    localCopyBellSteps_length, localCopyComputeAndParity_length]
  have hp : (localCopyControlledPhaseSteps n θ).length = 6 := by
    simp [localCopyControlledPhaseSteps, knownQubitControlSteps]
  rw [hp]
  simp only [List.length_cons, List.length_nil]
  omega

/-- The local controlled-swap word and its adjoint are legal and compile to `36 * n + 7` gates.
The forward circuit is unitary, has no queries, uses gates on at most two wires, and the
adjoint word represents the conjugate transpose. -/
theorem local_controlled_swap_actual_gate_table_and_inverse :
    ∀ (n : ℕ) (θ : ℝ), let gs := localControlledSwapSteps n θ
      reflectionLegal gs ∧ IsUnitaryCircuit (reflectionCompile gs) ∧
      gs.length = 36*n+7 ∧ QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = 36*n+7 ∧
      (∀ g ∈ gs, (reflectionGateWires g).card ≤ 2) ∧
      reflectionLegal (reflectionAdjoint gs) ∧
      GateCount (reflectionCompile (reflectionAdjoint gs)) = 36*n+7 ∧
      reflectionProgramMatrix (reflectionAdjoint gs) = (reflectionProgramMatrix gs)ᴴ := by
  intro n θ
  (try dsimp only)
  have hl := localControlledSwapSteps_legal n θ
  have hc := local_reflection_gate_support_unitarity_counts _ _ hl
  have hlen := localControlledSwapSteps_length n θ
  refine ⟨hl, hc.1, hlen, hc.2.1, hc.2.2.trans hlen, ?_,
    reflectionAdjoint_legal _ hl, ?_, reflectionAdjoint_matrix _ hl⟩
  · intro g _
    rcases g with ⟨w,U⟩ | ⟨c,t⟩
    · simp [reflectionGateWires]
    · exact le_trans (Finset.card_insert_le _ _) (by simp)
  · rw [gateCount_reflectionCompile, reflectionAdjoint_length, hlen]

/-- Splits the local copy register into the control and auxiliary bits together with the family
of data-copy bit pairs. -/
def localCopyPairSplit (n : ℕ) : Reg (3*n+2) ≃
    (Bool × (Reg n × Bool)) × (Fin n → Bool × Bool) where
  toFun x := ((x (localCopyControlWire n),
    (fun i => x (localCopyAndWire n i), x (localCopyParityWire n))),
    fun i => (x (localCopyDataWire n i), x (localCopyFreshWire n i)))
  invFun p := (localCopySplit n).symm
    ((p.1.1, (bitVecEquiv n (fun i => (p.2 i).1),
      bitVecEquiv n (fun i => (p.2 i).2))), p.1.2)
  left_inv x := by
    apply (localCopySplit n).injective
    simp only [Equiv.apply_symm_apply]
    rfl
  right_inv p := by
    rcases p with ⟨⟨b, a, q⟩, f⟩
    let x := (localCopySplit n).symm
      ((b, (bitVecEquiv n (fun i => (f i).1), bitVecEquiv n (fun i => (f i).2))), (a,q))
    have h := (localCopySplit n).apply_symm_apply
      ((b, (bitVecEquiv n (fun i => (f i).1),
        bitVecEquiv n (fun i => (f i).2))), (a,q))
    change ((x (localCopyControlWire n),
      (bitVecEquiv n (fun i => x (localCopyDataWire n i)),
       bitVecEquiv n (fun i => x (localCopyFreshWire n i)))),
      (fun i => x (localCopyAndWire n i), x (localCopyParityWire n))) = _ at h
    have hb := congrArg (fun p => p.1.1) h
    have ha := congrArg (fun p => p.2.1) h
    have hq := congrArg (fun p => p.2.2) h
    have hd := congrArg (fun p => (bitVecEquiv n).symm p.1.2.1) h
    have hf := congrArg (fun p => (bitVecEquiv n).symm p.1.2.2) h
    (try dsimp only at hb ha hq)
    simp only [Equiv.symm_apply_apply] at hd hf
    change ((x (localCopyControlWire n),
      (fun i => x (localCopyAndWire n i), x (localCopyParityWire n))),
      fun i => (x (localCopyDataWire n i), x (localCopyFreshWire n i))) = ((b, (a,q)), f)
    rw [hb, ha, hq]
    congr 1
    funext i
    exact Prod.ext (congrFun hd i) (congrFun hf i)

/-- The matrix tensor product of a family of two-bit operators, indexed by data-copy pair
configurations. -/
noncomputable def localCopyPairProduct (n : ℕ)
    (A : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix (Fin n → Bool × Bool) (Fin n → Bool × Bool) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

/-- Multiplication of pair-product matrices is componentwise multiplication of the pair
operators. -/
theorem localCopyPairProduct_mul (n : ℕ)
    (A B : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    localCopyPairProduct n A * localCopyPairProduct n B =
      localCopyPairProduct n (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, localCopyPairProduct]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => A i (x i) b * B i b (y i))).symm

/-- The pair product of identity matrices is the identity matrix. -/
theorem localCopyPairProduct_one (n : ℕ) :
    localCopyPairProduct n (fun _ => 1) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [localCopyPairProduct]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

/-- Taking the conjugate transpose of a pair product takes the conjugate transpose of each pair
operator. -/
theorem localCopyPairProduct_adjoint (n : ℕ)
    (A : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    (localCopyPairProduct n A)ᴴ = localCopyPairProduct n (fun i => (A i)ᴴ) := by
  ext x y
  simp [localCopyPairProduct, Matrix.conjTranspose_apply]

/-- Lifts a family of data-copy pair operators to the full local register, acting identically on
the other wires. -/
noncomputable def localCopyPairLift (n : ℕ)
    (A : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ :=
  relabelGate (localCopyPairSplit n).symm
    (TensorGate (1 : Matrix (Bool × (Reg n × Bool)) (Bool × (Reg n × Bool)) ℂ)
      (localCopyPairProduct n A))

/-- Multiplication of lifted pair operators is componentwise multiplication before lifting. -/
theorem localCopyPairLift_mul (n : ℕ)
    (A B : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    localCopyPairLift n A * localCopyPairLift n B =
      localCopyPairLift n (fun i => A i * B i) := by
  simp only [localCopyPairLift, relabelGate, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  rw [show TensorGate (1 : Matrix (Bool × (Reg n × Bool)) (Bool × (Reg n × Bool)) ℂ)
      (localCopyPairProduct n A) * TensorGate 1 (localCopyPairProduct n B) =
      TensorGate (1*1) (localCopyPairProduct n A * localCopyPairProduct n B) from
        (Matrix.mul_kronecker_mul _ _ _ _).symm]
  rw [one_mul, localCopyPairProduct_mul]

/-- The two-bit Bell-basis matrix formed by a Hadamard on the first bit followed by CNOT. -/
noncomputable def localCopyBellPairMatrix : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  CNOT * TensorGate Hadamard 1

/-- Conjugating two-bit swap by the Bell-basis matrix gives the diagonal sign that is negative
exactly on `(true, true)`. -/
theorem localCopyBellPair_swap_parity :
    localCopyBellPairMatrixᴴ * permMatrix Prod.swap * localCopyBellPairMatrix =
      Matrix.diagonal (fun p : Bool × Bool => if p.1 && p.2 then (-1 : ℂ) else 1) := by
  let D := Matrix.diagonal (fun p : Bool × Bool => if p.1 && p.2 then (-1 : ℂ) else 1)
  have he : permMatrix Prod.swap * localCopyBellPairMatrix = localCopyBellPairMatrix * D := by
    ext ⟨x,y⟩ ⟨a,b⟩
    cases x <;> cases y <;> cases a <;> cases b <;>
      simp [localCopyBellPairMatrix, D, Matrix.mul_apply, Fintype.sum_prod_type,
        permMatrix, CNOT, cnotFlip, tensorGate_apply, Hadamard,
        Matrix.one_apply, Matrix.diagonal_apply]
  have hu : localCopyBellPairMatrix ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
    (Matrix.unitaryGroup (Bool × Bool) ℂ).mul_mem cnot_unitary
      (tensorGate_unitary hadamard_unitary (Submonoid.one_mem _))
  have hi : localCopyBellPairMatrixᴴ * localCopyBellPairMatrix = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hu
  rw [mul_assoc, he, ← mul_assoc, hi, one_mul]

/-- Taking the conjugate transpose commutes with lifting pair operators. -/
theorem localCopyPairLift_adjoint (n : ℕ)
    (A : Fin n → Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    (localCopyPairLift n A)ᴴ = localCopyPairLift n (fun i => (A i)ᴴ) := by
  simp only [localCopyPairLift, relabelGate, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, TensorGate, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, localCopyPairProduct_adjoint]

/-- The pair product of diagonal matrices is diagonal, with entries given by the product of the
corresponding pair entries. -/
theorem localCopyPairProduct_diagonal (n : ℕ) (a : Fin n → Bool × Bool → ℂ) :
    localCopyPairProduct n (fun i => Matrix.diagonal (a i)) =
      Matrix.diagonal (fun x => ∏ i, a i (x i)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [localCopyPairProduct]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

/-- Bell-basis conjugation of the lifted pair swaps gives the lifted pairwise parity-sign
operators. -/
theorem localCopyPairLift_bell_swap (n : ℕ) :
    (localCopyPairLift n (fun _ => localCopyBellPairMatrix))ᴴ *
      localCopyPairLift n (fun _ => permMatrix Prod.swap) *
      localCopyPairLift n (fun _ => localCopyBellPairMatrix) =
    localCopyPairLift n (fun _ => Matrix.diagonal
      (fun p : Bool × Bool => if p.1 && p.2 then (-1 : ℂ) else 1)) := by
  rw [localCopyPairLift_adjoint, localCopyPairLift_mul, localCopyPairLift_mul]
  simp only [localCopyBellPair_swap_parity]

/-- Expresses `localCopyPairSplit` using the existing local register splitting and bit-vector
coordinates. -/
private theorem localCopyPairSplit_via_split (n : ℕ) (x : Reg (3*n+2)) :
    localCopyPairSplit n x =
      let p := localCopySplit n x
      ((p.1.1, p.2), fun i => ((bitVecEquiv n).symm p.1.2.1 i,
        (bitVecEquiv n).symm p.1.2.2 i)) := by
  simp [localCopyPairSplit, localCopySplit]

/-- Under the pair splitting, register swap exchanges the two bits of every pair and preserves
the remaining coordinates. -/
theorem localCopyPairSplit_swap (n : ℕ) (x : Reg (3*n+2)) :
    localCopyPairSplit n (localCopySwapBasis n x) =
      ((localCopyPairSplit n x).1, fun i => Prod.swap ((localCopyPairSplit n x).2 i)) := by
  rw [localCopyPairSplit_via_split, localCopySwapBasis]
  simp only [Equiv.apply_symm_apply]
  rw [localCopyPairSplit_via_split]
  rfl

/-- The full data-copy register swap is the lift of a swap on each bit pair. -/
theorem localCopyRegisterSwap_eq_pairLift (n : ℕ) :
    localCopyRegisterSwap n = localCopyPairLift n (fun _ => permMatrix Prod.swap) := by
  ext x y
  have he : x = localCopySwapBasis n y ↔
      (localCopyPairSplit n x).1 = (localCopyPairSplit n y).1 ∧
      ∀ i, (localCopyPairSplit n x).2 i = Prod.swap ((localCopyPairSplit n y).2 i) := by
    rw [← (localCopyPairSplit n).injective.eq_iff, localCopyPairSplit_swap]
    exact Prod.ext_iff.trans (and_congr_right fun _ => funext_iff)
  simp only [localCopyRegisterSwap, permMatrix, Matrix.of_apply, localCopyPairLift,
    relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    TensorGate, Matrix.kroneckerMap_apply, Matrix.one_apply, localCopyPairProduct,
    Matrix.of_apply]
  by_cases hx : x = localCopySwapBasis n y
  · obtain ⟨hs, hp⟩ := he.mp hx
    rw [if_pos hx, if_pos hs]
    simp only [hp, if_true, Finset.prod_const_one, mul_one]
  · rw [if_neg hx]
    by_cases hs : (localCopyPairSplit n x).1 = (localCopyPairSplit n y).1
    · rw [if_pos hs, one_mul]
      obtain ⟨i, hi⟩ : ∃ i, (localCopyPairSplit n x).2 i ≠
          Prod.swap ((localCopyPairSplit n y).2 i) := by
        by_contra h
        push Not at h
        exact hx (he.mpr ⟨hs,h⟩)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm
    · rw [if_neg hs, zero_mul]

/-- Every wire in the local copy layout is a control, data, fresh-copy, auxiliary AND, or parity
wire. -/
private theorem localCopyWire_cases (n : ℕ) (k : Fin (3*n+2)) :
    k = localCopyControlWire n ∨ (∃ i, k = localCopyDataWire n i) ∨
    (∃ i, k = localCopyFreshWire n i) ∨ (∃ i, k = localCopyAndWire n i) ∨
    k = localCopyParityWire n := by
  by_cases h0 : k.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases hd : k.val < 1+n
    · exact Or.inr (Or.inl ⟨⟨k.val-1, by omega⟩, Fin.ext (by dsimp [localCopyDataWire]; omega)⟩)
    · by_cases hf : k.val < 1+2*n
      · exact Or.inr (Or.inr (Or.inl ⟨⟨k.val-(1+n), by omega⟩,
          Fin.ext (by dsimp [localCopyFreshWire]; omega)⟩))
      · by_cases ha : k.val < 1+3*n
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨k.val-(1+2*n), by omega⟩,
            Fin.ext (by dsimp [localCopyAndWire]; omega)⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Fin.ext (by dsimp [localCopyParityWire]; omega)))))

/-- Agreement outside one data-copy pair is equivalent to agreement on all other split-register
coordinates. -/
private theorem localCopyPairSupport (n : ℕ) (i : Fin n) (x y : Reg (3*n+2)) :
    (∀ k, k ≠ localCopyDataWire n i → k ≠ localCopyFreshWire n i → x k = y k) ↔
      (localCopyPairSplit n x).1 = (localCopyPairSplit n y).1 ∧
      ∀ j, j ≠ i → (localCopyPairSplit n x).2 j = (localCopyPairSplit n y).2 j := by
  constructor
  · intro h
    constructor
    · apply Prod.ext
      · exact h _ (by
            intro he
            have hv := congrArg Fin.val he
            dsimp [localCopyControlWire,
            localCopyDataWire] at hv
            omega)
          (by
            intro he
            have hv := congrArg Fin.val he
            dsimp [localCopyControlWire,
            localCopyFreshWire] at hv
            omega)
      · apply Prod.ext
        · funext j
          exact h _ (by
            intro he
            have hv := congrArg Fin.val he
            dsimp [localCopyAndWire,
                localCopyDataWire] at hv
            omega)
            (by
            intro he
            have hv := congrArg Fin.val he
            dsimp [localCopyAndWire,
                localCopyFreshWire] at hv
            omega)
        · exact h _ (by
            intro he
            have hv := congrArg Fin.val he
            dsimp [localCopyParityWire,
              localCopyDataWire] at hv
            omega)
            (by
            intro he
            have hv := congrArg Fin.val he
            dsimp [localCopyParityWire,
              localCopyFreshWire] at hv
            omega)
    · intro j hj
      have hjv : j.val ≠ i.val := fun he => hj (Fin.ext he)
      apply Prod.ext
      · exact h _ (by
          intro he
          apply hjv
          have hv := congrArg Fin.val he
          dsimp [localCopyDataWire] at hv
          omega)
          (by
            intro he
            have hv := congrArg Fin.val he
            dsimp [localCopyDataWire, localCopyFreshWire] at hv
            omega)
      · exact h _ (by
            intro he
            have hv := congrArg Fin.val he
            dsimp [localCopyDataWire, localCopyFreshWire] at hv
            omega)
          (by
            intro he
            apply hjv
            have hv := congrArg Fin.val he
            dsimp [localCopyFreshWire] at hv
            omega)
  · rintro ⟨hs,hp⟩ k hkd hkf
    rcases localCopyWire_cases n k with rfl | ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩ | rfl
    · exact congrArg (fun p => p.1) hs
    · have hj : j ≠ i := fun he => hkd (congrArg (localCopyDataWire n) he)
      exact congrArg Prod.fst (hp j hj)
    · have hj : j ≠ i := fun he => hkf (congrArg (localCopyFreshWire n) he)
      exact congrArg Prod.snd (hp j hj)
    · exact congrFun (congrArg (fun p => p.2.1) hs) j
    · exact congrArg (fun p => p.2.2) hs

/-- Gives the entries of a single-pair lift: the chosen pair contributes `U` when all other
wires agree, and the entry is zero otherwise. -/
theorem localCopyPairLift_single_apply (n : ℕ) (i : Fin n)
    (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) (x y : Reg (3*n+2)) :
    localCopyPairLift n (fun j => if j = i then U else 1) x y =
      if ∀ k, k ≠ localCopyDataWire n i → k ≠ localCopyFreshWire n i → x k = y k
      then U (x (localCopyDataWire n i), x (localCopyFreshWire n i))
        (y (localCopyDataWire n i), y (localCopyFreshWire n i)) else 0 := by
  simp only [localCopyPairLift, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, TensorGate, Matrix.kroneckerMap_apply, localCopyPairProduct]
  by_cases h : ∀ k, k ≠ localCopyDataWire n i → k ≠ localCopyFreshWire n i → x k = y k
  · obtain ⟨hs,hp⟩ := (localCopyPairSupport n i x y).mp h
    rw [if_pos h, Matrix.one_apply, if_pos hs, one_mul, Finset.prod_eq_single i]
    · simp [localCopyPairSplit]
    · intro j _ hj
      rw [if_neg hj, Matrix.one_apply, if_pos (hp j hj)]
    · simp
  · rw [if_neg h]
    by_cases hs : (localCopyPairSplit n x).1 = (localCopyPairSplit n y).1
    · rw [Matrix.one_apply, if_pos hs, one_mul]
      obtain ⟨j,hji,hj⟩ : ∃ j, j ≠ i ∧
          (localCopyPairSplit n x).2 j ≠ (localCopyPairSplit n y).2 j := by
        by_contra he
        push Not at he
        exact h ((localCopyPairSupport n i x y).mpr ⟨hs,he⟩)
      exact Finset.prod_eq_zero (Finset.mem_univ j)
        (by rw [if_neg hji, Matrix.one_apply_ne hj])
    · rw [Matrix.one_apply_ne hs, zero_mul]

/-- A one-qubit gate on a data wire is the pair lift of `U ⊗ 1` at that position. -/
theorem localCopyDataGate_eq_pairLift (n : ℕ) (i : Fin n) (U : Matrix Bool Bool ℂ) :
    wireGate (3*n+2) (localCopyDataWire n i) U =
      localCopyPairLift n (fun j => if j = i then TensorGate U 1 else 1) := by
  ext x y
  let P := ∀ k, k ≠ localCopyDataWire n i → k ≠ localCopyFreshWire n i → x k = y k
  have he : (∀ k, k ≠ localCopyDataWire n i → x k = y k) ↔
      P ∧ x (localCopyFreshWire n i) = y (localCopyFreshWire n i) := by
    constructor
    · intro h
      exact ⟨fun k hd _ => h k hd, h _ (Ne.symm (localCopyData_ne_fresh n i))⟩
    · rintro ⟨h,hf⟩ k hd
      by_cases hk : k = localCopyFreshWire n i
      · simpa only [hk] using! hf
      · exact h k hd hk
  rw [wireGate_apply, localCopyPairLift_single_apply]
  simp only [he, tensorGate_apply, Matrix.one_apply]
  by_cases hp : P <;> by_cases hf : x (localCopyFreshWire n i) = y (localCopyFreshWire n i) <;>
    simp_all only [P, and_true, and_false, if_true, if_false, mul_one, mul_zero, ite_self]

/-- CNOT from a data wire to its matching fresh-copy wire is the corresponding single-pair lift
of CNOT. -/
theorem localCopyCnotGate_eq_pairLift (n : ℕ) (i : Fin n) :
    cnotGate (3*n+2) (localCopyDataWire n i) (localCopyFreshWire n i) =
      localCopyPairLift n (fun j => if j = i then CNOT else 1) := by
  ext x y
  let a := localCopyDataWire n i
  let b := localCopyFreshWire n i
  have hab : a ≠ b := localCopyData_ne_fresh n i
  let P := ∀ k, k ≠ a → k ≠ b → x k = y k
  let z := Function.update y b (y b ^^ y a)
  have hz : x = z ↔ P ∧ (x a, x b) = cnotFlip (y a, y b) := by
    constructor
    · intro h
      subst x
      constructor
      · intro k _ hk
        exact Function.update_of_ne hk _ _
      · simp [z, cnotFlip, Function.update_of_ne hab]
    · rintro ⟨hp,hv⟩
      have ha := congrArg Prod.fst hv
      have hb := congrArg Prod.snd hv
      dsimp [cnotFlip] at ha hb
      funext k
      change x k = Function.update y b (y b ^^ y a) k
      by_cases hk : k = b
      · subst k
        simpa only [Function.update_self] using! hb
      · rw [Function.update_of_ne hk]
        by_cases hka : k = a
        · subst k; exact ha
        · exact hp k hka hk
  rw [localCopyPairLift_single_apply]
  change (if x = z then (1 : ℂ) else 0) =
    if P then CNOT (x a, x b) (y a, y b) else 0
  simp only [CNOT, permMatrix, Matrix.of_apply]
  by_cases hp : P <;> simp [hz, hp]

/-- Lifting identity operators on all pairs gives the identity on the full register. -/
theorem localCopyPairLift_one (n : ℕ) : localCopyPairLift n (fun _ => 1) = 1 := by
  simp only [localCopyPairLift, localCopyPairProduct_one, TensorGate,
    Matrix.one_kronecker_one, relabelGate, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

/-- The Hadamard-and-CNOT block on one pair represents the Bell-basis matrix lifted at that
pair. -/
private theorem localCopyBellBlock_matrix (n : ℕ) (i : Fin n) :
    reflectionProgramMatrix
      [.inl (localCopyDataWire n i, Hadamard),
       .inr (localCopyDataWire n i, localCopyFreshWire n i)] =
    localCopyPairLift n (fun j => if j = i then localCopyBellPairMatrix else 1) := by
  simp only [reflectionProgramMatrix, reflectionGateMatrix, one_mul,
    localCopyDataGate_eq_pairLift, localCopyCnotGate_eq_pairLift, localCopyPairLift_mul]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h, localCopyBellPairMatrix]

/-- A Bell word over a duplicate-free list of pairs lifts the Bell-basis matrix on exactly the
listed pairs. -/
private theorem localCopyBellWord_matrix (n : ℕ) (xs : List (Fin n)) (hx : xs.Nodup) :
    reflectionProgramMatrix (xs.flatMap fun i =>
      [.inl (localCopyDataWire n i, Hadamard),
       .inr (localCopyDataWire n i, localCopyFreshWire n i)]) =
    localCopyPairLift n (fun j => if j ∈ xs then localCopyBellPairMatrix else 1) := by
  induction xs with
  | nil => simp [reflectionProgramMatrix, localCopyPairLift_one]
  | cons i xs ih =>
    have hi : i ∉ xs := (List.nodup_cons.mp hx).1
    have hn := (List.nodup_cons.mp hx).2
    rw [List.flatMap_cons, reflectionProgramMatrix_append, ih hn,
      localCopyBellBlock_matrix, localCopyPairLift_mul]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [hji]

/-- The full local Bell word represents the lift of a Bell-basis matrix on every data-copy pair. -/
theorem localCopyBellSteps_eq_pairLift (n : ℕ) :
    reflectionProgramMatrix (localCopyBellSteps n) =
      localCopyPairLift n (fun _ => localCopyBellPairMatrix) := by
  rw [localCopyBellSteps, localCopyBellWord_matrix n _ (List.nodup_finRange n)]
  simp

/-- A lift of diagonal pair operators is diagonal, with entries the product of the pair entries
in split coordinates. -/
private theorem localCopyPairLift_diagonal (n : ℕ) (a : Fin n → Bool × Bool → ℂ) :
    localCopyPairLift n (fun i => Matrix.diagonal (a i)) =
      Matrix.diagonal (fun x => ∏ i, a i ((localCopyPairSplit n x).2 i)) := by
  ext x y
  simp only [localCopyPairLift, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, localCopyPairProduct_diagonal, TensorGate,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst y
    simp
  · have he : localCopyPairSplit n x ≠ localCopyPairSplit n y :=
      fun hh => h ((localCopyPairSplit n).injective hh)
    have hp : ¬ ((localCopyPairSplit n x).1 = (localCopyPairSplit n y).1 ∧
        (localCopyPairSplit n x).2 = (localCopyPairSplit n y).2) :=
      fun hh => he (Prod.ext hh.1 hh.2)
    rw [if_neg h]
    by_cases hs : (localCopyPairSplit n x).1 = (localCopyPairSplit n y).1
    · have hd : (localCopyPairSplit n x).2 ≠ (localCopyPairSplit n y).2 :=
        fun hh => hp ⟨hs,hh⟩
      rw [if_pos hs, if_neg hd, mul_zero]
    · rw [if_neg hs, zero_mul]

/-- Conjugating register swap by the local Bell word gives the diagonal sign `(-1)` raised to
the number of pairs whose two bits are true. -/
theorem local_bell_basis_register_swap_parity :
    ∀ n : ℕ, let B := reflectionProgramMatrix (localCopyBellSteps n)
      Bᴴ * localCopyRegisterSwap n * B = Matrix.diagonal
        (fun x : Reg (3*n+2) => (-1 : ℂ) ^
          (∑ i : Fin n, if x (localCopyDataWire n i) && x (localCopyFreshWire n i)
            then (1 : ℕ) else 0)) := by
  intro n
  (try dsimp only)
  rw [localCopyBellSteps_eq_pairLift, localCopyRegisterSwap_eq_pairLift,
    localCopyPairLift_bell_swap, localCopyPairLift_diagonal]
  congr 1
  funext x
  have hp : ∀ i : Fin n,
      (if ((localCopyPairSplit n x).2 i).1 && ((localCopyPairSplit n x).2 i).2
        then (-1 : ℂ) else 1) =
      (-1 : ℂ) ^ (if x (localCopyDataWire n i) && x (localCopyFreshWire n i)
        then (1 : ℕ) else 0) := by
    intro i
    dsimp [localCopyPairSplit]
    split_ifs <;> simp
  simp only [hp]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- Updates one auxiliary AND bit by the conjunction of its data-copy pair, then XORs the
updated auxiliary bit into the parity wire. -/
def localCopyComputeBasisStep (n : ℕ) (i : Fin n) (x : Reg (3*n+2)) : Reg (3*n+2) :=
  let a := localCopyAndWire n i
  let p := localCopyParityWire n
  let y := Function.update x a
    (x a ^^ (x (localCopyDataWire n i) && x (localCopyFreshWire n i)))
  Function.update y p (y p ^^ y a)

/-- The local Toffoli-and-CNOT block acts on a basis ket by `localCopyComputeBasisStep`. -/
theorem localCopyComputeBlock_basis (n : ℕ) (i : Fin n) (x : Reg (3*n+2)) :
    ApplyGate (reflectionProgramMatrix
      (toffoliLocalSteps (localCopyDataWire n i) (localCopyFreshWire n i)
        (localCopyAndWire n i) ++ [.inr (localCopyAndWire n i, localCopyParityWire n)]))
      (Ket x) = Ket (localCopyComputeBasisStep n i x) := by
  have ht := (local_toffoli_fifteen_exact (3*n+2)
    (localCopyDataWire n i) (localCopyFreshWire n i) (localCopyAndWire n i)
    (localCopyData_ne_fresh n i) (localCopyData_ne_and n i) (localCopyFresh_ne_and n i)).2.2 x
  rw [run_reflectionCompile] at ht
  rw [reflectionProgramMatrix_append, applyGate_mul, ht]
  simp only [reflectionProgramMatrix, reflectionGateMatrix, one_mul]
  exact applyGate_cnotGate_ket _ _ _ (localCopyAnd_ne_parity n i) _

/-- The computation word over a list of pairs acts on basis kets by folding
`localCopyComputeBasisStep` over that list. -/
private theorem localCopyComputeWord_basis (n : ℕ) (xs : List (Fin n))
    (x : Reg (3*n+2)) :
    ApplyGate (reflectionProgramMatrix (xs.flatMap fun i =>
      toffoliLocalSteps (localCopyDataWire n i) (localCopyFreshWire n i)
        (localCopyAndWire n i) ++ [.inr (localCopyAndWire n i, localCopyParityWire n)]))
      (Ket x) = Ket (xs.foldl (fun y i => localCopyComputeBasisStep n i y) x) := by
  induction xs generalizing x with
  | nil => simp [reflectionProgramMatrix]
  | cons i xs ih =>
    rw [List.flatMap_cons, reflectionProgramMatrix_append, applyGate_mul,
      localCopyComputeBlock_basis, List.foldl_cons, ih]

/-- The full AND-and-parity word acts on basis kets by folding the basis update over all pair
indices. -/
theorem localCopyComputeAndParity_basis (n : ℕ) (x : Reg (3*n+2)) :
    ApplyGate (reflectionProgramMatrix (localCopyComputeAndParity n)) (Ket x) =
      Ket ((List.finRange n).foldl (fun y i => localCopyComputeBasisStep n i y) x) :=
  localCopyComputeWord_basis n (List.finRange n) x

/-- Splits the local register into the control-parity pair and the remaining data, fresh-copy,
and auxiliary registers. -/
def localCopyPhaseSplit (n : ℕ) : Reg (3*n+2) ≃
    (Bool × Bool) × ((Fin (2^n) × Fin (2^n)) × Reg n) :=
  (localCopySplit n).trans {
    toFun := fun p => ((p.1.1,p.2.2),(p.1.2,p.2.1))
    invFun := fun p => ((p.1.1,p.2.1),(p.2.2,p.1.2))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Lifts a two-bit operator on the control and parity wires to the full local register. -/
noncomputable def localCopyPhaseLift (n : ℕ)
    (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ :=
  relabelGate (localCopyPhaseSplit n).symm (TensorGate U 1)

/-- Two register configurations agree outside the control and parity wires exactly when their
remaining phase-split coordinates agree. -/
private theorem localCopyPhaseSupport (n : ℕ) (x y : Reg (3*n+2)) :
    (∀ k, k ≠ localCopyControlWire n → k ≠ localCopyParityWire n → x k = y k) ↔
      (localCopyPhaseSplit n x).2 = (localCopyPhaseSplit n y).2 := by
  constructor
  · intro h
    apply Prod.ext
    · apply Prod.ext <;> apply congrArg (bitVecEquiv n) <;> funext i
      · exact h _ (by intro he; have hv := congrArg Fin.val he; dsimp [localCopyDataWire,localCopyControlWire] at hv; omega)
          (by intro he; have hv := congrArg Fin.val he; dsimp [localCopyDataWire,localCopyParityWire] at hv; omega)
      · exact h _ (by intro he; have hv := congrArg Fin.val he; dsimp [localCopyFreshWire,localCopyControlWire] at hv; omega)
          (by intro he; have hv := congrArg Fin.val he; dsimp [localCopyFreshWire,localCopyParityWire] at hv; omega)
    · funext i
      exact h _ (by intro he; have hv := congrArg Fin.val he; dsimp [localCopyAndWire,localCopyControlWire] at hv; omega)
          (localCopyAnd_ne_parity n i)
  · intro h k hc hp
    rcases localCopyWire_cases n k with rfl | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | rfl
    · exact False.elim (hc rfl)
    · have hd := congrArg (fun p => p.1.1) h
      exact congrFun ((bitVecEquiv n).injective hd) i
    · have hf := congrArg (fun p => p.1.2) h
      exact congrFun ((bitVecEquiv n).injective hf) i
    · exact congrFun (congrArg Prod.snd h) i
    · exact False.elim (hp rfl)

/-- Gives the entries of a phase lift as the control-parity matrix entry when all other wires
agree, and zero otherwise. -/
theorem localCopyPhaseLift_apply (n : ℕ)
    (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) (x y : Reg (3*n+2)) :
    localCopyPhaseLift n U x y =
      if ∀ k, k ≠ localCopyControlWire n → k ≠ localCopyParityWire n → x k = y k
      then U (x (localCopyControlWire n),x (localCopyParityWire n))
        (y (localCopyControlWire n),y (localCopyParityWire n)) else 0 := by
  simp only [localCopyPhaseLift, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, TensorGate, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [← localCopyPhaseSupport]
  split_ifs <;> simp [localCopyPhaseSplit,localCopySplit]

/-- The phase lift preserves matrix multiplication. -/
theorem localCopyPhaseLift_mul (n : ℕ)
    (U V : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    localCopyPhaseLift n U * localCopyPhaseLift n V = localCopyPhaseLift n (U*V) := by
  simp only [localCopyPhaseLift, relabelGate, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, tensorGate_mul, Matrix.one_mul]

/-- The phase lift of the two-bit identity is the full-register identity. -/
theorem localCopyPhaseLift_one (n : ℕ) : localCopyPhaseLift n 1 = 1 := by
  simp only [localCopyPhaseLift, tensorGate_one, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

/-- A one-qubit gate on either the control or parity wire is the phase lift of the corresponding
tensor factor. -/
theorem localCopyPhaseWireGate (n : ℕ) (b : Bool) (U : Matrix Bool Bool ℂ) :
    wireGate (3*n+2) (if b then localCopyControlWire n else localCopyParityWire n) U =
      localCopyPhaseLift n (if b then TensorGate U 1 else TensorGate 1 U) := by
  cases b
  · ext x y
    let P := ∀ k, k ≠ localCopyControlWire n → k ≠ localCopyParityWire n → x k = y k
    have he : (∀ k, k ≠ localCopyParityWire n → x k = y k) ↔
        P ∧ x (localCopyControlWire n) = y (localCopyControlWire n) := by
      constructor
      · intro h
        exact ⟨fun k _ hp => h k hp, h _ (localCopyControl_ne_parity n)⟩
      · rintro ⟨h,hc⟩ k hp
        by_cases hk : k = localCopyControlWire n
        · simpa only [hk] using! hc
        · exact h k hk hp
    simp only [Bool.false_eq_true, if_false, wireGate_apply, localCopyPhaseLift_apply,
      he, tensorGate_apply, Matrix.one_apply]
    by_cases hp : P <;> by_cases hc : x (localCopyControlWire n) = y (localCopyControlWire n) <;>
      simp_all only [P, and_true, and_false, if_true, if_false, one_mul, zero_mul, ite_self]
  · ext x y
    let P := ∀ k, k ≠ localCopyControlWire n → k ≠ localCopyParityWire n → x k = y k
    have he : (∀ k, k ≠ localCopyControlWire n → x k = y k) ↔
        P ∧ x (localCopyParityWire n) = y (localCopyParityWire n) := by
      constructor
      · intro h
        exact ⟨fun k hc _ => h k hc, h _ (Ne.symm (localCopyControl_ne_parity n))⟩
      · rintro ⟨h,hp⟩ k hc
        by_cases hk : k = localCopyParityWire n
        · simpa only [hk] using! hp
        · exact h k hc hk
    simp only [if_true, wireGate_apply, localCopyPhaseLift_apply,
      he, tensorGate_apply, Matrix.one_apply]
    by_cases hp : P <;> by_cases ht : x (localCopyParityWire n) = y (localCopyParityWire n) <;>
      simp_all only [P, and_true, and_false, if_true, if_false, mul_one, mul_zero, ite_self]

/-- CNOT from the control wire to the parity wire is the phase lift of CNOT. -/
theorem localCopyPhaseCnotGate (n : ℕ) :
    cnotGate (3*n+2) (localCopyControlWire n) (localCopyParityWire n) =
      localCopyPhaseLift n CNOT := by
  ext x y
  let a := localCopyControlWire n
  let b := localCopyParityWire n
  have hab : a ≠ b := localCopyControl_ne_parity n
  let P := ∀ k, k ≠ a → k ≠ b → x k = y k
  let z := Function.update y b (y b ^^ y a)
  have hz : x = z ↔ P ∧ (x a, x b) = cnotFlip (y a, y b) := by
    constructor
    · intro h
      subst x
      constructor
      · intro k _ hk
        exact Function.update_of_ne hk _ _
      · simp [z, cnotFlip, Function.update_of_ne hab]
    · rintro ⟨hp,hv⟩
      have ha := congrArg Prod.fst hv
      have hb := congrArg Prod.snd hv
      dsimp [cnotFlip] at ha hb
      funext k
      change x k = Function.update y b (y b ^^ y a) k
      by_cases hk : k = b
      · subst k
        simpa only [Function.update_self] using! hb
      · rw [Function.update_of_ne hk]
        by_cases hka : k = a
        · subst k; exact ha
        · exact hp k hka hk
  rw [localCopyPhaseLift_apply]
  change (if x = z then (1 : ℂ) else 0) =
    if P then CNOT (x a, x b) (y a, y b) else 0
  simp only [CNOT, permMatrix, Matrix.of_apply]
  by_cases hp : P <;> simp [hz, hp]

/-- The embedded local control step represents the phase lift of its two-bit control-step
matrix. -/
theorem localCopyControlStep_matrix (n : ℕ) (g : KnownQubitControlStep) :
    reflectionGateMatrix (localCopyControlStep n g) =
      localCopyPhaseLift n (knownControlStepMatrix g) := by
  cases g with
  | single b p =>
    cases b
    · exact localCopyPhaseWireGate n false (knownQubitUnitary p)
    · exact localCopyPhaseWireGate n true (knownQubitUnitary p)
  | cnot => exact localCopyPhaseCnotGate n

/-- A word of embedded control steps represents the phase lift of the corresponding two-bit
program matrix. -/
theorem localCopyControlWord_matrix (n : ℕ) (gs : List KnownQubitControlStep) :
    reflectionProgramMatrix (gs.map (localCopyControlStep n)) =
      localCopyPhaseLift n (knownControlProgramMatrix gs) := by
  induction gs with
  | nil => simp [reflectionProgramMatrix, localCopyPhaseLift_one]
  | cons g gs ih =>
    simp only [List.map_cons, reflectionProgramMatrix, ih, localCopyControlStep_matrix,
      localCopyPhaseLift_mul, knownControlProgramMatrix_cons]

/-- The local controlled-phase word represents the phase lift of `ControlledGate (Rz (2 * θ))`. -/
theorem localCopyControlledPhaseSteps_matrix (n : ℕ) (θ : ℝ) :
    reflectionProgramMatrix (localCopyControlledPhaseSteps n θ) =
      localCopyPhaseLift n (ControlledGate (Rz (2*θ))) := by
  rw [localCopyControlledPhaseSteps, localCopyControlWord_matrix, knownControlProgramMatrix_steps,
    (knownQubitEuler_explicit_angles_cover_unitaries (Rz (2*θ)) (rz_unitary (2*θ))).1]

/-- The phase lift of a diagonal matrix is diagonal, evaluated on the control and parity bits. -/
theorem localCopyPhaseLift_diagonal (n : ℕ) (a : Bool × Bool → ℂ) :
    localCopyPhaseLift n (Matrix.diagonal a) = Matrix.diagonal
      (fun x => a (x (localCopyControlWire n),x (localCopyParityWire n))) := by
  ext x y
  simp only [localCopyPhaseLift, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, TensorGate, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.diagonal_apply]
  by_cases h : x = y
  · subst y
    simp [localCopyPhaseSplit,localCopySplit]
  · have he : localCopyPhaseSplit n x ≠ localCopyPhaseSplit n y :=
      fun hh => h ((localCopyPhaseSplit n).injective hh)
    have hp : ¬ ((localCopyPhaseSplit n x).1 = (localCopyPhaseSplit n y).1 ∧
        (localCopyPhaseSplit n x).2 = (localCopyPhaseSplit n y).2) :=
      fun hh => he (Prod.ext hh.1 hh.2)
    rw [if_neg h]
    by_cases hc : (localCopyPhaseSplit n x).1 = (localCopyPhaseSplit n y).1
    · have hs : (localCopyPhaseSplit n x).2 ≠ (localCopyPhaseSplit n y).2 :=
        fun hh => hp ⟨hc,hh⟩
      rw [if_pos hc,if_neg hs,mul_zero]
    · rw [if_neg hc,zero_mul]

/-- The local controlled-phase word is diagonal, multiplying the true-control, true-parity
sector by `exp (2 * θ * i)`. -/
theorem localCopyControlledPhaseSteps_diagonal (n : ℕ) (θ : ℝ) :
    reflectionProgramMatrix (localCopyControlledPhaseSteps n θ) = Matrix.diagonal
      (fun x => if x (localCopyControlWire n) && x (localCopyParityWire n)
        then Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I) else 1) := by
  have he : ControlledGate (Rz (2*θ)) = Matrix.diagonal
      (fun p : Bool × Bool => if p.1 && p.2
        then Complex.exp (((2*θ : ℝ) : ℂ)*Complex.I) else 1) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [ControlledGate,BlockDiag,Rz]
  rw [localCopyControlledPhaseSteps_matrix, he, localCopyPhaseLift_diagonal]

/-- A basis computation step preserves every wire other than its auxiliary AND wire and the
parity wire. -/
private theorem localCopyComputeBasisStep_preserves (n : ℕ) (i : Fin n)
    (x : Reg (3*n+2)) (k : Fin (3*n+2))
    (ha : k ≠ localCopyAndWire n i) (hp : k ≠ localCopyParityWire n) :
    localCopyComputeBasisStep n i x k = x k := by
  simp [localCopyComputeBasisStep,Function.update_of_ne ha,Function.update_of_ne hp]

/-- A fold of basis computation steps preserves a wire distinct from every touched auxiliary AND
wire and from the parity wire. -/
theorem localCopyComputeFold_preserves (n : ℕ) (xs : List (Fin n))
    (x : Reg (3*n+2)) (k : Fin (3*n+2))
    (ha : ∀ i ∈ xs, k ≠ localCopyAndWire n i) (hp : k ≠ localCopyParityWire n) :
    xs.foldl (fun y i => localCopyComputeBasisStep n i y) x k = x k := by
  induction xs generalizing x with
  | nil => rfl
  | cons i xs ih =>
    rw [List.foldl_cons, ih _ (fun j hj => ha j (List.mem_cons_of_mem i hj))]
    exact localCopyComputeBasisStep_preserves n i x k (ha i (List.mem_cons_self)) hp

/-- Every data wire is distinct from every auxiliary AND wire. -/
private theorem localCopyData_ne_any_and (n : ℕ) (i j : Fin n) :
    localCopyDataWire n i ≠ localCopyAndWire n j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [localCopyDataWire,localCopyAndWire] at hv
  omega

/-- Every fresh-copy wire is distinct from every auxiliary AND wire. -/
private theorem localCopyFresh_ne_any_and (n : ℕ) (i j : Fin n) :
    localCopyFreshWire n i ≠ localCopyAndWire n j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [localCopyFreshWire,localCopyAndWire] at hv
  omega

/-- Every data wire is distinct from the parity wire. -/
private theorem localCopyData_ne_parity (n : ℕ) (i : Fin n) :
    localCopyDataWire n i ≠ localCopyParityWire n := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [localCopyDataWire,localCopyParityWire] at hv
  omega

/-- Every fresh-copy wire is distinct from the parity wire. -/
private theorem localCopyFresh_ne_parity (n : ℕ) (i : Fin n) :
    localCopyFreshWire n i ≠ localCopyParityWire n := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [localCopyFreshWire,localCopyParityWire] at hv
  omega

/-- The auxiliary AND wire assignment is injective. -/
private theorem localCopyAnd_injective (n : ℕ) : Function.Injective (localCopyAndWire n) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  dsimp [localCopyAndWire] at hv
  omega

/-- A basis computation step preserves the conjunction of the data and fresh-copy bits at every
position. -/
private theorem localCopyComputeBasisStep_pair (n : ℕ) (i j : Fin n)
    (x : Reg (3*n+2)) :
    (localCopyComputeBasisStep n i x (localCopyDataWire n j) &&
      localCopyComputeBasisStep n i x (localCopyFreshWire n j)) =
    (x (localCopyDataWire n j) && x (localCopyFreshWire n j)) := by
  rw [localCopyComputeBasisStep_preserves n i x _ (localCopyData_ne_any_and n j i)
      (localCopyData_ne_parity n j),
    localCopyComputeBasisStep_preserves n i x _ (localCopyFresh_ne_any_and n j i)
      (localCopyFresh_ne_parity n j)]

/-- For a duplicate-free list with initially false auxiliary AND bits, the final parity is the
initial parity XORed with each listed data-copy conjunction. -/
theorem localCopyComputeFold_parity (n : ℕ) (xs : List (Fin n))
    (hx : xs.Nodup) (x : Reg (3*n+2))
    (ha : ∀ i ∈ xs, x (localCopyAndWire n i) = false) :
    xs.foldl (fun y i => localCopyComputeBasisStep n i y) x (localCopyParityWire n) =
      xs.foldl (fun b i => b ^^ (x (localCopyDataWire n i) &&
        x (localCopyFreshWire n i))) (x (localCopyParityWire n)) := by
  induction xs generalizing x with
  | nil => rfl
  | cons i xs ih =>
    have hni := (List.nodup_cons.mp hx).1
    have hns := (List.nodup_cons.mp hx).2
    rw [List.foldl_cons, ih hns]
    · have he : localCopyComputeBasisStep n i x (localCopyParityWire n) =
          (x (localCopyParityWire n) ^^ (x (localCopyDataWire n i) &&
            x (localCopyFreshWire n i))) := by
        simp [localCopyComputeBasisStep, Function.update_of_ne (Ne.symm (localCopyAnd_ne_parity n i)),
          ha i (List.mem_cons_self)]
      simp only [List.foldl_cons, he, localCopyComputeBasisStep_pair]
    · intro j hj
      rw [localCopyComputeBasisStep_preserves n i x _
        (fun he => hni ((localCopyAnd_injective n he) ▸ hj)) (localCopyAnd_ne_parity n j)]
      exact ha j (List.mem_cons_of_mem i hj)

/-- The sign associated with the XOR of two bits is the product of their individual signs. -/
private theorem localCopyXor_sign (a b : Bool) :
    (-1 : ℂ) ^ (if a ^^ b then (1 : ℕ) else 0) =
      (-1 : ℂ) ^ (if a then (1 : ℕ) else 0) *
        (-1 : ℂ) ^ (if b then (1 : ℕ) else 0) := by
  cases a <;> cases b <;> norm_num

/-- The sign of an XOR fold factors into the initial sign and `(-1)` raised to the number of
true list entries. -/
private theorem localCopyXorFold_sign {I : Type} (xs : List I) (f : I → Bool) (b : Bool) :
    (-1 : ℂ) ^ (if xs.foldl (fun a i => a ^^ f i) b then (1 : ℕ) else 0) =
      (-1 : ℂ) ^ (if b then (1 : ℕ) else 0) *
        (-1 : ℂ) ^ ((xs.map (fun i => if f i then (1 : ℕ) else 0)).sum) := by
  induction xs generalizing b with
  | nil => simp
  | cons i xs ih =>
    rw [List.foldl_cons, ih (b ^^ f i), localCopyXor_sign]
    simp only [List.map_cons, List.sum_cons, pow_add, mul_assoc]

/-- With initially false auxiliary AND and parity wires, the computed parity sign is `(-1)`
raised to the number of true data-copy conjunctions. -/
theorem localCopyComputeAndParity_sign (n : ℕ) (x : Reg (3*n+2))
    (ha : ∀ i, x (localCopyAndWire n i) = false)
    (hp : x (localCopyParityWire n) = false) :
    (-1 : ℂ) ^ (if (List.finRange n).foldl
        (fun y i => localCopyComputeBasisStep n i y) x (localCopyParityWire n)
        then (1 : ℕ) else 0) =
      (-1 : ℂ) ^ (∑ i : Fin n, if x (localCopyDataWire n i) &&
        x (localCopyFreshWire n i) then (1 : ℕ) else 0) := by
  rw [localCopyComputeFold_parity n _ (List.nodup_finRange n) x (fun i _ => ha i),
    localCopyXorFold_sign, hp]
  simp only [Bool.false_eq_true, if_false, pow_zero, one_mul]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

/-- The full AND-and-parity basis computation preserves the control bit. -/
theorem localCopyComputeAndParity_control (n : ℕ) (x : Reg (3*n+2)) :
    (List.finRange n).foldl (fun y i => localCopyComputeBasisStep n i y) x
      (localCopyControlWire n) = x (localCopyControlWire n) := by
  apply localCopyComputeFold_preserves
  · intro i _ he
    have hv := congrArg Fin.val he
    dsimp [localCopyControlWire,localCopyAndWire] at hv
    omega
  · exact localCopyControl_ne_parity n
end Qatlib.Concepts.FreshCopyExec.QpeConsumers
