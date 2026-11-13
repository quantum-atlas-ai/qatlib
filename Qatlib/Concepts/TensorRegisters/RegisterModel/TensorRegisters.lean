/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.RegisterMeasurement
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegistersDefs
import QuantumInfo.ForMathlib.HermitianMat.Proj
import QuantumInfo.ForMathlib.HermitianMat.Rpow

/-!
# Tensor registers, padded encodings, and partial traces

This module proves algebraic identities for `productMatrix` and the correctness of padded binary
register encodings. It also establishes naturality and density preservation of
`partitionReduce`, compatibility with local operations, and bundled statements for encoding and
measurement semantics. For background, see [Watrous2018].

## Main statements

* `paddingFrame_isometry`: the binary padding frame preserves inner products.
* `paddedGate_unitary`: unitary gates extend to the padded register.
* `partitionReduce_lift`: reduction commutes with conjugation by a lifted local matrix.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
universe u v w x y

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

open Matrix
open scoped BigOperators Kronecker ComplexOrder

/-- The adjoint of a product matrix is the product matrix of the component adjoints. -/
theorem productMatrix_adjoint {ι : Type*} [Fintype ι] {S : ι → Type*} {T : ι → Type*}
    (A : ∀ i, Matrix (S i) (T i) ℂ) :
    (productMatrix A)ᴴ = productMatrix (fun i => (A i)ᴴ) := by
  ext x y
  simp [productMatrix, Matrix.conjTranspose_apply]

/-- Multiplying two compatible product matrices gives the product matrix of their componentwise
products. -/
theorem productMatrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} {T : ι → Type*} {V : ι → Type*} [∀ i, Fintype (T i)]
    (A : ∀ i, Matrix (S i) (T i) ℂ) (B : ∀ i, Matrix (T i) (V i) ℂ) :
    productMatrix A * productMatrix B = productMatrix (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, productMatrix, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i t => A i (x i) t * B i t (y i))).symm

/-- The product matrix of identity matrices is the identity on the full register. -/
theorem productMatrix_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, DecidableEq (S i)] :
    productMatrix (fun i => (1 : Matrix (S i) (S i) ℂ)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [productMatrix]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

/-- The trace of a product matrix is the product of the component traces. -/
theorem productMatrix_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (A : ∀ i, Matrix (S i) (S i) ℂ) :
    Matrix.trace (productMatrix A) = ∏ i, Matrix.trace (A i) := by
  exact (Fintype.prod_sum (fun i s => A i s s)).symm

/-- Summing a product matrix over all component outcome choices equals the product matrix of the
component sums. -/
theorem productMatrix_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} {T : ι → Type*} {O : ι → Type*} [∀ i, Fintype (O i)]
    (A : ∀ i, O i → Matrix (S i) (T i) ℂ) :
    (∑ o : ∀ i, O i, productMatrix (fun i => A i (o i))) =
      productMatrix (fun i => ∑ o, A i o) := by
  ext x y
  simp only [Matrix.sum_apply, productMatrix]
  exact (Fintype.prod_sum (fun i o => A i o (x i) (y i))).symm

/-- A product matrix of positive semidefinite component matrices is positive semidefinite. -/
theorem productMatrix_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (A : ∀ i, Matrix (S i) (S i) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (productMatrix A).PosSemidef := by
  let H (i : ι) : HermitianMat (S i) ℂ := ⟨A i,(hA i).1⟩
  let B (i : ι) : Matrix (S i) (S i) ℂ := (H i ^ (1/2 : ℝ)).mat
  have hB (i : ι) : (B i)ᴴ * B i = A i := by
    have hH : 0 ≤ H i := HermitianMat.zero_le_iff.mpr (hA i)
    dsimp only [B]
    rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul hH]
    rfl
  have hp := Matrix.posSemidef_conjTranspose_mul_self (productMatrix B)
  rw [productMatrix_adjoint, productMatrix_mul] at hp
  simpa only [hB] using hp

/-- The padded encoding `toReg d q h` is injective. -/
theorem toReg_injective {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) : Function.Injective (toReg d q h) := by
  intro x y hxy
  apply (flatten d).injective
  apply Fin.ext
  have he := congrArg (fun b => (bitVecEquiv q b).val) hxy
  simpa only [toReg, Equiv.apply_symm_apply, Fin.val_castLE] using he

/-- Decoding a padded encoding returns the original label. -/
@[simp] theorem fromReg_toReg {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (x : Labels d) :
    fromReg d q (toReg d q h x) = some x := by
  simp [fromReg, toReg, (flatten d x).isLt]

/-- A binary word whose numeric value is at least the label cardinality decodes to `none`. -/
theorem fromReg_illegal {m : ℕ} (d : Fin m → ℕ) (q : ℕ) (b : Reg q)
    (h : (∏ i, d i) ≤ (bitVecEquiv q b).val) : fromReg d q b = none := by
  simp [fromReg, not_lt.mpr h]

/-- Label configurations and width-`q` binary registers have no equivalence when their
cardinalities differ. -/
theorem no_binary_equiv_of_card_ne {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≠ 2 ^ q) : ¬ Nonempty (Labels d ≃ Reg q) := by
  rintro ⟨e⟩
  apply h
  simpa [Labels, Reg] using Fintype.card_congr e

/-- The padding frame maps a label basis vector to the basis vector of its encoded binary word. -/
theorem paddingFrame_ket {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (x : Labels d) :
    paddingFrame d q h *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket (toReg d q h x) := by
  ext b
  simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, paddingFrame]

/-- The padding frame satisfies `Vᴴ * V = 1`. -/
theorem paddingFrame_isometry {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) :
    (paddingFrame d q h)ᴴ * paddingFrame d q h = 1 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, paddingFrame]
  rw [Finset.sum_eq_single (toReg d q h x)]
  · simp [(toReg_injective d q h).eq_iff, Matrix.one_apply]
  · intro b _ hb
    simp [hb]
  · simp

/-- Applying the padding frame to two state vectors preserves their inner product. -/
theorem paddingFrame_inner {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (ψ φ : QState (Labels d)) :
    Qatlib.Foundations.PureStateMath.Inner (paddingFrame d q h *ᵥ ψ) (paddingFrame d q h *ᵥ φ) = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    paddingFrame_isometry, Matrix.vecMul_one]

/-- A padded state is normalized exactly when its original label state is normalized. -/
theorem paddingFrame_normalized {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (ψ : QState (Labels d)) :
    Normalized (paddingFrame d q h *ᵥ ψ) ↔ Normalized ψ := by
  rw [normalized_iff_inner_self, paddingFrame_inner, normalized_iff_inner_self]

/-- The amplitude of a padded state at the encoding of `x` equals its original amplitude at `x`. -/
theorem paddingFrame_valid_amplitude {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (ψ : QState (Labels d)) (x : Labels d) :
    (paddingFrame d q h *ᵥ ψ) (toReg d q h x) = ψ x := by
  simp [Matrix.mulVec, dotProduct, paddingFrame, (toReg_injective d q h).eq_iff]

/-- The amplitude of a padded state is zero at every binary word outside the valid label range. -/
theorem paddingFrame_illegal_amplitude {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (ψ : QState (Labels d)) (b : Reg q)
    (hb : (∏ i, d i) ≤ (bitVecEquiv q b).val) :
    (paddingFrame d q h *ᵥ ψ) b = 0 := by
  have hne (x : Labels d) : b ≠ toReg d q h x := by
    intro hx
    rw [hx] at hb
    simp only [toReg, Equiv.apply_symm_apply, Fin.val_castLE] at hb
    exact (Nat.not_le_of_lt (flatten d x).isLt) hb
  simp [Matrix.mulVec, dotProduct, paddingFrame, hne]

/-- Padding preserves the Born probability of each encoded label. -/
theorem paddingFrame_born {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (ψ : QState (Labels d)) (x : Labels d) :
    BornProb (paddingFrame d q h *ᵥ ψ) (toReg d q h x) = BornProb ψ x := by
  simp only [BornProb, paddingFrame_valid_amplitude]

/-- The padded gate intertwines the padding frame with the original gate. -/
theorem paddedGate_frame {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (U : Matrix (Labels d) (Labels d) ℂ) :
    paddedGate d q h U * paddingFrame d q h = paddingFrame d q h * U := by
  simp only [paddedGate, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, paddingFrame_isometry, Matrix.mul_one, sub_self, add_zero]

/-- Acting with a padded gate on an encoded state equals encoding the original gate's output. -/
theorem paddedGate_whole_state {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (U : Matrix (Labels d) (Labels d) ℂ)
    (ψ : QState (Labels d)) :
    paddedGate d q h U *ᵥ (paddingFrame d q h *ᵥ ψ) =
      paddingFrame d q h *ᵥ (U *ᵥ ψ) := by
  rw [Matrix.mulVec_mulVec, paddedGate_frame, ← Matrix.mulVec_mulVec]

/-- A padded gate fixes every basis vector outside the valid encoding range. -/
theorem paddedGate_illegal_ket {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (U : Matrix (Labels d) (Labels d) ℂ) (b : Reg q)
    (hb : (∏ i, d i) ≤ (bitVecEquiv q b).val) :
    paddedGate d q h U *ᵥ Qatlib.Foundations.PureStateMath.Ket b = Qatlib.Foundations.PureStateMath.Ket b := by
  have hne (x : Labels d) : b ≠ toReg d q h x := by
    intro hx
    rw [hx] at hb
    simp only [toReg, Equiv.apply_symm_apply, Fin.val_castLE] at hb
    exact (Nat.not_le_of_lt (flatten d x).isLt) hb
  have hv : (paddingFrame d q h)ᴴ *ᵥ Qatlib.Foundations.PureStateMath.Ket b = 0 := by
    ext x
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, paddingFrame,
      Qatlib.Foundations.PureStateMath.Ket, hne]
  simp [paddedGate, Matrix.add_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv]

/-- The padded extension of a unitary matrix is unitary on the binary register. -/
theorem paddedGate_unitary {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (U : Matrix (Labels d) (Labels d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Labels d) ℂ) :
    paddedGate d q h U ∈ Matrix.unitaryGroup (Reg q) ℂ := by
  let V := paddingFrame d q h
  have hV : Vᴴ * V = 1 := paddingFrame_isometry d q h
  have hu : Uᴴ * U = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hU
  have hv_mul (W : Matrix (Labels d) (Reg q) ℂ) : Vᴴ * (V * W) = W := by
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hu_mul (W : Matrix (Labels d) (Reg q) ℂ) : Uᴴ * (U * W) = W := by
    rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (V * U * Vᴴ + (1 - V * Vᴴ))ᴴ * (V * U * Vᴴ + (1 - V * Vᴴ)) = 1
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hv_mul, hu_mul]
  abel

/-- Changing coordinates on both parts of a partition relabels the retained matrix only by the
retained-register equivalence. -/
theorem partitionReduce_natural {S A B A' B' : Type*}
    [Fintype B] [Fintype B'] (e : S ≃ A × B) (a : A ≃ A') (b : B ≃ B')
    (X : Matrix S S ℂ) :
    partitionReduce (e.trans (Equiv.prodCongr a b)) X =
      Matrix.reindex a a (partitionReduce e X) := by
  ext i j
  change (∑ k : B', X (e.symm (a.symm i,b.symm k)) (e.symm (a.symm j,b.symm k))) =
    ∑ k : B, X (e.symm (a.symm i,k)) (e.symm (a.symm j,k))
  exact Equiv.sum_comp b.symm
    (fun k : B => X (e.symm (a.symm i,k)) (e.symm (a.symm j,k)))

/-- Reducing a positive semidefinite matrix of trace one preserves positive semidefiniteness and
unit trace. -/
theorem partitionReduce_density {S A B : Type*}
    [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : S ≃ A × B) (X : Matrix S S ℂ)
    (hX : X.PosSemidef) (htr : Matrix.trace X = 1) :
    (partitionReduce e X).PosSemidef ∧ Matrix.trace (partitionReduce e X) = 1 := by
  refine ⟨(hX.submatrix e.symm).traceRight, ?_⟩
  rw [partitionReduce, Matrix.traceRight_trace]
  simpa only [Matrix.reindex_apply, Matrix.trace_submatrix] using htr

/-- Reduction using the swapped partition is the left partial trace. -/
theorem partitionReduce_swap {A B : Type*} [Fintype A]
    (X : Matrix (A × B) (A × B) ℂ) :
    partitionReduce (Equiv.prodComm A B) X = Matrix.traceLeft X := by
  rfl

/-- Discarding the last register and then the next register equals discarding their joint
register in one reduction. -/
theorem partitionReduce_iterated {S A B C : Type*} [Fintype B] [Fintype C]
    (e : S ≃ A × (B × C)) (X : Matrix S S ℂ) :
    Matrix.traceRight (partitionReduce (e.trans (Equiv.prodAssoc A B C).symm) X) =
      partitionReduce e X := by
  ext i j
  change (∑ b : B, ∑ c : C, X (e.symm (i,(b,c))) (e.symm (j,(b,c)))) =
    ∑ bc : B × C, X (e.symm (i,bc)) (e.symm (j,bc))
  exact (Fintype.sum_prod_type
    (fun bc : B × C => X (e.symm (i,bc)) (e.symm (j,bc)))).symm

/-- Swapping the two discarded registers leaves the retained matrix unchanged. -/
theorem partitionReduce_discard_order {S A B C : Type*} [Fintype B] [Fintype C]
    (e : S ≃ A × (B × C)) (X : Matrix S S ℂ) :
    partitionReduce (e.trans (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm B C))) X =
      partitionReduce e X := by
  simpa using partitionReduce_natural e (Equiv.refl A) (Equiv.prodComm B C) X

/-- A matrix acting on the retained row register can be pulled outside the right partial trace
on the left. -/
theorem traceRight_mul_local {A A' B C : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (U : Matrix A' A ℂ) (X : Matrix (A × B) (C × B) ℂ) :
    Matrix.traceRight ((U ⊗ₖ (1 : Matrix B B ℂ)) * X) = U * Matrix.traceRight X := by
  ext i j
  simp only [Matrix.traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A matrix acting on the retained column register can be pulled outside the right partial
trace on the right. -/
theorem traceRight_local_mul {A B C C' : Type*} [Fintype C] [Fintype B] [DecidableEq B]
    (V : Matrix C C' ℂ) (X : Matrix (A × B) (C × B) ℂ) :
    Matrix.traceRight (X * (V ⊗ₖ (1 : Matrix B B ℂ))) = Matrix.traceRight X * V := by
  ext i j
  simp only [Matrix.traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The right partial trace commutes with conjugation by a matrix acting only on the retained
register. -/
theorem traceRight_local_kraus {A A' B : Type*}
    [Fintype A] [Fintype A'] [Fintype B] [DecidableEq B]
    (K : Matrix A' A ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    Matrix.traceRight ((K ⊗ₖ (1 : Matrix B B ℂ)) * X *
      (K ⊗ₖ (1 : Matrix B B ℂ))ᴴ) = K * Matrix.traceRight X * Kᴴ := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    traceRight_local_mul, traceRight_mul_local]

/-- Reducing a joint matrix conjugated by `partitionLift e U` gives the reduced matrix
conjugated by `U`. -/
theorem partitionReduce_lift {S A B : Type*}
    [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : S ≃ A × B)
    (U : Matrix A A ℂ) (X : Matrix S S ℂ) :
    partitionReduce e (partitionLift e U * X * (partitionLift e U)ᴴ) =
      U * partitionReduce e X * Uᴴ := by
  let F := Matrix.reindexAlgEquiv ℂ ℂ e
  have hmul (M N : Matrix S S ℂ) :
      Matrix.reindex e e (M*N) = Matrix.reindex e e M * Matrix.reindex e e N :=
    F.map_mul M N
  simp only [partitionReduce, hmul, partitionLift, Matrix.conjTranspose_reindex]
  have hback (M : Matrix (A × B) (A × B) ℂ) :
      Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
    ext i j
    simp
  rw [hback, hback, traceRight_local_kraus]

/-- Decoding a binary word to `some x` is equivalent to that word being the padded encoding of
`x`. -/
theorem fromReg_eq_some_iff {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (b : Reg q) (x : Labels d) :
    fromReg d q b = some x ↔ toReg d q h x = b := by
  constructor
  · intro hx
    by_cases hb : (bitVecEquiv q b).val < ∏ i, d i
    · rw [fromReg, dif_pos hb] at hx
      have hl := Option.some.inj hx
      have hv := congrArg (fun y : Labels d => (flatten d y).val) hl
      simp only [Equiv.apply_symm_apply] at hv
      apply (bitVecEquiv q).injective
      apply Fin.ext
      simpa only [toReg, Equiv.apply_symm_apply, Fin.val_castLE] using hv.symm
    · simp [fromReg, hb] at hx
  · intro hx
    rw [← hx]
    exact fromReg_toReg d q h x

/-- Decoding returns `none` exactly when the binary word's numeric value lies outside the label
range. -/
theorem fromReg_none_iff {m : ℕ} (d : Fin m → ℕ) (q : ℕ) (b : Reg q) :
    fromReg d q b = none ↔ (∏ i, d i) ≤ (bitVecEquiv q b).val := by
  by_cases hb : (bitVecEquiv q b).val < ∏ i, d i
  · simp [fromReg, hb, Nat.not_le.mpr hb]
  · simp [fromReg, hb, Nat.le_of_not_gt hb]

/-- Padding preserves the measurement probability of any finite label event under its encoded
image. -/
theorem paddingFrame_measureProb {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (ψ : QState (Labels d)) (S : Finset (Labels d)) :
    MeasureProb (paddingFrame d q h *ᵥ ψ) (S.image (toReg d q h)) = MeasureProb ψ S := by
  unfold MeasureProb
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl fun x _ => paddingFrame_born d q h ψ x
  · intro a _ b _ hab
    exact toReg_injective d q h hab

/-- Label configurations are equivalent to width-`q` binary registers exactly when their
cardinalities agree. -/
theorem binary_equiv_iff_card {m : ℕ} (d : Fin m → ℕ) (q : ℕ) :
    Nonempty (Labels d ≃ Reg q) ↔ (∏ i, d i) = 2 ^ q := by
  constructor
  · rintro ⟨e⟩
    simpa [Labels, Reg] using Fintype.card_congr e
  · intro h
    exact ⟨exactRegEquiv d q h⟩

/-- When the cardinalities agree, the exact register equivalence coincides with the padded
encoding. -/
theorem exactRegEquiv_toReg {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) = 2 ^ q) (x : Labels d) :
    exactRegEquiv d q h x = toReg d q (Nat.le_of_eq h) x := by
  apply (bitVecEquiv q).injective
  apply Fin.ext
  simp [exactRegEquiv, toReg]

/-- Bundles the inverse laws for flattening, correctness and isometry of padded encodings,
preservation of measurement probabilities, gate extension, and the cardinality criterion for
exact encodings. -/
theorem part2_clause1 :
  (∀ (m : ℕ) (d : Fin m → ℕ),
    (∀ x : Labels d, (flatten d).symm (flatten d x) = x) ∧
    (∀ i : Fin (∏ j, d j), flatten d ((flatten d).symm i) = i)) ∧
  (∀ (m : ℕ) (d : Fin m → ℕ) (q : ℕ) (h : (∏ i, d i) ≤ 2 ^ q),
    Function.Injective (toReg d q h) ∧
    (∀ x : Labels d, fromReg d q (toReg d q h x) = some x) ∧
    (∀ (b : Reg q) (x : Labels d), fromReg d q b = some x ↔ toReg d q h x = b) ∧
    (∀ b : Reg q, fromReg d q b = none ↔ (∏ i, d i) ≤ (bitVecEquiv q b).val) ∧
    (paddingFrame d q h)ᴴ * paddingFrame d q h = 1 ∧
    (∀ ψ φ : QState (Labels d),
      Qatlib.Foundations.PureStateMath.Inner (paddingFrame d q h *ᵥ ψ) (paddingFrame d q h *ᵥ φ) = Qatlib.Foundations.PureStateMath.Inner ψ φ) ∧
    (∀ ψ : QState (Labels d), Normalized (paddingFrame d q h *ᵥ ψ) ↔ Normalized ψ) ∧
    (∀ (ψ : QState (Labels d)) (x : Labels d),
      BornProb (paddingFrame d q h *ᵥ ψ) (toReg d q h x) = BornProb ψ x) ∧
    (∀ (ψ : QState (Labels d)) (b : Reg q), (∏ i, d i) ≤ (bitVecEquiv q b).val →
      (paddingFrame d q h *ᵥ ψ) b = 0) ∧
    (∀ (ψ : QState (Labels d)) (S : Finset (Labels d)),
      MeasureProb (paddingFrame d q h *ᵥ ψ) (S.image (toReg d q h)) = MeasureProb ψ S) ∧
    (∀ U : Matrix (Labels d) (Labels d) ℂ,
      paddedGate d q h U * paddingFrame d q h = paddingFrame d q h * U) ∧
    (∀ (U : Matrix (Labels d) (Labels d) ℂ) (ψ : QState (Labels d)),
      paddedGate d q h U *ᵥ (paddingFrame d q h *ᵥ ψ) =
        paddingFrame d q h *ᵥ (U *ᵥ ψ)) ∧
    (∀ (U : Matrix (Labels d) (Labels d) ℂ) (b : Reg q),
      (∏ i, d i) ≤ (bitVecEquiv q b).val → paddedGate d q h U *ᵥ Qatlib.Foundations.PureStateMath.Ket b = Qatlib.Foundations.PureStateMath.Ket b) ∧
    (∀ U : Matrix (Labels d) (Labels d) ℂ,
      U ∈ Matrix.unitaryGroup (Labels d) ℂ → paddedGate d q h U ∈ Matrix.unitaryGroup (Reg q) ℂ)) ∧
  (∀ (m : ℕ) (d : Fin m → ℕ) (q : ℕ),
    Nonempty (Labels d ≃ Reg q) ↔ (∏ i, d i) = 2 ^ q) ∧
  (∀ (m : ℕ) (d : Fin m → ℕ) (q : ℕ) (h : (∏ i, d i) = 2 ^ q) (x : Labels d),
    exactRegEquiv d q h x = toReg d q (Nat.le_of_eq h) x) := by
  refine ⟨?_, ?_, (fun _ d q => binary_equiv_iff_card d q),
    (fun _ d q h x => exactRegEquiv_toReg d q h x)⟩
  · intro m d
    exact ⟨(flatten d).symm_apply_apply, (flatten d).apply_symm_apply⟩
  · intro m d q h
    exact ⟨toReg_injective d q h, fromReg_toReg d q h, fromReg_eq_some_iff d q h,
      fromReg_none_iff d q, paddingFrame_isometry d q h, paddingFrame_inner d q h,
      paddingFrame_normalized d q h, paddingFrame_born d q h,
      paddingFrame_illegal_amplitude d q h, paddingFrame_measureProb d q h,
      paddedGate_frame d q h, paddedGate_whole_state d q h,
      paddedGate_illegal_ket d q h, paddedGate_unitary d q h⟩

/-- Changing coordinates on the retained and complementary registers leaves the lifted matrix
unchanged when the local matrix is relabeled accordingly. -/
theorem partitionLift_natural {S A B A' B' : Type*} [DecidableEq B] [DecidableEq B']
    (e : S ≃ A × B) (a : A ≃ A') (b : B ≃ B') (U : Matrix A A ℂ) :
    partitionLift (e.trans (Equiv.prodCongr a b)) (Matrix.reindex a a U) = partitionLift e U := by
  ext i j
  simp [partitionLift, Matrix.reindex_apply, Matrix.one_apply, Prod.map, b.injective.eq_iff]

/-- Reindexing the full register transports a partition lift to the correspondingly transported
partition. -/
theorem partitionLift_reindex {S S' A B : Type*} [DecidableEq B]
    (e : S ≃ A × B) (s : S ≃ S') (U : Matrix A A ℂ) :
    Matrix.reindex s s (partitionLift e U) = partitionLift (s.symm.trans e) U := by
  rfl

/-- Applying a complex linear map to each retained-register block commutes with the right
partial trace. -/
theorem traceRight_local_linear {A A' B : Type*} [Fintype B]
    (T : Matrix A A ℂ →ₗ[ℂ] Matrix A' A' ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    Matrix.traceRight (fun (i : A' × B) (j : A' × B) =>
      T (fun a b => X (a,i.2) (b,j.2)) i.1 j.1) = T (Matrix.traceRight X) := by
  have hsum : Matrix.traceRight X = ∑ b : B, (fun a c => X (a,b) (c,b)) := by
    ext a c
    simp [Matrix.traceRight]
  rw [hsum]
  calc
    _ = ∑ b : B, T (fun a c => X (a,b) (c,b)) := by
      ext i j
      simp only [Matrix.traceRight, Matrix.of_apply, Matrix.sum_apply]
    _ = _ := (map_sum T (fun b : B => (fun a c => X (a,b) (c,b))) Finset.univ).symm

/-- Tracing out the auxiliary register after channel amplification equals applying the linear
map to the left partial trace. -/
theorem traceLeft_amplification {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) (r : ℕ)
    (X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    Matrix.traceLeft (ChannelAmplification T r X) = T (Matrix.traceLeft X) := by
  have hsum : Matrix.traceLeft X = ∑ a : Fin r, (fun i j => X (a,i) (a,j)) := by
    ext i j
    simp [Matrix.traceLeft]
  rw [hsum]
  calc
    _ = ∑ a : Fin r, T (fun i j => X (a,i) (a,j)) := by
      ext i j
      simp only [Matrix.traceLeft, ChannelAmplification, Matrix.of_apply, Matrix.sum_apply]
    _ = _ := (map_sum T (fun a : Fin r => (fun i j => X (a,i) (a,j))) Finset.univ).symm

/-- Bundles naturality and density preservation of register reduction, iterated discard
identities, and compatibility with local lifts, linear maps, channel amplification, and
Kraus conjugation. -/
theorem part3_clause1 :
  (∀ (S : Type u) (A : Type v) (B : Type w) (A' : Type x) (B' : Type y)
    [Fintype B] [Fintype B'] (e : S ≃ A × B) (a : A ≃ A') (b : B ≃ B')
    (X : Matrix S S ℂ),
    partitionReduce (e.trans (Equiv.prodCongr a b)) X = Matrix.reindex a a (partitionReduce e X)) ∧
  (∀ (S : Type u) (A : Type v) (B : Type w)
    [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (X : Matrix S S ℂ),
    X.PosSemidef → Matrix.trace X = 1 →
      (partitionReduce e X).PosSemidef ∧ Matrix.trace (partitionReduce e X) = 1) ∧
  (∀ (A : Type v) (B : Type w) [Fintype A] (X : Matrix (A × B) (A × B) ℂ),
    partitionReduce (Equiv.prodComm A B) X = Matrix.traceLeft X) ∧
  (∀ (S : Type u) (A : Type v) (B : Type w) (C : Type x) [Fintype B] [Fintype C]
    (e : S ≃ A × (B × C)) (X : Matrix S S ℂ),
    Matrix.traceRight (partitionReduce (e.trans (Equiv.prodAssoc A B C).symm) X) =
      partitionReduce e X ∧
    partitionReduce (e.trans (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm B C))) X =
      partitionReduce e X) ∧
  (∀ (S : Type u) (A : Type v) (B : Type w) (A' : Type x) (B' : Type y)
    [DecidableEq B] [DecidableEq B']
    (e : S ≃ A × B) (a : A ≃ A') (b : B ≃ B') (U : Matrix A A ℂ),
    partitionLift (e.trans (Equiv.prodCongr a b)) (Matrix.reindex a a U) = partitionLift e U) ∧
  (∀ (S : Type u) (S' : Type x) (A : Type v) (B : Type w) [DecidableEq B]
    (e : S ≃ A × B) (s : S ≃ S') (U : Matrix A A ℂ),
    Matrix.reindex s s (partitionLift e U) = partitionLift (s.symm.trans e) U) ∧
  (∀ (S : Type u) (A : Type v) (B : Type w)
    [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (U : Matrix A A ℂ) (X : Matrix S S ℂ),
    partitionReduce e (partitionLift e U * X * (partitionLift e U)ᴴ) =
      U * partitionReduce e X * Uᴴ) ∧
  (∀ (A : Type v) (A' : Type x) (B : Type w) [Fintype B]
    (T : Matrix A A ℂ →ₗ[ℂ] Matrix A' A' ℂ) (X : Matrix (A × B) (A × B) ℂ),
    Matrix.traceRight (fun (i : A' × B) (j : A' × B) =>
      T (fun a b => X (a,i.2) (b,j.2)) i.1 j.1) = T (Matrix.traceRight X)) ∧
  (∀ (D E r : ℕ) (T : QuantumChannel D E)
    (X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ),
    Matrix.traceLeft (ChannelAmplification T.map r X) = T.map (Matrix.traceLeft X)) ∧
  (∀ (A : Type v) (A' : Type x) (B : Type w)
    [Fintype A] [Fintype A'] [Fintype B] [DecidableEq B]
    (K : Matrix A' A ℂ) (X : Matrix (A × B) (A × B) ℂ),
    Matrix.traceRight ((K ⊗ₖ (1 : Matrix B B ℂ)) * X *
      (K ⊗ₖ (1 : Matrix B B ℂ))ᴴ) = K * Matrix.traceRight X * Kᴴ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S A B A' B' _ _ e a b X
    exact partitionReduce_natural e a b X
  · intro S A B _ _ _ _ _ _ e X hp ht
    exact partitionReduce_density e X hp ht
  · intro A B _ X
    exact partitionReduce_swap X
  · intro S A B C _ _ e X
    exact ⟨partitionReduce_iterated e X, partitionReduce_discard_order e X⟩
  · intro S A B A' B' _ _ e a b U
    exact partitionLift_natural e a b U
  · intro S S' A B _ e s U
    exact partitionLift_reindex e s U
  · intro S A B _ _ _ _ _ _ e U X
    exact partitionReduce_lift e U X
  · intro A A' B _ T X
    exact traceRight_local_linear T X
  · intro D E r T X
    exact traceLeft_amplification T.map r X
  · intro A A' B _ _ _ _ K X
    exact traceRight_local_kraus K X

/-- Bundles encoded event-instrument formulas for density matrices, probabilities, and
conditional states, together with qudit teleportation branch, normalization, and correction
identities. -/
theorem part5_clause1 :
  (∀ (I : Type u) [Fintype I] [DecidableEq I] (D : ℕ) (e : I ≃ Fin D)
      (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (S : Finset I),
    (∀ ρ : Matrix I I ℂ, ρ.PosSemidef ∧ Matrix.trace ρ = 1 → IsDensityOperator (relabelGate e ρ)) ∧
    (∀ (ρ : Matrix I I ℂ) (o : Bool),
      (encodedEventInstrument e U hU S).branch o (relabelGate e ρ) =
        relabelGate e ((if o then Projector S else 1 - Projector S) * (U * ρ * Uᴴ) *
          (if o then Projector S else 1 - Projector S)ᴴ)) ∧
    (∀ ψ : QState I,
      instrumentProb (encodedEventInstrument e U hU S) (relabelGate e (outerProduct ψ)) true =
        MeasureProb (ApplyGate U ψ) S) ∧
    (∀ (ψ : QState I) (o : Bool),
      (encodedEventInstrument e U hU S).branch o (relabelGate e (outerProduct ψ)) =
        relabelGate e (outerProduct (ProjectiveBranch (Projector S) o (ApplyGate U ψ))) ∧
      instrumentProb (encodedEventInstrument e U hU S) (relabelGate e (outerProduct ψ)) o =
        ProjectiveBranchMass (Projector S) o (ApplyGate U ψ) ∧
      (∀ hp : 0 < instrumentProb (encodedEventInstrument e U hU S)
          (relabelGate e (outerProduct ψ)) o,
        ∃ φ, ProjectiveConditionalState (Projector S) o (ApplyGate U ψ) = some φ ∧
          (encodedEventInstrument e U hU S).conditionalState
            (relabelGate e (outerProduct ψ)) o hp = relabelGate e (outerProduct φ)) ∧
      (ProjectiveBranchMass (Projector S) o (ApplyGate U ψ) = 0 →
        ProjectiveConditionalState (Projector S) o (ApplyGate U ψ) = none ∧
        (encodedEventInstrument e U hU S).branch o (relabelGate e (outerProduct ψ)) = 0))) ∧
  (∀ (n : ℕ) [NeZero n] (ψ : QState (Fin n)) (o : Fin n × Fin n),
    (quditCoarseInstrument n o).branch true (outerProduct (quditDecodedState n ψ)) =
      outerProduct (Collapse (quditDecodedState n ψ) (quditOutcomeEvent n o)) ∧
    Matrix.traceLeft (Matrix.reindex (quditRegisterEquiv n).symm (quditRegisterEquiv n).symm
      ((quditCoarseInstrument n o).branch true (outerProduct (quditDecodedState n ψ)))) =
        outerProduct (quditBranchKraus n o *ᵥ ψ) ∧
    instrumentProb (quditCoarseInstrument n o) (outerProduct (quditDecodedState n ψ)) true =
      MeasureProb (quditBranchKraus n o *ᵥ ψ) Finset.univ ∧
    quditCorrection n o *ᵥ (quditBranchKraus n o *ᵥ ψ) = (1 / (n : ℂ)) • ψ ∧
    (Normalized ψ →
      Normalized (quditDecodedState n ψ) ∧
      instrumentProb (quditCoarseInstrument n o) (outerProduct (quditDecodedState n ψ)) true =
        1 / (n : ℝ)^2 ∧
      ∀ hp : 0 < instrumentProb (quditCoarseInstrument n o)
          (outerProduct (quditDecodedState n ψ)) true,
        quditCorrection n o *
          Matrix.traceLeft (Matrix.reindex (quditRegisterEquiv n).symm (quditRegisterEquiv n).symm
            ((quditCoarseInstrument n o).conditionalState
              (outerProduct (quditDecodedState n ψ)) true hp)) *
          (quditCorrection n o)ᴴ = outerProduct ψ)) := by
  constructor
  · intro I _ _ D e U hU S
    refine ⟨relabel_density e, encoded_event_mixed_branch e U hU S,
      encoded_event_born e U hU S, ?_⟩
    intro ψ o
    exact ⟨encoded_event_pure_branch e U hU S ψ o, encoded_event_mass e U hU S ψ o,
      encoded_event_conditional e U hU S ψ o, encoded_event_zero e U hU S ψ o⟩
  · intro n _ ψ o
    refine ⟨qudit_coarse_branch n ψ o, qudit_coarse_bob n ψ o, qudit_coarse_mass n ψ o,
      qudit_corrected_vector n ψ o, ?_⟩
    intro hψ
    exact ⟨qudit_decoded_normalized n ψ hψ,
      (qudit_coarse_mass n ψ o).trans (qudit_kraus_mass n ψ hψ o),
      qudit_coarse_conditional_corrected n ψ hψ o⟩

end Qatlib.Concepts.TensorRegisters.RegisterModel
