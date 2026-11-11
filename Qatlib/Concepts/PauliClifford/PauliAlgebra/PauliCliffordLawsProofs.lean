/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsDefs
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters

/-!
# Pauli matrix identities and legal Clifford conjugation

This module proves that `op` preserves Pauli multiplication, computes its adjoint, and gives a
unitary matrix for every Pauli element. Tensor products of Pauli matrices satisfy the
commutation sign determined by the binary symplectic form, as in [DehaeneDeMoor2003].

The gate proofs establish unitarity and agreement with `verifiedCliffordAction` for H, S, and
CNOT with distinct sites. Explicit examples record the CNOT phase correction and the signs in
conjugating Y; the one-qubit CNOT with coincident sites provides a failure of unitarity.

## Main statements

* `op_mul`, `op_conjTranspose`, and `op_unitary`: matrix interpretation laws for Pauli elements.
* `pauliWordOp_symplectic`: binary symplectic pairing determines the Pauli commutation sign.
* `pauli_matrix_laws`: combined multiplication, adjoint, unitarity, and commutation laws.
* `cliffordGateOp_CNOT_conj`: verified CNOT action agrees with matrix conjugation when its sites
  differ.
* `legal_clifford_conjugacy`: combined gate laws, phase examples, and the coincident-site
  counterexample.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.TensorRegisters.RegisterModel

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

open Qatlib.Concepts.PauliClifford.PauliAlgebra Qatlib.Concepts.TensorRegisters.RegisterModel
open Matrix

/-- The identity, X, Y, and Z Pauli matrices with rows and columns indexed by Boolean basis
values. -/
def P1 : Pauli1 → Matrix Bool Bool ℂ
  | .I => fun x y => if x = y then 1 else 0
  | .X => fun x y => if x ≠ y then 1 else 0
  | .Y => fun x y => if x = y then 0 else if x then Complex.I else -Complex.I
  | .Z => fun x y => if x then if y then -1 else 0 else if y then 0 else 1

/-- The Boolean basis value `false` corresponds to index zero under `boolEquivFin2`. -/
theorem boolEquivFin2_false : boolEquivFin2 false = 0 := rfl

/-- The Boolean basis value `true` corresponds to index one under `boolEquivFin2`. -/
theorem boolEquivFin2_true : boolEquivFin2 true = 1 := rfl

/-- The Boolean-indexed matrix `P1 a` agrees entrywise with `pauli1Matrix a` after applying
`boolEquivFin2` to both indices. -/
theorem P1_apply (a : Pauli1) (x y : Bool) :
    P1 a x y = pauli1Matrix a (boolEquivFin2 x) (boolEquivFin2 y) := by
  cases a <;> cases x <;> cases y <;>
    simp [P1, pauli1Matrix, pauliX, pauliY, pauliZ,
      boolEquivFin2_false, boolEquivFin2_true]

/-- The matrix assigned by `P1` to the identity Pauli label is the identity matrix. -/
theorem P1_one : P1 .I = 1 := by
  ext x y
  cases x <;> cases y <;> simp [P1]

/-- The matrix of a Pauli word is the product matrix of its Boolean-indexed single-site Pauli
matrices. -/
theorem pauliWordOp_eq (n : ℕ) (w : PauliWord n) :
    pauliWordOp n w = productMatrix (fun i => P1 (w i)) := by
  ext x y
  simp only [pauliWordOp, productMatrix]
  exact Finset.prod_congr rfl fun i _ => (P1_apply (w i) (x i) (y i)).symm

/-- The canonical natural representative of one in `ZMod 4` is one. -/
theorem zmod4_val_one : (1 : ZMod 4).val = 1 := rfl

/-- The canonical natural representative of two in `ZMod 4` is two. -/
theorem zmod4_val_two : (2 : ZMod 4).val = 2 := rfl

/-- The canonical natural representative of three in `ZMod 4` is three. -/
theorem zmod4_val_three : (3 : ZMod 4).val = 3 := rfl

/-- The canonical natural representative of one in `ZMod 2` is one. -/
theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

/-- The sum of one with itself in `ZMod 2` is zero. -/
theorem zmod2_two : (1 + 1 : ZMod 2) = 0 := rfl

/-- The first power of the imaginary unit is the imaginary unit. -/
theorem I_pow_one : (Complex.I : ℂ) ^ 1 = Complex.I := pow_one _

/-- The square of the imaginary unit is negative one. -/
theorem I_pow_two : (Complex.I : ℂ) ^ 2 = -1 := by
  rw [pow_two, Complex.I_mul_I]

/-- The cube of the imaginary unit is the negative imaginary unit. -/
theorem I_pow_three : (Complex.I : ℂ) ^ 3 = -Complex.I := by
  rw [pow_succ, I_pow_two]
  ring

/-- The canonical natural representative of negative one in `ZMod 4` is three. -/
theorem zmod4_neg_one : (-1 : ZMod 4).val = 3 := rfl

/-- The canonical natural representative of negative two in `ZMod 4` is two. -/
theorem zmod4_neg_two : (-2 : ZMod 4).val = 2 := rfl

/-- The canonical natural representative of negative three in `ZMod 4` is one. -/
theorem zmod4_neg_three : (-3 : ZMod 4).val = 1 := rfl

/-- Exponentiating the imaginary unit by the representative of a sum in `ZMod 4` gives the
product of the corresponding powers. -/
theorem I_pow_val_add (a b : ZMod 4) :
    Complex.I ^ (a + b).val = Complex.I ^ a.val * Complex.I ^ b.val := by
  rw [ZMod.val_add, ← Complex.I_pow_eq_pow_mod (a.val + b.val), pow_add]

/-- Exponentiating the imaginary unit by a finite sum in `ZMod 4` gives the product of the
powers associated with each summand. -/
theorem I_pow_sum_val {ι : Type*} [DecidableEq ι] [Fintype ι] (k : ι → ZMod 4) :
    Complex.I ^ (∑ i, k i).val = ∏ i, Complex.I ^ (k i).val := by
  have hcast : (∑ i, k i : ZMod 4) = ((∑ i, (k i).val) : ℕ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => (ZMod.natCast_zmod_val _).symm
  rw [hcast, ZMod.val_natCast, ← Complex.I_pow_eq_pow_mod (∑ i, (k i).val),
    Finset.prod_pow_eq_pow_sum]

/-- Multiplying two scalar multiples of matrices gives the matrix product scaled by the product
of the scalars. -/
theorem smul_mul_smul' {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ℂ)
    (M N : Matrix ι ι ℂ) :
    (c • M) * (d • N) = (c * d) • (M * N) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- Two successive complex scalar multiplications of a matrix combine into multiplication by the
product scalar. -/
theorem smul_smul' {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ℂ)
    (M : Matrix ι ι ℂ) :
    c • (d • M) = (c * d) • M := by
  ext x y
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc]

/-- A product matrix of scaled single-site matrices equals the unscaled product matrix
multiplied by the product of all scalars. -/
theorem smul_pow_eq_pow_sum {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℂ)
    (A : ∀ _ : ι, Matrix Bool Bool ℂ) :
    productMatrix (fun i => c i • A i) = (∏ i, c i) • productMatrix A := by
  ext x y
  simp only [productMatrix, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- The product of two single-site Pauli matrices is the matrix of `pauliMul1` scaled by the
phase determined by `pauliMulPhase`. -/
theorem P1_mul (a b : Pauli1) :
    P1 a * P1 b = (Complex.I ^ (pauliMulPhase a b).val : ℂ) • P1 (pauliMul1 a b) := by
  ext x y
  simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.smul_apply, smul_eq_mul]
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp [P1, pauliMul1, pauliMulPhase, zmod4_val_one, zmod4_val_three]

/-- Every Boolean-indexed single-site Pauli matrix equals its conjugate transpose. -/
theorem P1_conjTranspose (a : Pauli1) : (P1 a)ᴴ = P1 a := by
  ext x y
  cases a <;> cases x <;> cases y <;> simp [P1, Matrix.conjTranspose_apply]

/-- Every Boolean-indexed single-site Pauli matrix squares to the identity. -/
theorem P1_mul_self (a : Pauli1) : P1 a * P1 a = 1 := by
  have h := P1_mul a a
  cases a <;> simpa [P1, pauliMul1, pauliMulPhase] using! h

/-- Multiplication of Pauli word matrices is sitewise Pauli multiplication with the global phase
obtained by summing the local multiplication phases. -/
theorem pauliWordOp_mul (n : ℕ) (w v : PauliWord n) :
    pauliWordOp n w * pauliWordOp n v
      = (Complex.I ^ (∑ i, pauliMulPhase (w i) (v i)).val : ℂ)
          • pauliWordOp n (fun i => pauliMul1 (w i) (v i)) := by
  rw [pauliWordOp_eq, pauliWordOp_eq, pauliWordOp_eq, productMatrix_mul]
  have hf : ∀ i, P1 (w i) * P1 (v i)
      = (Complex.I ^ (pauliMulPhase (w i) (v i)).val : ℂ)
          • P1 (pauliMul1 (w i) (v i)) :=
    fun i => P1_mul _ _
  rw [funext hf, smul_pow_eq_pow_sum]
  congr 1
  rw [I_pow_sum_val]

/-- Every Pauli word matrix equals its conjugate transpose. -/
theorem pauliWordOp_herm (n : ℕ) (w : PauliWord n) :
    (pauliWordOp n w)ᴴ = pauliWordOp n w := by
  rw [pauliWordOp_eq, productMatrix_adjoint]
  congr 1
  funext i
  exact P1_conjTranspose (w i)

/-- Every Pauli word matrix is unitary. -/
theorem pauliWordOp_unitary (n : ℕ) (w : PauliWord n) :
    pauliWordOp n w ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, pauliWordOp_eq,
    productMatrix_adjoint, productMatrix_mul]
  have h : ∀ i, (P1 (w i))ᴴ * P1 (w i) = 1 := by
    intro i
    rw [P1_conjTranspose]
    exact P1_mul_self (w i)
  rw [funext h]
  exact productMatrix_one

/-- Multiplying a single-site Pauli label by itself gives the identity label. -/
theorem pauliMul1_self (a : Pauli1) : pauliMul1 a a = .I := by cases a <;> rfl

/-- Multiplying a single-site Pauli label by itself produces zero phase increment. -/
theorem pauliMulPhase_self (a : Pauli1) : pauliMulPhase a a = 0 := by cases a <;> rfl

/-- The matrix interpretation of the identity Pauli element is the identity matrix. -/
theorem op_one {n : ℕ} : op (1 : PauliElem n) = 1 := by
  have hword : pauliWordOp n (fun _ => Pauli1.I) = 1 := by
    rw [pauliWordOp_eq]
    have h : (fun _ : Fin n => P1 Pauli1.I) = fun _ => (1 : Matrix Bool Bool ℂ) :=
      funext fun _ => P1_one
    rw [h, productMatrix_one]
  show (Complex.I ^ (0 : ZMod 4).val : ℂ) • pauliWordOp n (fun _ => Pauli1.I) = 1
  rw [hword]
  simp

/-- The matrix interpretation `op` preserves multiplication of Pauli elements. -/
theorem op_mul {n : ℕ} (p q : PauliElem n) : op (PauliElem.mul p q) = op p * op q := by
  show (Complex.I ^ (p.phase + q.phase + ∑ i, pauliMulPhase (p.word i) (q.word i)).val : ℂ)
      • pauliWordOp n (fun i => pauliMul1 (p.word i) (q.word i))
    = (Complex.I ^ p.phase.val : ℂ) • pauliWordOp n p.word
      * (Complex.I ^ q.phase.val : ℂ) • pauliWordOp n q.word
  rw [smul_mul_smul', pauliWordOp_mul, smul_smul']
  have hsum : Complex.I ^ (p.phase + q.phase + ∑ i, pauliMulPhase (p.word i) (q.word i)).val
      = Complex.I ^ p.phase.val * Complex.I ^ q.phase.val
        * Complex.I ^ (∑ i, pauliMulPhase (p.word i) (q.word i)).val := by
    rw [I_pow_val_add, I_pow_val_add]
  rw [hsum]

/-- The complex conjugate of any natural power of the imaginary unit multiplied by that power
equals one. -/
theorem star_I_pow_mul_self (m : ℕ) :
    star ((Complex.I : ℂ) ^ m) * Complex.I ^ m = 1 := by
  rw [Complex.I_pow_eq_pow_mod m]
  rcases show m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 by omega with h | h | h | h
  · rw [h, pow_zero]
    simp
  · rw [h, pow_one]
    simp [Complex.conj_I, Complex.I_mul_I]
  · rw [h, I_pow_two]
    simp
  · rw [h, I_pow_three]
    simp [Complex.conj_I, Complex.I_mul_I]

/-- The conjugate transpose of a Pauli element's matrix is obtained by negating its phase and
retaining its word. -/
theorem op_conjTranspose {n : ℕ} (p : PauliElem n) :
    (op p)ᴴ = op ⟨p.word, -p.phase⟩ := by
  simp only [op, Matrix.conjTranspose_smul, pauliWordOp_herm]
  have h : ∀ k : ZMod 4,
      star (Complex.I ^ k.val : ℂ) = (Complex.I ^ (-k).val : ℂ) := by
    intro k
    have h1 : star (Complex.I ^ k.val : ℂ) * Complex.I ^ k.val = 1 :=
      star_I_pow_mul_self k.val
    have h2 : Complex.I ^ (-k).val * Complex.I ^ k.val = 1 := by
      rw [← I_pow_val_add, neg_add_cancel k]
      simp
    have hne : (Complex.I ^ k.val : ℂ) ≠ 0 := pow_ne_zero _ (by simp)
    exact mul_right_cancel₀ hne (h1.trans h2.symm)
  rw [h p.phase]

/-- The matrix interpretation of every Pauli element is unitary. -/
theorem op_unitary {n : ℕ} (p : PauliElem n) : op p ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, op_conjTranspose,
    ← op_mul]
  have hmul : (⟨p.word, -p.phase⟩ : PauliElem n).mul p = 1 := by
    have hsum : ∑ i, pauliMulPhase (p.word i) (p.word i) = 0 :=
      Finset.sum_eq_zero fun i _ => pauliMulPhase_self (p.word i)
    have hone : (1 : PauliElem n) = ⟨fun _ => Pauli1.I, 0⟩ := rfl
    show (⟨fun i => pauliMul1 (p.word i) (p.word i),
      -p.phase + p.phase + ∑ i, pauliMulPhase (p.word i) (p.word i)⟩ : PauliElem n) = 1
    rw [funext fun i => pauliMul1_self (p.word i), hsum, hone, PauliElem.mk.injEq]
    exact ⟨rfl, by abel⟩
  rw [hmul]
  exact op_one

/-- The binary X coordinate of a single-site Pauli label, equal to one for X and Y and zero
otherwise. -/
def siteX (a : Pauli1) : ZMod 2 := if a = .X ∨ a = .Y then 1 else 0

/-- The binary Z coordinate of a single-site Pauli label, equal to one for Y and Z and zero
otherwise. -/
def siteZ (a : Pauli1) : ZMod 2 := if a = .Y ∨ a = .Z then 1 else 0

/-- The X coordinate of a Pauli word at site `i` is the single-site coordinate `siteX (w i)`. -/
theorem symplecticX_apply {n : ℕ} (w : PauliWord n) (i : Fin n) :
    symplecticX w i = siteX (w i) := rfl

/-- The Z coordinate of a Pauli word at site `i` is the single-site coordinate `siteZ (w i)`. -/
theorem symplecticZ_apply {n : ℕ} (w : PauliWord n) (i : Fin n) :
    symplecticZ w i = siteZ (w i) := rfl

/-- The binary symplectic pairing of two single-site Pauli labels, given by the sum of their
cross-products of X and Z coordinates. -/
def siteForm (a b : Pauli1) : ZMod 2 :=
  siteX a * siteZ b + siteZ a * siteX b

/-- Reducing a natural exponent modulo two leaves the corresponding complex power of negative
one unchanged. -/
theorem neg_one_pow_mod_two (m : ℕ) : (-1 : ℂ) ^ (m % 2) = (-1 : ℂ) ^ m := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · rw [hk, Nat.mul_mod_right, pow_zero, pow_mul,
      (by norm_num : ((-1 : ℂ)) ^ 2 = 1), one_pow]
  · rw [hk, (by omega : (2 * k + 1) % 2 = 1), pow_one, pow_succ, pow_mul,
      (by norm_num : ((-1 : ℂ)) ^ 2 = 1), one_pow, one_mul]

/-- The sign determined by a finite sum in `ZMod 2` is the product of the signs determined by
its summands. -/
theorem neg_one_pow_sum_val {ι : Type*} [DecidableEq ι] [Fintype ι] (s : ι → ZMod 2) :
    (-1 : ℂ) ^ (∑ i, s i).val = ∏ i, (-1 : ℂ) ^ (s i).val := by
  have hcast : (∑ i, s i : ZMod 2) = ((∑ i, (s i).val) : ℕ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => (ZMod.natCast_zmod_val _).symm
  rw [hcast, ZMod.val_natCast, neg_one_pow_mod_two, Finset.prod_pow_eq_pow_sum]

/-- Exchanging two single-site Pauli labels changes their multiplication phase by the sign
determined by `siteForm`. -/
theorem P1_site_comm (a b : Pauli1) :
    Complex.I ^ (pauliMulPhase a b).val
      = ((-1 : ℂ) ^ (siteForm a b).val) * Complex.I ^ (pauliMulPhase b a).val := by
  cases a <;> cases b <;>
    simp [pauliMulPhase, siteForm, siteX, siteZ, zmod4_val_one, zmod4_val_three,
      zmod2_val_one, zmod2_two]

/-- The single-site product label `pauliMul1` is unchanged when its two arguments are exchanged. -/
theorem pauliMul1_comm (a b : Pauli1) : pauliMul1 a b = pauliMul1 b a := by
  cases a <;> cases b <;> rfl

/-- The binary symplectic pairing of two Pauli words is the sum of their single-site pairings
`siteForm`. -/
theorem symplecticForm_eq_sum_site {n : ℕ} (w v : PauliWord n) :
    symplecticForm (symplecticX w, symplecticZ w) (symplecticX v, symplecticZ v)
      = ∑ i, siteForm (w i) (v i) := by
  simp only [symplecticForm, Qatlib.Concepts.PauliClifford.ExactRank.booleanDot, siteForm,
    symplecticX_apply, symplecticZ_apply]
  rw [← Finset.sum_add_distrib]

/-- Exchanging two Pauli word matrices introduces the sign determined by their binary symplectic
pairing [DehaeneDeMoor2003]. -/
theorem pauliWordOp_symplectic (n : ℕ) (w v : PauliWord n) :
    pauliWordOp n w * pauliWordOp n v
      = ((-1 : ℂ) ^ (symplecticForm (symplecticX w, symplecticZ w)
          (symplecticX v, symplecticZ v)).val)
        • (pauliWordOp n v * pauliWordOp n w) := by
  rw [pauliWordOp_mul n w v, pauliWordOp_mul n v w]
  have hcomm : (fun i => pauliMul1 (w i) (v i)) = fun i => pauliMul1 (v i) (w i) :=
    funext fun i => pauliMul1_comm _ _
  rw [hcomm]
  have hscalar : Complex.I ^ (∑ i, pauliMulPhase (w i) (v i)).val
      = ((-1 : ℂ) ^ (symplecticForm (symplecticX w, symplecticZ w)
          (symplecticX v, symplecticZ v)).val)
        * Complex.I ^ (∑ i, pauliMulPhase (v i) (w i)).val := by
    rw [I_pow_sum_val, I_pow_sum_val, symplecticForm_eq_sum_site w v,
      neg_one_pow_sum_val, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => P1_site_comm (w i) (v i)
  rw [hscalar, smul_smul']

/-- Combine preservation of Pauli multiplication, Hermiticity and unitarity of word matrices,
and unitarity and the adjoint formula for Pauli elements. The result also gives the
commutation sign from the binary symplectic pairing [DehaeneDeMoor2003]. -/
theorem pauli_matrix_laws :
    ∀ (n : ℕ) (p q : PauliElem n) (w v : PauliWord n),
      (op (PauliElem.mul p q) = op p * op q)
      ∧ ((pauliWordOp n w)ᴴ = pauliWordOp n w)
      ∧ (pauliWordOp n w ∈ Matrix.unitaryGroup (Reg n) ℂ)
      ∧ (op p ∈ Matrix.unitaryGroup (Reg n) ℂ)
      ∧ ((op p)ᴴ = op ⟨p.word, -p.phase⟩)
      ∧ (pauliWordOp n w * pauliWordOp n v
          = ((-1 : ℂ) ^ (symplecticForm (symplecticX w, symplecticZ w)
              (symplecticX v, symplecticZ v)).val)
            • (pauliWordOp n v * pauliWordOp n w)) := by
  intro n p q w v
  exact ⟨op_mul p q, pauliWordOp_herm n w, pauliWordOp_unitary n w, op_unitary p,
    op_conjTranspose p, pauliWordOp_symplectic n w v⟩

/-- A complex scalar multiplying the right matrix factor can be factored out of the matrix
product. -/
theorem smul_mul_right'' {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ)
    (M N : Matrix ι ι ℂ) : M * (c • N) = c • (M * N) := by
  rw [← one_smul ℂ M, smul_mul_smul', one_mul, one_smul]

/-- A complex scalar multiplying the left matrix factor can be factored out of the matrix
product. -/
theorem smul_mul_left'' {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ)
    (M N : Matrix ι ι ℂ) : (c • M) * N = c • (M * N) := by
  rw [← one_smul ℂ N, smul_mul_smul', mul_one, one_smul]

/-- The sum over `Fin n` of a `ZMod 4` value supported only at site `i` is that value. -/
theorem sum_ite_single4 {n : ℕ} (i : Fin n) (c : ZMod 4) :
    ∑ k : Fin n, (if k = i then c else 0) = c := by
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg hk])
      (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]

/-- A complex scalar multiplying the factor at a single site can be factored out of the full
product matrix. -/
theorem productMatrix_if_smul {n : ℕ} (i : Fin n) (c : ℂ) (B : Matrix Bool Bool ℂ)
    (A : ∀ _ : Fin n, Matrix Bool Bool ℂ) :
    productMatrix (fun k => if k = i then c • B else A k)
      = c • productMatrix (fun k => if k = i then B else A k) := by
  ext x y
  simp only [productMatrix, Matrix.smul_apply, smul_eq_mul]
  have hL : ∏ k : Fin n, (if k = i then c • B else A k) (x k) (y k)
      = (if i = i then c • B else A i) (x i) (y i)
          * ∏ k ∈ Finset.univ.erase i, (if k = i then c • B else A k) (x k) (y k) :=
    (Finset.mul_prod_erase Finset.univ
      (fun k => (if k = i then c • B else A k) (x k) (y k)) (Finset.mem_univ i)).symm
  have hR : ∏ k : Fin n, (if k = i then B else A k) (x k) (y k)
      = (if i = i then B else A i) (x i) (y i)
          * ∏ k ∈ Finset.univ.erase i, (if k = i then B else A k) (x k) (y k) :=
    (Finset.mul_prod_erase Finset.univ
      (fun k => (if k = i then B else A k) (x k) (y k)) (Finset.mem_univ i)).symm
  have hE : ∏ k ∈ Finset.univ.erase i, (if k = i then c • B else A k) (x k) (y k)
      = ∏ k ∈ Finset.univ.erase i, (if k = i then B else A k) (x k) (y k) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Finset.mem_erase] at hk
    rw [if_neg hk.1, if_neg hk.1]
  rw [hL, hR, hE, if_pos rfl, if_pos rfl, Matrix.smul_apply, smul_eq_mul, mul_assoc]

/-- Applying `P1` to a Pauli word with one conditional site replacement is the corresponding
conditional replacement of its single-site matrices. -/
theorem P1_if {n : ℕ} (i : Fin n) (w : PauliWord n) (a : Pauli1) :
    (fun k => P1 (if k = i then a else w k))
      = fun k => if k = i then P1 a else P1 (w k) := by
  funext k
  by_cases hk : k = i <;> simp [hk]

/-- Left multiplication by a matrix acting only at site `i` multiplies the factor at that site
in the product matrix. -/
theorem prod_if_left {n : ℕ} (i : Fin n) (B : Matrix Bool Bool ℂ)
    (A : ∀ _ : Fin n, Matrix Bool Bool ℂ) :
    productMatrix (fun k => if k = i then B else (1 : Matrix Bool Bool ℂ)) * productMatrix A
      = productMatrix (fun k => if k = i then B * A k else A k) := by
  rw [productMatrix_mul]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

/-- Right multiplication by a matrix acting only at site `i` multiplies the factor at that site
in the product matrix. -/
theorem prod_if_right {n : ℕ} (i : Fin n) (C : Matrix Bool Bool ℂ)
    (A : ∀ _ : Fin n, Matrix Bool Bool ℂ) :
    productMatrix A * productMatrix (fun k => if k = i then C else (1 : Matrix Bool Bool ℂ))
      = productMatrix (fun k => if k = i then A k * C else A k) := by
  rw [productMatrix_mul]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

/-- The H gate on site `i` is the product matrix with a Hadamard factor at `i` and identity
factors elsewhere. -/
theorem cliffordGateOp_H (n : ℕ) (i : Fin n) :
    cliffordGateOp n (.H i)
      = productMatrix (fun k => if k = i then Hadamard else (1 : Matrix Bool Bool ℂ)) := by
  ext x y
  by_cases hx : ∀ j : Fin n, j ≠ i → x j = y j
  · simp only [cliffordGateOp, productMatrix]
    rw [if_pos hx,
      Finset.prod_eq_single i (fun k _ hk => by
        rw [if_neg hk, Matrix.one_apply, if_pos (hx k hk)])
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  · have hcond : ¬ ∀ j : Fin n, j ≠ i → x j = y j := hx
    push Not at hx
    obtain ⟨k, hk, hxy⟩ := hx
    simp only [cliffordGateOp, productMatrix, if_neg hcond]
    exact (Finset.prod_eq_zero
      (f := fun t => (if t = i then Hadamard else (1 : Matrix Bool Bool ℂ)) (x t) (y t))
      (Finset.mem_univ k)
      (by show (if k = i then Hadamard else (1 : Matrix Bool Bool ℂ)) (x k) (y k) = 0
          rw [if_neg hk, Matrix.one_apply, if_neg hxy])).symm

/-- The S gate on site `i` is the product matrix with an `sGate` factor at `i` and identity
factors elsewhere. -/
theorem cliffordGateOp_S (n : ℕ) (i : Fin n) :
    cliffordGateOp n (.S i)
      = productMatrix (fun k => if k = i then sGate else (1 : Matrix Bool Bool ℂ)) := by
  ext x y
  by_cases hx : ∀ j : Fin n, j ≠ i → x j = y j
  · simp only [cliffordGateOp, productMatrix]
    rw [if_pos hx,
      Finset.prod_eq_single i (fun k _ hk => by
        rw [if_neg hk, Matrix.one_apply, if_pos (hx k hk)])
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  · have hcond : ¬ ∀ j : Fin n, j ≠ i → x j = y j := hx
    push Not at hx
    obtain ⟨k, hk, hxy⟩ := hx
    simp only [cliffordGateOp, productMatrix, if_neg hcond]
    exact (Finset.prod_eq_zero
      (f := fun t => (if t = i then sGate else (1 : Matrix Bool Bool ℂ)) (x t) (y t))
      (Finset.mem_univ k)
      (by show (if k = i then sGate else (1 : Matrix Bool Bool ℂ)) (x k) (y k) = 0
          rw [if_neg hk, Matrix.one_apply, if_neg hxy])).symm

/-- The product of two inverse square roots of two in the complex numbers is one half. -/
theorem sqrt2_inv_sq : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹
    = (1 : ℂ) / 2 := by
  field_simp [sqrt2_sq]
  exact sqrt2_sq.symm

/-- Multiplying the imaginary unit on both sides by the inverse square root of two gives half
the imaginary unit. -/
theorem sqrt2_inv_sq_mid : ((Real.sqrt 2 : ℂ))⁻¹ * Complex.I * ((Real.sqrt 2 : ℂ))⁻¹
    = Complex.I / 2 := by
  field_simp [sqrt2_sq]
  exact sqrt2_sq.symm

/-- Two copies of the inverse of two sum to one in the complex numbers. -/
theorem half_add_half : (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 := by norm_num

/-- Two copies of the negative inverse of two sum to negative one in the complex numbers. -/
theorem neg_half_add_neg_half : -(2 : ℂ)⁻¹ + -(2 : ℂ)⁻¹ = -1 := by
  rw [← neg_add]
  norm_num

/-- Two copies of half the imaginary unit sum to the imaginary unit. -/
theorem half_add_half_I : Complex.I / 2 + Complex.I / 2 = Complex.I := by norm_num

/-- Two copies of the negative half of the imaginary unit sum to the negative imaginary unit. -/
theorem neg_half_add_neg_half_I :
    -(Complex.I / 2) + -(Complex.I / 2) = -Complex.I := by
  rw [← neg_add]
  norm_num

/-- Conjugating a single-site Pauli matrix by Hadamard gives the word update `conjHWord` with
phase `conjHPhase`. -/
theorem hadamard_conj_P1 (a : Pauli1) :
    Hadamard * P1 a * Hadamardᴴ
      = (Complex.I ^ (conjHPhase a).val : ℂ) • P1 (conjHWord a) := by
  rw [hadamard_conjTranspose]
  ext x y
  simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.smul_apply, smul_eq_mul]
  cases a <;> cases x <;> cases y <;>
    simp [P1, Hadamard, conjHWord, conjHPhase, sqrt2_inv_sq, sqrt2_inv_sq_mid,
      zmod4_val_two, half_add_half, neg_half_add_neg_half, neg_half_add_neg_half_I]

/-- The conjugate transpose of `sGate` is diagonal, with entries one at `false` and the negative
imaginary unit at `true`. -/
theorem sGate_conjTranspose :
    sGateᴴ = Matrix.diagonal fun b => if b then -Complex.I else 1 := by
  ext x y
  cases x <;> cases y <;>
    simp [sGate, Matrix.conjTranspose_apply, Complex.conj_I]

/-- Conjugating a single-site Pauli matrix by `sGate` gives the word update `conjSWord` with
phase `conjSPhase`. -/
theorem sGate_conj_P1 (a : Pauli1) :
    sGate * P1 a * sGateᴴ
      = (Complex.I ^ (conjSPhase a).val : ℂ) • P1 (conjSWord a) := by
  rw [sGate_conjTranspose]
  ext x y
  simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply]
  cases a <;> cases x <;> cases y <;>
    simp [P1, sGate, conjSWord, conjSPhase, zmod4_val_two]

/-- Embedding a matrix satisfying `Gᴴ * G = 1` at one site and identities elsewhere preserves
this identity on the full register. -/
theorem single_site_unitary {n : ℕ} (i : Fin n) (G : Matrix Bool Bool ℂ)
    (hG : Gᴴ * G = 1) :
    (productMatrix (fun k => if k = i then G else (1 : Matrix Bool Bool ℂ)))ᴴ
      * productMatrix (fun k => if k = i then G else (1 : Matrix Bool Bool ℂ)) = 1 := by
  have hAd : productMatrix (fun k => (if k = i then G else (1 : Matrix Bool Bool ℂ))ᴴ)
      = productMatrix (fun k => if k = i then Gᴴ else (1 : Matrix Bool Bool ℂ)) := by
    congr 1
    funext k
    by_cases hk : k = i <;> simp [hk, Matrix.conjTranspose_one]
  rw [productMatrix_adjoint, hAd, productMatrix_mul]
  have h : ∀ k, (if k = i then Gᴴ else (1 : Matrix Bool Bool ℂ))
      * (if k = i then G else (1 : Matrix Bool Bool ℂ)) = 1 := by
    intro k
    by_cases hk : k = i <;> simp [hk, hG]
  rw [funext h]
  exact productMatrix_one

/-- The conjugate transpose of Hadamard multiplied by Hadamard is the identity. -/
theorem hadamard_mul_self' : Hadamardᴴ * Hadamard = 1 := by
  rw [hadamard_conjTranspose]
  exact hadamard_mul_self

/-- The conjugate transpose of `sGate` multiplied by `sGate` is the identity. -/
theorem sGate_mul_self' : sGateᴴ * sGate = 1 := by
  ext x y
  cases x <;> cases y <;>
    simp [sGate, Matrix.mul_apply, Matrix.diagonal_apply, Complex.conj_I,
      Complex.I_mul_I]

/-- The H gate matrix on any site is unitary. -/
theorem cliffordGateOp_H_unitary (n : ℕ) (i : Fin n) :
    cliffordGateOp n (.H i) ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, cliffordGateOp_H]
  exact single_site_unitary i Hadamard hadamard_mul_self'

/-- The S gate matrix on any site is unitary. -/
theorem cliffordGateOp_S_unitary (n : ℕ) (i : Fin n) :
    cliffordGateOp n (.S i) ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, cliffordGateOp_S]
  exact single_site_unitary i sGate sGate_mul_self'

/-- Conjugation of a Pauli matrix by the H gate on site `i` agrees with
`verifiedCliffordAction`. -/
theorem cliffordGateOp_H_conj {n : ℕ} (i : Fin n) (p : PauliElem n) :
    cliffordGateOp n (.H i) * op p * (cliffordGateOp n (.H i))ᴴ
      = op (verifiedCliffordAction (.H i) p) := by
  have hP1 : productMatrix (fun k => if k = i then Hadamard else (1 : Matrix Bool Bool ℂ))
      * pauliWordOp n p.word
      * productMatrix (fun k => if k = i then Hadamardᴴ else (1 : Matrix Bool Bool ℂ))
      = (Complex.I ^ (conjHPhase (p.word i)).val : ℂ)
          • productMatrix (fun k =>
              if k = i then P1 (conjHWord (p.word i)) else P1 (p.word k)) := by
    rw [pauliWordOp_eq n p.word, prod_if_left, prod_if_right]
    have hsite : (fun k : Fin n =>
          if k = i then (if k = i then Hadamard * P1 (p.word k) else P1 (p.word k))
              * Hadamardᴴ
          else if k = i then Hadamard * P1 (p.word k) else P1 (p.word k))
        = fun k => if k = i then (Complex.I ^ (conjHPhase (p.word i)).val : ℂ)
              • P1 (conjHWord (p.word i)) else P1 (p.word k) := by
      funext k
      by_cases hk : k = i
      · rw [hk, if_pos rfl, if_pos rfl, if_pos rfl]
        exact hadamard_conj_P1 (p.word i)
      · rw [if_neg hk, if_neg hk, if_neg hk]
    rw [hsite, productMatrix_if_smul]
  rw [cliffordGateOp_H, productMatrix_adjoint]
  have hAd : productMatrix (fun k => (if k = i then Hadamard else (1 : Matrix Bool Bool ℂ))ᴴ)
      = productMatrix (fun k => if k = i then Hadamardᴴ else (1 : Matrix Bool Bool ℂ)) := by
    congr 1
    funext k
    by_cases hk : k = i <;> simp [hk, Matrix.conjTranspose_one]
  rw [hAd]
  show productMatrix (fun k => if k = i then Hadamard else (1 : Matrix Bool Bool ℂ))
      * ((Complex.I ^ p.phase.val : ℂ) • pauliWordOp n p.word)
      * productMatrix (fun k => if k = i then Hadamardᴴ else (1 : Matrix Bool Bool ℂ))
    = (Complex.I ^ (p.phase + ∑ k : Fin n,
          (if k = i then conjHPhase (p.word i) else 0)).val : ℂ)
        • pauliWordOp n (fun k => if k = i then conjHWord (p.word i) else p.word k)
  rw [Matrix.mul_assoc, smul_mul_left'', smul_mul_right'', ← Matrix.mul_assoc, hP1,
    smul_smul', sum_ite_single4, I_pow_val_add, pauliWordOp_eq, P1_if]

/-- Conjugation of a Pauli matrix by the S gate on site `i` agrees with
`verifiedCliffordAction`. -/
theorem cliffordGateOp_S_conj {n : ℕ} (i : Fin n) (p : PauliElem n) :
    cliffordGateOp n (.S i) * op p * (cliffordGateOp n (.S i))ᴴ
      = op (verifiedCliffordAction (.S i) p) := by
  have hP1 : productMatrix (fun k => if k = i then sGate else (1 : Matrix Bool Bool ℂ))
      * pauliWordOp n p.word
      * productMatrix (fun k => if k = i then sGateᴴ else (1 : Matrix Bool Bool ℂ))
      = (Complex.I ^ (conjSPhase (p.word i)).val : ℂ)
          • productMatrix (fun k =>
              if k = i then P1 (conjSWord (p.word i)) else P1 (p.word k)) := by
    rw [pauliWordOp_eq n p.word, prod_if_left, prod_if_right]
    have hsite : (fun k : Fin n =>
          if k = i then (if k = i then sGate * P1 (p.word k) else P1 (p.word k))
              * sGateᴴ
          else if k = i then sGate * P1 (p.word k) else P1 (p.word k))
        = fun k => if k = i then (Complex.I ^ (conjSPhase (p.word i)).val : ℂ)
              • P1 (conjSWord (p.word i)) else P1 (p.word k) := by
      funext k
      by_cases hk : k = i
      · rw [hk, if_pos rfl, if_pos rfl, if_pos rfl]
        exact sGate_conj_P1 (p.word i)
      · rw [if_neg hk, if_neg hk, if_neg hk]
    rw [hsite, productMatrix_if_smul]
  rw [cliffordGateOp_S, productMatrix_adjoint]
  have hAd : productMatrix (fun k => (if k = i then sGate else (1 : Matrix Bool Bool ℂ))ᴴ)
      = productMatrix (fun k => if k = i then sGateᴴ else (1 : Matrix Bool Bool ℂ)) := by
    congr 1
    funext k
    by_cases hk : k = i <;> simp [hk, Matrix.conjTranspose_one]
  rw [hAd]
  show productMatrix (fun k => if k = i then sGate else (1 : Matrix Bool Bool ℂ))
      * ((Complex.I ^ p.phase.val : ℂ) • pauliWordOp n p.word)
      * productMatrix (fun k => if k = i then sGateᴴ else (1 : Matrix Bool Bool ℂ))
    = (Complex.I ^ (p.phase + ∑ k : Fin n,
          (if k = i then conjSPhase (p.word i) else 0)).val : ℂ)
        • pauliWordOp n (fun k => if k = i then conjSWord (p.word i) else p.word k)
  rw [Matrix.mul_assoc, smul_mul_left'', smul_mul_right'', ← Matrix.mul_assoc, hP1,
    smul_smul', sum_ite_single4, I_pow_val_add, pauliWordOp_eq, P1_if]

/-- The register transformation preserving site `i` and, when the sites differ, replacing site
`j` by its XOR with site `i`, while preserving all other sites. -/
def cnotT {n : ℕ} (i j : Fin n) (x : Reg n) : Reg n :=
  fun k => if k = i then x i else if k = j then x j ^^ x i else x k

/-- Applying the register transformation `cnotT i j` twice returns the original register, even
when the sites coincide. -/
theorem cnotT_involutive {n : ℕ} (i j : Fin n) : Function.Involutive (cnotT i j) := by
  intro x
  funext k
  by_cases hki : k = i
  · simp [cnotT, hki]
  · by_cases hkj : k = j
    · have hji : j ≠ i := fun h => hki (hkj.trans h)
      simp [cnotT, hkj, hji]
    · simp [cnotT, hki, hkj]

/-- The register transformation `cnotT i j` preserves the bit at the control site `i`. -/
theorem cnotT_apply_self {n : ℕ} (i j : Fin n) (x : Reg n) :
    cnotT i j x i = x i := by
  simp [cnotT]

/-- When `j` differs from `i`, the bit at target site `j` under `cnotT i j` is the XOR of the
original target and control bits. -/
theorem cnotT_apply_other {n : ℕ} (i j : Fin n) (hji : j ≠ i) (x : Reg n) :
    cnotT i j x j = (x j ^^ x i) := by
  simp [cnotT, hji]

/-- For distinct sites, a CNOT matrix entry is one exactly when its row register is `cnotT i j`
of its column register, and zero otherwise. -/
theorem cliffordGateOp_CNOT_apply {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x y : Reg n) :
    cliffordGateOp n (.CNOT i j) x y = if x = cnotT i j y then 1 else 0 := by
  by_cases hrest : ∀ k : Fin n, k ≠ i ∧ k ≠ j → x k = y k
  · have hji : j ≠ i := Ne.symm hij
    by_cases hx : x = cnotT i j y
    · rw [if_pos hx]
      have h1 : x i = y i := by rw [hx]; exact cnotT_apply_self i j y
      have h2 : x j = (y j ^^ y i) := by rw [hx]; exact cnotT_apply_other i j hji y
      simp only [cliffordGateOp, if_pos hrest, CNOT, permMatrix, Matrix.of_apply,
        cnotFlip]
      rw [h1, h2, if_pos rfl]
    · rw [if_neg hx]
      simp only [cliffordGateOp, if_pos hrest, CNOT, permMatrix, Matrix.of_apply,
        cnotFlip]
      have hne : ¬((x i, x j) = (y i, y j ^^ y i)) := by
        intro heq
        rw [Prod.mk.injEq] at heq
        refine hx ?_
        funext k
        by_cases hki : k = i
        · rw [hki]
          simp [cnotT, heq.1]
        · by_cases hkj : k = j
          · rw [hkj]
            simp only [cnotT, if_neg hji]
            exact heq.2
          · simp only [cnotT, if_neg hki, if_neg hkj]
            exact hrest k ⟨hki, hkj⟩
      rw [if_neg hne]
  · have hne : x ≠ cnotT i j y := by
      intro heq
      obtain ⟨k, hk⟩ := Classical.not_forall.mp hrest
      refine hk fun hboth => ?_
      rw [heq]
      simp only [cnotT, if_neg hboth.1, if_neg hboth.2]
    simp only [cliffordGateOp, if_neg hrest, if_neg hne]

/-- For distinct control and target sites, left multiplication by CNOT reindexes the rows of a
matrix by `cnotT i j`. -/
theorem cnot_mul_apply {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (M : Matrix (Reg n) (Reg n) ℂ) (x t : Reg n) :
    (cliffordGateOp n (.CNOT i j) * M) x t = M (cnotT i j x) t := by
  simp only [Matrix.mul_apply, cliffordGateOp_CNOT_apply i j hij]
  have key : ∀ b : Reg n, b ≠ cnotT i j x →
      (if x = cnotT i j b then (1 : ℂ) else 0) * M b t = 0 := by
    intro b hb
    by_cases h : x = cnotT i j b
    · exfalso
      have h1 : cnotT i j x = b := by rw [h, cnotT_involutive i j b]
      exact hb h1.symm
    · rw [if_neg h]
      simp
  rw [Finset.sum_eq_single (cnotT i j x) (fun b _ hb => key b hb)
    (fun h => absurd (Finset.mem_univ _) h), if_pos ((cnotT_involutive i j x).symm),
    one_mul]

/-- A CNOT matrix with distinct control and target sites equals its conjugate transpose. -/
theorem cnot_conjTranspose {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (cliffordGateOp n (.CNOT i j))ᴴ = cliffordGateOp n (.CNOT i j) := by
  ext x y
  rw [Matrix.conjTranspose_apply, cliffordGateOp_CNOT_apply i j hij,
    cliffordGateOp_CNOT_apply i j hij]
  by_cases h : y = cnotT i j x
  · rw [if_pos h, star_one, if_pos (by rw [h, cnotT_involutive i j x])]
  · rw [if_neg h, star_zero, if_neg (fun he => h (by rw [he, cnotT_involutive i j y]))]

/-- A CNOT matrix with distinct control and target sites squares to the identity. -/
theorem cnot_mul_self {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    cliffordGateOp n (.CNOT i j) * cliffordGateOp n (.CNOT i j) = 1 := by
  ext x y
  simp only [Matrix.mul_apply, cliffordGateOp_CNOT_apply i j hij, Matrix.one_apply]
  rw [Finset.sum_eq_single (cnotT i j y)
    (fun b _ hb => by rw [if_neg hb]; simp)
    (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, mul_one,
    cnotT_involutive i j y]

/-- A CNOT matrix with distinct control and target sites is unitary. -/
theorem cliffordGateOp_CNOT_unitary {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    cliffordGateOp n (.CNOT i j) ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    cnot_conjTranspose i j hij]
  exact cnot_mul_self i j hij

/-- For distinct control and target sites, CNOT conjugation reindexes both matrix indices by
`cnotT i j`. -/
theorem cnot_conj_entry {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (M : Matrix (Reg n) (Reg n) ℂ) (x y : Reg n) :
    (cliffordGateOp n (.CNOT i j) * M * (cliffordGateOp n (.CNOT i j))ᴴ) x y
      = M (cnotT i j x) (cnotT i j y) := by
  have h2 : ∀ t : Reg n, ((cliffordGateOp n (.CNOT i j))ᴴ) t y
      = (if y = cnotT i j t then (1 : ℂ) else 0) := by
    intro t
    rw [Matrix.conjTranspose_apply, cliffordGateOp_CNOT_apply i j hij]
    by_cases h : y = cnotT i j t <;> simp [h]
  rw [Matrix.mul_apply]
  simp only [cnot_mul_apply i j hij M x, h2]
  rw [Finset.sum_eq_single (cnotT i j y)
    (fun b _ hb => by
      rw [if_neg (fun he => hb (by rw [he, cnotT_involutive i j b]))]
      simp)
    (fun h => absurd (Finset.mem_univ _) h),
    if_pos ((cnotT_involutive i j y).symm), mul_one]

/-- The two-site Pauli matrix entries after the CNOT bit transformation equal the updated Pauli
entries multiplied by the phase specified by `cnotPhaseCorrection`. -/
theorem P1_cnot_core (a b : Pauli1) (c d c' d' : Bool) :
    P1 a c c' * P1 b (d ^^ c) (d' ^^ c')
      = (Complex.I ^ (cnotPhaseCorrection a b).val : ℂ)
          * (P1 (pauliMul1 a (cnotTargetCross b)) c c'
              * P1 (pauliMul1 (cnotControlCross a) b) d d') := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases c' <;> cases d' <;>
    simp [P1, pauliMul1, cnotPhaseCorrection, cnotTargetCross, cnotControlCross,
      zmod4_val_two, Complex.I_mul_I]

/-- A Pauli element's matrix entry is its global phase multiplied by the product of its
single-site Pauli matrix entries. -/
theorem op_apply {n : ℕ} (p : PauliElem n) (x y : Reg n) :
    op p x y = (Complex.I ^ p.phase.val : ℂ) * ∏ k, P1 (p.word k) (x k) (y k) := by
  simp only [op, Matrix.smul_apply, smul_eq_mul, pauliWordOp_eq, productMatrix]

/-- If two families agree away from two distinct sites and their two selected factors differ by
a scalar `c`, their full products differ by the same scalar. -/
theorem prod_mod_two {n : ℕ} (i j : Fin n) (hij : i ≠ j) (f g : Fin n → ℂ) (c : ℂ)
    (hi : f i * f j = c * g i * g j)
    (hrest : ∀ k, k ≠ i ∧ k ≠ j → f k = g k) :
    ∏ k, f k = c * ∏ k, g k := by
  have hji : j ≠ i := Ne.symm hij
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  have hrestf : ∏ k ∈ (Finset.univ.erase i).erase j, f k
      = ∏ k ∈ (Finset.univ.erase i).erase j, g k := by
    refine Finset.prod_congr rfl fun k hk => hrest k ?_
    simp only [Finset.mem_erase, Finset.mem_univ] at hk
    exact ⟨hk.2.1, hk.1⟩
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) f hjmem,
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) g hjmem, ← mul_assoc, hi, hrestf]
  ring

/-- For distinct control and target sites, conjugation of a Pauli matrix by CNOT agrees with
`verifiedCliffordAction`, including its phase correction [DehaeneDeMoor2003]. -/
theorem cliffordGateOp_CNOT_conj {n : ℕ} (i j : Fin n) (hij : i ≠ j) (p : PauliElem n) :
    cliffordGateOp n (.CNOT i j) * op p * (cliffordGateOp n (.CNOT i j))ᴴ
      = op (verifiedCliffordAction (.CNOT i j) p) := by
  ext x y
  rw [cnot_conj_entry i j hij, op_apply, op_apply]
  have hji : j ≠ i := Ne.symm hij
  show (Complex.I ^ p.phase.val : ℂ) * ∏ k, P1 (p.word k) (cnotT i j x k) (cnotT i j y k)
      = (Complex.I ^ (p.phase + cnotPhaseCorrection (p.word i) (p.word j)).val : ℂ)
        * ∏ k, P1 (if k = i then pauliMul1 (p.word i) (cnotTargetCross (p.word j))
              else if k = j then pauliMul1 (cnotControlCross (p.word i)) (p.word j)
              else p.word k) (x k) (y k)
  have hprod : ∏ k, P1 (p.word k) (cnotT i j x k) (cnotT i j y k)
      = (Complex.I ^ (cnotPhaseCorrection (p.word i) (p.word j)).val : ℂ)
        * ∏ k, P1 (if k = i then pauliMul1 (p.word i) (cnotTargetCross (p.word j))
              else if k = j then pauliMul1 (cnotControlCross (p.word i)) (p.word j)
              else p.word k) (x k) (y k) := by
    refine prod_mod_two i j hij _ _ _ ?_ ?_
    · rw [cnotT_apply_self i j x, cnotT_apply_self i j y,
        cnotT_apply_other i j hji x, cnotT_apply_other i j hji y,
        if_pos rfl, if_neg hji, if_pos rfl, mul_assoc]
      exact P1_cnot_core (p.word i) (p.word j) (x i) (x j) (y i) (y j)
    · intro k hk
      simp only [cnotT, if_neg hk.1, if_neg hk.2]
  rw [hprod, I_pow_val_add]
  ring

/-- The verified action of CNOT from site zero to one sends phase-zero XZ to YY with phase two,
representing negative YY. -/
theorem vca_cnot_XZ :
    verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 2) 1) ⟨![.X, .Z], 0⟩
      = ⟨![.Y, .Y], 2⟩ := by
  simp only [verifiedCliffordAction, PauliElem.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext k
    fin_cases k <;>
      simp [pauliMul1, cnotTargetCross, cnotControlCross]
  · simp [cnotPhaseCorrection]

/-- The original `cliffordAction` sends phase-zero XZ to phase-zero YY for CNOT from site zero
to one. -/
theorem cliffordAction_cnot_XZ :
    cliffordAction (CliffordGate.CNOT (0 : Fin 2) 1) ⟨![.X, .Z], 0⟩
      = ⟨![.Y, .Y], 0⟩ := by
  simp only [cliffordAction, PauliElem.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext k
    fin_cases k <;> simp [pauliMul1, cnotTargetCross, cnotControlCross]
  · simp

/-- The verified action of CNOT from site zero to one sends phase-zero YY to XZ with phase two,
representing negative XZ. -/
theorem vca_cnot_YY :
    verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 2) 1) ⟨![.Y, .Y], 0⟩
      = ⟨![.X, .Z], 2⟩ := by
  simp only [verifiedCliffordAction, PauliElem.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext k
    fin_cases k <;>
      simp [pauliMul1, cnotTargetCross, cnotControlCross]
  · simp [cnotPhaseCorrection]

/-- The verified action of a one-qubit H gate sends phase-zero Y to Y with phase two,
representing negative Y. -/
theorem vca_H_Y :
    verifiedCliffordAction (CliffordGate.H (0 : Fin 1)) ⟨![.Y], 0⟩
      = ⟨![.Y], 2⟩ := by
  simp only [verifiedCliffordAction, PauliElem.mk.injEq, conjHWord]
  refine ⟨?_, ?_⟩
  · funext k
    fin_cases k; simp
  · simp [conjHPhase]

/-- The verified action of a one-qubit S gate sends phase-zero Y to X with phase two,
representing negative X. -/
theorem vca_S_Y :
    verifiedCliffordAction (CliffordGate.S (0 : Fin 1)) ⟨![.Y], 0⟩
      = ⟨![.X], 2⟩ := by
  simp only [verifiedCliffordAction, PauliElem.mk.injEq, conjSWord]
  refine ⟨?_, ?_⟩
  · funext k
    fin_cases k; simp
  · simp [conjSPhase]

/-- The verified action of CNOT from site one to zero sends phase-zero ZX to YY with phase two,
representing negative YY. -/
theorem vca_cnot_ZX_reversed :
    verifiedCliffordAction (CliffordGate.CNOT (1 : Fin 2) 0) ⟨![.Z, .X], 0⟩
      = ⟨![.Y, .Y], 2⟩ := by
  simp only [verifiedCliffordAction, PauliElem.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext k
    fin_cases k <;>
      simp [pauliMul1, cnotTargetCross, cnotControlCross]
  · simp [cnotPhaseCorrection]

/-- On three qubits, the verified action of CNOT from site zero to two sends phase-zero XIZ to
YIY with phase two. -/
theorem vca_cnot_n3 :
    verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 3) 2) ⟨![.X, .I, .Z], 0⟩
      = ⟨![.Y, .I, .Y], 2⟩ := by
  simp only [verifiedCliffordAction, PauliElem.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext k
    fin_cases k <;>
      simp [pauliMul1, cnotTargetCross, cnotControlCross]
  · simp [cnotPhaseCorrection]

/-- The one-qubit CNOT matrix with both control and target at site zero is not unitary. -/
theorem cnot_same_site_not_unitary :
    ¬ (cliffordGateOp 1 (CliffordGate.CNOT (0 : Fin 1) 0)
        ∈ Matrix.unitaryGroup (Reg 1) ℂ) := by
  intro h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  have e1 : ((cliffordGateOp 1 (CliffordGate.CNOT (0 : Fin 1) 0))ᴴ
      * cliffordGateOp 1 (CliffordGate.CNOT (0 : Fin 1) 0))
      (fun _ => true) (fun _ => true)
      = (1 : Matrix (Reg 1) (Reg 1) ℂ) (fun _ => true) (fun _ => true) := by
    rw [h, Matrix.one_apply_eq]
  have hzero : ∀ t : Reg 1,
      cliffordGateOp 1 (CliffordGate.CNOT (0 : Fin 1) 0) t (fun _ => true) = 0 := by
    intro t
    cases ht : t 0 <;>
      simp [cliffordGateOp, CNOT, permMatrix, cnotFlip, ht]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hzero] at e1
  simp at e1

/-- Combine unitarity and verified Pauli conjugation for every legal Clifford gate with explicit
H, S, and CNOT phase computations [DehaeneDeMoor2003]. The result also records the original
CNOT action on XZ and the failure of unitarity for the one-qubit CNOT with coincident sites. -/
theorem legal_clifford_conjugacy :
    (∀ (n : ℕ) (g : CliffordGate n) (p : PauliElem n),
      legalGate g →
        (cliffordGateOp n g ∈ Matrix.unitaryGroup (Reg n) ℂ)
        ∧ (cliffordGateOp n g * op p * (cliffordGateOp n g)ᴴ
            = op (verifiedCliffordAction g p)))
    ∧ (verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 2) 1) ⟨![.X, .Z], 0⟩
        = ⟨![.Y, .Y], 2⟩
      ∧ cliffordAction (CliffordGate.CNOT (0 : Fin 2) 1) ⟨![.X, .Z], 0⟩
        = ⟨![.Y, .Y], 0⟩
      ∧ verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 2) 1) ⟨![.Y, .Y], 0⟩
        = ⟨![.X, .Z], 2⟩)
    ∧ (verifiedCliffordAction (CliffordGate.H (0 : Fin 1)) ⟨![.Y], 0⟩ = ⟨![.Y], 2⟩
      ∧ verifiedCliffordAction (CliffordGate.S (0 : Fin 1)) ⟨![.Y], 0⟩
        = ⟨![.X], 2⟩)
    ∧ (verifiedCliffordAction (CliffordGate.CNOT (1 : Fin 2) 0) ⟨![.Z, .X], 0⟩
        = ⟨![.Y, .Y], 2⟩
      ∧ verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 3) 2) ⟨![.X, .I, .Z], 0⟩
        = ⟨![.Y, .I, .Y], 2⟩)
    ∧ ¬ (cliffordGateOp 1 (CliffordGate.CNOT (0 : Fin 1) 0)
        ∈ Matrix.unitaryGroup (Reg 1) ℂ) := by
  refine ⟨?_, ⟨vca_cnot_XZ, cliffordAction_cnot_XZ, vca_cnot_YY⟩,
    ⟨vca_H_Y, vca_S_Y⟩, ⟨vca_cnot_ZX_reversed, vca_cnot_n3⟩,
    cnot_same_site_not_unitary⟩
  intro n g p hg
  cases g with
  | H i => exact ⟨cliffordGateOp_H_unitary n i, cliffordGateOp_H_conj i p⟩
  | S i => exact ⟨cliffordGateOp_S_unitary n i, cliffordGateOp_S_conj i p⟩
  | CNOT i j =>
    have hij : i ≠ j := hg
    exact ⟨cliffordGateOp_CNOT_unitary i j hij, cliffordGateOp_CNOT_conj i j hij p⟩

end Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
