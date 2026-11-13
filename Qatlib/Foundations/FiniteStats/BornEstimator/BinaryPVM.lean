/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.BornLaw
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Joint measurements from binary projectors

This module constructs products of binary matrix families through `binaryProduct`. Commuting
Hermitian idempotents give positive semidefinite products, while pairwise normalization gives a
sum equal to the identity and explicit signed marginals.

The construction `binaryJointPOVM` packages these products as a finite POVM. It supplies the
joint-measurement algebra used in context-based estimation as in [XuEtAl2026].

## Main statements

* `binaryProduct_psd`: A binary product of pairwise commuting Hermitian idempotents is positive
  semidefinite.
* `binaryProduct_marginal`: If each binary pair sums to the identity, the signed marginal at
  coordinate `i` equals `F i false - F i true`.
* `binaryJointPOVM`: The joint POVM whose effects are the binary products of commuting Hermitian
  complementary idempotents.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators ComplexOrder
open Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The sign encoding that sends `false` to one and `true` to minus one. -/
def binarySign (b : Bool) : ℝ := if b then -1 else 1

/-- The square of a binary sign equals one. -/
theorem binarySign_sq (b : Bool) : binarySign b^2=1 := by cases b <;> norm_num [binarySign]

/-- A sum over Boolean strings of length `n+1` splits into a sum over the first bit and the
remaining string. -/
theorem sum_binary_cons {R : Type*} [AddCommMonoid R] (n : ℕ) (f : (Fin (n+1) → Bool) → R) :
    (∑ s,f s)=∑ b : Bool,∑ t : Fin n → Bool,f (Fin.cons b t) := by
  calc _ = ∑ p : Bool×(Fin n → Bool),f (Fin.cons p.1 p.2) :=
           (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)) _ _ (by intro p;rfl)).symm
       _ = _ := Fintype.sum_prod_type _

/-- The ordered product of the matrices selected by a Boolean string, with the empty product
equal to the identity. -/
def binaryProduct : (n : ℕ) → (Fin n → Bool → Matrix d d ℂ) → (Fin n → Bool) → Matrix d d ℂ
  | 0,_,_ => 1
  | n+1,F,s => F 0 (s 0)*binaryProduct n (fun i => F i.succ) (fun i => s i.succ)

/-- A matrix commuting with every selected factor commutes with their binary product. -/
theorem commute_binaryProduct (n : ℕ) (F : Fin n → Bool → Matrix d d ℂ) (s : Fin n → Bool)
    (A : Matrix d d ℂ) (h : ∀ i,Commute A (F i (s i))) : Commute A (binaryProduct n F s) := by
  induction n with
  | zero => exact Commute.one_right A
  | succ n ih => exact (h 0).mul_right (ih (fun i => F i.succ) (fun i => s i.succ) (fun i => h i.succ))

/-- A binary product of pairwise commuting Hermitian factors is Hermitian. -/
theorem binaryProduct_hermitian (n : ℕ) (F : Fin n → Bool → Matrix d d ℂ)
    (hH : ∀ i b,(F i b)ᴴ=F i b) (hC : ∀ i b j c,Commute (F i b) (F j c)) (s : Fin n → Bool) :
    (binaryProduct n F s)ᴴ=binaryProduct n F s := by
  induction n with
  | zero => simp [binaryProduct]
  | succ n ih =>
    change (F 0 (s 0)*binaryProduct n (fun i => F i.succ) (fun i => s i.succ))ᴴ=_
    rw [Matrix.conjTranspose_mul,hH,ih (fun i => F i.succ) (fun i => hH i.succ) (fun i b j c => hC i.succ b j.succ c)]
    exact (commute_binaryProduct n _ _ (F 0 (s 0)) (fun i => hC 0 (s 0) i.succ (s i.succ))).eq.symm

/-- A binary product of pairwise commuting idempotent factors is idempotent. -/
theorem binaryProduct_idempotent (n : ℕ) (F : Fin n → Bool → Matrix d d ℂ)
    (hI : ∀ i b,F i b*F i b=F i b) (hC : ∀ i b j c,Commute (F i b) (F j c)) (s : Fin n → Bool) :
    binaryProduct n F s*binaryProduct n F s=binaryProduct n F s := by
  induction n with
  | zero => simp [binaryProduct]
  | succ n ih =>
    have ht :=
        ih (fun i => F i.succ) (fun i => hI i.succ) (fun i b j c => hC i.succ b j.succ c)
        (fun i => s i.succ)
    have hc := commute_binaryProduct n (fun i => F i.succ) (fun i => s i.succ)
      (F 0 (s 0)) (fun i => hC 0 (s 0) i.succ (s i.succ))
    rw [← pow_two]
    change (F 0 (s 0)*binaryProduct n (fun i => F i.succ) (fun i => s i.succ))^2=_
    rw [hc.mul_pow,pow_two,pow_two,hI,ht]
    rfl

/-- A binary product of pairwise commuting Hermitian idempotents is positive semidefinite. -/
theorem binaryProduct_psd (n : ℕ) (F : Fin n → Bool → Matrix d d ℂ)
    (hH : ∀ i b,(F i b)ᴴ=F i b) (hI : ∀ i b,F i b*F i b=F i b)
    (hC : ∀ i b j c,Commute (F i b) (F j c)) (s : Fin n → Bool) :
    (binaryProduct n F s).PosSemidef := by
  have hg := Matrix.posSemidef_conjTranspose_mul_self (binaryProduct n F s)
  rw [binaryProduct_hermitian n F hH hC s,binaryProduct_idempotent n F hI hC s] at hg
  exact hg

/-- If each binary pair sums to the identity, the sum of all binary products is the identity. -/
theorem binaryProduct_normalized (n : ℕ) (F : Fin n → Bool → Matrix d d ℂ)
    (hN : ∀ i,F i false+F i true=1) : ∑ s,binaryProduct n F s=1 := by
  induction n with
  | zero => simp [binaryProduct]
  | succ n ih =>
    rw [sum_binary_cons]
    simp only [binaryProduct,Fin.cons_zero,Fin.cons_succ]
    simp_rw [← Finset.mul_sum,ih (fun i => F i.succ) (fun i => hN i.succ),mul_one]
    simpa only [Fintype.sum_bool,add_comm] using hN 0

/-- If each binary pair sums to the identity, the signed marginal at coordinate `i` equals `F i
false - F i true`. -/
theorem binaryProduct_marginal (n : ℕ) (F : Fin n → Bool → Matrix d d ℂ)
    (hN : ∀ i,F i false+F i true=1) (i : Fin n) :
    (∑ s,binarySign (s i) • binaryProduct n F s)=F i false-F i true := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sum_binary_cons]
      simp only [binaryProduct,Fin.cons_zero,Fin.cons_succ]
      simp_rw [← smul_mul_assoc,← Finset.mul_sum,binaryProduct_normalized n _ (fun i => hN i.succ),mul_one]
      simp [binarySign,sub_eq_add_neg,add_comm]
    · rw [sum_binary_cons]
      simp only [binaryProduct,Fin.cons_succ,Fin.cons_zero]
      simp only [← mul_smul_comm]
      simp only [← Finset.mul_sum,ih (fun i => F i.succ) (fun i => hN i.succ) j]
      have hn : (∑ b : Bool,F 0 b)=1 := by simpa only [Fintype.sum_bool,add_comm] using hN 0
      rw [← Finset.sum_mul,hn,one_mul]

/-- For complementary idempotents `A` and `B`, their difference acts on the branch selected by
`b` with eigenvalue `binarySign b`. -/
theorem binary_difference_action (A B : Matrix d d ℂ) (hA : A*A=A) (hB : B*B=B)
    (hN : A+B=1) (b : Bool) : (A-B)*(if b then B else A)=binarySign b • (if b then B else A) := by
  have hAB : A*B=0 := by
    have h := congrArg (fun X : Matrix d d ℂ => X*B) hN
    change (A+B)*B=1*B at h
    rw [add_mul,hB,one_mul] at h
    exact add_right_cancel (show A*B+B=0+B by simpa only [zero_add] using h)
  have hBA : B*A=0 := by
    have h := congrArg (fun X : Matrix d d ℂ => X*A) hN
    change (A+B)*A=1*A at h
    rw [add_mul,hA,one_mul] at h
    exact add_left_cancel (show A+B*A=A+0 by simpa only [add_zero] using h)
  cases b <;> simp [binarySign,sub_mul,hA,hB,hAB,hBA]

/-- For commuting complementary idempotent pairs, the difference at a coordinate acts on a
binary product with the sign of that coordinate. -/
theorem binaryProduct_coordinate_action (n : ℕ) (F : Fin n → Bool → Matrix d d ℂ)
    (hI : ∀ i b,F i b*F i b=F i b) (hC : ∀ i b j c,Commute (F i b) (F j c))
    (hN : ∀ i,F i false+F i true=1) (i : Fin n) (s : Fin n → Bool) :
    (F i false-F i true)*binaryProduct n F s=binarySign (s i) • binaryProduct n F s := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (F 0 false-F 0 true)*(F 0 (s 0)*binaryProduct n (fun i => F i.succ) (fun i => s i.succ))=_
      have he :=
          binary_difference_action (F 0 false) (F 0 true) (hI 0 false) (hI 0 true) (hN 0) (s 0)
      have he' : (F 0 false-F 0 true)*F 0 (s 0)=binarySign (s 0) • F 0 (s 0) := by
        cases hs : s 0 <;> simpa only [hs,ite_false,ite_true] using! he
      rw [← mul_assoc,he',smul_mul_assoc]
      rfl
    · change (F j.succ false-F j.succ true)*(F 0 (s 0)*binaryProduct n (fun i => F i.succ) (fun i => s i.succ))=_
      have hc : (F j.succ false-F j.succ true)*F 0 (s 0)=F 0 (s 0)*(F j.succ false-F j.succ true) := by
        rw [sub_mul,mul_sub,(hC j.succ false 0 (s 0)).eq,(hC j.succ true 0 (s 0)).eq]
      rw [← mul_assoc,hc,mul_assoc,ih (fun i => F i.succ) (fun i => hI i.succ)
        (fun i a j b => hC i.succ a j.succ b) (fun i => hN i.succ) j (fun i => s i.succ),mul_smul_comm]
      rfl

/-- The joint POVM whose effects are the binary products of commuting Hermitian complementary
idempotents. -/
def binaryJointPOVM (n : ℕ) (F : Fin n → Bool → Matrix d d ℂ)
    (hH : ∀ i b,(F i b)ᴴ=F i b) (hI : ∀ i b,F i b*F i b=F i b)
    (hC : ∀ i b j c,Commute (F i b) (F j c)) (hN : ∀ i,F i false+F i true=1) :
    POVM (Fin n → Bool) d where
  mats s := ⟨binaryProduct n F s,binaryProduct_hermitian n F hH hC s⟩
  nonneg s := HermitianMat.zero_le_iff.mpr (binaryProduct_psd n F hH hI hC s)
  normalized := by
    apply HermitianMat.ext
    simpa only [HermitianMat.mat_finset_sum,HermitianMat.mat_mk] using!
        binaryProduct_normalized n F hN

end Qatlib.Foundations.FiniteStats.BornEstimator
