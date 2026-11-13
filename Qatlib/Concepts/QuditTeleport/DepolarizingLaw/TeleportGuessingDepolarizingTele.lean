/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.DepolarizingLaw.TeleportGuessingDepolarizingStat

/-!
# Uncorrected teleportation is depolarizing

The entry formulas for permutation and Weyl conjugations show that summing all uncorrected qudit
branches removes off-diagonal entries and averages the diagonal. `teleportGuessingDepolarizing`
packages this depolarizing law together with its qubit specialization. The law describes the
receiver's information before the classical teleportation message arrives
[BennettEtAl1993Teleportation].

## Main statements

* `qudit_guessing_depolarizing`: Summing all uncorrected qudit branches sends `ρ` to `(trace ρ /
  n) • 1`.
* `teleportGuessingDepolarizing`: The uncorrected qubit and qudit teleportation branches sum to
  the completely depolarizing map. This expresses loss of the input without the classical
  outcome [BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.DepolarizingLaw
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- Conjugating by a permutation matrix reindexes both matrix coordinates by the inverse
permutation. -/
private theorem perm_conj_entry {I : Type} [Fintype I] [DecidableEq I]
    (e : I ≃ I) (ρ : Matrix I I ℂ) (k l : I) :
    (permMatrix e*ρ*(permMatrix e)ᴴ) k l=ρ (e.symm k) (e.symm l) := by
  rw [qudit_perm_adjoint]
  have he (j : I) : k=e j ↔ j=e.symm k := by
    rw [eq_comm]
    exact e.apply_eq_iff_eq_symm_apply
  simp [Matrix.mul_apply,permMatrix,he]

/-- Conjugation by `quditX n b * quditZ n a` shifts both indices and multiplies the entry by the
additive character of their phase difference. -/
private theorem weyl_conj_entry (n : ℕ) [NeZero n] (b a : ZMod n)
    (ρ : Operator n) (k l : Fin n) :
    ((quditX n b*quditZ n a)*ρ*(quditX n b*quditZ n a)ᴴ) k l=
      ZMod.stdAddChar (a*((ZMod.finEquiv n) k-(ZMod.finEquiv n) l))*
        ρ ((quditShiftEquiv n b).symm k) ((quditShiftEquiv n b).symm l) := by
  rw [Matrix.conjTranspose_mul]
  have he : (quditX n b*quditZ n a)*ρ*((quditZ n a)ᴴ*(quditX n b)ᴴ)=
      quditX n b*(quditZ n a*ρ*(quditZ n a)ᴴ)*(quditX n b)ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [he,quditX_perm,perm_conj_entry,quditZ_adjoint]
  simp only [quditZ,Matrix.mul_diagonal,Matrix.diagonal_mul]
  simp only [quditShiftEquiv,Equiv.coe_fn_symm_mk,
    RingEquiv.apply_symm_apply]
  rw [mul_comm (ZMod.stdAddChar _) (ρ _ _),mul_assoc,
    ← AddChar.map_add_eq_mul]
  have hp : a*((ZMod.finEquiv n) k-b)+(-a)*((ZMod.finEquiv n) l-b)=
      a*((ZMod.finEquiv n) k-(ZMod.finEquiv n) l) := by ring
  rw [hp]
  ring

/-- An uncorrected qudit branch has entries given by a shifted input entry times its outcome
phase and the factor `1 / n²`. -/
private theorem raw_branch_entry (n : ℕ) [NeZero n] (o : Fin n × Fin n)
    (ρ : Operator n) (k l : Fin n) :
    conjBranch (quditBranchKraus n o) ρ k l=
      (1/(n : ℂ))^2*(ZMod.stdAddChar (-((ZMod.finEquiv n) o.1)*
        ((ZMod.finEquiv n) k-(ZMod.finEquiv n) l))*
        ρ ((quditShiftEquiv n ((ZMod.finEquiv n) o.2)).symm k)
          ((quditShiftEquiv n ((ZMod.finEquiv n) o.2)).symm l)) := by
  simp only [conjBranch_apply,quditBranchKraus_formula,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.smul_apply,weyl_conj_entry]
  simp [smul_eq_mul,pow_two]

/-- Summing all uncorrected qudit branches sends `ρ` to `(trace ρ / n) • 1`. -/
private theorem qudit_guessing_depolarizing (n : ℕ) [NeZero n] (ρ : Operator n) :
    (∑ o : Fin n × Fin n, conjBranch (quditBranchKraus n o) ρ)=
      (Matrix.trace ρ/(n : ℂ)) • (1 : Operator n) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  ext k l
  have hchar : (∑ a : Fin n, ZMod.stdAddChar (-((ZMod.finEquiv n) a)*
      ((ZMod.finEquiv n) k-(ZMod.finEquiv n) l)))=if k=l then (n : ℂ) else 0 := by
    calc
      _ = ∑ a : ZMod n, ZMod.stdAddChar (-((ZMod.finEquiv n) k-(ZMod.finEquiv n) l)*a) := by
        rw [← (ZMod.finEquiv n).sum_comp]
        apply Finset.sum_congr rfl
        intro a _
        congr 1
        change -((ZMod.finEquiv n) a)*((ZMod.finEquiv n) k-(ZMod.finEquiv n) l)=
          -((ZMod.finEquiv n) k-(ZMod.finEquiv n) l)*(ZMod.finEquiv n) a
        ring
      _ = _ := by
        rw [sum_stdAddChar_mul]
        simp only [neg_eq_zero,sub_eq_zero,(ZMod.finEquiv n).injective.eq_iff]
  have hdiag : (∑ b : Fin n,
      ρ ((quditShiftEquiv n ((ZMod.finEquiv n) b)).symm k)
        ((quditShiftEquiv n ((ZMod.finEquiv n) b)).symm k))=Matrix.trace ρ := by
    let e : Fin n ≃ Fin n :=
      { toFun := fun b => (ZMod.finEquiv n).symm ((ZMod.finEquiv n) k-(ZMod.finEquiv n) b)
        invFun := fun j => (ZMod.finEquiv n).symm ((ZMod.finEquiv n) k-(ZMod.finEquiv n) j)
        left_inv := by intro b; simp
        right_inv := by intro j; simp }
    simpa [e,quditShiftEquiv,Matrix.trace,Matrix.diag_apply] using
      e.sum_comp (fun j => ρ j j)
  simp only [Matrix.sum_apply,raw_branch_entry,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul,hchar]
  by_cases hkl : k=l
  · subst l
    simp only [ite_true,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one]
    rw [← Finset.mul_sum,hdiag]
    field_simp
  · simp [hkl,Matrix.smul_apply,Matrix.one_apply_ne hkl]

/-- The uncorrected qubit and qudit teleportation branches sum to the completely depolarizing
map. This expresses loss of the input without the classical outcome
[BennettEtAl1993Teleportation]. -/
theorem teleportGuessingDepolarizing : TeleportGuessingDepolarizing := by
  constructor
  · intro ρ
    ext i j
    simp only [Matrix.sum_apply,Fintype.sum_prod_type,Fintype.sum_bool,
      bell_decoded_branch_operators.2]
    fin_cases i <;> fin_cases j <;>
      norm_num [conjBranch_apply,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
        Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,Matrix.smul_apply,
        PauliX,PauliZ,permMatrix,Matrix.one_apply,Matrix.diagonal_apply,boolEquivFin2,
        RCLike.star_def,Matrix.trace,Matrix.diag_apply] <;> ring
  · exact qudit_guessing_depolarizing

end Qatlib.Concepts.QuditTeleport.DepolarizingLaw
