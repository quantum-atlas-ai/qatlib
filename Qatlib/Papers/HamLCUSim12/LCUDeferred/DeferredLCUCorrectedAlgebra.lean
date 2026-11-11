/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedAlgebra

/-!
# Algebra of corrected deferred LCU circuits

This module proves algebraic properties of the corrected deferred LCU gates used to implement
the construction of [ChildsWiebe2012]. `PreservesLCUBit` expresses block diagonality in an
ancilla bit, while `IndependentLCUBit` expresses invariance under simultaneously flipping that
bit in the row and column indices.

These properties propagate through corrected rotations, controlled gates, and chains. The
unitarity results require unitary system matrices, positive chain weights, and the stated
conditions ensuring that the control bits are preserved.

## Main statements

* `ctrlGateCorrected_unitary` and `lcuLevelGateCorrected_unitary` establish unitarity when both
  branches preserve the control bit.
* `chainFoldCorrected_preserves` and `chainFoldCorrected_independent` propagate the two bit
  properties along a chain.
* `chainCircuitCorrected_unitary` proves unitarity for positive weights, unitary payloads, and
  pairwise distinct listed bits.

## References

- [Childs and Wiebe, 2012][ChildsWiebe2012], Lemma 2 and Theorem 3.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- A matrix preserves ancilla bit `i` when every entry connecting row and column strings with
different values at `i` is zero. -/
def PreservesLCUBit {k : ℕ} (i : Fin k) (C : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) : Prop :=
  ∀ p q,p.1 i≠q.1 i→C p q=0

omit [Fintype I] in

/-- Evaluates a corrected rotation entry as the corresponding entry of `V` on the selected bit,
multiplied by the indicator that all other ancilla bits and the system indices agree. -/
theorem rotGateCorrected_apply {k : ℕ} (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : (Fin k→Bool)×I) :
    rotGateCorrected k i V p q = V (boolEquivFin2 (p.1 i)) (boolEquivFin2 (q.1 i))*
      (if (∀ j : Fin k,j≠i→p.1 j=q.1 j) ∧ p.2=q.2 then 1 else 0) := by
  change V (boolEquivFin2 (p.1 i)) (boolEquivFin2 (q.1 i))*
    (if ((fun j : {j : Fin k //j≠i}=>p.1 j),p.2)=((fun j : {j : Fin k //j≠i}=>q.1 j),q.2) then 1 else 0)=_
  simp only [Prod.mk.injEq,funext_iff,Subtype.forall]

omit [Fintype I] [DecidableEq I] in

/-- A lifted system matrix preserves every ancilla bit. -/
theorem preservesLCUBit_liftSys {k : ℕ} (i : Fin k) (U : Matrix I I ℂ) :
    PreservesLCUBit i (liftSys k U) := by
  intro p q h
  have hne : p.1≠q.1 := fun he=>h (congrFun he i)
  simp [liftSys,hne]

omit [Fintype I] in

/-- A corrected rotation on bit `i` preserves each distinct ancilla bit `j`. -/
theorem preservesLCUBit_rot_other {k : ℕ} (i j : Fin k) (hji : j≠i)
    (V : Matrix (Fin 2) (Fin 2) ℂ) : PreservesLCUBit j (rotGateCorrected (I := I) k i V) := by
  intro p q h
  rw [rotGateCorrected_apply]
  have hn : ¬((∀ l : Fin k,l≠i→p.1 l=q.1 l) ∧ p.2=q.2) := fun he=>h (he.1 j hji)
  rw [if_neg hn,mul_zero]

omit [Fintype I] [DecidableEq I] in

/-- The corrected controlled gate preserves its selected control bit, for arbitrary branch
matrices. -/
theorem preservesLCUBit_ctrl {k : ℕ} (i : Fin k)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) :
    PreservesLCUBit i (ctrlGateCorrected k i Cx Cy) := by
  intro p q h
  simp [ctrlGateCorrected,h]

omit [Fintype I] [DecidableEq I] in

/-- If both branch matrices preserve bit `j`, their corrected controlled gate also preserves bit
`j`. -/
theorem preservesLCUBit_ctrl_other {k : ℕ} (i j : Fin k)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hx : PreservesLCUBit j Cx) (hy : PreservesLCUBit j Cy) :
    PreservesLCUBit j (ctrlGateCorrected k i Cx Cy) := by
  intro p q h
  simp only [ctrlGateCorrected,Matrix.of_apply]
  split_ifs <;> first | exact hx p q h | exact hy p q h | rfl

omit [DecidableEq I] in

/-- The product of two matrices preserving the same ancilla bit also preserves that bit. -/
theorem preservesLCUBit_mul {k : ℕ} (i : Fin k)
    (A B : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (ha : PreservesLCUBit i A) (hb : PreservesLCUBit i B) :
    PreservesLCUBit i (A*B) := by
  intro p q hpq
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hpr : p.1 i=r.1 i
  · have hrq : r.1 i≠q.1 i := by rw [← hpr]; exact hpq
    rw [hb r q hrq,mul_zero]
  · rw [ha p r hpr,zero_mul]

omit [Fintype I] [DecidableEq I] in

/-- Taking the conjugate transpose preserves the property of preserving a specified ancilla bit. -/
theorem preservesLCUBit_adjoint {k : ℕ} (i : Fin k)
    (A : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (ha : PreservesLCUBit i A) :
    PreservesLCUBit i Aᴴ := by
  intro p q hpq
  simp only [Matrix.conjTranspose_apply,ha q p (Ne.symm hpq),star_zero]

/-- The corrected controlled gate is unitary when both branch matrices are unitary and preserve
its control bit. -/
theorem ctrlGateCorrected_unitary {k : ℕ} (i : Fin k)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hx : Cx∈Matrix.unitaryGroup _ ℂ) (hy : Cy∈Matrix.unitaryGroup _ ℂ)
    (hpx : PreservesLCUBit i Cx) (hpy : PreservesLCUBit i Cy) :
    ctrlGateCorrected k i Cx Cy∈Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext p q
  by_cases hpq : p.1 i=q.1 i
  · let A := if p.1 i then Cy else Cx
    have hA : A∈Matrix.unitaryGroup _ ℂ := by dsimp [A]; split_ifs <;> assumption
    have hAp : PreservesLCUBit i A := by dsimp [A]; split_ifs <;> assumption
    have he (r s : (Fin k→Bool)×I) (hs : p.1 i=s.1 i) : ctrlGateCorrected k i Cx Cy r s=A r s := by
      by_cases hrs : r.1 i=s.1 i
      · have hrp : r.1 i=p.1 i := hrs.trans hs.symm
        simp only [ctrlGateCorrected,Matrix.of_apply,hrp,if_pos hs,A]
      · simp only [ctrlGateCorrected,Matrix.of_apply,if_neg hrs]
        exact (hAp r s hrs).symm
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
    simp_rw [he _ p rfl,he _ q hpq]
    have hh := Unitary.star_mul_self_of_mem hA
    exact congrArg (fun M : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ=>M p q) hh
  · have hpres := preservesLCUBit_ctrl (I := I) i Cx Cy
    rw [preservesLCUBit_mul i _ _ (preservesLCUBit_adjoint i _ hpres) hpres p q hpq]
    have hne : p≠q := fun he=>hpq (congrArg (fun t=>t.1 i) he)
    simp [hne]

/-- Lifting a unitary two-dimensional matrix to the selected ancilla bit gives a unitary
corrected rotation. -/
theorem rotGateCorrected_unitary {k : ℕ} (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (hV : V∈Matrix.unitaryGroup _ ℂ) :
    rotGateCorrected (I := I) k i V∈Matrix.unitaryGroup _ ℂ := by
  exact (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary hV (Submonoid.one_mem _))

/-- For nonnegative `κ`, a corrected LCU level using `vKappaSource κ` is unitary when both
branches are unitary and preserve the control bit. -/
theorem lcuLevelGateCorrected_unitary {k : ℕ} (i : Fin k) (κ : ℝ) (hκ : 0≤κ)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hx : Cx∈Matrix.unitaryGroup _ ℂ) (hy : Cy∈Matrix.unitaryGroup _ ℂ)
    (hpx : PreservesLCUBit i Cx) (hpy : PreservesLCUBit i Cy) :
    lcuLevelGateCorrected k i (vKappaSource κ) Cx Cy∈Matrix.unitaryGroup _ ℂ := by
  have hv := vKappaSource_unitary κ hκ
  have hv' : (vKappaSource κ)ᴴ∈Matrix.unitaryGroup _ ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hv
  exact mul_mem (rotGateCorrected_unitary i _ hv')
    (mul_mem (ctrlGateCorrected_unitary i Cx Cy hx hy hpx hpy) (rotGateCorrected_unitary i _ hv))

/-- A corrected LCU level on bit `i` preserves a distinct bit `j` whenever both branches
preserve `j`. -/
theorem preservesLCUBit_level_other {k : ℕ} (i j : Fin k) (hji : j≠i)
    (V : Matrix (Fin 2) (Fin 2) ℂ)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hx : PreservesLCUBit j Cx) (hy : PreservesLCUBit j Cy) :
    PreservesLCUBit j (lcuLevelGateCorrected k i V Cx Cy) := by
  exact preservesLCUBit_mul j _ _ (preservesLCUBit_rot_other i j hji Vᴴ)
    (preservesLCUBit_mul j _ _ (preservesLCUBit_ctrl_other i j Cx Cy hx hy)
      (preservesLCUBit_rot_other i j hji V))

/-- The corrected chain fold preserves bit `j` if the initial accumulator preserves `j` and no
listed level uses `j` as its control bit. -/
theorem chainFoldCorrected_preserves {k : ℕ} (j : Fin k)
    (L : List (Fin k×(ℝ×Matrix I I ℂ))) (W : ℝ)
    (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hL : ∀ t∈L,j≠t.1) (hacc : PreservesLCUBit j acc) :
    PreservesLCUBit j (chainFoldCorrected k W acc L) := by
  induction L generalizing W acc with
  | nil => exact hacc
  | cons t L ih =>
    rcases t with ⟨bit,w,U⟩
    apply ih (W+w) (chainGateCorrected k bit W w acc U)
    · intro t ht; exact hL t (List.mem_cons_of_mem _ ht)
    · exact preservesLCUBit_level_other bit j (hL _ (List.mem_cons_self)) _ _ _ hacc
        (preservesLCUBit_liftSys j U)

/-- The corrected chain fold is unitary for a positive initial weight, positive listed weights,
unitary payloads and accumulator, pairwise distinct listed bits, and an accumulator
preserving every listed bit. -/
theorem chainFoldCorrected_unitary {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ))) (W : ℝ)
    (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hW : 0<W) (hacc : acc∈Matrix.unitaryGroup _ ℂ)
    (hweight : ∀ t∈L,0<t.2.1) (hU : ∀ t∈L,t.2.2∈Matrix.unitaryGroup I ℂ)
    (hfresh : ∀ t∈L,PreservesLCUBit t.1 acc)
    (hbits : L.Pairwise (fun a b=>a.1≠b.1)) :
    chainFoldCorrected k W acc L∈Matrix.unitaryGroup _ ℂ := by
  induction L generalizing W acc with
  | nil => exact hacc
  | cons t L ih =>
    rcases t with ⟨bit,w,U⟩
    have hw : 0<w := hweight _ (List.mem_cons_self)
    have hU0 : U∈Matrix.unitaryGroup I ℂ := hU _ (List.mem_cons_self)
    have hlu : liftSys k U∈Matrix.unitaryGroup _ ℂ := by
      have he : liftSys k U=TensorGate (1 : Matrix (Fin k→Bool) (Fin k→Bool) ℂ) U := by
        ext p q
        by_cases h : p.1=q.1 <;> simp [liftSys,TensorGate,Matrix.one_apply,h]
      rw [he]
      exact tensorGate_unitary (Submonoid.one_mem _) hU0
    have hpairs := List.pairwise_cons.mp hbits
    apply ih (W+w) (chainGateCorrected k bit W w acc U)
    · linarith
    · exact lcuLevelGateCorrected_unitary bit (W/w) (div_nonneg hW.le hw.le) acc (liftSys k U)
        hacc hlu (hfresh _ (List.mem_cons_self)) (preservesLCUBit_liftSys bit U)
    · intro t ht; exact hweight t (List.mem_cons_of_mem _ ht)
    · intro t ht; exact hU t (List.mem_cons_of_mem _ ht)
    · intro t ht
      exact preservesLCUBit_level_other bit t.1 (Ne.symm (hpairs.1 t ht)) _ _ _
        (hfresh t (List.mem_cons_of_mem _ ht)) (preservesLCUBit_liftSys t.1 U)
    · exact hpairs.2

/-- The involutive equivalence that negates ancilla bit `i` and leaves the other ancilla bits
and the system index fixed. -/
def flipLCUBit {k : ℕ} (i : Fin k) : ((Fin k→Bool)×I) ≃ ((Fin k→Bool)×I) where
  toFun p := (Function.update p.1 i (!(p.1 i)),p.2)
  invFun p := (Function.update p.1 i (!(p.1 i)),p.2)
  left_inv := by
    rintro ⟨z,x⟩
    apply Prod.ext
    · funext j
      by_cases h : j=i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · rfl
  right_inv := by
    rintro ⟨z,x⟩
    apply Prod.ext
    · funext j
      by_cases h : j=i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · rfl

/-- A matrix is independent in bit `i` in the sense that its entries are invariant under
simultaneously flipping `i` in the row and column indices. -/
def IndependentLCUBit {k : ℕ} (i : Fin k)
    (A : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) : Prop :=
  ∀ p q,A (flipLCUBit i p) (flipLCUBit i q)=A p q

omit [Fintype I] [DecidableEq I] in

/-- Every lifted system matrix is invariant under a simultaneous flip of any ancilla bit in its
row and column indices. -/
theorem independentLCUBit_liftSys {k : ℕ} (i : Fin k) (U : Matrix I I ℂ) :
    IndependentLCUBit i (liftSys k U) := by
  intro p q
  have hmask : (flipLCUBit i p).1=(flipLCUBit i q).1 ↔ p.1=q.1 := by
    constructor
    · intro h
      have he : flipLCUBit (I := I) i (p.1,p.2)=flipLCUBit i (q.1,p.2) := by
        apply Prod.ext
        · exact h
        · rfl
      have hh : (p.1,p.2)=(q.1,p.2) := (flipLCUBit i).injective he
      have hh1 := Prod.mk.inj hh
      exact hh1.1
    · intro h; simp [flipLCUBit,h]
  simp only [liftSys,Matrix.of_apply,hmask]
  rfl

omit [Fintype I] in

/-- A corrected rotation on bit `i` is independent in every distinct bit `j` under simultaneous
row and column flips. -/
theorem independentLCUBit_rot_other {k : ℕ} (i j : Fin k) (hji : j≠i)
    (V : Matrix (Fin 2) (Fin 2) ℂ) : IndependentLCUBit j (rotGateCorrected (I := I) k i V) := by
  intro p q
  rw [rotGateCorrected_apply,rotGateCorrected_apply]
  have he (l : Fin k) : (flipLCUBit j p).1 l=(flipLCUBit j q).1 l ↔ p.1 l=q.1 l := by
    by_cases hl : l=j
    · subst l; simp [flipLCUBit]
    · simp [flipLCUBit,Function.update_of_ne hl]
  have hrest : (∀ l : Fin k,l≠i→(flipLCUBit j p).1 l=(flipLCUBit j q).1 l) ↔
      (∀ l : Fin k,l≠i→p.1 l=q.1 l) := by
    simp_rw [he]
  simp only [hrest]
  simp only [flipLCUBit,Equiv.coe_fn_mk,Function.update_of_ne (Ne.symm hji)]

omit [Fintype I] [DecidableEq I] in

/-- A corrected gate controlled by `i` is independent in a distinct bit `j` whenever both branch
matrices are independent in `j`. -/
theorem independentLCUBit_ctrl_other {k : ℕ} (i j : Fin k) (hji : j≠i)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hx : IndependentLCUBit j Cx) (hy : IndependentLCUBit j Cy) :
    IndependentLCUBit j (ctrlGateCorrected k i Cx Cy) := by
  intro p q
  simp only [ctrlGateCorrected,Matrix.of_apply]
  have hpi : (flipLCUBit j p).1 i=p.1 i := by simp [flipLCUBit,Ne.symm hji]
  have hqi : (flipLCUBit j q).1 i=q.1 i := by simp [flipLCUBit,Ne.symm hji]
  rw [hpi,hqi]
  split_ifs <;> first | exact hx p q | exact hy p q | rfl

omit [DecidableEq I] in

/-- Simultaneous row and column flip invariance in an ancilla bit is closed under matrix
multiplication. -/
theorem independentLCUBit_mul {k : ℕ} (i : Fin k)
    (A B : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (ha : IndependentLCUBit i A) (hb : IndependentLCUBit i B) :
    IndependentLCUBit i (A*B) := by
  intro p q
  rw [Matrix.mul_apply,Matrix.mul_apply]
  rw [← (flipLCUBit (I := I) i).sum_comp (fun r=>A (flipLCUBit i p) r*B r (flipLCUBit i q))]
  exact Finset.sum_congr rfl (fun r _=>congrArg₂ (·*·) (ha p r) (hb r q))

omit [Fintype I] in

/-- The identity matrix preserves each ancilla bit. -/
theorem preservesLCUBit_one {k : ℕ} (i : Fin k) :
    PreservesLCUBit i (1 : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) := by
  intro p q hpq
  have hne : p≠q := fun he=>hpq (congrArg (fun p=>p.1 i) he)
  simp [hne]

omit [Fintype I] in

/-- The identity matrix is invariant under simultaneously flipping any ancilla bit in its row
and column indices. -/
theorem independentLCUBit_one {k : ℕ} (i : Fin k) :
    IndependentLCUBit i (1 : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) := by
  intro p q
  have he : flipLCUBit (I := I) i p=flipLCUBit i q ↔ p=q := (flipLCUBit i).injective.eq_iff
  simp [Matrix.one_apply,he]

omit [Fintype I] [DecidableEq I] in

/-- Negating a matrix preserves its simultaneous row and column flip invariance in a specified
ancilla bit. -/
theorem independentLCUBit_neg {k : ℕ} (i : Fin k)
    (A : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (ha : IndependentLCUBit i A) :
    IndependentLCUBit i (-A) := by
  intro p q
  change -(A (flipLCUBit i p) (flipLCUBit i q))= -A p q
  rw [ha p q]

omit [Fintype I] [DecidableEq I] in

/-- Negating a matrix that preserves an ancilla bit still preserves that bit. -/
theorem preservesLCUBit_neg {k : ℕ} (i : Fin k)
    (A : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (ha : PreservesLCUBit i A) :
    PreservesLCUBit i (-A) := by
  intro p q hpq
  change -(A p q)=0
  rw [ha p q hpq,neg_zero]

/-- Lifting a unitary system matrix by the identity on the ancillas yields a unitary matrix on
the combined register. -/
theorem liftSys_unitary_corrected (k : ℕ) (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) :
    liftSys k U∈Matrix.unitaryGroup _ ℂ := by
  have he : liftSys k U=TensorGate (1 : Matrix (Fin k→Bool) (Fin k→Bool) ℂ) U := by
    ext p q
    by_cases h : p.1=q.1 <;> simp [liftSys,TensorGate,Matrix.one_apply,h]
  rw [he]
  exact tensorGate_unitary (Submonoid.one_mem _) hU

/-- A corrected LCU level on bit `i` is independent in a distinct bit `j` if both branch
matrices are independent in `j`. -/
theorem independentLCUBit_level_other {k : ℕ} (i j : Fin k) (hji : j≠i)
    (V : Matrix (Fin 2) (Fin 2) ℂ)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hx : IndependentLCUBit j Cx) (hy : IndependentLCUBit j Cy) :
    IndependentLCUBit j (lcuLevelGateCorrected k i V Cx Cy) := by
  exact independentLCUBit_mul j _ _ (independentLCUBit_rot_other i j hji Vᴴ)
    (independentLCUBit_mul j _ _ (independentLCUBit_ctrl_other i j hji Cx Cy hx hy)
      (independentLCUBit_rot_other i j hji V))

/-- The corrected chain fold remains independent in bit `j` if its initial accumulator is
independent in `j` and none of the listed levels uses `j`. -/
theorem chainFoldCorrected_independent {k : ℕ} (j : Fin k)
    (L : List (Fin k×(ℝ×Matrix I I ℂ))) (W : ℝ)
    (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hL : ∀ t∈L,j≠t.1) (hacc : IndependentLCUBit j acc) :
    IndependentLCUBit j (chainFoldCorrected k W acc L) := by
  induction L generalizing W acc with
  | nil => exact hacc
  | cons t L ih =>
    rcases t with ⟨bit,w,U⟩
    apply ih (W+w) (chainGateCorrected k bit W w acc U)
    · intro t ht; exact hL t (List.mem_cons_of_mem _ ht)
    · exact independentLCUBit_level_other bit j (hL _ (List.mem_cons_self)) _ _ _ hacc
        (independentLCUBit_liftSys j U)

/-- A corrected chain circuit preserves any ancilla bit absent from the control positions of the
list's tail. -/
theorem chainCircuitCorrected_preserves {k : ℕ} (j : Fin k)
    (L : List (Fin k×(ℝ×Matrix I I ℂ))) (hL : ∀ t∈L.tail,j≠t.1) :
    PreservesLCUBit j (chainCircuitCorrected k L) := by
  cases L with
  | nil => exact preservesLCUBit_one j
  | cons t L =>
    rcases t with ⟨bit,w,U⟩
    exact chainFoldCorrected_preserves j L w (liftSys k U) hL (preservesLCUBit_liftSys j U)

/-- A corrected chain circuit is independent in any ancilla bit absent from the control
positions of the list's tail. -/
theorem chainCircuitCorrected_independent {k : ℕ} (j : Fin k)
    (L : List (Fin k×(ℝ×Matrix I I ℂ))) (hL : ∀ t∈L.tail,j≠t.1) :
    IndependentLCUBit j (chainCircuitCorrected k L) := by
  cases L with
  | nil => exact independentLCUBit_one j
  | cons t L =>
    rcases t with ⟨bit,w,U⟩
    exact chainFoldCorrected_independent j L w (liftSys k U) hL (independentLCUBit_liftSys j U)

/-- A corrected chain circuit is unitary when every listed weight is positive, every payload is
unitary, and the listed ancilla positions are pairwise distinct. -/
theorem chainCircuitCorrected_unitary {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ)))
    (hweight : ∀ t∈L,0<t.2.1) (hU : ∀ t∈L,t.2.2∈Matrix.unitaryGroup I ℂ)
    (hbits : L.Pairwise (fun a b=>a.1≠b.1)) :
    chainCircuitCorrected k L∈Matrix.unitaryGroup _ ℂ := by
  cases L with
  | nil => exact Submonoid.one_mem _
  | cons t L =>
    rcases t with ⟨bit,w,U⟩
    apply chainFoldCorrected_unitary L w (liftSys k U)
    · exact hweight _ (List.mem_cons_self)
    · exact liftSys_unitary_corrected k U (hU _ (List.mem_cons_self))
    · intro t ht; exact hweight t (List.mem_cons_of_mem _ ht)
    · intro t ht; exact hU t (List.mem_cons_of_mem _ ht)
    · intro t _; exact preservesLCUBit_liftSys t.1 U
    · exact (List.pairwise_cons.mp hbits).2

end Qatlib.Papers.HamLCUSim12.LCUDeferred
