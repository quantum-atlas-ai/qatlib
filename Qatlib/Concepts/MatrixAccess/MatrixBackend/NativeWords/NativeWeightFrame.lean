/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeBinaryHouseholder
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.WorkspaceCP
/-! Canonical local source layout: m labels, work, w AND-pool bits, seed.
The seed is the highest wire and initially one; work and pool are zero.
The explicit clean frame is a row-reindexed existing coordinate fiber. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Abbreviation for weight Width in the native weight frame model. -/
abbrev weightWidth (m w : ℕ) := m+(w+2)

/-- Construction for weight Split in the native weight frame model. -/
def weightSplit (m w : ℕ) : Reg (weightWidth m w) ≃ Reg (w+2) × Reg m :=
  (regAppendEquiv m (w+2)).trans (Equiv.prodComm _ _)

/-- Construction for weight Aux Seed in the native weight frame model. -/
def weightAuxSeed (w : ℕ) : Reg (w+2) := fun j => decide (j.val=w+1)

/-- Construction for weight Input in the native weight frame model. -/
def weightInput (m w : ℕ) (x : Reg m) : Reg (weightWidth m w) :=
  (weightSplit m w).symm (weightAuxSeed w,x)

/-- Construction for weight Label Wire in the native weight frame model. -/
def weightLabelWire (m w : ℕ) (j : Fin m) : Fin (weightWidth m w) := Fin.castAdd (w+2) j
/-- Construction for weight Work Wire in the native weight frame model. -/
def weightWorkWire (m w : ℕ) : Fin (weightWidth m w) := Fin.natAdd m 0
/-- Construction for weight Pool Wire in the native weight frame model. -/
def weightPoolWire (m w : ℕ) (j : Fin w) : Fin (weightWidth m w) :=
  Fin.natAdd m ⟨j.val+1,by have := j.isLt; omega⟩
/-- Construction for weight Seed Wire in the native weight frame model. -/
def weightSeedWire (m w : ℕ) : Fin (weightWidth m w) := Fin.natAdd m (Fin.last (w+1))
/-- Construction for weight Pool in the native weight frame model. -/
def weightPool (m w : ℕ) : List (Fin (weightWidth m w)) := List.ofFn (weightPoolWire m w)
/-- Construction for weight Lift in the native weight frame model. -/
def weightLift (m w : ℕ) (xs : List (Fin m)) : List (Fin (weightWidth m w)) := xs.map (weightLabelWire m w)

/-- The finite native construction `weightLabelWire_val` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem weightLabelWire_val (m w : ℕ) (j : Fin m) : (weightLabelWire m w j).val=j.val := rfl
/-- The finite native construction `weightWorkWire_val` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem weightWorkWire_val (m w : ℕ) : (weightWorkWire m w).val=m := rfl
/-- The finite native construction `weightPoolWire_val` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem weightPoolWire_val (m w : ℕ) (j : Fin w) : (weightPoolWire m w j).val=m+(j.val+1) := rfl
/-- The finite native construction `weightSeedWire_val` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem weightSeedWire_val (m w : ℕ) : (weightSeedWire m w).val=m+(w+1) := rfl
/-- The allocated pool contains exactly the requested number of work wires. -/
@[simp] theorem weightPool_length (m w : ℕ) : (weightPool m w).length=w := by simp [weightPool]

/-- The concrete input frame preserves each selected label coordinate. -/
theorem weightInput_label (m w : ℕ) (x : Reg m) (j : Fin m) :
    weightInput m w x (weightLabelWire m w j)=x j :=
  congrArg (fun z : Reg (w+2) × Reg m => z.2 j) ((weightSplit m w).apply_symm_apply (weightAuxSeed w,x))

/-- The finite native construction `weightInput_aux` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightInput_aux (m w : ℕ) (x : Reg m) (j : Fin (w+2)) :
    weightInput m w x (Fin.natAdd m j)=weightAuxSeed w j :=
  congrArg (fun z : Reg (w+2) × Reg m => z.1 j) ((weightSplit m w).apply_symm_apply (weightAuxSeed w,x))

/-- The finite native construction `weightInput_injective` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightInput_injective (m w : ℕ) : Function.Injective (weightInput m w) := by
  intro x y he
  funext j
  have hh := congrFun he (weightLabelWire m w j)
  simpa only [weightInput_label] using hh

/-- The finite native construction `weightInput_work` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem weightInput_work (m w : ℕ) (x : Reg m) :
    weightInput m w x (weightWorkWire m w)=false := by
  rw [weightWorkWire, weightInput_aux]
  simp [weightAuxSeed]

/-- The finite native construction `weightInput_seed` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem weightInput_seed (m w : ℕ) (x : Reg m) :
    weightInput m w x (weightSeedWire m w)=true := by
  rw [weightSeedWire, weightInput_aux]
  simp [weightAuxSeed]

/-- The finite native construction `weightInput_pool` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightInput_pool (m w : ℕ) (x : Reg m) : ∀ q∈weightPool m w,weightInput m w x q=false := by
  intro q hq
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
  rw [weightPoolWire, weightInput_aux]
  have hj := j.isLt
  simp [weightAuxSeed]
  omega

/-- The finite native construction `weightLabelWire_injective` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightLabelWire_injective (m w : ℕ) : Function.Injective (weightLabelWire m w) := by
  intro i j he
  exact Fin.ext (congrArg (fun q : Fin (weightWidth m w) => q.val) he)

/-- The finite native construction `weightLift_mem` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem weightLift_mem (m w : ℕ) (xs : List (Fin m)) (j : Fin m) :
    weightLabelWire m w j∈weightLift m w xs ↔ j∈xs := by
  simp only [weightLift, List.mem_map]
  constructor
  · rintro ⟨i,hi,he⟩
    exact weightLabelWire_injective m w he ▸ hi
  · intro hj
    exact ⟨j,hj,rfl⟩

/-- The finite native construction `weightLift_aux_not_mem` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightLift_aux_not_mem (m w : ℕ) (xs : List (Fin m)) (j : Fin (w+2)) :
    Fin.natAdd m j∉weightLift m w xs := by
  intro hh
  obtain ⟨i,_,he⟩ := List.mem_map.mp hh
  have hv := congrArg (fun q : Fin (weightWidth m w) => q.val) he
  have hi := i.isLt
  simp only [weightLabelWire_val, Fin.val_natAdd] at hv
  omega

/-- The actual finite allocation satisfies the displayed wire, guard or workspace condition. -/
theorem weightPool_bounds (m w : ℕ) (q : Fin (weightWidth m w)) (hq : q∈weightPool m w) :
    m + 1 ≤ q.val ∧ q.val ≤ m + w := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
  have hj := j.isLt
  simp only [weightPoolWire_val]
  omega

/-- The actual finite allocation satisfies the displayed wire, guard or workspace condition. -/
theorem weightPool_nodup (m w : ℕ) : (weightPool m w).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j he
  apply Fin.ext
  have hv := congrArg (fun q : Fin (weightWidth m w) => q.val) he
  simp only [weightPoolWire_val] at hv
  omega

/-- The actual finite allocation satisfies the displayed wire, guard or workspace condition. -/
theorem weightAllocation (m w : ℕ) (xs : List (Fin m)) (hxs : xs.Nodup) :
    (weightLift m w xs++[weightWorkWire m w]++weightPool m w).Nodup := by
  have hw : weightWorkWire m w∉weightPool m w := by
    intro hh
    have hb := weightPool_bounds m w _ hh
    simp only [weightWorkWire_val] at hb
    omega
  have ha : (weightWorkWire m w::weightPool m w).Nodup := List.nodup_cons.mpr ⟨hw,weightPool_nodup m w⟩
  have hl : (weightLift m w xs).Nodup := hxs.map (weightLabelWire_injective m w)
  have hd : ∀ a∈weightLift m w xs,∀ b∈weightWorkWire m w::weightPool m w,a≠b := by
    intro a hmem b hb he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
    have hlow : m≤b.val := by
      rcases List.mem_cons.mp hb with rfl|hb
      · simp
      · exact (Nat.le_succ m).trans (weightPool_bounds m w b hb).1
    have hv := congrArg (fun q : Fin (weightWidth m w) => q.val) he
    have hi := i.isLt
    simp only [weightLabelWire_val] at hv
    omega
  simpa only [List.append_assoc, List.singleton_append] using List.nodup_append.mpr ⟨hl,ha,hd⟩

/-- Construction for weight Frame in the native weight frame model. -/
def weightFrame (m w : ℕ) : Matrix (Reg (weightWidth m w)) (Reg m) ℂ :=
  (encodingFiber (I := Reg m) (weightAuxSeed w)).submatrix (weightSplit m w) id

/-- The concrete rectangular frame has identity Gram matrix. -/
theorem weightFrame_isometry (m w : ℕ) : IsIsometry (weightFrame m w) := by
  unfold IsIsometry weightFrame
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  simpa only [IsIsometry, Matrix.submatrix_id_id] using
    encodingFiber_isIsometry (I := Reg m) (weightAuxSeed w)

/-- The concrete matrix entries have the displayed exact coordinate formula. -/
theorem weightFrame_entry (m w : ℕ) (z : Reg (weightWidth m w)) (x : Reg m) :
    weightFrame m w z x=Qatlib.Foundations.PureStateMath.Ket (weightInput m w x) z := by
  simp only [weightFrame, Matrix.submatrix_apply, encodingFiber_apply, id_eq]
  have he : (weightSplit m w) z=(weightAuxSeed w,x) ↔ z=weightInput m w x :=
    (weightSplit m w).apply_eq_iff_eq_symm_apply
  simp only [he, Qatlib.Foundations.PureStateMath.Ket]

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem weightFrame_ket (m w : ℕ) (x : Reg m) :
    weightFrame m w *ᵥ Qatlib.Foundations.PureStateMath.Ket x=Qatlib.Foundations.PureStateMath.Ket (weightInput m w x) := by
  funext z
  change (∑ y,weightFrame m w z y * Qatlib.Foundations.PureStateMath.Ket x y) = _
  rw [Finset.sum_eq_single x]
  · simp [Qatlib.Foundations.PureStateMath.Ket, weightFrame_entry]
  · intro y _ hy
    simp [Qatlib.Foundations.PureStateMath.Ket, hy]
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))

/-- The concrete matrix entries have the displayed exact coordinate formula. -/
theorem weightFrame_input_entry (m w : ℕ) (x y : Reg m) :
    weightFrame m w (weightInput m w x) y = if x=y then 1 else 0 := by
  rw [weightFrame_entry]
  simp only [Qatlib.Foundations.PureStateMath.Ket, (weightInput_injective m w).eq_iff]

/-- The finite native construction `weightFrame_apply_at_input` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightFrame_apply_at_input (m w : ℕ) (ψ : QState (Reg m)) (x : Reg m) :
    (weightFrame m w *ᵥ ψ) (weightInput m w x)=ψ x := by
  change (∑ y,weightFrame m w (weightInput m w x) y * ψ y)=ψ x
  rw [Finset.sum_eq_single x]
  · simp [weightFrame_input_entry]
  · intro y _ hy
    simp [weightFrame_input_entry, Ne.symm hy]
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
