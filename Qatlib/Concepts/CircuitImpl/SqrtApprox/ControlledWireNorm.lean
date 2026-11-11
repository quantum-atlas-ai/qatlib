/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Norm bound for a controlled single-wire gate

This module separates a target wire from the remaining register by `elementaryWireSplit`. The
resulting tensor representation of `multiWireState` reduces a controlled register operation to
single-qubit blocks, as used in the multi-controlled gate constructions of [BarencoEtAl1995].

## Main statements

* `elementary_wire_fiber_split`: the target-wire state as a relabeled tensor state.
* `elementary_controlled_distance`: the register operation's distance from identity is at most
  `‖U - 1‖`.

## References

* [Barenco et al., 1995, Section 7][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth

namespace Qatlib.Concepts.CircuitImpl.SqrtApprox
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Applying a matrix to a basis ket returns the matrix column indexed by that basis element. -/
private theorem elementary_apply_ket {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (x y : I) : ApplyGate A (Qatlib.Foundations.PureStateMath.Ket x) y=A y x := by
  simp [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite]

/-- Registers whose target bit is false, used to label the remaining-wire configurations. -/
abbrev ElementaryWireLabel {N : ℕ} (t : Fin N) := {x : Reg N // x t=false}

/-- Split a register into a label with its target bit cleared and the original target bit. -/
def elementaryWireSplit {N : ℕ} (t : Fin N) : Reg N ≃ (ElementaryWireLabel t × Bool) where
  toFun x := (⟨Function.update x t false, by simp⟩, x t)
  invFun p := Function.update p.1.1 t p.2
  left_inv x := by simp
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change Function.update (Function.update p.1.1 t p.2) t false = p.1.1
      rw [Function.update_idem]
      exact Function.update_eq_self_iff.mpr p.1.2.symm
    · simp

/-- A target-wire state is the relabeling of the tensor product of its remaining-wire basis
label and its single-qubit state. -/
theorem elementary_wire_fiber_split {N : ℕ} (t : Fin N) (x : Reg N) (φ : QState Bool) :
    multiWireState t x φ = relabelState (elementaryWireSplit t).symm
      (TensorState (Qatlib.Foundations.PureStateMath.Ket ((elementaryWireSplit t x).1)) φ) := by
  funext z
  change (φ false • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false) + φ true • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true)) z = _
  simp only [relabelState, Function.comp_apply, Equiv.symm_symm, TensorState,
      Qatlib.Foundations.PureStateMath.Ket, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change _ = (if (elementaryWireSplit t z).1 = (elementaryWireSplit t x).1 then 1 else 0) * φ (z t)
  have he (b : Bool) : z = Function.update x t b ↔
      (elementaryWireSplit t z).1 = (elementaryWireSplit t x).1 ∧ z t=b := by
    constructor
    · intro h
      constructor
      · apply Subtype.ext
        change Function.update z t false = Function.update x t false
        rw [h, Function.update_idem]
      · have h' := congrArg (fun y : Reg N => y t) h
        simpa using! h'
    · rintro ⟨h,hb⟩
      have h' := congrArg (fun p : ElementaryWireLabel t => p.1) h
      have h'' := congrArg (fun y : Reg N => Function.update y t b) h'
      change Function.update (Function.update z t false) t b = Function.update
          (Function.update x t false) t b at h''
      simpa [← hb] using! h''
  simp only [he]
  cases hz : z t <;> by_cases h : (elementaryWireSplit t z).1 = (elementaryWireSplit t x).1 <;>
    simp [h]

/-- If `G` applies `U` exactly when all specified control bits are true and otherwise acts
identically, then `‖G - 1‖ ≤ ‖U - 1‖`, provided the controls avoid the target. -/
theorem elementary_controlled_distance {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hct : ∀ i < m, c i≠t) (U : Matrix Bool Bool ℂ) (G : Matrix (Reg N) (Reg N) ℂ)
    (hG : ∀ x φ, ApplyGate G (multiWireState t x φ) = multiWireState t x
      (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U else 1) φ)) :
    ‖G-1‖ ≤ ‖U-1‖ := by
  let e := elementaryWireSplit t
  let a := fun y : ElementaryWireLabel t => noWorkPrefixAnd (fun i => y.1 (c i)) m
  let M : Matrix (ElementaryWireLabel t × Bool) (ElementaryWireLabel t × Bool) ℂ :=
    fun z w => if z.1=w.1 then (if a w.1 then U else 1) z.2 w.2 else 0
  have hcond (x : Reg N) : a (e x).1 = noWorkPrefixAnd (fun i => x (c i)) m := by
    change noWorkPrefixAnd (fun i => Function.update x t false (c i)) m = noWorkPrefixAnd
        (fun i => x (c i)) m
    apply Bool.eq_iff_iff.mpr
    simp only [noWorkPrefixAnd,List.all_eq_true,List.mem_range]
    have he (i : ℕ) (hi : i < m) : Function.update x t false (c i)=x (c i) :=
      Function.update_of_ne (hct i hi) _ _
    constructor <;> intro h i hi
    · simpa only [he i hi] using! h i hi
    · simpa only [he i hi] using! h i hi
  have hmat : relabelGate e G=M := by
    ext z w
    let x := e.symm w
    have h := hG x (Qatlib.Foundations.PureStateMath.Ket (x t))
    rw [multiWireState_ket,elementary_wire_fiber_split] at h
    have he := congrFun h (e.symm z)
    rw [elementary_apply_ket] at he
    change G (e.symm z) x = _ at he
    change G (e.symm z) (e.symm w) = _
    rw [he]
    have hex : e x=w := e.apply_symm_apply w
    have hez : e (e.symm z)=z := e.apply_symm_apply z
    have hxt : x t=w.2 := congrArg Prod.snd hex
    change (TensorState (Qatlib.Foundations.PureStateMath.Ket (e x).1)
      (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U else 1) (Qatlib.Foundations.PureStateMath.Ket (x t)))) (e (e.symm z)) = M z w
    rw [hez,← hcond x,hex,hxt]
    change (if z.1=w.1 then (1 : ℂ) else 0) *
      (ApplyGate (if a w.1 then U else 1) (Qatlib.Foundations.PureStateMath.Ket w.2) z.2) = M z w
    rw [elementary_apply_ket]
    simp only [M]
    by_cases hzw : z.1=w.1
    · simp only [if_pos hzw,one_mul]
    · simp only [if_neg hzw,zero_mul]
  have hsub : M-1=TensorGate (diagonal (fun y => if a y then (1 : ℂ) else 0)) (U-1) := by
    ext ⟨y,b⟩ ⟨z,d⟩
    simp only [M,Matrix.sub_apply,Matrix.one_apply,TensorGate]
    by_cases hz : y=z
    · subst z
      cases ha : a y <;> simp [ha,Prod.ext_iff,Matrix.one_apply]
    · have hne : (y,b)≠(z,d) := fun h => hz (congrArg Prod.fst h)
      simp [hz,hne]
  have hdiag : ‖(diagonal (fun y : ElementaryWireLabel t => if a y then (1 : ℂ) else 0))‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal,pi_norm_le_iff_of_nonneg zero_le_one]
    intro y
    cases a y <;> simp
  have hnorm : ‖G-1‖=‖M-1‖ := by
    have h1 : relabelGate e (1 : Matrix (Reg N) (Reg N) ℂ)=1 := by
      ext i j
      simp [relabelGate,Matrix.one_apply,e.symm.injective.eq_iff]
    have hn := l2_norm_relabelGate_sub e G 1
    rw [hmat,h1] at hn
    exact hn.symm
  rw [hnorm,hsub,l2_norm_tensorGate]
  exact mul_le_of_le_one_left (norm_nonneg _) hdiag
end Qatlib.Concepts.CircuitImpl.SqrtApprox
