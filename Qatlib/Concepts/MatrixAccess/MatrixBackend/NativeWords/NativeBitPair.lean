/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeTwoLevelTransport

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! The actual nonpivot controls and set-bit CNOT targets of a binary
address. Their moved-zero predicate singles out exactly zero and that
address, for any pivot whose supplied address bit is one. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for binary Pair Controls in the native bit pair model. -/
def binaryPairControls {m : ℕ} (pivot : Fin m) : List (Fin m) :=
  (List.finRange m).filter (fun w => decide (w≠pivot))

/-- Construction for binary Pair Targets in the native bit pair model. -/
def binaryPairTargets {m : ℕ} (pivot : Fin m) (mask : Reg m) : List (Fin m) :=
  (List.finRange m).filter (fun w => decide (w≠pivot) && mask w)

/-- The finite native construction `mem_binaryPairControls` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem mem_binaryPairControls {m : ℕ} (pivot w : Fin m) :
    w∈binaryPairControls pivot ↔ w≠pivot := by simp [binaryPairControls]

/-- The finite native construction `mem_binaryPairTargets` satisfies the displayed exact coordinate or algebraic relation. -/
@[simp] theorem mem_binaryPairTargets {m : ℕ} (pivot w : Fin m) (mask : Reg m) :
    w∈binaryPairTargets pivot mask ↔ w≠pivot ∧ mask w=true := by simp [binaryPairTargets]

/-- The actual finite allocation satisfies the displayed wire, guard or workspace condition. -/
theorem binaryPair_guard {m : ℕ} (pivot : Fin m) (mask x : Reg m) (hp : mask pivot=true) :
    (binaryPairControls pivot).all (fun w => !nativePivotBasis pivot (binaryPairTargets pivot mask) x w)=true ↔
      x=(fun _ => false) ∨ x=mask := by
  constructor
  · intro hg
    have hy (w : Fin m) (hw : w≠pivot) :
        nativePivotBasis pivot (binaryPairTargets pivot mask) x w=false := by
      exact Bool.eq_false_of_not_eq_true'
        (List.all_eq_true.mp hg w (mem_binaryPairControls pivot w |>.mpr hw))
    cases hx : x pivot with
    | false =>
      left
      funext w
      by_cases hw : w=pivot
      · simpa [hw] using hx
      · simpa [nativePivotBasis, hx] using hy w hw
    | true =>
      right
      funext w
      by_cases hw : w=pivot
      · simp [hw, hx, hp]
      · have hh := hy w hw
        cases hm : mask w <;> cases hxw : x w <;>
          simp [nativePivotBasis, hw, hx, hm, hxw] at hh ⊢
  · rintro (hzero|hmask)
    · subst x
      apply List.all_eq_true.mpr
      intro w _
      simp [nativePivotBasis]
    · subst x
      apply List.all_eq_true.mpr
      intro w hw
      have hwp : w≠pivot := (mem_binaryPairControls pivot w).mp hw
      cases hm : mask w <;> simp [nativePivotBasis, hwp, hp, hm]

/-- The finite native construction `binaryPair_endpoint` satisfies the displayed exact coordinate or algebraic relation. -/
theorem binaryPair_endpoint {m : ℕ} (pivot : Fin m) (mask x : Reg m) (hp : mask pivot=true)
    (hg : (binaryPairControls pivot).all
      (fun w => !nativePivotBasis pivot (binaryPairTargets pivot mask) x w)=true) (b : Bool) :
    nativePairAddress pivot (binaryPairTargets pivot mask) x b =
      fun w => if b then mask w else false := by
  rcases (binaryPair_guard pivot mask x hp).mp hg with hzero|hmask
  all_goals subst x
  all_goals
    funext w
    by_cases hw : w=pivot
    · subst w
      cases b <;> simp [nativePairAddress, hp]
    · cases hm : mask w <;> cases b <;> simp [nativePairAddress, hw, hm]

/-- The finite native construction `binaryPairGate_zero` satisfies the displayed exact coordinate or algebraic relation. -/
theorem binaryPairGate_zero {m : ℕ} (pivot : Fin m) (mask : Reg m) (hp : mask pivot=true) (r : Circle) :
    ApplyGate (nativePairGate (binaryPairControls pivot) pivot (binaryPairTargets pivot mask) r)
      (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) =
      (r.c : ℂ) • Qatlib.Foundations.PureStateMath.Ket (fun _ => false) + (r.s : ℂ) • Qatlib.Foundations.PureStateMath.Ket mask := by
  have hg := (binaryPair_guard pivot mask (fun _ => false) hp).mpr (Or.inl rfl)
  rw [nativePairGate_ket, nativePairColumn, ite_eq_left hg,
    binaryPair_endpoint pivot mask _ hp hg false, binaryPair_endpoint pivot mask _ hp hg true]
  rfl

/-- The finite native construction `binaryPairGate_mask` satisfies the displayed exact coordinate or algebraic relation. -/
theorem binaryPairGate_mask {m : ℕ} (pivot : Fin m) (mask : Reg m) (hp : mask pivot=true) (r : Circle) :
    ApplyGate (nativePairGate (binaryPairControls pivot) pivot (binaryPairTargets pivot mask) r)
      (Qatlib.Foundations.PureStateMath.Ket mask) =
      -(r.s : ℂ) • Qatlib.Foundations.PureStateMath.Ket (fun _ => false) + (r.c : ℂ) • Qatlib.Foundations.PureStateMath.Ket mask := by
  have hg := (binaryPair_guard pivot mask mask hp).mpr (Or.inr rfl)
  rw [nativePairGate_ket, nativePairColumn, ite_eq_left hg,
    binaryPair_endpoint pivot mask _ hp hg false, binaryPair_endpoint pivot mask _ hp hg true]
  rw [hp]
  rfl

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem binaryPairGate_other {m : ℕ} (pivot : Fin m) (mask x : Reg m)
    (hp : mask pivot=true) (r : Circle) (hx0 : x≠fun _ => false) (hxm : x≠mask) :
    ApplyGate (nativePairGate (binaryPairControls pivot) pivot (binaryPairTargets pivot mask) r) (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket x := by
  have hg : ¬(binaryPairControls pivot).all
      (fun w => !nativePivotBasis pivot (binaryPairTargets pivot mask) x w)=true := by
    rw [binaryPair_guard pivot mask x hp]
    exact not_or.mpr ⟨hx0,hxm⟩
  rw [nativePairGate_ket, nativePairColumn, ite_eq_right hg]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
