/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeWeightFrame

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! The source CNOT moves and two physical endpoint addresses commute with
the explicit canonical clean input. Auxiliary coordinates are retained. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- The finite native construction `weightPivotBasis` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightPivotBasis (m w : ℕ) (pivot : Fin m) (xs : List (Fin m)) (x : Reg m) :
    nativePivotBasis (weightLabelWire m w pivot) (weightLift m w xs) (weightInput m w x) =
      weightInput m w (nativePivotBasis pivot xs x) := by
  funext q
  refine Fin.addCases (fun j => ?_) (fun j => ?_) q
  · change nativePivotBasis _ _ _ (weightLabelWire m w j) =
      weightInput m w _ (weightLabelWire m w j)
    simp only [nativePivotBasis, weightLift_mem, weightInput_label]
  · rw [nativePivotBasis_outside _ _ _ _ (weightLift_aux_not_mem m w xs j)]
    simp only [weightInput_aux]

/-- The finite native construction `weightPairAddress` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightPairAddress (m w : ℕ) (pivot : Fin m) (xs : List (Fin m)) (x : Reg m) (b : Bool) :
    nativePairAddress (weightLabelWire m w pivot) (weightLift m w xs) (weightInput m w x) b =
      weightInput m w (nativePairAddress pivot xs x b) := by
  funext q
  refine Fin.addCases (fun j => ?_) (fun j => ?_) q
  · change nativePairAddress _ _ _ b (weightLabelWire m w j) =
      weightInput m w _ (weightLabelWire m w j)
    have he : weightLabelWire m w j=weightLabelWire m w pivot ↔ j=pivot :=
      (weightLabelWire_injective m w).eq_iff
    simp only [nativePairAddress, he, weightLift_mem, weightInput_label]
  · have he : Fin.natAdd m j≠weightLabelWire m w pivot := by
      intro he
      have hv := congrArg (fun q : Fin (weightWidth m w) => q.val) he
      have hp := pivot.isLt
      simp only [Fin.val_natAdd, weightLabelWire_val] at hv
      omega
    change (if Fin.natAdd m j=weightLabelWire m w pivot ∨ Fin.natAdd m j∈weightLift m w xs
      then b else weightInput m w x (Fin.natAdd m j)) = _
    rw [ite_eq_right (not_or.mpr ⟨he,weightLift_aux_not_mem m w xs j⟩)]
    simp only [weightInput_aux]

/-- The finite native construction `weightLabel_ne_work` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightLabel_ne_work (m w : ℕ) (pivot : Fin m) :
    weightLabelWire m w pivot≠weightWorkWire m w := by
  intro he
  have hv := congrArg (fun q : Fin (weightWidth m w) => q.val) he
  have hp := pivot.isLt
  simp only [weightLabelWire_val, weightWorkWire_val] at hv
  omega

/-- The finite native construction `weightLabel_not_pool` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightLabel_not_pool (m w : ℕ) (pivot : Fin m) :
    weightLabelWire m w pivot∉weightPool m w := by
  intro hp
  have hb := weightPool_bounds m w _ hp
  have hi := pivot.isLt
  simp only [weightLabelWire_val] at hb
  omega

/-- The actual finite allocation satisfies the displayed wire, guard or workspace condition. -/
theorem binaryPairControls_nodup {m : ℕ} (pivot : Fin m) : (binaryPairControls pivot).Nodup :=
  (List.nodup_finRange m).filter _

/-- The actual finite allocation satisfies the displayed wire, guard or workspace condition. -/
theorem binaryPairTargets_nodup {m : ℕ} (pivot : Fin m) (mask : Reg m) :
    (binaryPairTargets pivot mask).Nodup := (List.nodup_finRange m).filter _

/-- The actual finite allocation satisfies the displayed wire, guard or workspace condition. -/
theorem weightPair_budget (m w : ℕ) (pivot : Fin m) (hw : m-2≤w) :
    (weightLift m w (binaryPairControls pivot)).length-2≤(weightPool m w).length := by
  have hs : List.Sublist (binaryPairControls pivot) (List.finRange m) := List.filter_sublist
  have hl : (binaryPairControls pivot).length ≤ m := by simpa using hs.length_le
  simp only [weightLift, List.length_map, weightPool_length]
  omega

/-- The finite native construction `weightPair_targets_subset` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightPair_targets_subset (m w : ℕ) (pivot : Fin m) (mask : Reg m) :
    ∀ q∈weightLift m w (binaryPairTargets pivot mask),q∈weightLift m w (binaryPairControls pivot) := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  exact (weightLift_mem m w _ j).mpr ((mem_binaryPairControls pivot j).mpr
    ((mem_binaryPairTargets pivot j mask).mp hj).1)

/-- The finite native construction `weightPair_pivot_not_control` satisfies the displayed exact coordinate or algebraic relation. -/
theorem weightPair_pivot_not_control (m w : ℕ) (pivot : Fin m) :
    weightLabelWire m w pivot∉weightLift m w (binaryPairControls pivot) := by simp

/-- The actual finite allocation satisfies the displayed wire, guard or workspace condition. -/
theorem weightPivot_guard (m w : ℕ) (pivot : Fin m) (mask x : Reg m) :
    (weightLift m w (binaryPairControls pivot)).all (fun q =>
      !nativePivotBasis (weightLabelWire m w pivot) (weightLift m w (binaryPairTargets pivot mask))
        (weightInput m w x) q) =
    (binaryPairControls pivot).all (fun j => !nativePivotBasis pivot (binaryPairTargets pivot mask) x j) := by
  rw [weightPivotBasis]
  simp only [weightLift, List.all_map, Function.comp_def, weightInput_label]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
