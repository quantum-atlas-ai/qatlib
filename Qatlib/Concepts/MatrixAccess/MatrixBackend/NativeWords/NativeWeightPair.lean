/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeWeightGeometry

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! The actual canonical source pair word transports the explicit physical
clean frame to the previously derived binary pair operator. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical Kronecker

/-- Construction for weight Pair Word in the native weight pair model. -/
def weightPairWord (m w : ℕ) (pivot : Fin m) (mask : Reg m) (r : Circle) :
    List (ReflectionGate (weightWidth m w)) :=
  nativeTwoLevelWord (weightLift m w (binaryPairControls pivot)) (weightWorkWire m w)
    (weightLabelWire m w pivot) (weightPool m w) (weightLift m w (binaryPairTargets pivot mask)) r

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem weightPairWord_basis (m w : ℕ) (pivot : Fin m) (mask : Reg m) (r : Circle)
    (hw : m-2≤w) (x : Reg m) :
    Run (1 : Matrix (Reg (weightWidth m w)) (Reg (weightWidth m w)) ℂ)
      (reflectionCompile (weightPairWord m w pivot mask r)) (Qatlib.Foundations.PureStateMath.Ket (weightInput m w x)) =
      weightFrame m w *ᵥ nativePairColumn (binaryPairControls pivot) pivot (binaryPairTargets pivot mask) r x := by
  have ht : (weightLift m w (binaryPairTargets pivot mask)).Nodup :=
    (binaryPairTargets_nodup pivot mask).map (weightLabelWire_injective m w)
  have hb := nativeTwoLevelWord_basis (weightLift m w (binaryPairControls pivot))
    (weightWorkWire m w) (weightLabelWire m w pivot) (weightPool m w)
    (weightLift m w (binaryPairTargets pivot mask)) r
    (weightAllocation m w _ (binaryPairControls_nodup pivot)) (weightPair_budget m w pivot hw)
    ht (weightPair_targets_subset m w pivot mask) (weightLabel_ne_work m w pivot)
    (weightPair_pivot_not_control m w pivot) (weightLabel_not_pool m w pivot)
    (weightInput m w x) (weightInput_pool m w x) (weightInput_work m w x)
  simp only [weightPivot_guard, weightInput_label, weightPairAddress] at hb
  change Run 1 (reflectionCompile (nativeTwoLevelWord _ _ _ _ _ _)) _ = _
  rw [hb]
  unfold nativePairColumn
  by_cases hg : (binaryPairControls pivot).all
      (fun j => !nativePivotBasis pivot (binaryPairTargets pivot mask) x j)=true
  · rw [ite_eq_left hg, ite_eq_left hg, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      weightFrame_ket, weightFrame_ket]
  · rw [ite_eq_right hg, ite_eq_right hg, weightFrame_ket]

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem weightPairWord_frame (m w : ℕ) (pivot : Fin m) (mask : Reg m) (r : Circle) (hw : m-2≤w) :
    reflectionProgramMatrix (weightPairWord m w pivot mask r) * weightFrame m w =
      weightFrame m w * nativePairGate (binaryPairControls pivot) pivot (binaryPairTargets pivot mask) r := by
  apply Qatlib.Concepts.GateVocabulary.GateVocab.matrix_ext_on_kets
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, weightFrame_ket]
  change ApplyGate (reflectionProgramMatrix (weightPairWord m w pivot mask r)) (Qatlib.Foundations.PureStateMath.Ket (weightInput m w x)) =
    weightFrame m w *ᵥ ApplyGate (nativePairGate _ _ _ _) (Qatlib.Foundations.PureStateMath.Ket x)
  rw [← run_reflectionCompile, nativePairGate_ket]
  exact weightPairWord_basis m w pivot mask r hw x

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem weightPairWord_legal (m w : ℕ) (pivot : Fin m) (mask : Reg m) (r : Circle) (hw : m-2≤w) :
    reflectionLegal (weightPairWord m w pivot mask r) :=
  nativeTwoLevelWord_legal _ _ _ _ _ r
    (weightAllocation m w _ (binaryPairControls_nodup pivot)) (weightPair_budget m w pivot hw)
    (weightPair_targets_subset m w pivot mask) (weightLabel_ne_work m w pivot)
    (weightPair_pivot_not_control m w pivot)

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem weightPairWord_counts (m w : ℕ) (pivot : Fin m) (mask : Reg m) (r : Circle) (hw : m-2≤w) :
    QueryCount (reflectionCompile (weightPairWord m w pivot mask r)) = 0 ∧
    GateCount (reflectionCompile (weightPairWord m w pivot mask r)) =
      2*(binaryPairTargets pivot mask).length+2*(2*(binaryPairControls pivot).length+
        (if (binaryPairControls pivot).length≤1 then 1 else 15*(2*(binaryPairControls pivot).length-3)))+6 := by
  simpa [weightPairWord, weightLift, List.length_map] using
    nativeTwoLevelWord_counts (weightLift m w (binaryPairControls pivot)) (weightWorkWire m w)
      (weightLabelWire m w pivot) (weightPool m w) (weightLift m w (binaryPairTargets pivot mask)) r
      (weightPair_budget m w pivot hw)

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem weightPairWord_tensor_frame {H I : Type*} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (m w : ℕ) (pivot : Fin m) (mask : Reg m) (r : Circle)
    (hw : m-2≤w) (F : Matrix H I ℂ) :
    (reflectionProgramMatrix (weightPairWord m w pivot mask r) ⊗ₖ (1 : Matrix H H ℂ)) *
      (weightFrame m w ⊗ₖ F) =
      (weightFrame m w ⊗ₖ F) *
        (nativePairGate (binaryPairControls pivot) pivot (binaryPairTargets pivot mask) r ⊗ₖ
          (1 : Matrix I I ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, weightPairWord_frame m w pivot mask r hw]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
