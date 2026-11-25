/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.Preparation
public import Qatlib.Concepts.QueryComplexity.PrepQueries.NativeOracle
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.QsvtCore.PhaseExistence.SparseAccessConstruction

@[expose] public section

/-!
# Coherent conditional rotations for a cached mass split

Each occupied node defines a single-qubit rotation. A vacant or all-zero node
can use the identity, since no mass flows into it from a positive-mass parent.
At each level, the address prefix controls the choice of rotation. This supplies
unitary level operations for the amplitude-loading procedures of
[KerenidisPrakash2017], Appendix A, and [ChenXueChenEtAl2022], Appendix E.
The cached masses specify exact gates. Synthesizing the rotation angles from
finite encoded words requires a precision model.
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QRAM.AmplitudeAccess

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QueryComplexity.PrepQueries (rotation rotation_unitary)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Foundations.PureStateMath (ApplyGate Ket)
open Matrix

variable {depth : ℕ}

/-- Rotate the next address bit using the two cached child masses. -/
noncomputable def branchGate (tree : Tree ℝ (depth + 1)) : Matrix Bool Bool ℂ :=
  if 0 < mass tree then rotation (branchAmplitude tree false) (branchAmplitude tree true) else 1

/-- Every branch rotation is unitary, including the zero-mass identity branch. -/
theorem branch_gate_unitary (tree : Tree ℝ (depth + 1)) (h : Valid tree) :
    branchGate tree ∈ Matrix.unitaryGroup Bool ℂ := by
  by_cases hPos : 0 < mass tree
  · rw [branchGate, ite_eq_left hPos]
    apply rotation_unitary
    have hLeft := mass_nonneg _ (valid_child tree false h)
    have hRight := mass_nonneg _ (valid_child tree true h)
    simp only [branchAmplitude, Real.sq_sqrt (div_nonneg hLeft hPos.le),
      Real.sq_sqrt (div_nonneg hRight hPos.le)]
    rw [← add_div, ← mass_eq_children tree h, div_self hPos.ne']
  · rw [branchGate, ite_eq_right hPos]
    exact (Matrix.unitaryGroup Bool ℂ).one_mem

/-- An occupied node's gate produces the two square-root branch amplitudes from a clean bit. -/
theorem branch_gate_ket_false (tree : Tree ℝ (depth + 1)) (hPos : 0 < mass tree) :
    ApplyGate (branchGate tree) (Ket false) =
      (branchAmplitude tree false : ℂ) • Ket false + (branchAmplitude tree true : ℂ) • Ket true := by
  rw [branchGate, ite_eq_left hPos]
  funext bit
  cases bit <;> simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, rotation]

/-- Apply the next-bit rotation controlled by the already loaded prefix. -/
noncomputable def controlledSplit {remaining : ℕ} (levels : ℕ)
    (tree : Tree ℝ (remaining + 1 + levels)) :
    Matrix (Address levels × Bool) (Address levels × Bool) ℂ :=
  blockDiagFirst (fun address => branchGate (subtree levels tree address))

/-- Superpositions of prefixes undergo a unitary next-bit operation. -/
theorem controlled_split_unitary {remaining : ℕ} (levels : ℕ)
    (tree : Tree ℝ (remaining + 1 + levels)) (h : Valid tree) :
    controlledSplit levels tree ∈ Matrix.unitaryGroup (Address levels × Bool) ℂ :=
  blockDiagFirst_unitary _ fun address => branch_gate_unitary _ (valid_subtree levels tree address h)

end Qatlib.Concepts.QRAM.AmplitudeAccess
