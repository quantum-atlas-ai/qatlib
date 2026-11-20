/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.Recovery.Kraus
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Correcting an ancillary bit flip while preserving the logical and reference systems -/

namespace QatlibTests.KrausRecovery

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ErrorCorrection.Recovery
open scoped Matrix

/-- Encode a logical qubit into the first ancillary sector. -/
def encoding : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1, 0; 0, 1; 0, 0; 0, 0]

/-- Reset the ancillary bit using one Kraus operator per input sector. -/
def reset (i : Fin 2) : Operator 4 :=
  if i = 0 then !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
  else !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

/-- Swap the two ancillary sectors while leaving the logical coordinate unchanged. -/
def flip (_ : Fin 1) : Operator 4 :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

/-- The encoding has orthonormal columns. -/
theorem encoding_iso : encodingᴴ * encoding = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [encoding, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The two ancillary reset branches are complete. -/
theorem reset_complete : KrausComplete reset := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [KrausComplete, reset, Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- The ancillary flip is a complete one-operator noise channel. -/
theorem flip_complete : KrausComplete flip := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [KrausComplete, flip, Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- After the flip, the first branch vanishes and the second branch restores the encoding. -/
theorem flip_correctable (j : Fin 1) : flip j ∈ correctable encoding reset := by
  rw [mem_correctable]
  intro i
  fin_cases i
  · refine ⟨0, ?_⟩
    apply Matrix.ext
    intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [encoding, reset, flip, Matrix.mul_apply, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    apply Matrix.ext
    intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [encoding, reset, flip, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A logical qubit survives the ancillary flip and reset along with any finite reference. -/
theorem reset_ref {ref : ℕ} (A : Matrix (Fin 2 × Fin ref) (Fin 2 × Fin ref) ℂ) :
    tensorLeft (krausMap reset) (tensorLeft (krausMap flip) (tensorLeft (conjBranch encoding) A)) =
      tensorLeft (conjBranch encoding) A :=
  recovers_ref encoding encoding_iso reset reset_complete flip flip_complete flip_correctable A

end QatlibTests.KrausRecovery
