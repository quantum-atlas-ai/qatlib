/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CssCodeCS96.Construction.Steane
import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The original Hamming table and the provider's coordinates

Equation (1) of the fixed Calderbank--Shor source lists these sixteen binary
words from left to right. The explicit permutation below identifies its check
matrix and full classical code with the canonical public Steane coordinates.
This is a coordinate bridge, not a proof of all the source's character-basis
identities or its arbitrary-decoherence recovery statement.
-/

namespace Qatlib.Papers.CssCodeCS96.Construction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Matrix

/-- The sixteen words in source equation (1), with the leftmost coordinate numbered zero. -/
def sourceWords : List (Fin 7 → ZMod 2) :=
  [![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 1],
   ![0, 0, 1, 0, 1, 1, 0], ![0, 0, 1, 1, 1, 0, 1],
   ![0, 1, 0, 0, 1, 1, 1], ![0, 1, 0, 1, 1, 0, 0],
   ![0, 1, 1, 0, 0, 0, 1], ![0, 1, 1, 1, 0, 1, 0],
   ![1, 0, 0, 0, 1, 0, 1], ![1, 0, 0, 1, 1, 1, 0],
   ![1, 0, 1, 0, 0, 1, 1], ![1, 0, 1, 1, 0, 0, 0],
   ![1, 1, 0, 0, 0, 1, 0], ![1, 1, 0, 1, 0, 0, 1],
   ![1, 1, 1, 0, 1, 0, 0], ![1, 1, 1, 1, 1, 1, 1]]

/-- A parity-check matrix for the source's systematic coordinate order. -/
def sourceCheck : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  ![![1, 1, 1, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 1, 0], ![1, 1, 0, 1, 0, 0, 1]]

/-- The source-to-provider coordinate permutation, with both inverse laws verified. -/
def sourcePerm : Equiv.Perm (Fin 7) where
  toFun := ![4, 6, 3, 5, 0, 1, 2]
  invFun := ![4, 5, 6, 2, 0, 3, 1]
  left_inv := by decide
  right_inv := by decide

set_option maxRecDepth 4096 in
/-- The original table is exactly the kernel of its stated-coordinate parity check. -/
theorem source_kernel : ∀ v : Fin 7 → ZMod 2,
    v ∈ sourceWords ↔ sourceCheck *ᵥ v = 0 := by decide

/-- Relabeling the public Steane columns gives the source-coordinate check matrix. -/
theorem source_check_eq : sourceCheck = steaneH.submatrix id sourcePerm := by decide

/-- The same coordinate permutation transports every syndrome, not only a sample word. -/
theorem source_syndrome (v : Fin 7 → ZMod 2) :
    steaneH *ᵥ (v ∘ sourcePerm.symm) = sourceCheck *ᵥ v := by
  rw [source_check_eq]
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix, Matrix.of_apply, id_eq,
    Function.comp_apply]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp sourcePerm (fun j => steaneH i j * v (sourcePerm.symm j))).symm

/-- Every source word, and only such a word, becomes a public Steane kernel word. -/
theorem source_table (v : Fin 7 → ZMod 2) :
    v ∈ sourceWords ↔ steaneH *ᵥ (v ∘ sourcePerm.symm) = 0 := by
  rw [source_syndrome]
  exact source_kernel v

end Qatlib.Papers.CssCodeCS96.Construction
