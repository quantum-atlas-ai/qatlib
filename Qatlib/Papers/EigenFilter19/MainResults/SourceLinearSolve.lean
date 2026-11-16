/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic
public import Qatlib.Papers.EigenFilter19.MainResults.SourceProductInequality
public import Qatlib.Papers.EigenFilter19.MainResults.SourceQSVT
public import Qatlib.Papers.EigenFilter19.MainResults.SourceOverlap

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open scoped Classical BigOperators Matrix

open Qatlib.Papers.EigenFilter19.MainResults

namespace Qatlib.Papers.EigenFilter19.MainResults

section

/-- The `i`-th singular value `sqrt(λ_i(A†A))`. -/
def qsv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hAA : (Aᴴ * A).IsHermitian)
    (i : Fin n) : ℝ :=
  Real.sqrt (hAA.eigenvalues i)

/-- Row-wise `d`-sparsity: every row has at most `d` non-zero entries. -/
def RowSparse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (d : ℕ) : Prop :=
  ∀ i : Fin n, (Finset.univ.filter (fun j : Fin n => A i j ≠ 0)).card ≤ d

/-- The row sparsity predicate unfolds to its support-cardinality condition. -/
theorem rowSparse_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (d : ℕ) :
    RowSparse A d ↔
      ∀ i : Fin n, (Finset.univ.filter (fun j : Fin n => A i j ≠ 0)).card ≤ d :=
  Iff.rfl

end

end Qatlib.Papers.EigenFilter19.MainResults
