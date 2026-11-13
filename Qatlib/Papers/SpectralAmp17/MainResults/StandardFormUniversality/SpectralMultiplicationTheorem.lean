/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Matrix.Spectrum

set_option backward.isDefEq.respectTransparency false

/-!
# SpectralMultiplicationTheorem — resource specifications

**Statement only — not proved in Qatlib.**

The paper's quantum algorithm is not constructed in this module. Declarations
ending in `_statement` specify abstract output accuracy and resource targets;
they are propositions, with no existence proof or counted implementation.
The legacy record fields alone do not certify execution costs.
-/

set_option autoImplicit false

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Polynomial
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

namespace Qatlib.Papers.SpectralAmp17.MainResults.StandardFormUniversality

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- **Statement only — not proved in Qatlib.**
Resource and accuracy specification for `theorem4_spectralMultiplication`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def theorem4_spectralMultiplication_statement
    (F : StandardForm S A) (B : Polynomial ℝ) (N : ℕ)
    (hα : F.α = 1) (hpar : IsParityPoly B N) (hdeg : B.natDegree ≤ N)
    (hB0 : B.eval 0 = 0) (hunit : unitRangeOnUnit B) : Prop :=
    ∃ (F' : StandardForm S (A × Fin 4)),
      F'.Uᴴ * F'.U = 1 ∧ 0 ≤ F'.queries ∧ 0 ≤ F'.gates ∧
      F'.H = polyEval B F.H ∧ F'.α = 1 ∧
      bigOConst F'.queries (N : ℝ) ∧
      bigOConst F'.gates ((N : ℝ) * Real.log (Fintype.card A))

end Qatlib.Papers.SpectralAmp17.MainResults.StandardFormUniversality
