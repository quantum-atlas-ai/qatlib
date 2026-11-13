/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# LinearCombinationEncoding — resource specifications

**Statement only — not proved in Qatlib.**

The paper's quantum algorithm is not constructed in this module. Declarations
ending in `_statement` specify abstract output accuracy and resource targets;
they are propositions, with no existence proof or counted implementation.
The legacy record fields alone do not certify execution costs.
-/

set_option autoImplicit false

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

namespace Qatlib.Papers.SpectralAmp17.MainResults.FlexibleQSP

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Statement only — not proved in Qatlib.**
Resource and accuracy specification for `corollary3_linearCombination`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def corollary3_linearCombination_statement (H : Matrix n n ℂ) (ε : ℝ)
    (hH : H.IsHermitian) (hnorm : ‖H‖ ≤ 1 / 2) (hε0 : 0 < ε) : Prop :=
    ∃ (F' : StandardForm n (Fin 4)),
      F'.Uᴴ * F'.U = 1 ∧ 0 ≤ F'.queries ∧ 0 ≤ F'.gates ∧
      F'.α = 1 ∧ ‖F'.H - H‖ ≤ ε ∧
      bigOConst F'.queries (Real.log (1 / ε))

end Qatlib.Papers.SpectralAmp17.MainResults.FlexibleQSP
