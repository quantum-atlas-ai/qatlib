/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TuraevViro10.MainResults.BqpHardness

@[expose] public section

/-!
# Strict gate approximation budget

The converse part of Theorem 1 uses the strict overlap gap in Eq. (2).
A total state approximation error below one twelfth provides this gap.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TuraevViro10.MainResults

open Qatlib.Papers.TuraevViro10.MainResults.BqpHardness

/-- A strict state error budget yields the strict squared-overlap gap in Eq. (2). -/
theorem gate_error_lt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : ℕ} (U V : Fin T → H → H) (ψ : H) (η : ℝ) (hη : 0 ≤ η) (hψ : ‖ψ‖ = 1)
    (hU : ∀ i z w, ‖U i z - U i w‖ = ‖z - w‖)
    (hV : ∀ i z, ‖V i z - U i z‖ ≤ η)
    (hUle : ‖inner ℂ ψ (gateRun U ψ)‖ ≤ 1)
    (hVle : ‖inner ℂ ψ (gateRun V ψ)‖ ≤ 1)
    (hprec : (T : ℝ) * η < 1 / 12) :
    |‖inner ℂ ψ (gateRun U ψ)‖ ^ 2 - ‖inner ℂ ψ (gateRun V ψ)‖ ^ 2| < 1 / 6 := by
  have hstate := gateRun_error_le U V ψ η hη hU hV
  have hbound := matrixElement_normSq_error ψ hψ (gateRun U) (gateRun V)
    (by simpa [norm_sub_rev] using hstate) hUle hVle
  exact hbound.trans_lt (by linarith)

end Qatlib.Papers.TuraevViro10.MainResults
