/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped Classical

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountSpec

def expected : Prop :=
  ∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N) (ε : ℝ), 0 < ε → ε ≤ 1 →
  ∀ (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
      2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)),
  (S.card = 0 →
    ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
      basicApproxCountPrefixWeight hN S ω *
        basicApproxCountFinalZero hN S ε ω (hω ω) = 1) ∧
  (0 < S.card →
    ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
      basicApproxCountPrefixWeight hN S ω *
        basicApproxCountFinalGood hN S ε ω (hω ω) ≥ 2/3)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountSpec
