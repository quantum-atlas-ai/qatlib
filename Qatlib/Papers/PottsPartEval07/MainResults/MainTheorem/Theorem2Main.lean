/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Potts evaluation headline specification

**Statement only — not proved in Qatlib.**

The quantum evaluator of Theorem 2 is not constructed here. The definition below
records a contract relative to supplied subroutine-call semantics. A call word
must produce the scheme's output and success value, and its length must equal
the cost. The supplied semantics must be instantiated by an implementation;
none is constructed here. The pointwise constant does not express a uniform
asymptotic bound.
-/
open Qatlib.Papers.PottsPartEval07.MainResults
open Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators

/- ## The Potts partition function -/

/-- **Statement only — not proved in Qatlib.**
Contract inspired by Theorem 2, relative to an externally supplied interpreter
`execute` for unit-cost subroutine calls. Cost is the length of the call word.
No interpreter implementation, uniform asymptotic bound or quantum success
analysis is proved here. -/
def theorem2_main_statement
    (q : ℕ) (hq : 2 ≤ q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (s : ℕ → ℕ)
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (J : E → ℝ)
    (Call : Type*) (execute : List Call → ℝ × ℝ)
    (n k : ℕ) (hn : n = Fintype.card E)
    (hk : k = Fintype.card E - Fintype.card V + 1)
    (hk1 : 1 ≤ k) (hiccc : IsIccc q n k ε) : Prop :=
    ∃ (scheme : PottsScheme q ends J) (calls : List Call) (C : ℝ),
      scheme.output = (execute calls).1 ∧
      scheme.successProb = (execute calls).2 ∧
      scheme.cost = calls.length ∧ 0 < C ∧
      (scheme.cost : ℝ) ≤ C * (1 / ε) * (k : ℝ) ^ 2 * max (1 : ℝ) (s k) *
        (Real.log (q : ℝ)) ^ 2 ∧
      scheme.successProb ≥ 1 - delta q k ε

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
