/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.FiniteExecution
public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.Counting

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — Theorem 1.1 (`thm:main`)

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`introduction.tex` lines 13--18, Theorem `thm:main`.

Paper statement: "Under the arithmetic and compiler conditions in Appendix A,
the fresh complete execution documented in Section 7 certifies that there are no
four pairwise mutually unbiased orthonormal bases in `ℂ^6`. Consequently,
`N(6) = 3`."

This file states both halves:
* `main_no_four` is the exclusion under the explicit finite-execution contract
  (`FiniteExecutionContract`, whose fields are the paper's Section 5--7
  propositions and the Appendix A contract);
* `main_N6_eq_three` adds the elementary lower bound `lem:three-mub-six` through
  `maximum_three_of_no_four`.

The statements do not drop the computer-assisted hypotheses: the unconditional
`N(6)=3` is only available in this library after the finite execution and the
binary64 arithmetic are certified, which is exactly the contract encoded here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge
open Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- Theorem 1.1, first sentence: the fresh complete execution (with Appendix A
arithmetic) certifies that no four pairwise mutually unbiased orthonormal bases
exist in `ℂ^6`. -/
theorem main_no_four (C : FiniteExecutionContract) : NoFourMUBs :=
  finite_execution_certificate C

/-- Theorem 1.1, second sentence: consequently `N(6) = 3`. -/
theorem main_N6_eq_three (C : FiniteExecutionContract) : MaximumNumberIs 3 :=
  maximum_three_of_no_four (main_no_four C)

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
