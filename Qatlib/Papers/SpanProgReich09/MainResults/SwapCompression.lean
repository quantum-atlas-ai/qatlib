/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.SwapCompress.Swap

@[expose] public section


/-! # The two adjacency identities in the source Lemma 9.7

This source bridge does not assert the separate walk-oracle identity or query implementation.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath.SwapCompress

namespace Qatlib.Papers.SpanProgReich09.MainResults

/-- The two adjacency equalities in the source Lemma 9.7 follow from factorization. -/
theorem lemma97 {V : Type} [Fintype V] [DecidableEq V]
    (φ φx : V → V → ℂ) (AG AGx : Matrix V V ℂ)
    (hAG : ∀ v w, AG v w = star (φ v w) * φ w v)
    (hAGx : ∀ v w, AGx v w = star (φx v w) * φx w v) :
    szegedyM φ = AG ∧ szegedyM φx = AGx := by
  constructor
  · ext v w
    rw [swapEntry, hAG]
  · ext v w
    rw [swapEntry, hAGx]

end Qatlib.Papers.SpanProgReich09.MainResults
