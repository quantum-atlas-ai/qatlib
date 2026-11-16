/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUBProductBases

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — shared paper-level model

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
(PDF SHA-256 `b4cc74c840c902494d589b51c8e9706490f37cf2735e69a0486122131c6b7446`),
Section 1 (`introduction.tex`, pp. 1--3).

This file only fixes the paper's notation at dimension six on top of the existing
frozen implementation of orthonormal families:

* `QState6` is the ambient amplitude vector `ℂ^6`;
* `Family k` is a `k`-tuple of orthonormal bases of `ℂ^6` (each basis has six
  columns, exactly as in `Mub6Maximum.ThreeBasis.IsFamily`);
* `HasMUBFamily k` is the paper's assertion that `k` pairwise mutually unbiased
  orthonormal bases exist;
* `NoFourMUBs` is the assertion of Theorem 1.1 (`thm:main`) that no four exist;
* `MaximumNumberIs k` is the paper's `N(6) = k`.

No new mathematical hypothesis is introduced here. The definitions are literal
transcriptions of the paper's `N(d)` and of the frozen `IsFamily` contract, which
quantifies over all complex orthonormal bases and every pairwise overlap.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- The ambient Hilbert space `ℂ^6` of the paper. -/
abbrev QState6 : Type := QState (Fin 6)

/-- A `k`-tuple of orthonormal bases of `ℂ^6`, each listed as six column vectors. -/
abbrev Family (k : ℕ) : Type := Fin k → Fin 6 → QState6

/-- Paper Section 1: `k` pairwise mutually unbiased orthonormal bases of `ℂ^6`
exist (orthonormality and every cross overlap of squared modulus `1/6`). -/
def HasMUBFamily (k : ℕ) : Prop := ∃ B : Family k, IsFamily B

/-- Theorem 1.1 (`thm:main`) conclusion: there are no four pairwise mutually
unbiased orthonormal bases in `ℂ^6`. -/
def NoFourMUBs : Prop := ¬ HasMUBFamily 4

/-- Paper Section 1: `N(6) = k`, i.e. `k` bases exist and no larger family does. -/
noncomputable def MaximumNumberIs (k : ℕ) : Prop :=
  HasMUBFamily k ∧ ∀ m : ℕ, HasMUBFamily m → m ≤ k

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
