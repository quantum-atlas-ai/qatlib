/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesisDefs
import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateSynthesis

/-!
# Fixed-gate synthesis requests and ledger obligations

This module defines the request data and predicates used by the fixed-gate synthesis interface
associated with [DawsonNielsen2006]. `SynthesisRequest` stores a local gate and precision,
`requestBits` records its input bit requirement, and `uniformLedgerObligation` states the
universal resource-ledger obligation; `middleWindow` specifies the intermediate exponent range.

## Main statements

* `SynthesisRequest`: A synthesis request consisting of a local QFT gate and a natural-number
  precision parameter.
* `uniformLedgerObligation`: The proposition that every synthesis compiler satisfies
  `UniformSynthLedger`.

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit
open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Papers.SolovayKitaev05.MainResults

open Qatlib

set_option autoImplicit false

/-- The ambient local QFT gate type at width `w`, used as the synthesis alphabet. -/
abbrev FixedAlphabet (w : ℕ) := LocalQFTGate w

/-- A synthesis request consisting of a local QFT gate and a natural-number precision parameter. -/
structure SynthesisRequest (w : ℕ) where

  gate : LocalQFTGate w

  precision : ℕ

/-- The input bit count required by the gate and precision in a synthesis request. -/
def requestBits {w : ℕ} (r : SynthesisRequest w) : ℕ :=
  Qatlib.Concepts.NumericalWord.MixedWordError.synthInputBits w r.gate r.precision

/-- The proposition that every synthesis compiler satisfies `UniformSynthLedger`. -/
def uniformLedgerObligation : Prop :=
  ∀ c : SynthCompiler, UniformSynthLedger c

/-- The intermediate exponent range `4 ≤ e ≤ k + 1`. -/
def middleWindow (e k : ℕ) : Prop := 4 ≤ e ∧ e ≤ k + 1

end Qatlib.Papers.SolovayKitaev05.MainResults
