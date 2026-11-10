/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesisDefs
import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateSynthesis
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

abbrev FixedAlphabet (w : ℕ) := LocalQFTGate w

structure SynthesisRequest (w : ℕ) where

  gate : LocalQFTGate w

  precision : ℕ

def requestBits {w : ℕ} (r : SynthesisRequest w) : ℕ :=
  Qatlib.Concepts.NumericalWord.MixedWordError.synthInputBits w r.gate r.precision

def uniformLedgerObligation : Prop :=
  ∀ c : SynthCompiler, UniformSynthLedger c

def middleWindow (e k : ℕ) : Prop := 4 ≤ e ∧ e ≤ k + 1

end Qatlib.Papers.SolovayKitaev05.MainResults
