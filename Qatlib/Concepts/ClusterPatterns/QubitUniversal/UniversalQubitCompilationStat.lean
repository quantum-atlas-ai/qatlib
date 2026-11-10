/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalGraphDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
set_option autoImplicit false
namespace Qatlib.Concepts.ClusterPatterns.QubitUniversal
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

def UniversalQubitCompilation : Prop :=
  ∀ (U : Matrix Bool Bool ℂ), U ∈ Matrix.unitaryGroup Bool ℂ →
    (mbqcQubitWord U).length = 4 ∧ (∀ ζ ∈ mbqcQubitWord U, ‖ζ‖=1) ∧
    ‖mbqcQubitScalar U‖=1 ∧
    clusterSequenceUnitary (mbqcQubitWord U) =
      mbqcQubitScalar U • relabelGate boolEquivFin2 U

end Qatlib.Concepts.ClusterPatterns.QubitUniversal
