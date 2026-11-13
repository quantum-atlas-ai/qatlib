/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl
import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution

/-!
# Shared Controlled-Swap Imports

This module gathers the local reflection-gate vocabulary, known qubit control synthesis, and
controlled-copy evolution interfaces used by the fresh copy constructions. The imported
`ReflectionGate`, `knownQubitControlSteps`, and `controlledSwapRawGate` connect local circuit
descriptions with logical controlled interactions, using the circuit framework of
[NielsenChuang2010].

The module supplies a common namespace and import surface; the explicit layout, word semantics,
and clean frame implementation are developed in the companion modules.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators
set_option autoImplicit false

end Qatlib.Concepts.FreshCopyExec.QpeConsumers
