/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.SearchStopping.KnownCount

noncomputable def DiffusionCircuit (n : ℕ) : Circuit (Reg n) :=
  [Step.gate (HadamardN n), Step.gate (ZeroPhaseReflection n), Step.gate (HadamardN n)]

noncomputable def ExpandedStep (n : ℕ) : Circuit (Reg n) :=
  Step.query :: DiffusionCircuit n

noncomputable def ExpandedCircuit (n j : ℕ) : Circuit (Reg n) :=
  RepeatCircuit (ExpandedStep n) j
end Qatlib.Concepts.SearchStopping.KnownCount
