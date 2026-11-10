/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.KnownCount

def Theorem1 : Prop :=
  ∀ n : ℕ, Diffusion (Reg n) = HadamardN n * ZeroPhaseReflection n * HadamardN n

end Qatlib.Concepts.SearchStopping.KnownCount
