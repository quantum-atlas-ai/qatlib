/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchInstance

@[expose] public section
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.OrderedOracle.TiSdpBridge
def Proposition19CyclicSymmetry : Prop :=
  ∀ (n : ℕ) [NeZero n],
    IsBssSymmetry (m := 2 * n) (X := Fin (2 * n)) (Y := Fin n) (ospBit n) (ospFun n)
      (finShiftEquiv (2 * n)) (finShiftEquiv (2 * n)).symm (finShiftEquiv n)

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
