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
def Corollary20InvariantSolutions : Prop :=
  ∀ (n k : ℕ) [NeZero n] (ε : ℝ),
    bssFeasible (m := 2 * n) (X := Fin (2 * n)) (Y := Fin n) (ospBit n) (ospFun n) k ε →
    ∃ M : Fin (2 * n) → ℕ → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ,
    ∃ N : ℕ → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ,
    ∃ Γ : Fin n → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ,
      ospInvariantFamily n M N Γ ∧
        bssFamilyFeasible (m := 2 * n) (X := Fin (2 * n)) (Y := Fin n)
          (ospBit n) (ospFun n) k ε M N Γ

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
