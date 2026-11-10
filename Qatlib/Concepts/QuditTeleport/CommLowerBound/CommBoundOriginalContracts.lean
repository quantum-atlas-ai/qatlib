/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib

def CommBoundMessageInjectiveQuditLegacy : Prop :=
  ∀ (n : ℕ) [NeZero n] (κ : Type) [Fintype κ] (m : Fin n × Fin n → κ)
    (Cm : κ → Operator n),
    (∀ ρ : Operator n,
      (∑ w : Fin n × Fin n, conjBranch (Cm (m w) * quditBranchKraus n w) ρ) = ρ) →
      Function.Injective m ∧ n * n ≤ Fintype.card κ

def CommBoundMessageInjectiveBellLegacy : Prop :=
  ∀ (κ : Type) [Fintype κ] (m : Bool × Bool → κ) (Cm : κ → Operator 2),
    (∀ ρ : Operator 2,
      (∑ o : Bool × Bool, conjBranch (Cm (m o) * teleportBranchKraus o) ρ) = ρ) →
      Function.Injective m ∧ Fintype.card (Bool × Bool) ≤ Fintype.card κ

end Qatlib.Concepts.QuditTeleport.CommLowerBound
