/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open scoped ComplexOrder

def QuditResourceMarginalConverse : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (U : Fin n × Fin n → Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ),
    ω.PosSemidef → QuditFixedCorrectionsTeleport n K U ω →
    PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n)) ω)
      = (1 / (n : ℂ)) • (1 : Operator n)

end Qatlib.Concepts.QuditTeleport.QdLoccModel
