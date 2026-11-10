/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux
set_option warningAsError false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

def QuditPureResourceMaxEntForm : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (U : Fin n × Fin n → Operator n) (Ψ : QState (Fin n × Fin n)),
    Normalized Ψ →
    QuditFixedCorrectionsTeleport n K U (outerProduct Ψ) →
    ∃ u v : Fin n → QState (Fin n),
      QuditOrthonormalFamily n u ∧ QuditOrthonormalFamily n v ∧
        quditMaxEntResource n u v = Ψ

end Qatlib.Concepts.QuditTeleport.QdLoccModel
