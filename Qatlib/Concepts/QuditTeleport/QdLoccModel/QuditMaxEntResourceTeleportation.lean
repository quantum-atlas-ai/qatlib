/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.ResourceIff
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open Matrix

def QuditMaxEntResourceTeleportation : Prop :=
  ∀ (n : ℕ) [NeZero n] (u v : Fin n → QState (Fin n)),
    QuditOrthonormalFamily n u → QuditOrthonormalFamily n v →
    ∀ o : Fin n × Fin n,
      (((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ)
          ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
      ∀ ρ : Operator n,
        (((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ *
            quditResourceBranchKraus n (quditMaxEntResource n u v) o) * ρ *
          ((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ *
            quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ)
          = (1 / (n : ℂ) ^ 2) • ρ

end Qatlib.Concepts.QuditTeleport.QdLoccModel
