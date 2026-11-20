/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib.Papers.QAdversary11.WitnessCompose.LiteralComposition

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.QAdversary11.WitnessCompose.LiteralComposition

#check span_program_composition

example : identityComposition.wsizeS (fun _ _ => 1) (fun _ _ => true) = 1 :=
  identity_wsize

example : ¬ Nonempty (identityComposition.WitnessSet (fun _ _ => false)) :=
  identity_rejects
