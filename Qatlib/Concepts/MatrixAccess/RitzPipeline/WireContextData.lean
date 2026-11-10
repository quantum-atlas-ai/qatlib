/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open scoped BigOperators
set_option autoImplicit false

noncomputable def wireContextExtend {a L : ℕ} (e : Fin a ↪ Fin L)
    (s : Reg L) (x : Reg a) : Reg L := Function.extend e x s

noncomputable def wireContextEmbed {a L : ℕ} (e : Fin a ↪ Fin L)
    (s : Reg L) (ψ : QState (Reg a)) : QState (Reg L) :=
  ∑ x, ψ x • Ket (wireContextExtend e s x)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
