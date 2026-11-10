/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState
open Qatlib.Foundations.PureStateMath
open Qatlib

open Matrix

variable {D : ℕ}

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra

noncomputable def rejectRound (P Q : Operator D) (s : Bool) : Operator D :=
  (1 - P) * (if s then Q else 1 - Q) * (1 - P)

noncomputable def rejectWord (P Q : Operator D) (n : ℕ) (s : Fin n → Bool) : Operator D :=
  Fin.foldr n (fun j acc => rejectRound P Q (s j) * acc) 1

noncomputable def rejectFailProb (P Q : Operator D) (ψ : QState (Fin D)) (n : ℕ) : ℝ :=
  ∑ s : Fin n → Bool,
    (Inner (rejectWord P Q n s *ᵥ ((1 - P) *ᵥ ((1 - Q) *ᵥ ψ)))
      (rejectWord P Q n s *ᵥ ((1 - P) *ᵥ ((1 - Q) *ᵥ ψ)))).re
end Qatlib.Concepts.MixedInstrument.RewindAlgebra
