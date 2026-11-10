/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.KnownCount

noncomputable def distinguishedAfterC (N : ℕ) (k l : ℂ) : ℂ :=
  (2 / (N : ℂ) - 1) * k + 2 * ((N : ℂ) - 1) / N * l

noncomputable def ordinaryAfterC (N : ℕ) (k l : ℂ) : ℂ :=
  2 / (N : ℂ) * k + ((N : ℂ) - 2) / N * l

def Theorem2 : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (w : I) (k l : ℂ),
    ApplyGate (Diffusion I) (MarkedVector {w} k l) =
      MarkedVector {w} (distinguishedAfterC (Fintype.card I) k l)
        (ordinaryAfterC (Fintype.card I) k l)

end Qatlib.Concepts.SearchStopping.KnownCount
