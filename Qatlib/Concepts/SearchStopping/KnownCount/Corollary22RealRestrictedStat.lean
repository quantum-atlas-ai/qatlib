/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic

namespace Qatlib.Concepts.SearchStopping.KnownCount

noncomputable def distinguishedAfter (N : ℕ) (k l : ℝ) : ℝ :=
  (2 / (N : ℝ) - 1) * k + (2 * ((N : ℝ) - 1) / N) * l

noncomputable def ordinaryAfter (N : ℕ) (k l : ℝ) : ℝ :=
  (2 / (N : ℝ)) * k + (1 - 2 / (N : ℝ)) * l

noncomputable def twoAmplitudeMass (N : ℕ) (k l : ℝ) : ℝ :=
  k ^ 2 + ((N : ℝ) - 1) * l ^ 2

def Corollary2_2RealRestricted : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (k l : ℝ),
    twoAmplitudeMass N (distinguishedAfter N k l) (ordinaryAfter N k l) =
      twoAmplitudeMass N k l

end Qatlib.Concepts.SearchStopping.KnownCount
