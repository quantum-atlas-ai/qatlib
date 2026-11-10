/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

namespace Qatlib.Concepts.ProbabilityCore.Concentration

noncomputable def finiteHashAverage {H : Type} [Fintype H] (f : H → ℝ) : ℝ :=
  (Fintype.card H : ℝ)⁻¹ * ∑ r : H, f r

noncomputable def weightedHashBucket {H X A : Type}
    [Fintype X] [DecidableEq A]
    (hash : H → X → A) (f : X → ℂ) (r : H) (a : A) : ℂ :=
  ∑ x : X, if hash r x = a then f x else 0

end Qatlib.Concepts.ProbabilityCore.Concentration
