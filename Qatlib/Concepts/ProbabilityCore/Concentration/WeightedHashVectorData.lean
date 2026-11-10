/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashData
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Qatlib.Concepts.ProbabilityCore.Concentration

noncomputable def weightedHashDeviation {H X A : Type}
    [Fintype X] [Fintype A] [DecidableEq A]
    (hash : H → X → A) (f : X → ℂ) (r : H) (a : A) : ℂ :=
  weightedHashBucket hash f r a -
    (Fintype.card A : ℂ)⁻¹ * ∑ x : X, f x

noncomputable def weightedHashVectorDeviation {H X A T : Type}
    [Fintype X] [Fintype A] [DecidableEq A] [Fintype T]
    (hash : H → X → A) (f : T → X → ℂ) (r : H) : ℝ :=
  ∑ a : A, Real.sqrt (∑ k : T, Complex.normSq
    (weightedHashDeviation hash (f k) r a))

noncomputable def weightedHashVectorMass {X T : Type}
    [Fintype X] [Fintype T] (f : T → X → ℂ) : ℝ :=
  ∑ k : T, ∑ x : X, Complex.normSq (f k x)

end Qatlib.Concepts.ProbabilityCore.Concentration
