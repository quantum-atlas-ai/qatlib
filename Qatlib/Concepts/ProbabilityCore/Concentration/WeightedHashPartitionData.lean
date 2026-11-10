/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashVectorData

namespace Qatlib.Concepts.ProbabilityCore.Concentration

noncomputable def weightedHashPartitionWeight {X T : Type} [DecidableEq T]
    (side : X → T) (p : X → ℂ) (t : T) (x : X) : ℂ :=
  if side x = t then p x else 0

noncomputable def weightedHashSideMass {X T : Type}
    [Fintype X] [DecidableEq T] (side : X → T) (p : X → ℂ) (t : T) : ℂ :=
  ∑ x : X, if side x = t then p x else 0

noncomputable def weightedHashPartitionBucket {H X A T : Type}
    [Fintype X] [DecidableEq A] [DecidableEq T]
    (hash : H → X → A) (side : X → T) (p : X → ℂ)
    (r : H) (a : A) (t : T) : ℂ :=
  ∑ x : X, if hash r x = a ∧ side x = t then p x else 0

noncomputable def weightedHashPartitionDeviation {H X A T : Type}
    [Fintype X] [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]
    (hash : H → X → A) (side : X → T) (p : X → ℂ) (r : H) : ℝ :=
  ∑ a : A, ∑ t : T, ‖weightedHashPartitionBucket hash side p r a t -
    (Fintype.card A : ℂ)⁻¹ * weightedHashSideMass side p t‖

end Qatlib.Concepts.ProbabilityCore.Concentration
