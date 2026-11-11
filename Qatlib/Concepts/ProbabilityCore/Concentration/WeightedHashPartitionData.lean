/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashVectorData

/-!
# Hash partitions and side information weights

The module defines complex weights masked to a side information class, total class masses, and
joint hash and side information buckets. `weightedHashPartitionDeviation` sums the norms of
their deviations from uniform hashing within each class.

These quantities describe finite weighted aggregation in the broader sampling and sketching
setting of [ChiaEtAl2022].

## Main statements

* `weightedHashPartitionWeight`: a complex weight restricted to one side information class.
* `weightedHashPartitionBucket`: a joint bucket mass.
* `weightedHashPartitionDeviation`: total absolute deviation from uniform bucket masses.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

namespace Qatlib.Concepts.ProbabilityCore.Concentration

/-- The complex weight `p x` when `side x = t`, and zero otherwise. -/
noncomputable def weightedHashPartitionWeight {X T : Type} [DecidableEq T]
    (side : X → T) (p : X → ℂ) (t : T) (x : X) : ℂ :=
  if side x = t then p x else 0

/-- The sum of complex weights in a fixed side information class. -/
noncomputable def weightedHashSideMass {X T : Type}
    [Fintype X] [DecidableEq T] (side : X → T) (p : X → ℂ) (t : T) : ℂ :=
  ∑ x : X, if side x = t then p x else 0

/-- The complex mass of inputs with both the specified hash value and side information value. -/
noncomputable def weightedHashPartitionBucket {H X A T : Type}
    [Fintype X] [DecidableEq A] [DecidableEq T]
    (hash : H → X → A) (side : X → T) (p : X → ℂ)
    (r : H) (a : A) (t : T) : ℂ :=
  ∑ x : X, if hash r x = a ∧ side x = t then p x else 0

/-- The sum over hash and side information values of the norm of each joint bucket's deviation
from its uniform share of the side mass. -/
noncomputable def weightedHashPartitionDeviation {H X A T : Type}
    [Fintype X] [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]
    (hash : H → X → A) (side : X → T) (p : X → ℂ) (r : H) : ℝ :=
  ∑ a : A, ∑ t : T, ‖weightedHashPartitionBucket hash side p r a t -
    (Fintype.card A : ℂ)⁻¹ * weightedHashSideMass side p t‖

end Qatlib.Concepts.ProbabilityCore.Concentration
