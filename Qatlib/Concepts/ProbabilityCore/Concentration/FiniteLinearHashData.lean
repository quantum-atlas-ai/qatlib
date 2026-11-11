/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashData
import Mathlib.Data.Matrix.Mul

/-!
# Finite matrix hash maps

`finiteLinearMatrixHash` defines a linear hash from input coordinates to output coordinates
using a finite matrix over a commutative semiring. Each output is the sum of the input
coordinates weighted by the corresponding matrix column.

This is the finite linear map underlying the random linear constructions considered in
[Ivanyos2008].

## Main statements

* `finiteLinearMatrixHash`: matrix column sums defining the hash output.

## References

* [Ivanyos, 2008][Ivanyos2008]
-/

namespace Qatlib.Concepts.ProbabilityCore.Concentration

/-- The hash sending `v` to the vector with coordinate `j` equal to `∑ i, A i j * v i`. -/
noncomputable def finiteLinearMatrixHash {K I J : Type}
    [CommSemiring K] [Fintype I]
    (A : Matrix I J K) (v : I → K) : J → K :=
  fun j => ∑ i : I, A i j * v i

end Qatlib.Concepts.ProbabilityCore.Concentration
