/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashData
import Mathlib.Data.Matrix.Mul

namespace Qatlib.Concepts.ProbabilityCore.Concentration

noncomputable def finiteLinearMatrixHash {K I J : Type}
    [CommSemiring K] [Fintype I]
    (A : Matrix I J K) (v : I → K) : J → K :=
  fun j => ∑ i : I, A i j * v i

end Qatlib.Concepts.ProbabilityCore.Concentration
