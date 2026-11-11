/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent

/-!
# Normalization statement for bosonic permanent weights

`BosonDistributionNormalization` states that the permanent weights of all occupations sum to one
whenever the input matrix has orthonormal columns. It packages the normalization property
independently of its proof.

The mathematical background is described in [KoehlerLeung2026].

## Main statements

* `BosonDistributionNormalization`: the normalization property for isometric input matrices.

## References

* [Koehler and Leung, 2026][KoehlerLeung2026]
-/

open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib

open scoped Matrix

/-- The proposition that the sum of `bosonWeight A S` over all occupations is one for every
matrix `A` satisfying `Aᴴ * A = 1`. -/
def BosonDistributionNormalization : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
    ∑ S : FockOccupation m n, bosonWeight A S = 1

end Qatlib.Concepts.BosonFock.PermAnalysis
