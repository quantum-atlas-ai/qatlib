/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib

open scoped Matrix

def BosonDistributionNormalization : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
    ∑ S : FockOccupation m n, bosonWeight A S = 1

end Qatlib.Concepts.BosonFock.PermAnalysis
