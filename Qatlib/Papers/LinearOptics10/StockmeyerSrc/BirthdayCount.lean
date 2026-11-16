/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.FockCard
public import Qatlib.Concepts.BosonFock.BosonOperators.FockFree
public import Qatlib.Concepts.BosonFock.BosonOperators.ChooseRatio

@[expose] public section


/-! # Complete actual occupation counting bound

Aaronson--Arkhipov, arXiv:1011.3245v1, Proposition 71. Both finite
cardinalities come from explicit equivalences on the actual public types;
the positive-integer binomial ratio bound is proved independently.
-/

set_option autoImplicit false
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.BirthdayCount
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.BosonFock.BosonOperators

/-- The complete original collision-free fraction bound holds for all positive n at most m. -/
theorem freeFraction (m n : ℕ) (hm : 0 < m) (hn1 : 1 ≤ n) (hn : n ≤ m) :
    1 - (n : ℝ)^2/(m : ℝ) < ((collisionFreeFock m n).card : ℝ)/
      (Fintype.card (FockOccupation m n) : ℝ) := by
  rw [FockFree.freeCard, FockCard.occCard]
  exact ChooseRatio.lowerBound m n hm hn1 hn

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.BirthdayCount
