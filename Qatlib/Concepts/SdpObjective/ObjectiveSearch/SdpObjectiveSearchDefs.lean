/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs

/-!
# Rational objective search state and recursion

`SearchState` stores rational interval endpoints, a candidate dual point, and the history of
ellipsoid solver calls. `searchLoop` bisects the interval using feasible and exhausted outcomes,
while `solve` chooses the tolerance and iteration count from the input matrix and ε.

For the mathematical background, see [Watrous2018].

## Main statements

* `solve`: Runs objective search from `initial` with tolerance ε/8 and the prescribed dyadic
  iteration count.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.SdpObjective.ObjectiveSearch
open Qatlib.Concepts.DyadicFloor.FloorRounding
/-- The state of rational objective bisection, containing interval endpoints, the best
coordinate vector, and the history of thresholds and ellipsoid results. -/
structure SearchState (D E : ℕ) where
  lower : ℚ
  upper : ℚ
  best : DiamondRationalCoordinates D E
  trace : List (ℚ × RationalEllipsoidRunResult (diamondDyadicWordCount D E))
/-- Performs at most the specified number of midpoint solver calls, updating the interval on
feasible or exhausted outcomes and returning immediately on an invalid outcome. -/
def searchLoop {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (η : ℚ) :
    ℕ → SearchState D E → SearchState D E
  | 0,s => s
  | k+1,s =>
      let mid := (s.lower+s.upper)/2
      let out := diamondEllipsoidSolve J mid η
      let tr := s.trace ++ [(mid,out)]
      match out.outcome with
      | .feasible => searchLoop J η k ⟨s.lower,mid,out.state.center,tr⟩
      | .exhausted => searchLoop J η k ⟨mid-η,s.upper,s.best,tr⟩
      | .invalid => ⟨s.lower,s.upper,s.best,tr⟩

/-- The initial search state with lower endpoint zero, the rational center as candidate, its
score as upper endpoint, and empty history. -/
def initial {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : SearchState D E :=
  let c := diamondRationalCenterCoordinates J
  ⟨0,diamondRationalScore c,c,[]⟩
/-- Runs objective search from `initial` with tolerance ε/8 and the prescribed dyadic iteration
count. -/
def solve {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : SearchState D E :=
  let s := initial J
  let steps := dyadicPrecision ⌈4*(s.upper+1)/ε⌉₊
  searchLoop J (ε/8) steps s
/-- The total number of ellipsoid trace entries across all objective-search calls stored in the
state. -/
def calls {D E : ℕ} (s : SearchState D E) : ℕ :=
  (s.trace.map (fun t => t.2.trace.length)).sum
end Qatlib.Concepts.SdpObjective.ObjectiveSearch
