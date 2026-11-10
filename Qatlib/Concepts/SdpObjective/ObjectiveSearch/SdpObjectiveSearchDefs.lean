/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.SdpObjective.ObjectiveSearch
open Qatlib.Concepts.DyadicFloor.FloorRounding
structure SearchState (D E : ℕ) where
  lower : ℚ
  upper : ℚ
  best : DiamondRationalCoordinates D E
  trace : List (ℚ × RationalEllipsoidRunResult (diamondDyadicWordCount D E))
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

def initial {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : SearchState D E :=
  let c := diamondRationalCenterCoordinates J
  ⟨0,diamondRationalScore c,c,[]⟩
def solve {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : SearchState D E :=
  let s := initial J
  let steps := dyadicPrecision ⌈4*(s.upper+1)/ε⌉₊
  searchLoop J (ε/8) steps s
def calls {D E : ℕ} (s : SearchState D E) : ℕ :=
  (s.trace.map (fun t => t.2.trace.length)).sum
end Qatlib.Concepts.SdpObjective.ObjectiveSearch
