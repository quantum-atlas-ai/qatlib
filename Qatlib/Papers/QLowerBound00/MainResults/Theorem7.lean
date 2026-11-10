/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLowerBound00.MainResults.Model.ValueOracle
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.Theorem7

open Qatlib.Papers.QLowerBound00.MainResults.Model

theorem onePos_unique {N : ℕ} {one : Fin N} {x : InputD N N}
    (hinj : Function.Injective x) {i j : Fin N}
    (hi : x i = one) (hj : x j = one) : i = j :=
  hinj (hi.trans hj.symm)

def swapInput {N : ℕ} (x : InputD N N) (i j : Fin N) : InputD N N :=
  fun p => x (Equiv.swap i j p)

theorem swapInput_bijective {N : ℕ} {x : InputD N N} (hx : Function.Bijective x)
    (i j : Fin N) : Function.Bijective (swapInput x i j) :=
  hx.comp (Equiv.swap i j).bijective

theorem swapInput_apply {N : ℕ} (x : InputD N N) (i j p : Fin N) :
    swapInput x i j p = x (Equiv.swap i j p) := rfl

end Qatlib.Papers.QLowerBound00.MainResults.Theorem7
