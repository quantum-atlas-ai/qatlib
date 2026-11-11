/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLowerBound00.MainResults.Model.ValueOracle

/-!
# Swapping positions of permutation inputs

This module supplies elementary facts about permutation-valued inputs. The operation `swapInput`
exchanges two input positions and preserves bijectivity; `onePos_unique` gives uniqueness of the
position of a specified value for an injective input. See [Ambainis2002] for the paper's
setting.

## Main statements

* `onePos_unique`: For an injective input, two positions carrying the same specified value are
  equal.
* `swapInput_apply`: The value of `swapInput x i j` at `p` is `x (Equiv.swap i j p)`.

## References

* [Ambainis, 2002][Ambainis2002]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.Theorem7

open Qatlib.Papers.QLowerBound00.MainResults.Model

/-- For an injective input, two positions carrying the same specified value are equal. -/
theorem onePos_unique {N : ℕ} {one : Fin N} {x : InputD N N}
    (hinj : Function.Injective x) {i j : Fin N}
    (hi : x i = one) (hj : x j = one) : i = j :=
  hinj (hi.trans hj.symm)

/-- The input obtained by precomposing `x` with the transposition of positions `i` and `j`. -/
def swapInput {N : ℕ} (x : InputD N N) (i j : Fin N) : InputD N N :=
  fun p => x (Equiv.swap i j p)

/-- Swapping two positions of a bijective input preserves bijectivity. -/
theorem swapInput_bijective {N : ℕ} {x : InputD N N} (hx : Function.Bijective x)
    (i j : Fin N) : Function.Bijective (swapInput x i j) :=
  hx.comp (Equiv.swap i j).bijective

/-- The value of `swapInput x i j` at `p` is `x (Equiv.swap i j p)`. -/
theorem swapInput_apply {N : ℕ} (x : InputD N N) (i j p : Fin N) :
    swapInput x i j p = x (Equiv.swap i j p) := rfl

end Qatlib.Papers.QLowerBound00.MainResults.Theorem7
