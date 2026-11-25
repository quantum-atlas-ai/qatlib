/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommuteTest05.QueryDefs

@[expose] public section

/-!
# Phase kickback for the Boolean value oracle

The phase-kickback step of [Itakura2005], §1.2.5 reads the value of a Boolean function into a
sign on the input register. On the unnormalized difference vector `|x⟩ ⊗ (|0⟩ - |1⟩)` the
Boolean value oracle `Qatlib.Papers.CommuteTest05.QueryDefs.oracle` acts as the diagonal sign
`(-1)^{f x}`.

This module states the identity on the unnormalized vector, so no normalization side condition
enters. The vector is `kickbackVec x`, whose entries are `-1` on `(x, true)`, `1` on
`(x, false)`, and `0` elsewhere. It is the difference `|x, 0⟩ - |x, 1⟩` without the factor
`1 / sqrt 2`.

## Main statements

* `phaseSign_xor`: the bit sign is a character for exclusive-or.
* `oracle_phase_kickback`: the oracle sends `kickbackVec x` to its pointwise product with
  `phaseSign (f x)`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.CommuteTest05.QueryModel

/-- The sign attached to a Boolean bit: `-1` for `true` and `1` for `false`. -/
def phaseSign (b : Bool) : ℂ := if b then -1 else 1

/-- The bit sign is multiplicative over exclusive-or, i.e. it is a character of `Bool`. -/
theorem phaseSign_xor (a b : Bool) : phaseSign (Bool.xor a b) = phaseSign a * phaseSign b := by
  cases a <;> cases b <;> norm_num [phaseSign]

/-- The unnormalized two-branch vector `|x, 0⟩ - |x, 1⟩`, supported on the input label `x`. -/
def kickbackVec {X : Type} [DecidableEq X] (x : X) : X × Bool → ℂ :=
  fun p => if p.1 = x then phaseSign p.2 else 0

/-- The Boolean value oracle acts on `kickbackVec x` by the sign `(-1)^{f x}`. This is the
phase-kickback identity of [Itakura2005], §1.2.5, stated on the unnormalized difference vector. -/
theorem oracle_phase_kickback {X : Type} [Fintype X] [DecidableEq X]
    (f : X → Bool) (x : X) :
    Qatlib.Papers.CommuteTest05.QueryDefs.oracle f *ᵥ kickbackVec x =
      fun p : X × Bool => phaseSign (f x) * kickbackVec x p := by
  funext p
  rw [Matrix.mulVec, dotProduct]
  have hsingle :
      (∑ q : X × Bool,
          Qatlib.Papers.CommuteTest05.QueryDefs.oracle f p q * kickbackVec x q) =
        kickbackVec x (p.1, Bool.xor p.2 (f p.1)) := by
    rw [Fintype.sum_eq_single (p.1, Bool.xor p.2 (f p.1))]
    · rw [Qatlib.Papers.CommuteTest05.QueryDefs.oracle_apply, ite_eq_left rfl, one_mul]
    · intro q hq
      rw [Qatlib.Papers.CommuteTest05.QueryDefs.oracle_apply, ite_eq_right hq, zero_mul]
  rw [hsingle]
  simp only [kickbackVec]
  by_cases hp : p.1 = x
  · rw [ite_eq_left hp, ite_eq_left hp, phaseSign_xor, hp, mul_comm]
  · rw [ite_eq_right hp, ite_eq_right hp, mul_zero]

end Qatlib.Papers.CommuteTest05.QueryModel
