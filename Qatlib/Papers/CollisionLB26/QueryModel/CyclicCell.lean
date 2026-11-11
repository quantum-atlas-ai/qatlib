/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.Entries
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Cyclic characters and recording matrices

This module specializes the recording construction to the standard additive characters of `ZMod
N`, with `N` nonzero. Character orthogonality yields formulas for recording entries used in the
compressed query model associated with [MagniezZur2026].

## Main statements

* `character_sum`: vanishing sum for nonzero phase.
* `actualRecording_unitary`: the matrix identity expressing unitarity.
* `actualRecording_zero`, `actualRecording_empty`, and `actualRecording_labels`: explicit entry
  identities.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix AddChar
open scoped Classical BigOperators
namespace Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {N : ℕ} [NeZero N]

/-- The cyclic complex character `ZMod.stdAddChar (p*y)` indexed by the phase `p`. -/
def character (p y : ZMod N) : ℂ := ZMod.stdAddChar (p*y)

/-- Every value of the cyclic character has complex norm one. -/
theorem character_norm (p y : ZMod N) : ‖character p y‖=1 := AddChar.norm_apply _ _

/-- The product of the conjugate of a cyclic character value with that value is one. -/
theorem character_unitary (p y : ZMod N) : star (character p y)*character p y=1 := by
  rw [Complex.star_def,RCLike.conj_mul,character_norm]
  norm_num

/-- The sum of the cyclic character over all labels vanishes when the phase is nonzero. -/
theorem character_sum (p : ZMod N) (hp : p ≠ 0) : ∑ y : ZMod N,character p y=0 := by
  exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N hp)

/-- The recording matrix on optional cyclic labels associated with the character at phase `p`. -/
def actualRecording (p : ZMod N) : Matrix (Option (ZMod N)) (Option (ZMod N)) ℂ :=
    recording (character p)

/-- The conjugate transpose of the cyclic recording matrix times that matrix equals the
identity; see [MagniezZur2026]. -/
theorem actualRecording_unitary (p : ZMod N) : (actualRecording p)ᴴ*actualRecording p=1 := by
  ext i j
  have h := congrArg (fun M : Matrix (Option (ZMod N)) (Option (ZMod N)) ℂ => M i j)
    (recording_unitary (character p) (character_unitary p))
  by_cases hij : i=j <;> simpa [actualRecording,Matrix.one_apply,hij] using h

/-- The cyclic recording matrix at phase zero is the identity; see [MagniezZur2026]. -/
theorem actualRecording_zero : actualRecording (N := N) 0=1 := by
  have h : character (N := N) 0=fun _ => 1 := by funext y;simp [character]
  unfold actualRecording
  rw [h,recording_trivial]
  ext i j
  by_cases hij : i=j <;> simp [Matrix.one_apply,hij]

/-- For a nonzero phase, the empty-to-empty entry of the cyclic recording matrix is zero; see
[MagniezZur2026]. -/
theorem actualRecording_empty (p : ZMod N) (hp : p ≠ 0) : actualRecording p none none=0 :=
  recording_none_none (character p) (character_sum p hp)

/-- For a nonzero phase, expresses a label-to-label recording entry as a diagonal character term
plus the squared-coefficient correction; see [MagniezZur2026]. -/
theorem actualRecording_labels (p : ZMod N) (hp : p ≠ 0) (x y : ZMod N) :
    actualRecording p (some x) (some y)=
      (if x=y then character p x else 0)+(coefficient (ZMod N) : ℂ)^2*(1-character p x-character p y) := by
  by_cases hxy : x=y <;> simpa [actualRecording,hxy] using
    recording_some_some (character p) (character_sum p hp) x y
end Qatlib.Papers.CollisionLB26.QueryDefs
