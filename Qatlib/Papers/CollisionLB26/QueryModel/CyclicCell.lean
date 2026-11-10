/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.Entries
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Ring.Finite

set_option autoImplicit false
noncomputable section
open Matrix AddChar
open scoped Classical BigOperators
namespace Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {N : ℕ} [NeZero N]

def character (p y : ZMod N) : ℂ := ZMod.stdAddChar (p*y)

theorem character_norm (p y : ZMod N) : ‖character p y‖=1 := AddChar.norm_apply _ _

theorem character_unitary (p y : ZMod N) : star (character p y)*character p y=1 := by
  rw [Complex.star_def,RCLike.conj_mul,character_norm]
  norm_num

theorem character_sum (p : ZMod N) (hp : p ≠ 0) : ∑ y : ZMod N,character p y=0 := by
  exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N hp)

def actualRecording (p : ZMod N) : Matrix (Option (ZMod N)) (Option (ZMod N)) ℂ :=
    recording (character p)

theorem actualRecording_unitary (p : ZMod N) : (actualRecording p)ᴴ*actualRecording p=1 := by
  ext i j
  have h := congrArg (fun M : Matrix (Option (ZMod N)) (Option (ZMod N)) ℂ => M i j)
    (recording_unitary (character p) (character_unitary p))
  by_cases hij : i=j <;> simpa [actualRecording,Matrix.one_apply,hij] using h

theorem actualRecording_zero : actualRecording (N := N) 0=1 := by
  have h : character (N := N) 0=fun _ => 1 := by funext y;simp [character]
  unfold actualRecording
  rw [h,recording_trivial]
  ext i j
  by_cases hij : i=j <;> simp [Matrix.one_apply,hij]

theorem actualRecording_empty (p : ZMod N) (hp : p ≠ 0) : actualRecording p none none=0 :=
  recording_none_none (character p) (character_sum p hp)

theorem actualRecording_labels (p : ZMod N) (hp : p ≠ 0) (x y : ZMod N) :
    actualRecording p (some x) (some y)=
      (if x=y then character p x else 0)+(coefficient (ZMod N) : ℂ)^2*(1-character p x-character p y) := by
  by_cases hxy : x=y <;> simpa [actualRecording,hxy] using
    recording_some_some (character p) (character_sum p hp) x y
end Qatlib.Papers.CollisionLB26.QueryDefs
