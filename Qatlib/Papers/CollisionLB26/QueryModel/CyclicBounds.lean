/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionLB26.QueryModel.CyclicCell
import Qatlib.Concepts.CompressedQuery.CyclicRecord.OffDiagonal
import Qatlib.Concepts.CompressedQuery.CyclicRecord.Action

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {N : ℕ} [NeZero N]

theorem actual_coefficient : coefficient (ZMod N)=1/Real.sqrt (N : ℝ) := by
    simp [coefficient,ZMod.card]

theorem actualRecording_empty_label (p : ZMod N) (hp : p ≠ 0) (y : ZMod N) :
    actualRecording p none (some y)=((1/Real.sqrt (N : ℝ) : ℝ) : ℂ)*character p y := by
  simpa only [actualRecording,actual_coefficient] using
      recording_none_some (character p) (character_sum p hp) y

theorem actualRecording_label_empty (p : ZMod N) (hp : p ≠ 0) (y : ZMod N) :
    actualRecording p (some y) none=((1/Real.sqrt (N : ℝ) : ℝ) : ℂ)*character p y := by
  simpa only [actualRecording,actual_coefficient] using
      recording_some_none (character p) (character_sum p hp) y

theorem actualRecording_off_diagonal (p : ZMod N) (hp : p ≠ 0) (x y : ZMod N) (hxy : x ≠ y) :
    ‖actualRecording p (some x) (some y)‖ ≤ 3/(N : ℝ) := by
  simpa only [actualRecording,ZMod.card] using
    recording_off_diagonal_bound (character p) (character_sum p hp) (character_norm p) x y hxy

def actualRecordingAction (p : ZMod N) :
    EuclideanSpace ℂ (Option (ZMod N)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Option (ZMod N)) :=
  recordingAction (character p) (character_unitary p)

theorem actualRecordingAction_apply (p : ZMod N) (ψ : EuclideanSpace ℂ (Option (ZMod N))) :
    actualRecordingAction p ψ=WithLp.toLp 2 (actualRecording p*ᵥ WithLp.ofLp ψ) := rfl
end Qatlib.Papers.CollisionLB26.QueryDefs
