/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionLB26.QueryModel.CyclicCell
import Qatlib.Concepts.CompressedQuery.CyclicRecord.OffDiagonal
import Qatlib.Concepts.CompressedQuery.CyclicRecord.Action

/-!
# Entry bounds for cyclic recording queries

This module computes empty-label recording entries and bounds off-diagonal label entries for the
cyclic recording matrix used in the query analysis of [MagniezZur2026]. It also packages the
matrix as the isometry `actualRecordingAction`.

## Main statements

* `actual_coefficient`: the coefficient `1/sqrt N`.
* `actualRecording_off_diagonal`: the entry-norm bound `3/N` for distinct labels and nonzero
  phase.
* `actualRecordingAction_apply`: agreement between the isometry and matrix action.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {N : ℕ} [NeZero N]

/-- The recording coefficient for `ZMod N` is `1/sqrt N`. -/
theorem actual_coefficient : coefficient (ZMod N)=1/Real.sqrt (N : ℝ) := by
    simp [coefficient,ZMod.card]

/-- For a nonzero phase, the recording-matrix entry from a label column to the empty row is the
character value scaled by `1/sqrt N`; see [MagniezZur2026]. -/
theorem actualRecording_empty_label (p : ZMod N) (hp : p ≠ 0) (y : ZMod N) :
    actualRecording p none (some y)=((1/Real.sqrt (N : ℝ) : ℝ) : ℂ)*character p y := by
  simpa only [actualRecording,actual_coefficient] using
      recording_none_some (character p) (character_sum p hp) y

/-- For a nonzero phase, the recording-matrix entry from the empty column to a label row is the
character value scaled by `1/sqrt N`; see [MagniezZur2026]. -/
theorem actualRecording_label_empty (p : ZMod N) (hp : p ≠ 0) (y : ZMod N) :
    actualRecording p (some y) none=((1/Real.sqrt (N : ℝ) : ℝ) : ℂ)*character p y := by
  simpa only [actualRecording,actual_coefficient] using
      recording_some_none (character p) (character_sum p hp) y

/-- For a nonzero phase and distinct labels, the norm of the corresponding recording-matrix
entry is at most `3/N`; see [MagniezZur2026]. -/
theorem actualRecording_off_diagonal (p : ZMod N) (hp : p ≠ 0) (x y : ZMod N) (hxy : x ≠ y) :
    ‖actualRecording p (some x) (some y)‖ ≤ 3/(N : ℝ) := by
  simpa only [actualRecording,ZMod.card] using
    recording_off_diagonal_bound (character p) (character_sum p hp) (character_norm p) x y hxy

/-- The complex linear isometric equivalence induced by the cyclic recording matrix. -/
def actualRecordingAction (p : ZMod N) :
    EuclideanSpace ℂ (Option (ZMod N)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Option (ZMod N)) :=
  recordingAction (character p) (character_unitary p)

/-- The recording isometry acts by multiplication with `actualRecording p`, transported to
Euclidean-space coordinates. -/
theorem actualRecordingAction_apply (p : ZMod N) (ψ : EuclideanSpace ℂ (Option (ZMod N))) :
    actualRecordingAction p ψ=WithLp.toLp 2 (actualRecording p*ᵥ WithLp.ofLp ψ) := rfl
end Qatlib.Papers.CollisionLB26.QueryDefs
