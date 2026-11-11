/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Assumption21

/-!
# Feedback spins and finite field histories

`feedbackState` evolves three-dimensional spins using their own tensor-contraction fields, while
`fieldHistory` records the corresponding finite memory. The rotation-product identities identify
the spin readout with `phi` and connect clipped feedback to the bounded AMP representation used
in [GohMuller2026].

## Main statements

* `feedbackState_eq_product`: feedback spins equal rotation products evaluated on their field
  histories.
* `bounded_feedback_eq_spinOutput`: the clipped spin readout agrees with the AMP spin output.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
open Qatlib.Foundations.MatrixGeometry.AxisRotations.History
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
/-- The space of real three-component spin vectors. -/
abbrev Spin := Fin 3 → ℝ

/-- The initial spin vector `(1, 0, 0)`. -/
def initialSpin : Spin := ![1,0,0]

/-- The next field entry obtained by applying `κ` to the affine update of the tensor interaction
and local history. -/
def historyNext {r N : ℕ} (κ : ℝ → ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (s : ℕ → ℝ) (t : ℕ) (U : Fin (t+1) → Fin N → ℝ) : Fin N → ℝ :=
  fun i => κ (FCoord (s t) (interaction J (spinReadout s t U) i) (fun a => U a i))

/-- The recursively accumulated field history, starting from the seed transformed by `κ` and
appending `historyNext` at each step. -/
def fieldHistory {r N : ℕ} (κ : ℝ → ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) : (t : ℕ) → Fin (t+1) → Fin N → ℝ
  | 0 => fun _ i => κ (seed i)
  | t+1 => let U := fieldHistory κ J seed s t
    Fin.snoc U (historyNext κ J s t U)

/-- The field obtained by applying `κ` to the tensor interaction of the current z-components
plus the transformed-seed catalyst term. -/
def feedbackField {r N : ℕ} (κ : ℝ → ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) (n : Fin N → Spin) : Fin N → ℝ :=
  fun i => κ (interaction J (fun j => n j 2) i+κ (seed i)*(s t)^2*(1-s t))

/-- The recursive spin evolution from `initialSpin`, with each rotation driven by the field of
the current spin configuration. -/
def feedbackState {r N : ℕ} (κ : ℝ → ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) : ℕ → Fin N → Spin
  | 0 => fun _ => initialSpin
  | t+1 => let n := feedbackState κ J seed s t
    fun i => rotationStep (s (t+1)) (feedbackField κ J seed s t n i) *ᵥ n i

/-- The first entry of every field history is the seed transformed by `κ`. -/
theorem fieldHistory_initial {r N : ℕ} (κ : ℝ → ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) :
    fieldHistory κ J seed s t 0=fun i => κ (seed i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change Fin.snoc (α:=fun _ : Fin (t+2) => Fin N → ℝ) (fieldHistory κ J seed s t)
      (historyNext κ J s t (fieldHistory κ J seed s t)) ((0:Fin (t+1)).castSucc)=_
    rw [Fin.snoc_castSucc]
    exact ih

/-- Each feedback spin is the history rotation product applied to `initialSpin`, evaluated on
that site's accumulated fields. See [GohMuller2026]. -/
theorem feedbackState_eq_product {r N : ℕ} (κ : ℝ → ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) :
    feedbackState κ J seed s t=fun i =>
      historyProduct s t (fun a => fieldHistory κ J seed s t a.succ i) *ᵥ initialSpin := by
  induction t with
  | zero => funext i; simp [feedbackState, historyProduct]
  | succ t ih =>
    let U := fieldHistory κ J seed s t
    have hz : (fun i => feedbackState κ J seed s t i 2)=spinReadout s t U := by
      funext i
      rw [congrFun ih i]
      simp [spinReadout, fCoord, phi, initialSpin, Matrix.mulVec, dotProduct, Fin.sum_univ_three, U]
    have hm (i : Fin N) : fieldHistory κ J seed s (t+1) (Fin.last (t+1)) i=
        feedbackField κ J seed s t (feedbackState κ J seed s t) i := by
      simp only [fieldHistory, Fin.snoc_last, historyNext, FCoord]
      change κ (interaction J (spinReadout s t U) i+U 0 i*(s t)^2*(1-s t))=_
      rw [← hz]
      have h0 : U 0 i=κ (seed i) := congrFun (fieldHistory_initial κ J seed s t) i
      rw [h0]
      rfl
    funext i
    have hp : (fun a : Fin t => fieldHistory κ J seed s (t+1) a.castSucc.succ i)=
        (fun a : Fin t => fieldHistory κ J seed s t a.succ i) := by
      funext a
      simp only [fieldHistory, Fin.succ_castSucc, Fin.snoc_castSucc]
    change rotationStep (s (t+1)) (feedbackField κ J seed s t (feedbackState κ J seed s t) i) *ᵥ
        feedbackState κ J seed s t i =
      (rotationStep (s (t+1)) (fieldHistory κ J seed s (t+1) (Fin.last (t+1)) i) *
        historyProduct s t (fun a => fieldHistory κ J seed s (t+1) a.castSucc.succ i)) *ᵥ initialSpin
    rw [hp, hm, ← Matrix.mulVec_mulVec, congrFun ih i]

/-- The z-component of a feedback spin equals `phi` evaluated on its local field history. See
[GohMuller2026]. -/
theorem actual_feedback_phi {r N : ℕ} (κ : ℝ → ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) (i : Fin N) :
    feedbackState κ J seed s t i 2=
      phi s t (fun a => fieldHistory κ J seed s t a.succ i) := by
  rw [feedbackState_eq_product]
  simp [phi, initialSpin, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The field computed from the feedback spins equals the final entry appended to the next field
history. See [GohMuller2026]. -/
theorem actual_feedback_field {r N : ℕ} (κ : ℝ → ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) (i : Fin N) :
    feedbackField κ J seed s t (feedbackState κ J seed s t) i=
      fieldHistory κ J seed s (t+1) (Fin.last (t+1)) i := by
  simp only [fieldHistory, Fin.snoc_last, historyNext, feedbackField, FCoord]
  have hz : (fun j => feedbackState κ J seed s t j 2)=spinReadout s t (fieldHistory κ J seed s t) := by
    funext j
    exact actual_feedback_phi κ J seed s t j
  rw [hz]
  congr 1
  rw [congrFun (fieldHistory_initial κ J seed s t) i]

/-- Using `clip M` in the feedback history gives exactly `ampHistory M`. -/
theorem clipped_history_eq_amp {r N : ℕ} (M : ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) :
    fieldHistory (clip M) J seed s t=ampHistory M J seed s t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [fieldHistory, ampHistory, ih]
    rfl

/-- The z-component of the clipped feedback state equals the bounded AMP `spinOutput`. See
[GohMuller2026]. -/
theorem bounded_feedback_eq_spinOutput {r N : ℕ} (M : ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (T : ℕ) (i : Fin N) :
    feedbackState (clip M) J seed s T i 2=Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity.spinOutput M J seed s T i := by
  rw [actual_feedback_phi, clipped_history_eq_amp]
  rfl

end Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
