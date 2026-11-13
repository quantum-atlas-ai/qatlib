/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback

/-!
# A fixed data separation of AMP and spin dynamics

`generalAmpStep` allows coordinate maps beyond the particular mean field spin construction.
Constant regular maps produce output one on zero data, whereas zero data keeps the raw feedback
state at `initialSpin`; `reverse_fixed_data_error` quantifies the resulting unit readout
discrepancy. This example delimits the converse direction of the AMP representation discussed in
[GohMuller2026].

## Main statements

* `constant_amp_output`: For the specified one coordinate zero data example, the constant AMP
  update produces the vector with value one.
* `reverse_fixed_data_error`: On the specified zero data example, the constant AMP output
  differs by exactly one from the raw feedback readout for every schedule and time.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
open Qatlib.Foundations.MatrixGeometry.AxisRotations.History
open Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.MainResults.CapacityBoundary

/-- With zero interaction tensor and zero seed, every raw feedback state equals `initialSpin`
for any schedule and time. -/
theorem zero_data_feedback {r N : ℕ} (s : ℕ → ℝ) (t : ℕ) :
    feedbackState id (fun _ : Fin N => fun _ : Fin r → Fin N => 0) (fun _ => 0) s t=
      fun _ => initialSpin := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext i
    simp only [feedbackState, feedbackField, interaction, zero_mul, Finset.sum_const_zero,
      id_eq, zero_add, ih]
    ext a
    simpa [initialSpin, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using
      congrFun (zero_step_column (s (t+1))) a

/-- A single clipped AMP update using a tensor interaction, a history readout `f`, and an update
map `F` on a one entry history. -/
def generalAmpStep {r N : ℕ} (M : ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (f : (Fin 1 → ℝ) → ℝ) (F : ℝ → (Fin 1 → ℝ) → ℝ)
    (U : Fin 1 → Fin N → ℝ) : Fin N → ℝ :=
  fun i => clip M (F (interaction J (fun j => f (fun a => U a j)) i) (fun a => U a i))

/-- The constant zero history readout vanishes at zero and is one Lipschitz, while the constant
one update map is also one Lipschitz. -/
theorem constant_amp_regular :
    (fun _ : Fin 1 → ℝ => (0:ℝ)) (fun _ => 0)=0 ∧
    LipschitzWith 1 (fun _ : Fin 1 → ℝ => (0:ℝ)) ∧
    LipschitzWith 1 (fun _ : ℝ × (Fin 1 → ℝ) => (1:ℝ)) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact (LipschitzWith.const 0).weaken (by norm_num)
  · exact (LipschitzWith.const 1).weaken (by norm_num)

/-- For the specified one coordinate zero data example, the constant AMP update produces the
vector with value one. -/
theorem constant_amp_output :
    generalAmpStep (r:=3) (N:=1) 1 (fun _ _ => 0) (fun _ => 0) (fun _ _ => 1) (fun _ _ => 0)=
      fun _ => 1 := by
  funext i
  norm_num [generalAmpStep, clip]

/-- On the specified zero data example, the constant AMP output differs by exactly one from the
raw feedback readout for every schedule and time. -/
theorem reverse_fixed_data_error (s : ℕ → ℝ) (T : ℕ) :
    |generalAmpStep (r:=3) (N:=1) 1 (fun _ _ => 0) (fun _ => 0) (fun _ _ => 1) (fun _ _ => 0) 0-
      feedbackState id (fun _ : Fin 1 => fun _ : Fin 3 → Fin 1 => 0) (fun _ => 0) s T 0 2|=1 := by
  rw [constant_amp_output, zero_data_feedback]
  change |(1:ℝ)-(0:ℝ)|=1
  norm_num

end Qatlib.Papers.OverlapGapGoh26.MainResults.CapacityBoundary
