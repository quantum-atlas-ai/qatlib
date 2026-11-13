/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SharedAncilla.AncillaProduct.UnitaryFamilyWord

/-!
# Shared Ancilla Word Postselection

This module turns a family of unitary block encodings sharing one isometric frame into a
postselection guarantee for the evaluated word. `shared_ancilla_actual_word_postselection`
controls both success probability and the normalized output using `sharedAncillaWordError`.

The explicit two dimensional example `shared_ancilla_rotation_leakage_consumer` computes the
compression and success probability after reusing the same workspace twice. These results use
the block encoding and postselection viewpoint of [GilyenSuLowWiebe2019].

## Main statements

* `shared_ancilla_actual_word_postselection` gives success probability at least `(1 -
  sharedAncillaWordError e)^2` when the error is below one.
* `shared_ancilla_rotation_leakage_consumer` exhibits a two query compression error of `15/32`
  from individual errors of `1/8`.

## References

* [Gilyen et al., 2019][GilyenSuLowWiebe2019], Quantum singular value transformation and beyond:
  exponential improvements for quantum matrix arithmetics.
-/

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.SharedAncilla.AncillaProduct

namespace Qatlib.Concepts.FrameEncoding.SharedAncilla
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- For unitary targets block encoded through one isometric frame, a normalized input and shared
word error below one give postselection success probability at least the square of one minus
that error. The postselected output exists and approximates the normalized target word
action with error at most twice the shared word error. -/
theorem shared_ancilla_actual_word_postselection :
∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
 (m : ℕ) (A : Fin m→Matrix I I ℂ) (U : Fin m→Matrix H H ℂ) (F : Matrix H I ℂ)
 (e : Fin m→ℝ) (ψ : QState I), IsIsometry F →
 (∀i,A i∈Matrix.unitaryGroup I ℂ ∧ BlockEncoding (A i) (U i) F F 1 (e i)) →
 Normalized ψ → sharedAncillaWordError e<1 →
 let V:=unitaryFamilyEvaluate U (unitaryFamilyWord m);
 let B:=unitaryFamilyEvaluate A (unitaryFamilyWord m);
 (1-sharedAncillaWordError e)^2 ≤ postselectionProbability V F F ψ ∧
 ∃φ : QState I,postselectionOutput V F F ψ=some φ ∧
 IsNormalizedApplication B ψ φ (2*sharedAncillaWordError e) := by
  intro H I _ _ _ _ m A U F e ψ hF hs hψ hgap
  (try dsimp only)
  have h := shared_ancilla_heterogeneous_word_encoding H I m A U F e hF hs
  have hu := unitaryFamilyEvaluate_unitary A (fun i => (hs i).1) (unitaryFamilyWord m)
  have hiso : IsIsometry (unitaryFamilyEvaluate A (unitaryFamilyWord m)) := by
    simpa only [Matrix.star_eq_conjTranspose] using! hu.1
  have hn : ‖stateVector (unitaryFamilyEvaluate A (unitaryFamilyWord m) *ᵥ ψ)‖ = 1 := by
    rw [(Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.stateVector_norm hiso),(normalized_iff_stateVector_norm ψ).mp hψ]
  have hp :=
      (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower h) hψ (by rw [hn]; exact hgap.le)
  have ho :=
      (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap h) hψ (by rw [hn]; exact hgap)
  refine ⟨by simpa only [hn,div_one] using hp,?_⟩
  simpa only [hn,div_one] using ho.2

/-- Defines the one dimensional frame in the Boolean workspace that sends its basis vector to
the false basis state. -/
noncomputable def sharedToyFrame : Matrix Bool Unit ℂ := fun b _ => if b then 0 else 1

/-- Defines a real Boolean workspace rotation with diagonal entries `7/8` and off diagonal
entries of opposite signs and magnitude `sqrt 15 / 8`. -/
noncomputable def sharedToyRotation : Matrix Bool Bool ℂ := fun b c =>
 if b=c then (7/8:ℂ) else if b then -(Real.sqrt 15:ℂ)/8 else (Real.sqrt 15:ℂ)/8

/-- The Euclidean operator norm of a complex scalar times the identity on the one dimensional
`Unit` space equals the scalar's complex norm. -/
theorem shared_scalar_norm (z : ℂ) : ‖z • (1:Matrix Unit Unit ℂ)‖ = ‖z‖ := by
  have he : z • (1:Matrix Unit Unit ℂ) = Matrix.diagonal (fun _ : Unit => z) := by
    ext i j; cases i; cases j; simp
  rw [he,Matrix.l2_opNorm_diagonal]
  simp

/-- The toy frame selecting the false Boolean workspace state is an isometry. -/
theorem sharedToyFrame_isometry : IsIsometry sharedToyFrame := by
  change sharedToyFrameᴴ*sharedToyFrame = 1
  ext i j
  cases i; cases j
  norm_num [sharedToyFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_bool]

/-- Compression through the toy frame extracts the false false entry of a Boolean workspace
matrix as a scalar operator on `Unit`. -/
theorem sharedToyFrame_corner (V : Matrix Bool Bool ℂ) :
    compress sharedToyFrame V sharedToyFrame = V false false • (1:Matrix Unit Unit ℂ) := by
  ext i j
  cases i; cases j
  simp [compress,sharedToyFrame,Matrix.mul_apply,Matrix.conjTranspose_apply]

/-- The toy rotation is a unitary block encoding of the identity with error `1/8`, while two
applications using the shared frame compress to `17/32` times the identity and succeed with
probability `289/1024`. The resulting compression error is `15/32`, exceeds `1/4`, and uses
exactly two word queries. -/
theorem shared_ancilla_rotation_leakage_consumer :
sharedToyRotation∈Matrix.unitaryGroup Bool ℂ ∧
 BlockEncoding (1:Matrix Unit Unit ℂ) sharedToyRotation sharedToyFrame sharedToyFrame 1 (1/8) ∧
 let V:=unitaryFamilyEvaluate (fun _ : Fin 2=>sharedToyRotation) (unitaryFamilyWord 2);
 compress sharedToyFrame V sharedToyFrame=(17/32:ℂ) • (1:Matrix Unit Unit ℂ) ∧
 postselectionProbability V sharedToyFrame sharedToyFrame (Qatlib.Foundations.PureStateMath.Ket ())=289/1024 ∧
 ‖(1:Matrix Unit Unit ℂ)-compress sharedToyFrame V sharedToyFrame‖=15/32 ∧
 (1/4:ℝ)<15/32 ∧ unitaryFamilyQueries (unitaryFamilyWord 2)=2 := by
  have hs : (Real.sqrt 15:ℂ)^2 = 15 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15))
  have hu : sharedToyRotation ∈ Matrix.unitaryGroup Bool ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    ext b c
    cases b <;> cases c <;>
      norm_num [sharedToyRotation,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_bool,map_ofNat]
      <;> ring_nf <;> norm_num [hs]
  have hc : compress sharedToyFrame sharedToyRotation sharedToyFrame = (7/8:ℂ) • (1:Matrix Unit Unit ℂ) := by
    rw [sharedToyFrame_corner]
    rfl
  have he1 : (1:Matrix Unit Unit ℂ)-(7/8:ℂ) • (1:Matrix Unit Unit ℂ) =
      (1/8:ℂ) • (1:Matrix Unit Unit ℂ) := by
    ext i j; cases i; cases j; norm_num
  have hb : BlockEncoding (1:Matrix Unit Unit ℂ) sharedToyRotation sharedToyFrame sharedToyFrame 1 (1/8) := by
    refine ⟨hu,sharedToyFrame_isometry,sharedToyFrame_isometry,by norm_num,by norm_num,?_⟩
    rw [one_smul,hc,he1,shared_scalar_norm]
    norm_num
  have hv : unitaryFamilyEvaluate (fun _ : Fin 2 => sharedToyRotation) (unitaryFamilyWord 2) =
      sharedToyRotation*sharedToyRotation := by
    simp [unitaryFamilyEvaluate,unitaryFamilyWord,List.ofFn_succ]
  have hc2 : compress sharedToyFrame (sharedToyRotation*sharedToyRotation) sharedToyFrame =
      (17/32:ℂ) • (1:Matrix Unit Unit ℂ) := by
    rw [sharedToyFrame_corner]
    congr 1
    norm_num [Matrix.mul_apply,Fintype.sum_bool,sharedToyRotation]
    ring_nf
    norm_num [hs]
  refine ⟨hu,hb,?_⟩
  (try dsimp only)
  rw [hv,hc2]
  refine ⟨rfl,?_,?_,by norm_num,?_⟩
  · rw [postselectionProbability_eq_norm_sq sharedToyFrame_isometry]
    unfold postselectionVector
    rw [hc2,stateVector_norm_sq]
    norm_num [MeasureProb,BornProb,Matrix.mulVec,Matrix.smul_apply,Qatlib.Foundations.PureStateMath.Ket]
  · have he : (1:Matrix Unit Unit ℂ)-(17/32:ℂ) • (1:Matrix Unit Unit ℂ) =
        (15/32:ℂ) • (1:Matrix Unit Unit ℂ) := by
      ext i j; cases i; cases j; norm_num
    rw [he,shared_scalar_norm]
    norm_num
  · simp [unitaryFamilyQueries,unitaryFamilyWord]

end Qatlib.Concepts.FrameEncoding.SharedAncilla
