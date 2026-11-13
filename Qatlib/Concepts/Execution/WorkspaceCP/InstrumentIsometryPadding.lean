/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Padding instruments along isometric embeddings

`isometryPad` places an instrument with possibly different input and output dimensions in a
common ambient space, using specified isometric embeddings. It adds a `none` outcome for the
orthogonal complement of the input range, following the completely positive instrument framework
of [Watrous2018].

The padded branches form an instrument on the ambient space. On embedded inputs, each original
branch is the embedded original output, its weight is preserved, and the additional branch
vanishes.

## Main statements

* `paddedBranches_total`: the sum of padded branches preserves trace.
* `isometryPad_some_onEmbedding`: original branches act correctly on embedded inputs.
* `isometryPad_none_onEmbedding`: the complementary branch vanishes on embedded inputs.
* `isometryPad_prob_onEmbedding`: original branch weights are unchanged.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.Execution.WorkspaceCP
open Matrix
open Matrix
variable {N D E : ℕ} {O : Type*} [Fintype O]

/-- Extends the instrument branches by input compression and output embedding, adding a `none`
branch given by conjugation with `1 - rangeProjector Ein`. -/
private noncomputable def paddedBranches (Ein : Matrix (Fin N) (Fin D) ℂ)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (I : Instrument O D E) :
    Option O → (Operator N →ₗ[ℂ] Operator N)
  | none => conjBranch (1 - rangeProjector Ein)
  | some o => conjBranch Eout ∘ₗ I.branch o ∘ₗ conjBranch Ein.conjTranspose

/-- Each padded branch is completely positive. -/
private theorem paddedBranches_cp (Ein : Matrix (Fin N) (Fin D) ℂ)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (I : Instrument O D E) (o : Option O) :
    CompletelyPositive (paddedBranches Ein Eout I o) := by
  cases o with
  | none => exact completelyPositive_conjBranch _
  | some o =>
    exact (completelyPositive_conjBranch Eout).comp
      ((I.cp o).comp (completelyPositive_conjBranch Ein.conjTranspose))

/-- Conjugation by an isometric embedding preserves the trace of every input operator. -/
private theorem embedded_trace (V : Matrix (Fin N) (Fin D) ℂ) (hV : IsIsometry V)
    (A : Operator D) : trace (conjBranch V A) = trace A := by
  have h : V.conjTranspose * V = 1 := hV
  rw [conjBranch_apply, Matrix.trace_mul_cycle, h, Matrix.one_mul]

/-- The trace after compression by `V.conjTranspose` equals the trace of `rangeProjector V * X`. -/
private theorem compressed_trace (V : Matrix (Fin N) (Fin D) ℂ) (X : Operator N) :
    trace (conjBranch V.conjTranspose X) = trace (rangeProjector V * X) := by
  rw [conjBranch_apply, Matrix.trace_mul_cycle]
  simp [rangeProjector]

/-- For an isometry `V`, conjugating by its complementary range projector has trace equal to
`trace ((1 - rangeProjector V) * X)`. -/
private theorem complement_trace (V : Matrix (Fin N) (Fin D) ℂ) (hV : IsIsometry V)
    (X : Operator N) :
    trace (conjBranch (1 - rangeProjector V) X) = trace ((1 - rangeProjector V) * X) := by
  have hp := rangeProjector_isOrthogonalProjector hV
  have hself : (1 - rangeProjector V).conjTranspose = 1 - rangeProjector V := by
    simp [rangeProjector]
  rw [conjBranch_apply, Matrix.trace_mul_cycle, hself, hp.one_sub.1]

/-- For isometric input and output embeddings, the sum of all padded branches preserves trace. -/
private theorem paddedBranches_total (Ein : Matrix (Fin N) (Fin D) ℂ)
    (hi : IsIsometry Ein) (Eout : Matrix (Fin N) (Fin E) ℂ) (ho : IsIsometry Eout)
    (I : Instrument O D E) (X : Operator N) :
    trace (∑ o, paddedBranches Ein Eout I o X) = trace X := by
  classical
  rw [Fintype.sum_option]
  simp only [paddedBranches, LinearMap.comp_apply, Matrix.trace_add, Matrix.trace_sum]
  simp_rw [embedded_trace Eout ho]
  rw [← Matrix.trace_sum, I.total, compressed_trace, complement_trace Ein hi]
  rw [← Matrix.trace_add, ← Matrix.add_mul]
  simp

/-- Embeds an instrument in a common ambient space, adding a complementary outcome so that the
total map preserves trace. -/
noncomputable def isometryPad (I : Instrument O D E)
    (Ein : Matrix (Fin N) (Fin D) ℂ) (hi : IsIsometry Ein)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (ho : IsIsometry Eout) : Instrument (Option O) N N :=
  .ofBranches (paddedBranches Ein Eout I) (paddedBranches_cp Ein Eout I)
    (paddedBranches_total Ein hi Eout ho I)

/-- An original padded outcome compresses the input, applies the corresponding instrument
branch, and embeds its output. -/
theorem isometryPad_some (I : Instrument O D E)
    (Ein : Matrix (Fin N) (Fin D) ℂ) (hi : IsIsometry Ein)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (ho : IsIsometry Eout) (o : O) (X : Operator N) :
    ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) Ein hi Eout ho).branch (some o) X =
      conjBranch Eout (I.branch o (conjBranch Ein.conjTranspose X)) := rfl

/-- The added outcome is conjugation by the orthogonal complement of the input range projector. -/
theorem isometryPad_none (I : Instrument O D E)
    (Ein : Matrix (Fin N) (Fin D) ℂ) (hi : IsIsometry Ein)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (ho : IsIsometry Eout) (X : Operator N) :
    ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) Ein hi Eout ho).branch none X =
      conjBranch (1 - rangeProjector Ein) X := rfl

/-- On an embedded input, each original padded branch equals the embedding of the corresponding
original output. -/
theorem isometryPad_some_onEmbedding (I : Instrument O D E)
    (Ein : Matrix (Fin N) (Fin D) ℂ) (hi : IsIsometry Ein)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (ho : IsIsometry Eout) (o : O) (A : Operator D) :
    ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) Ein hi Eout ho).branch (some o) (conjBranch Ein A) =
      conjBranch Eout (I.branch o A) := by
  have h : Ein.conjTranspose * Ein = 1 := hi
  rw [isometryPad_some]
  have hc : conjBranch Ein.conjTranspose (conjBranch Ein A) = A := by
    change (conjBranch Ein.conjTranspose ∘ₗ conjBranch Ein) A = A
    rw [conjBranch_comp, h]
    simp
  rw [hc]

/-- The complementary padded branch vanishes on every embedded input operator. -/
theorem isometryPad_none_onEmbedding (I : Instrument O D E)
    (Ein : Matrix (Fin N) (Fin D) ℂ) (hi : IsIsometry Ein)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (ho : IsIsometry Eout) (A : Operator D) :
    ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) Ein hi Eout ho).branch none (conjBranch Ein A) = 0 := by
  have hz : (1 - rangeProjector Ein) * Ein = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul hi, sub_self]
  rw [isometryPad_none]
  change (conjBranch (1 - rangeProjector Ein) ∘ₗ conjBranch Ein) A = 0
  rw [conjBranch_comp, hz]
  simp

/-- Isometric padding preserves each original branch weight on embedded inputs. -/
theorem isometryPad_prob_onEmbedding (I : Instrument O D E)
    (Ein : Matrix (Fin N) (Fin D) ℂ) (hi : IsIsometry Ein)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (ho : IsIsometry Eout) (o : O) (A : Operator D) :
    instrumentProb ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) Ein hi Eout ho) (conjBranch Ein A) (some o) =
      instrumentProb I A o := by
  unfold instrumentProb
  rw [isometryPad_some_onEmbedding, embedded_trace Eout ho]

/-- The complementary outcome has zero branch weight on every embedded input. -/
theorem isometryPad_none_prob_onEmbedding (I : Instrument O D E)
    (Ein : Matrix (Fin N) (Fin D) ℂ) (hi : IsIsometry Ein)
    (Eout : Matrix (Fin N) (Fin E) ℂ) (ho : IsIsometry Eout) (A : Operator D) :
    instrumentProb ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) Ein hi Eout ho) (conjBranch Ein A) none = 0 := by
  unfold instrumentProb
  rw [isometryPad_none_onEmbedding]
  simp

end Qatlib.Concepts.Execution.WorkspaceCP
