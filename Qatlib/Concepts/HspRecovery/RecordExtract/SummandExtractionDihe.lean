/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.SummandExtractionStat
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics
import Mathlib.Tactic.SimpRw

/-!
# Unitary regular summand extraction

This module proves `SourceSummandExtraction` using the permutation matrix of the regular
difference map. Its intertwining identity transports diagonal left invariance to left invariance
on the right factor while preserving positivity and trace. See [Kuperberg2005] for the
mathematical background.

## Main statements

* `sourceSummandExtraction`: construct the unitary intertwiner and transport density matrices.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false
open scoped ComplexOrder

namespace Qatlib.Concepts.HspRecovery.RecordExtract
open Matrix

/-- Multiplication of the finite map matrices `permMatrix σ` and `permMatrix τ` agrees with
composition `σ ∘ τ`. -/
private theorem source_permMatrix_mul {I : Type*} [Fintype I] [DecidableEq I]
    (σ τ : I → I) : permMatrix σ * permMatrix τ = permMatrix (σ ∘ τ) := by
  ext i j
  simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (τ j)]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

/-- The regular difference gate is unitary, intertwines the two regular actions, and transports
invariant positive trace-one matrices as specified by `SourceSummandExtraction`
[Kuperberg2005]. -/
theorem sourceSummandExtraction : SourceSummandExtraction := by
  intro G _ _ H
  classical
  have hU : sourceDifferenceGate G ∈ Matrix.unitaryGroup (G × G) ℂ := by
    apply permMatrix_unitary_of_injective
    intro p q hpq
    have hb := congrArg (fun z : G × G => z.2) hpq
    have ha := congrArg (fun z : G × G => z.1) hpq
    change p.2 = q.2 at hb
    change p.2⁻¹ * p.1 = q.2⁻¹ * q.1 at ha
    rw [hb] at ha
    exact Prod.ext (mul_left_cancel ha) hb
  have hinter (g : G) : sourceDifferenceGate G * sourceDiagonalLeft G g =
      sourceRightFactorLeft G g * sourceDifferenceGate G := by
    simp only [sourceDifferenceGate, sourceDiagonalLeft, sourceRightFactorLeft,
      source_permMatrix_mul]
    congr 1
    funext p
    simp [mul_assoc]
  refine ⟨hU, hinter, ?_⟩
  intro rho hpos htrace hinv
  have hUU : (sourceDifferenceGate G).conjTranspose * sourceDifferenceGate G = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp hU
  refine ⟨hpos.mul_mul_conjTranspose_same _, ?_, ?_⟩
  · rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, htrace]
  · intro h
    calc
      sourceRightFactorLeft G h.val * (sourceDifferenceGate G * rho *
          (sourceDifferenceGate G).conjTranspose) =
          (sourceRightFactorLeft G h.val * sourceDifferenceGate G) * rho *
            (sourceDifferenceGate G).conjTranspose := by simp only [Matrix.mul_assoc]
      _ = (sourceDifferenceGate G * sourceDiagonalLeft G h.val) * rho *
          (sourceDifferenceGate G).conjTranspose := by rw [hinter]
      _ = sourceDifferenceGate G * rho * (sourceDifferenceGate G).conjTranspose := by
        rw [Matrix.mul_assoc (sourceDifferenceGate G), hinv]

end Qatlib.Concepts.HspRecovery.RecordExtract
