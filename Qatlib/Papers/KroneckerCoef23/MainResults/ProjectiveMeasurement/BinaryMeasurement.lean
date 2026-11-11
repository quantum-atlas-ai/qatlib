/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace.KroneckerTraceFormula

set_option backward.isDefEq.respectTransparency false

/-!
# BinaryMeasurement — binary projective measurement `{P, I − P}`

Fixed version: arXiv:2302.11454v3 (7 May 2024).  Used by Theorem 1 (p. 5) and
Theorem 2 (p. 6), both of which produce measurements of the form `{P, I − P}`.

A binary measurement on a finite-dimensional complex space is described by a
single effect `P`; the two outcomes carry the effects `P` and `1 - P`.  When `P`
is idempotent (the paper proves this for `Π^L`-built projectors) the measurement
is projective: both effects are idempotent and their sum is the identity.

The `Bool` outcome is written out as the two explicit outcomes `true`/`false`
instead of a `Finset.univ` sum, so that no `Fintype Bool` summation lemma is
needed.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two effects of the binary measurement `{P, I − P}`: outcome `true` is the
selected effect `P`, outcome `false` is its complement `I − P`. -/
def binaryEffect (P : Matrix V V ℂ) : Bool → Matrix V V ℂ :=
  fun b => if b then P else 1 - P

/-- The two outcomes of a binary measurement are exhaustive: `P + (I − P) = I`. -/
theorem binaryEffect_total (P : Matrix V V ℂ) :
    binaryEffect P true + binaryEffect P false = 1 := by
  simp only [binaryEffect, Bool.false_eq_true, if_false, if_true]
  abel

/-- The selected outcome of a binary measurement is idempotent whenever its effect is. -/
theorem binaryEffect_true_idempotent (P : Matrix V V ℂ) (hP : P * P = P) :
    binaryEffect P true * binaryEffect P true = binaryEffect P true := by
  simp [binaryEffect, hP]

/-- The complement `I − P` of an idempotent effect is idempotent:
`(1 − P)(1 − P) = 1 − P`, so the binary measurement is projective. -/
theorem binaryEffect_false_idempotent (P : Matrix V V ℂ) (hP : P * P = P) :
    binaryEffect P false * binaryEffect P false = binaryEffect P false := by
  simp only [binaryEffect, Bool.false_eq_true, if_false]
  calc (1 - P) * (1 - P) = 1 * (1 - P) - P * (1 - P) := by rw [Matrix.sub_mul]
    _ = (1 - P) - (P * 1 - P * P) := by rw [Matrix.one_mul, Matrix.mul_sub]
    _ = (1 - P) - (P - P) := by rw [Matrix.mul_one, hP]
    _ = 1 - P := by abel

/-- Conjugating an idempotent effect by a unitary `F` (`F F† = F† F = 1`) gives an
idempotent effect: this is the operator form of "apply `F`, project, apply `F†`"
(the structure of Lemma 6). -/
theorem conjugated_idempotent (F P : Matrix V V ℂ) (hP : P * P = P)
    (hF : F * Fᴴ = 1) (hF' : Fᴴ * F = 1) :
    (F * P * Fᴴ) * (F * P * Fᴴ) = F * P * Fᴴ := by
  calc (F * P * Fᴴ) * (F * P * Fᴴ) = F * P * (Fᴴ * F) * P * Fᴴ := by
        noncomm_ring
    _ = F * P * 1 * P * Fᴴ := by rw [hF']
    _ = F * P * P * Fᴴ := by rw [Matrix.mul_one]
    _ = F * (P * P) * Fᴴ := by noncomm_ring
    _ = F * P * Fᴴ := by rw [hP]

end Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement
