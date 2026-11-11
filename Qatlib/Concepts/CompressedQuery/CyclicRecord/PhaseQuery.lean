/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.UniformSwap

/-!
# Recording phase queries by uniform conjugation

`phaseGate` extends a diagonal label phase to the optional-label basis, fixing the empty state.
Conjugating it by `uniformSwap` defines `recording`, whose unitarity and intertwining relation
with `compression` are established here.

The mathematical context is discussed in [MagniezZur2026].

## Main statements

* `recording_unitary`: The recording matrix is unitary for unit modulus phases.
* `compression_intertwines`: Compression intertwines the label phase and recording matrices.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {L : Type*} [Fintype L] [Nonempty L]

/-- The diagonal phase matrix on optional labels, with value one on `none` and value `phase y`
on `some y`. -/
def phaseGate (phase : L → ℂ) : Matrix (Option L) (Option L) ℂ :=
  diagonal (fun i => match i with | none => 1 | some y => phase y)

/-- The recording query matrix obtained by conjugating `phaseGate phase` by the uniform swap. -/
def recording (phase : L → ℂ) : Matrix (Option L) (Option L) ℂ :=
  uniformSwap*phaseGate phase*uniformSwap
omit [Nonempty L] in

/-- The extended phase matrix satisfies `Uᴴ * U = 1` when each label phase has conjugate product
one. -/
theorem phaseGate_unitary (phase : L → ℂ) (hp : ∀ y, star (phase y)*phase y=1) :
    (phaseGate phase)ᴴ*phaseGate phase=1 := by
  ext i j
  simp only [phaseGate,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  by_cases h : i=j
  · subst j
    cases i with
    | none => simp
    | some y =>
      simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
      change star (phase y)*phase y=1
      exact hp y
  · simp [h]
omit [Nonempty L] in

/-- The product of two matrices satisfying `Uᴴ * U = 1` again satisfies this identity. -/
theorem product_unitary (U V : Matrix (Option L) (Option L) ℂ) (hU : Uᴴ*U=1) (hV : Vᴴ*V=1) :
    (U*V)ᴴ*(U*V)=1 := by
  calc
    _ = Vᴴ*(Uᴴ*U)*V := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = 1 := by rw [hU,Matrix.mul_one,hV]

/-- The recording matrix satisfies `Uᴴ * U = 1` when all label phases have conjugate product
one. -/
theorem recording_unitary (phase : L → ℂ) (hp : ∀ y, star (phase y)*phase y=1) :
    (recording phase)ᴴ*recording phase=1 :=
  product_unitary _ _ (product_unitary _ _ uniformSwap_unitary (phaseGate_unitary phase hp)) uniformSwap_unitary

/-- The recording query with every phase equal to one is the identity matrix. -/
theorem recording_trivial : recording (L := L) (fun _ => 1)=1 := by
  have h : phaseGate (L := L) (fun _ => 1)=1 := by
    ext i j
    cases i <;> cases j <;> simp [phaseGate,Matrix.diagonal_apply,Matrix.one_apply]
  unfold recording
  rw [h,Matrix.mul_one,uniformSwap_squared]

/-- Multiplying a recording matrix on the right by the uniform swap equals the uniform swap
multiplied by the extended phase matrix. -/
theorem recording_swap (phase : L → ℂ) : recording phase*uniformSwap=uniformSwap*phaseGate phase := by
  unfold recording
  rw [Matrix.mul_assoc (uniformSwap*phaseGate phase),uniformSwap_squared,Matrix.mul_one]

/-- The recording matrix composed with compression equals compression composed with the diagonal
label phase matrix. -/
theorem compression_intertwines (phase : L → ℂ) :
    recording phase*compression=compression*diagonal phase := by
  ext i y
  change ((recording phase*uniformSwap) : Matrix (Option L) (Option L) ℂ) i (some y)=_
  rw [recording_swap,phaseGate,Matrix.mul_diagonal,Matrix.mul_diagonal]
  rfl
end Qatlib.Concepts.CompressedQuery.CyclicRecord
