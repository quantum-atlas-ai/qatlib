/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.Resources.LabelWidth
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Encoding finite labels into qubit registers

The embedding `labelIndex` maps `d` classical labels into a register of `qubitCount d` qubits,
and `labelFrame` is its coordinate matrix. The frame is isometric; conjugation by it preserves
density matrices and recovers the original entries at encoded labels. This makes the logarithmic
register representation in [LloydEtAl2020] explicit.

## Main statements

* `labelFrame_isometry`: The label encoding frame has identity Gram matrix.
* `encoded_density`: Conjugating a positive semidefinite trace-one matrix by the label frame
  produces another positive semidefinite trace-one matrix.
* `encoded_entry`: The encoded density matrix evaluated at two encoded labels equals the
  corresponding original matrix entry.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical ComplexOrder

namespace Qatlib.Papers.NonlinearDE20.Resources.Encoding
open Qatlib.Papers.NonlinearDE20.Resources.LabelWidth
open Qatlib.Foundations.PureStateMath

/-- An injection of `d` labels into the computational basis of a `qubitCount d`-qubit register. -/
def labelIndex (d : ℕ) : Fin d ↪ Reg (qubitCount d) where
  toFun := fun j => (bitVecEquiv (qubitCount d)).symm (Fin.castLE (dim_le_two_pow_qubitCount d) j)
  inj' := by
    intro a b h
    have he := (bitVecEquiv (qubitCount d)).symm.injective h
    exact Fin.ext (congrArg (fun z : Fin (2 ^ qubitCount d) => z.val) he)

/-- The coordinate matrix with a one at each encoded label and zeros elsewhere. -/
def labelFrame (d : ℕ) : Matrix (Reg (qubitCount d)) (Fin d) ℂ :=
  fun i j => if i = labelIndex d j then 1 else 0

/-- The label encoding frame has identity Gram matrix [LloydEtAl2020]. -/
theorem labelFrame_isometry (d : ℕ) : (labelFrame d)ᴴ * labelFrame d = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (labelIndex d i)]
  · by_cases hij : i = j
    · subst j
      simp [labelFrame]
    · have he : labelIndex d i ≠ labelIndex d j := fun h => hij ((labelIndex d).injective h)
      simp [labelFrame, he, hij]
  · intro a _ ha
    simp [labelFrame, ha]
  · simp

/-- Conjugating a positive semidefinite trace-one matrix by the label frame produces another
positive semidefinite trace-one matrix [LloydEtAl2020]. -/
theorem encoded_density (d : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (labelFrame d * ρ * (labelFrame d)ᴴ).PosSemidef ∧
      (labelFrame d * ρ * (labelFrame d)ᴴ).trace = 1 := by
  refine ⟨hρ.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_mul_cycle, labelFrame_isometry, Matrix.one_mul, htr]

/-- The encoded density matrix evaluated at two encoded labels equals the corresponding original
matrix entry [LloydEtAl2020]. -/
theorem encoded_entry (d : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (labelFrame d * ρ * (labelFrame d)ᴴ) (labelIndex d i) (labelIndex d j) = ρ i j := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, labelFrame,
    (labelIndex d).injective.eq_iff]

end Qatlib.Papers.NonlinearDE20.Resources.Encoding
