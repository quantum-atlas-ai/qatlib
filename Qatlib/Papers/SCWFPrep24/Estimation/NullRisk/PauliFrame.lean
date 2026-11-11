/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Mathlib.Tactic.Linarith
import QuantumInfo.ForMathlib.HermitianMat.Inner

set_option backward.isDefEq.respectTransparency false

/-!
# Pauli Frame

The exact second moment of the six actual Pauli eigenprojectors; this is a finite design identity, not an assumed prior likelihood bound.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The exact second moment of the six actual Pauli eigenprojectors; this is a finite design identity, not an assumed prior likelihood bound. -/
theorem six_pauli_second_moment (B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ a : Fin 3, ∑ b : Bool,
      Matrix.trace (PauliProjector a b * B) *
        Matrix.trace (PauliProjector a b * C)) / 6 =
      (Matrix.trace B * Matrix.trace C + Matrix.trace (B * C)) / 6 := by
  simp only [Fin.sum_univ_three, sum_bool, PauliProjector, Bool.false_eq_true,
    ite_false, ite_true, pauliMatrix_zero, pauliMatrix_one, pauliMatrix_two,
    Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul]
  rw [trace_pauliX_mul, trace_pauliY_mul, trace_pauliZ_mul,
    trace_pauliX_mul, trace_pauliY_mul, trace_pauliZ_mul]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The actual six Pauli eigenprojectors are Hermitian in the existing matrix representation. -/
theorem pauliProjector_hermitian (a : Fin 3) (b : Bool) :
    (PauliProjector a b).IsHermitian := by
  change (PauliProjector a b)ᴴ = PauliProjector a b
  fin_cases a <;> cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [PauliProjector, pauliMatrix, pauliX, pauliY, pauliZ,
      Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Complex.star_def]

/-- The actual Pauli eigenprojector bundled in the canonical Hermitian-matrix type. -/
def pauliPriorDensity (a : Fin 3) (b : Bool) : HermitianMat (Fin 2) ℂ :=
  ⟨PauliProjector a b, pauliProjector_hermitian a b⟩

/-- The exact six-state physical second moment in real Hermitian trace coordinates. -/
theorem six_pauli_hermitian_second_moment (B C : HermitianMat (Fin 2) ℂ) :
    (∑ a : Fin 3, ∑ b : Bool,
      inner ℝ (pauliPriorDensity a b) B * inner ℝ (pauliPriorDensity a b) C) / 6 =
        (B.trace*C.trace + inner ℝ B C) / 6 := by
  have h := six_pauli_second_moment B.mat C.mat
  have hb (a : Fin 3) (b : Bool) : Matrix.trace (PauliProjector a b * B.mat) =
      (inner ℝ (pauliPriorDensity a b) B : ℂ) := by
    exact (HermitianMat.inner_eq_trace_mul (pauliPriorDensity a b) B).symm
  have hc (a : Fin 3) (b : Bool) : Matrix.trace (PauliProjector a b * C.mat) =
      (inner ℝ (pauliPriorDensity a b) C : ℂ) := by
    exact (HermitianMat.inner_eq_trace_mul (pauliPriorDensity a b) C).symm
  simp_rw [hb, hc] at h
  rw [← B.trace_eq_trace, ← C.trace_eq_trace, ← HermitianMat.inner_eq_trace_mul B C] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-- The null ensemble's finite six-state second moment dominates the trace product for actual positive effects. -/
theorem six_pauli_positive_trace_lower (B C : HermitianMat (Fin 2) ℂ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    B.trace*C.trace/6 ≤ (∑ a : Fin 3, ∑ b : Bool,
      inner ℝ (pauliPriorDensity a b) B * inner ℝ (pauliPriorDensity a b) C) / 6 := by
  rw [six_pauli_hermitian_second_moment]
  linarith [HermitianMat.inner_ge_zero hB hC]

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
