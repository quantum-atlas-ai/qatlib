/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MutuallyUnbiasedGauge

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis
open scoped Matrix

noncomputable def sixthAmplitude : ℝ := Real.sqrt ((1 : ℝ) / 6)

/-- The normalization amplitude `sixthAmplitude` is positive. -/
theorem sixthAmplitude_pos : 0 < sixthAmplitude := by
  exact Real.sqrt_pos.mpr (by norm_num)

/-- The square of `sixthAmplitude` is one sixth. -/
theorem sixthAmplitude_sq : sixthAmplitude ^ 2 = (1 : ℝ) / 6 := by
  exact Real.sq_sqrt (by norm_num)

abbrev MatrixSix := Matrix (Fin 6) (Fin 6) ℂ

noncomputable def normalizeHadamard (A : MatrixSix) : MatrixSix :=
  (sixthAmplitude : ℂ) • A

/-- The product of the complex normalization amplitude with its conjugate is one sixth. -/
theorem sixthAmplitude_conj_mul :
    (starRingEnd ℂ) (sixthAmplitude : ℂ) * (sixthAmplitude : ℂ) = (1 / 6 : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_ofReal,
    ← pow_two, sixthAmplitude_sq]
  norm_num

/-- Normalizing both Hadamard matrices scales their relative Gram matrix by one sixth. -/
theorem normalizeHadamard_relative_apply (A B : MatrixSix) (i j : Fin 6) :
    ((normalizeHadamard A)ᴴ * normalizeHadamard B) i j =
      (1 / 6 : ℂ) * (Aᴴ * B) i j := by
  rw [← inner_matrixColumns]
  change Qatlib.Foundations.PureStateMath.Inner (fun t => (sixthAmplitude : ℂ) * A t i)
    (fun t => (sixthAmplitude : ℂ) * B t j) = _
  rw [inner_rephase, sixthAmplitude_conj_mul, inner_matrixColumns]

/-- Hadamard normalization scales each entry's squared norm by one sixth. -/
theorem normSq_normalizeHadamard_entry (A : MatrixSix) (i j : Fin 6) :
    Complex.normSq (normalizeHadamard A i j) =
      (1 / 6 : ℝ) * Complex.normSq (A i j) := by
  change Complex.normSq ((sixthAmplitude : ℂ) * A i j) = _
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two, sixthAmplitude_sq]

/-- Hadamard normalization scales squared norms in the relative Gram matrix by one thirty-sixth. -/
theorem normSq_normalizeHadamard_relative (A B : MatrixSix) (i j : Fin 6) :
    Complex.normSq (((normalizeHadamard A)ᴴ * normalizeHadamard B) i j) =
      (1 / 36 : ℝ) * Complex.normSq ((Aᴴ * B) i j) := by
  rw [normalizeHadamard_relative_apply, Complex.normSq_mul]
  norm_num

/-- A normalized Hadamard matrix is unitary exactly when its unnormalized Gram matrix is six
times the identity. -/
theorem normalizeHadamard_unitary_iff (A : MatrixSix) :
    normalizeHadamard A ∈ Matrix.unitaryGroup (Fin 6) ℂ ↔
      Aᴴ * A = (6 : ℂ) • (1 : MatrixSix) := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have heq : (normalizeHadamard A)ᴴ * normalizeHadamard A =
      (1 / 6 : ℂ) • (Aᴴ * A) := by
    ext i j
    exact normalizeHadamard_relative_apply A A i j
  rw [heq]
  constructor
  · intro h
    calc
      Aᴴ * A = (6 : ℂ) • ((1 / 6 : ℂ) • (Aᴴ * A)) := by simp [smul_smul]
      _ = (6 : ℂ) • (1 : MatrixSix) := congrArg (fun M => (6 : ℂ) • M) h
  · intro h
    rw [h, smul_smul]
    norm_num

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
