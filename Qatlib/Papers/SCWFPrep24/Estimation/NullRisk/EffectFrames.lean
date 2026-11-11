/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PauliFrame
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PairCoefficients

set_option backward.isDefEq.respectTransparency false

/-!
# Effect Frames

The actual rank-one positive effect of an arbitrary unnormalized two-component row.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
open Matrix
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The actual rank-one positive effect of an arbitrary unnormalized two-component row. -/
def rowEffect (a : Fin 2 → ℂ) : HermitianMat (Fin 2) ℂ :=
  ⟨Matrix.vecMulVec (star a) a, (Matrix.posSemidef_vecMulVec_star_self a).isHermitian⟩

/-- Every literal row effect is positive; no spectral or likelihood certificate is supplied. -/
theorem rowEffect_nonneg (a : Fin 2 → ℂ) : 0 ≤ rowEffect a := by
  exact HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_vecMulVec_star_self a)

/-- Its actual trace is the complete squared row norm. -/
theorem rowEffect_trace (a : Fin 2 → ℂ) :
    (rowEffect a).trace = ∑ b, Complex.normSq (a b) := by
  change (∑ b : Fin 2, star (a b)*a b).re = _
  simp only [Complex.re_sum, Complex.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, neg_mul, sub_neg_eq_add, Complex.normSq_apply]

/-- The actual complementary qubit effect used on the odd checkerboard sublattice. -/
def qubitTraceComplement (B : HermitianMat (Fin 2) ℂ) : HermitianMat (Fin 2) ℂ :=
  B.trace • 1 - B

/-- Positivity of the complementary qubit effect follows from the existing trace bound. -/
theorem qubitTraceComplement_nonneg (B : HermitianMat (Fin 2) ℂ) (hB : 0 ≤ B) :
    0 ≤ qubitTraceComplement B := by
  exact sub_nonneg.mpr (HermitianMat.le_trace_smul_one hB)

/-- In the actual two-dimensional spin space complementation preserves the full trace. -/
theorem qubitTraceComplement_trace (B : HermitianMat (Fin 2) ℂ) :
    (qubitTraceComplement B).trace = B.trace := by
  simp only [qubitTraceComplement, HermitianMat.trace_sub, HermitianMat.trace_smul,
    HermitianMat.trace_one, Fintype.card_fin, Nat.cast_ofNat]
  ring

/-- The null prior's spin effect sums every full-address row block, with its actual parity. -/
def nullSpinEffect {A : Type*} [Fintype A] (parity : A → Bool)
    (a : A → Fin 2 → ℂ) : HermitianMat (Fin 2) ℂ :=
  ∑ x, if parity x then qubitTraceComplement (rowEffect (a x)) else rowEffect (a x)

/-- All full-address blocks contribute positive effects to the null prior. -/
theorem nullSpinEffect_nonneg {A : Type*} [Fintype A]
    (parity : A → Bool) (a : A → Fin 2 → ℂ) : 0 ≤ nullSpinEffect parity a := by
  apply Finset.sum_nonneg
  intro x _
  cases parity x
  · simp only [Bool.false_eq_true, ite_false]
    exact rowEffect_nonneg (a x)
  · simp only [ite_true]
    exact qubitTraceComplement_nonneg _ (rowEffect_nonneg (a x))

/-- The null prior retains the full squared norm of every coherent address row. -/
theorem nullSpinEffect_trace {A : Type*} [Fintype A]
    (parity : A → Bool) (a : A → Fin 2 → ℂ) :
    (nullSpinEffect parity a).trace = ∑ x, ∑ b, Complex.normSq (a x b) := by
  classical
  let f := fun x => if parity x then qubitTraceComplement (rowEffect (a x)) else rowEffect (a x)
  have hsum (s : Finset A) : (∑ x ∈ s, f x).trace = ∑ x ∈ s, (f x).trace := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
      rw [Finset.sum_insert hx, HermitianMat.trace_add, Finset.sum_insert hx, ih]
  change (∑ x, f x).trace = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [f]
  cases parity x
  · simp only [Bool.false_eq_true, ite_false]
    exact rowEffect_trace (a x)
  · simp only [ite_true, qubitTraceComplement_trace]
    exact rowEffect_trace (a x)

/-- The actual null spin effects obey the dimension-independent six-state trace-product moment bound, with every address row included. -/
theorem nullSpinEffect_six_moment {A : Type*} [Fintype A]
    (parity : A → Bool) (a b : A → Fin 2 → ℂ) :
    (∑ x, ∑ i, Complex.normSq (a x i))*(∑ x, ∑ i, Complex.normSq (b x i))/6 ≤
      (∑ axis : Fin 3, ∑ sign : Bool,
        inner ℝ (pauliPriorDensity axis sign) (nullSpinEffect parity a) *
          inner ℝ (pauliPriorDensity axis sign) (nullSpinEffect parity b))/6 := by
  have h := six_pauli_positive_trace_lower (nullSpinEffect parity a) (nullSpinEffect parity b)
    (nullSpinEffect_nonneg parity a) (nullSpinEffect_nonneg parity b)
  simpa only [nullSpinEffect_trace] using h

/-- The canonical matrix trace of an actual pure state against an actual row effect is the literal squared full spin amplitude. -/
theorem rowEffect_eval_vector (v a : Fin 2 → ℂ) :
    inner ℝ (rowEffect (star v)) (rowEffect a) = Complex.normSq (∑ i, a i*v i) := by
  rw [HermitianMat.inner_eq_re_trace]
  simp only [rowEffect, HermitianMat.mat_mk, star_star]
  change (Matrix.trace (Matrix.vecMulVec v (star v) * Matrix.vecMulVec (star a) a)).re = _
  rw [normSq_sum_cross]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Complex.re_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [star_mul, Complex.star_def]
  ring

/-- The complementary actual Pauli outcomes sum to the identity, in the existing Hermitian matrix representation. -/
theorem pauliPriorDensity_complement (a : Fin 3) (b : Bool) :
    (1 : HermitianMat (Fin 2) ℂ) - pauliPriorDensity a b = pauliPriorDensity a (!b) := by
  apply HermitianMat.ext
  cases b <;> simp only [pauliPriorDensity, HermitianMat.mat_sub, HermitianMat.mat_one,
    HermitianMat.mat_mk, Qatlib.Concepts.ChannelTheory.Stinespring.PauliProjector,
    Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.not_true] <;> module

/-- Every actual prior Pauli projector has unit trace. -/
theorem pauliPriorDensity_trace (a : Fin 3) (b : Bool) : (pauliPriorDensity a b).trace = 1 := by
  fin_cases a <;> cases b <;>
    norm_num [pauliPriorDensity, HermitianMat.trace_eq_re_trace,
      Qatlib.Concepts.ChannelTheory.Stinespring.PauliProjector,
      Qatlib.Concepts.ChannelTheory.Stinespring.pauliMatrix,
      Qatlib.Concepts.ChannelTheory.Stinespring.pauliX,
      Qatlib.Concepts.ChannelTheory.Stinespring.pauliY,
      Qatlib.Concepts.ChannelTheory.Stinespring.pauliZ,
      Matrix.trace_fin_two, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]

/-- Passing a row effect to the odd checkerboard color equals passing the prior state to its actual orthogonal Pauli outcome. -/
theorem qubitTraceComplement_pauli_duality (a : Fin 3) (b : Bool)
    (B : HermitianMat (Fin 2) ℂ) :
    inner ℝ (pauliPriorDensity a b) (qubitTraceComplement B) =
      inner ℝ (pauliPriorDensity a (!b)) B := by
  rw [qubitTraceComplement, HermitianMat.inner_sub_left, HermitianMat.inner_smul_right,
    HermitianMat.inner_one, pauliPriorDensity_trace, mul_one,
    ← pauliPriorDensity_complement, HermitianMat.inner_sub_right, HermitianMat.one_inner]

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
