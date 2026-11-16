/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.TraceBounds.GaussianGain
public import Qatlib.Concepts.GibbsSource.SpectralGeom.BlockSpectralCertification

@[expose] public section


/-! # Full matrix-unit traces and unitary probability clocks

The left-minus-right gradient is represented by its actual positive Gram
operator. Its trace uses every matrix unit. Unitary conjugation preserves
that trace, so averaging over a probability measure preserves the complete
source mass without a time-grid approximation.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Concepts.GibbsSource.SourceForms
open Qatlib.Concepts.GibbsSource.SpectralGeom
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.TraceBounds

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section
variable {D : ℕ}

/-- Multiplication by the complete orthonormal matrix units, with all entries
retained. -/
theorem mul_matUnit_entry (S : Operator D) (i j k l : Fin D) :
    (S * matUnit i j 1) k l = if l = j then S k i else 0 := by
  simp [Matrix.mul_apply, matUnit_apply, ite_and]

/-- Right multiplication by a matrix unit retains its specified row. -/
theorem matUnit_mul_entry (F : Operator D) (i j k l : Fin D) :
    (matUnit i j 1 * F) k l = if k = i then F j l else 0 := by
  simp [Matrix.mul_apply, matUnit_apply, ite_and]

/-- The squared mass of a left-multiplied matrix unit is its source column mass. -/
theorem hsInner_left_matUnit (S : Operator D) (i j : Fin D) :
    hsInner (S * matUnit i j 1) (S * matUnit i j 1) =
      ∑ k, star (S k i) * S k i := by
  simp [hsInner_eq_sum, mul_matUnit_entry, apply_ite]

/-- The squared mass of a right-multiplied matrix unit is its source row mass. -/
theorem hsInner_right_matUnit (F : Operator D) (i j : Fin D) :
    hsInner (matUnit i j 1 * F) (matUnit i j 1 * F) =
      ∑ l, star (F j l) * F j l := by
  simp [hsInner_eq_sum, matUnit_mul_entry, apply_ite]

/-- The cross term of left and right multiplication uses their diagonal entries. -/
theorem hsInner_cross_matUnit (S F : Operator D) (i j : Fin D) :
    hsInner (S * matUnit i j 1) (matUnit i j 1 * F) =
      star (S i i) * F j j := by
  simp [hsInner_eq_sum, mul_matUnit_entry, matUnit_mul_entry, apply_ite]

/-- Exact full-space trace identity for a left-minus-right multiplier. -/
theorem sum_matrixUnit_gradient_square (S F : Operator D) :
    (∑ i, ∑ j, hsInner (S * matUnit i j 1 - matUnit i j 1 * F)
      (S * matUnit i j 1 - matUnit i j 1 * F)) =
      (D : ℂ) * hsInner S S + (D : ℂ) * hsInner F F -
        star (Matrix.trace S) * Matrix.trace F -
        star (Matrix.trace F) * Matrix.trace S := by
  have hrev (i j : Fin D) :
      hsInner (matUnit i j 1 * F) (S * matUnit i j 1) =
        star (F j j) * S i i := by
    rw [hsInner_conj_swap, hsInner_cross_matUnit]
    simp [mul_comm]
  have hleft :
      (∑ i, ∑ j, hsInner (S * matUnit i j 1) (S * matUnit i j 1)) =
      (D : ℂ) * hsInner S S := by
    simp only [hsInner_left_matUnit, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_comm, hsInner_eq_sum]
  have hright :
      (∑ i, ∑ j, hsInner (matUnit i j 1 * F) (matUnit i j 1 * F)) =
      (D : ℂ) * hsInner F F := by
    simp_rw [hsInner_right_matUnit]
    simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsInner_eq_sum]
  have hc₁ : (∑ i, ∑ j, star (S i i) * F j j) =
      star (Matrix.trace S) * Matrix.trace F := by
    simp only [Matrix.trace, Matrix.diag_apply, star_sum, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_comm
  have hc₂ : (∑ i, ∑ j, star (F j j) * S i i) =
      star (Matrix.trace F) * Matrix.trace S := by
    rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag_apply, star_sum, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_comm
  simp only [hsInner_sub_left, hsInner_sub_right, Finset.sum_sub_distrib]
  rw [hleft, hright]
  simp_rw [hsInner_cross_matUnit, hrev]
  rw [hc₁, hc₂]
  ring


/-- A left-minus-right gradient as a complex-linear map. -/
def gradientMap (S F : Operator D) : Operator D →ₗ[ℂ] Operator D where
  toFun X := S * X - X * F
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]; rfl

/-- The Hilbert--Schmidt adjoint of a left-minus-right gradient. -/
theorem gradientMap_adjoint (S F X Y : Operator D) :
    hsInner (gradientMap S F X) Y = hsInner X (gradientMap Sᴴ Fᴴ Y) := by
  simp only [gradientMap, LinearMap.coe_mk, AddHom.coe_mk, hsInner,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
  congr 1
  rw [Matrix.trace_mul_comm Fᴴ (Xᴴ * Y), Matrix.mul_assoc]

/-- The actual positive Gram map of a left-minus-right gradient. -/
def gradientGram (S F : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  (gradientMap Sᴴ Fᴴ).comp (gradientMap S F)

/-- The Gram quadratic form is the squared mass of the actual gradient. -/
theorem gradientGram_energy (S F X : Operator D) :
    hsInner X (gradientGram S F X) = hsInner (gradientMap S F X) (gradientMap S F X) :=
  (gradientMap_adjoint S F X (gradientMap S F X)).symm

/-- A gradient Gram map is self-adjoint on the complete complex operator space. -/
theorem gradientGram_selfAdjoint (S F : Operator D) : SourceSelfAdjoint (gradientGram S F) := by
  intro X Y
  change hsInner (gradientMap Sᴴ Fᴴ (gradientMap S F X)) Y =
    hsInner X (gradientMap Sᴴ Fᴴ (gradientMap S F Y))
  rw [gradientMap_adjoint, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, ← gradientMap_adjoint]

/-- A gradient Gram map is positive on every complex input. -/
theorem gradientGram_nonneg (S F X : Operator D) :
    0 ≤ (hsInner X (gradientGram S F X)).re := by
  rw [gradientGram_energy]
  exact hsInner_self_nonneg _

/-- The source trace is the exact sum of quadratic forms on all matrix units. -/
theorem sourceTrace_eq_matrixUnit_sum (L : Operator D →ₗ[ℂ] Operator D) :
    sourceTrace L = ∑ i, ∑ j, (hsInner (matUnit i j 1) (L (matUnit i j 1))).re := by
  simp only [sourceTrace, sourceSuperMatrix, Matrix.trace, Matrix.diag_apply,
    Complex.re_sum, Fintype.sum_prod_type, hsInner_matUnit_left]

/-- A source whose two factors preserve the same trace has a nonpositive trace correction. -/
theorem gradientGram_trace_le (S F A : Operator D)
    (hS : Matrix.trace S = Matrix.trace A) (hF : Matrix.trace F = Matrix.trace A)
    (hSn : (hsInner S S).re ≤ (hsInner A A).re)
    (hFn : (hsInner F F).re ≤ (hsInner A A).re) :
    sourceTrace (gradientGram S F) ≤ 2 * (D : ℝ) * (hsInner A A).re := by
  have he : sourceTrace (gradientGram S F) =
      (D : ℝ) * (hsInner S S).re + (D : ℝ) * (hsInner F F).re -
        2 * Complex.normSq (Matrix.trace A) := by
    have hu : sourceTrace (gradientGram S F) =
        ∑ i, ∑ j, (hsInner (S * matUnit i j 1 - matUnit i j 1 * F)
          (S * matUnit i j 1 - matUnit i j 1 * F)).re := by
      rw [sourceTrace_eq_matrixUnit_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg Complex.re (gradientGram_energy S F (matUnit i j 1))
    rw [hu]
    have h := congrArg Complex.re (sum_matrixUnit_gradient_square S F)
    rw [hS, hF] at h
    simp only [Complex.re_sum, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply] at h ⊢
    linear_combination h
  rw [he]
  have hp := mul_le_mul_of_nonneg_left (add_le_add hSn hFn)
    (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
  nlinarith [Complex.normSq_nonneg (Matrix.trace A)]

/-- The Gaussian thermal Gram parent with the original one-half source mass. -/
def spectralGaussianParent {ι P : Type*} [Fintype ι] [Fintype P]
    (flags : ι → Operator D) (E : ι → ℝ) (β : ℝ)
    (A : P → Operator D) : Operator D →ₗ[ℂ] Operator D :=
  (((1/2 : ℝ) : ℂ)) • ∑ p,
    gradientGram
      (spectralMultiplier flags (fun i j => (gaussianGain ((-β) * (E i-E j)) : ℂ)) (A p))
      (spectralMultiplier flags (fun i j => (gaussianGain (β * (E i-E j)) : ℂ)) (A p))

/-- Every complete normalized Hermitian proposal frame has a Gaussian parent trace at most D squared. -/
theorem spectralGaussianParent_trace_le_dimension_sq
    {ι P : Type*} [Fintype ι] [DecidableEq ι] [Fintype P]
    (flags : ι → Operator D) (hflags : ∀ i, (flags i).IsHermitian)
    (horth : ∀ i j, flags i * flags j = if i = j then flags i else 0)
    (hsum : ∑ i, flags i = 1) (E : ι → ℝ) (β : ℝ)
    (A : P → Operator D) (hA : ∀ p, (A p).IsHermitian)
    (hframe : ∑ p, (A p)ᴴ * A p = 1) :
    sourceTrace (spectralGaussianParent flags E β A) ≤ (D : ℝ)^2 := by
  have hm : (∑ p, (hsInner (A p) (A p)).re) = (D : ℝ) := by
    rw [← Complex.re_sum]
    simp only [hsInner, ← Matrix.trace_sum, hframe, Matrix.trace_one]
    simp
  have hk (p : P) :
      sourceTrace (gradientGram
        (spectralMultiplier flags (fun i j => (gaussianGain ((-β) * (E i-E j)) : ℂ)) (A p))
        (spectralMultiplier flags (fun i j => (gaussianGain (β * (E i-E j)) : ℂ)) (A p))) ≤
      2 * (D : ℝ) * (hsInner (A p) (A p)).re := by
    apply gradientGram_trace_le _ _ (A p)
    · apply trace_spectralMultiplier flags horth hsum
      intro i
      simp [gaussianGain]
    · apply trace_spectralMultiplier flags horth hsum
      intro i
      simp [gaussianGain]
    · exact spectralMultiplier_gaussianGain_hsSquare_le flags hflags horth hsum E (-β) _ (hA p)
    · exact spectralMultiplier_gaussianGain_hsSquare_le flags hflags horth hsum E β _ (hA p)
  have h := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hk p)
  rw [← Finset.mul_sum, hm] at h
  rw [spectralGaussianParent, sourceTrace_real_smul, sourceTrace_sum]
  nlinarith


/-- A change of complete linear coordinates preserves the real source trace. -/
theorem sourceTrace_conj (L : Operator D →ₗ[ℂ] Operator D)
    (e : Operator D ≃ₗ[ℂ] Operator D) : sourceTrace (e.conj L) = sourceTrace L := by
  rw [sourceTrace_eq_linearTrace, sourceTrace_eq_linearTrace, LinearMap.trace_conj']

/-- Unitary conjugation as a linear equivalence on every complex matrix. -/
def unitaryEquiv (U : Operator D) (hU : Uᴴ * U = 1) : Operator D ≃ₗ[ℂ] Operator D where
  toFun := fullUnitaryConj U
  invFun := fullUnitaryConj Uᴴ
  left_inv := fun X => fullUnitaryConj_leftInverse U X hU
  right_inv := fun X => fullUnitaryConj_inverse U X hU
  map_add' X Y := by simp only [fullUnitaryConj, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [fullUnitaryConj, Matrix.mul_smul, Matrix.smul_mul]; rfl

/-- Summing a quadratic form over the unitarily transported complete frame preserves its trace. -/
theorem sum_unitary_energy (L : Operator D →ₗ[ℂ] Operator D)
    (U : Operator D) (hU : Uᴴ * U = 1) :
    (∑ i, ∑ j, (hsInner (fullUnitaryConj U (matUnit i j 1))
      (L (fullUnitaryConj U (matUnit i j 1)))).re) = sourceTrace L := by
  let e := unitaryEquiv U hU
  have he (X : Operator D) :
      hsInner (e X) (L (e X)) = hsInner X (e.symm (L (e X))) := by
    have hh := fullUnitaryConj_hsInner U X (e.symm (L (e X))) hU
    change hsInner (e X) (e (e.symm (L (e X)))) = _ at hh
    simpa only [e.apply_symm_apply] using hh
  change (∑ i, ∑ j, (hsInner (e (matUnit i j 1)) (L (e (matUnit i j 1)))).re) = _
  simp_rw [he]
  change (∑ i, ∑ j, (hsInner (matUnit i j 1) (e.symm.conj L (matUnit i j 1))).re) = _
  rw [← sourceTrace_eq_matrixUnit_sum, sourceTrace_conj]

end
end Qatlib.Concepts.GibbsSource.TraceBounds
