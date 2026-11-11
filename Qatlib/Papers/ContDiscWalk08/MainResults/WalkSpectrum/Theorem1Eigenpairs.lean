/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.WalkDefs

/-!
# Eigenpairs of the discrete walk

The phases `phasePlus` and `phaseMinus` and the lifted vector `muState` implement the spectral
correspondence of Theorem 1 in [Childs2010]. The module derives the walk eigenvector equations,
computes their squared norms, and normalizes both branches when the Hamiltonian eigenvalue has
square strictly below one.

## Main statements

* `theorem1_eigenvalues_arcsin`: arcsine expressions for the two walk eigenvalues.
* `theorem1_normalized_eigenvector_phasePlus` and `theorem1_normalized_eigenvector_phaseMinus`:
  normalized lifted eigenvectors.

## References

* [Childs, 2010][Childs2010]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped ComplexConjugate

namespace Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Defines the complex phase `exp(i * arccos lam)`. -/
def phasePlus (lam : ℝ) : ℂ := Complex.exp (Complex.I * (Real.arccos lam : ℂ))

/-- Defines the complex phase `exp(-i * arccos lam)`. -/
def phaseMinus (lam : ℝ) : ℂ := Complex.exp (-(Complex.I * (Real.arccos lam : ℂ)))

/-- Defines the lifted vector `D.T *ᵥ v - c • (SwapGate *ᵥ (D.T *ᵥ v))`. -/
def muState (D : WalkSetup I) (v : QState I) (c : ℂ) : QState (I × I) :=
  D.T *ᵥ v - c • (SwapGate *ᵥ (D.T *ᵥ v))

/-- Expands the positive imaginary exponential into its cosine and sine components. -/
theorem phasePlus_eq_cos_sin (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ))
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [mul_comm Complex.I (θ : ℂ), Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- Expands the negative imaginary exponential into its cosine and sine components. -/
theorem phaseMinus_eq_cos_sin (θ : ℝ) :
    Complex.exp (-(Complex.I * (θ : ℂ)))
      = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  rw [show -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  rw [Complex.exp_mul_I]
  rw [show Complex.cos ((-θ : ℝ) : ℂ) = (Real.cos θ : ℂ) from by
        rw [← Complex.ofReal_cos, Real.cos_neg],
      show Complex.sin ((-θ : ℝ) : ℂ) = -((Real.sin θ : ℂ)) from by
        rw [← Complex.ofReal_sin, Real.sin_neg]; push_cast; ring]
  ring

/-- Complex conjugation sends the positive imaginary exponential to the negative imaginary
exponential. -/
theorem phasePlus_conj (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ)))
      = Complex.exp (-(Complex.I * (θ : ℂ))) := by
  rw [phasePlus_eq_cos_sin θ, phaseMinus_eq_cos_sin θ]
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The positive imaginary exponential multiplied by its conjugate equals one. -/
theorem exp_I_unit (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) * (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ))) = 1 := by
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  have hconj : (starRingEnd ℂ)
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hsq : ((Real.cos θ : ℂ)) ^ 2 + ((Real.sin θ : ℂ)) ^ 2 = 1 := by
    have h : ((Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 : ℝ) = 1 := Real.cos_sq_add_sin_sq θ
    have hcast : ((Real.cos θ : ℂ)) ^ 2 + ((Real.sin θ : ℂ)) ^ 2
        = (((Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, h]; norm_num
  rw [phasePlus_eq_cos_sin θ, hconj]
  linear_combination hsq - ((Real.sin θ : ℂ)) ^ 2 * hI

/-- The phase `phasePlus lam` multiplied by its conjugate equals one. -/
theorem phasePlus_unit (lam : ℝ) :
    phasePlus lam * (starRingEnd ℂ) (phasePlus lam) = 1 :=
  exp_I_unit (Real.arccos lam)

/-- The phase `phaseMinus lam` multiplied by its conjugate equals one. -/
theorem phaseMinus_unit (lam : ℝ) :
    phaseMinus lam * (starRingEnd ℂ) (phaseMinus lam) = 1 := by
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  have hconj : (starRingEnd ℂ)
      ((Real.cos (Real.arccos lam) : ℂ) - (Real.sin (Real.arccos lam) : ℂ) * Complex.I)
      = (Real.cos (Real.arccos lam) : ℂ)
        + (Real.sin (Real.arccos lam) : ℂ) * Complex.I := by
    rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hsq : ((Real.cos (Real.arccos lam) : ℂ)) ^ 2
      + ((Real.sin (Real.arccos lam) : ℂ)) ^ 2 = 1 := by
    have h : ((Real.cos (Real.arccos lam)) ^ 2 + (Real.sin (Real.arccos lam)) ^ 2 : ℝ) = 1 :=
      Real.cos_sq_add_sin_sq (Real.arccos lam)
    have hcast : ((Real.cos (Real.arccos lam) : ℂ)) ^ 2
        + ((Real.sin (Real.arccos lam) : ℂ)) ^ 2
        = (((Real.cos (Real.arccos lam)) ^ 2 + (Real.sin (Real.arccos lam)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, h]; norm_num
  unfold phaseMinus
  rw [phaseMinus_eq_cos_sin (Real.arccos lam), hconj]
  linear_combination hsq - ((Real.sin (Real.arccos lam) : ℂ)) ^ 2 * hI

/-- For `lam ∈ [-1, 1]`, the phase `phasePlus lam` solves `c ^ 2 - 2 * lam * c + 1 = 0` over the
complex numbers. -/
theorem phasePlus_quadratic (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    phasePlus lam ^ 2 - 2 * (lam : ℂ) * phasePlus lam + 1 = 0 := by
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  have hsq : ((Real.sin (Real.arccos lam) : ℂ)) ^ 2 = 1 - (lam : ℂ) ^ 2 := by
    have hreal : (Real.sin (Real.arccos lam)) ^ 2 = 1 - lam ^ 2 := by
      have h := Real.sin_sq_add_cos_sq (Real.arccos lam)
      rw [Real.cos_arccos h1 h2] at h
      linarith
    have hcast : ((Real.sin (Real.arccos lam) : ℂ)) ^ 2
        = (((Real.sin (Real.arccos lam)) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, hreal]; push_cast; ring
  unfold phasePlus
  rw [phasePlus_eq_cos_sin (Real.arccos lam), Real.cos_arccos h1 h2]
  linear_combination (-1 : ℂ) * hsq
    + ((Real.sin (Real.arccos lam) : ℂ)) ^ 2 * hI

/-- For `lam ∈ [-1, 1]`, the phase `phaseMinus lam` solves `c ^ 2 - 2 * lam * c + 1 = 0` over
the complex numbers. -/
theorem phaseMinus_quadratic (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    phaseMinus lam ^ 2 - 2 * (lam : ℂ) * phaseMinus lam + 1 = 0 := by
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  have hsq : ((Real.sin (Real.arccos lam) : ℂ)) ^ 2 = 1 - (lam : ℂ) ^ 2 := by
    have hreal : (Real.sin (Real.arccos lam)) ^ 2 = 1 - lam ^ 2 := by
      have h := Real.sin_sq_add_cos_sq (Real.arccos lam)
      rw [Real.cos_arccos h1 h2] at h
      linarith
    have hcast : ((Real.sin (Real.arccos lam) : ℂ)) ^ 2
        = (((Real.sin (Real.arccos lam)) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, hreal]; push_cast; ring
  unfold phaseMinus
  rw [phaseMinus_eq_cos_sin (Real.arccos lam), Real.cos_arccos h1 h2]
  linear_combination (-1 : ℂ) * hsq
    + ((Real.sin (Real.arccos lam) : ℂ)) ^ 2 * hI

/-- For `lam ∈ [-1, 1]`, expresses `i * phasePlus lam` as `-√(1 - lam ^ 2) + i * lam`. -/
theorem phasePlus_eigenvalue_sqrt (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    Complex.I * phasePlus lam
      = -((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) + Complex.I * (lam : ℂ) := by
  have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  unfold phasePlus
  rw [phasePlus_eq_cos_sin (Real.arccos lam), Real.cos_arccos h1 h2, Real.sin_arccos]
  linear_combination ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) * hI

/-- For `lam ∈ [-1, 1]`, expresses `i * phaseMinus lam` as `√(1 - lam ^ 2) + i * lam`. -/
theorem phaseMinus_eigenvalue_sqrt (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    Complex.I * phaseMinus lam
      = ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) + Complex.I * (lam : ℂ) := by
  have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  unfold phaseMinus
  rw [phaseMinus_eq_cos_sin (Real.arccos lam), Real.cos_arccos h1 h2, Real.sin_arccos]
  linear_combination (-((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)) * hI

/-- If `v` satisfies the normalized Hamiltonian eigenvector equation and `c` solves the
associated quadratic, then `muState D v c` satisfies the walk eigenvector equation with
scalar `i * c`. -/
theorem walkOperator_muState (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (c : ℂ) (hc : c ^ 2 - 2 * (lam : ℂ) * c + 1 = 0) :
    walkOperator D *ᵥ muState D v c = (Complex.I * c) • muState D v c := by
  unfold muState
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul,
    walkOperator_mulVec_T, walkOperator_mulVec_swap D lam v heig]
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (Complex.I * ((SwapGate *ᵥ (D.T *ᵥ v)) x)) * hc

/-- For `lam ∈ [-1, 1]`, the plus-phase lift of a vector satisfying the normalized Hamiltonian
eigenvector equation satisfies the walk equation with scalar `i * phasePlus lam`. -/
theorem walkOperator_muState_phasePlus (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    walkOperator D *ᵥ muState D v (phasePlus lam)
      = (Complex.I * phasePlus lam) • muState D v (phasePlus lam) :=
  walkOperator_muState D lam v heig (phasePlus lam) (phasePlus_quadratic lam h1 h2)

/-- For `lam ∈ [-1, 1]`, the minus-phase lift of a vector satisfying the normalized Hamiltonian
eigenvector equation satisfies the walk equation with scalar `i * phaseMinus lam`. -/
theorem walkOperator_muState_phaseMinus (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    walkOperator D *ᵥ muState D v (phaseMinus lam)
      = (Complex.I * phaseMinus lam) • muState D v (phaseMinus lam) :=
  walkOperator_muState D lam v heig (phaseMinus lam) (phaseMinus_quadratic lam h1 h2)

/-- The embedding `D.T` preserves the self inner product of a state. -/
theorem inner_Tv_Tv (D : WalkSetup I) (v : QState I) :
    Inner (D.T *ᵥ v) (D.T *ᵥ v) = Inner v v := by
  rw [inner_mulVec_left_rect D.T v (D.T *ᵥ v)]
  rw [Matrix.mulVec_mulVec, D.isometry, Matrix.one_mulVec]

/-- For a vector satisfying the normalized Hamiltonian eigenvector equation, its embedded inner
product with its swapped embedding equals `lam` times its self inner product. -/
theorem inner_Tv_Sv (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v) :
    Inner (D.T *ᵥ v) (SwapGate *ᵥ (D.T *ᵥ v)) = (lam : ℂ) * Inner v v := by
  rw [inner_mulVec_left_rect D.T v (SwapGate *ᵥ (D.T *ᵥ v))]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, D.gram, heig,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right]

/-- For a vector satisfying the normalized Hamiltonian eigenvector equation, the inner product
of its swapped embedding with its embedding equals `lam` times its self inner product. -/
theorem inner_Sv_Tv (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v) :
    Inner (SwapGate *ᵥ (D.T *ᵥ v)) (D.T *ᵥ v) = (lam : ℂ) * Inner v v := by
  rw [inner_mulVec_left_rect SwapGate (D.T *ᵥ v) (D.T *ᵥ v)]
  rw [swap_conjTranspose]
  exact inner_Tv_Sv D lam v heig

/-- Swapping the embedded state preserves its self inner product. -/
theorem inner_Sv_Sv (D : WalkSetup I) (v : QState I) :
    Inner (SwapGate *ᵥ (D.T *ᵥ v)) (SwapGate *ᵥ (D.T *ᵥ v)) = Inner v v := by
  rw [inner_mulVec_left_rect SwapGate (D.T *ᵥ v) (SwapGate *ᵥ (D.T *ᵥ v))]
  rw [swap_conjTranspose, Matrix.mulVec_mulVec, swap_mul_self, Matrix.one_mulVec]
  exact inner_Tv_Tv D v

/-- For a normalized Hamiltonian eigenvector, computes the self inner product of `muState D v c`
as `1 - lam * (c + conj c) + conj c * c`. -/
theorem inner_muState_self (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (hv : Normalized v)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v) (c : ℂ) :
    Inner (muState D v c) (muState D v c)
      = 1 - (lam : ℂ) * (c + (starRingEnd ℂ) c) + (starRingEnd ℂ) c * c := by
  have hvv : Inner v v = 1 := (normalized_iff_inner_self v).mp hv
  unfold muState
  rw [Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_left,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right]
  rw [inner_Tv_Tv D v, inner_Tv_Sv D lam v heig, inner_Sv_Sv D v,
    inner_Sv_Tv D lam v heig, hvv]
  ring

/-- For `lam ∈ [-1, 1]`, the sum of `phasePlus lam` and its conjugate is `2 * lam`. -/
theorem phasePlus_add_conj (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    phasePlus lam + (starRingEnd ℂ) (phasePlus lam) = 2 * (lam : ℂ) := by
  have hconj : (starRingEnd ℂ)
      ((lam : ℂ) + (Real.sin (Real.arccos lam) : ℂ) * Complex.I)
      = (lam : ℂ) - (Real.sin (Real.arccos lam) : ℂ) * Complex.I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  unfold phasePlus
  rw [phasePlus_eq_cos_sin (Real.arccos lam), Real.cos_arccos h1 h2, hconj]
  ring

/-- For `lam ∈ [-1, 1]`, the sum of `phaseMinus lam` and its conjugate is `2 * lam`. -/
theorem phaseMinus_add_conj (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    phaseMinus lam + (starRingEnd ℂ) (phaseMinus lam) = 2 * (lam : ℂ) := by
  have hconj : (starRingEnd ℂ)
      ((lam : ℂ) - (Real.sin (Real.arccos lam) : ℂ) * Complex.I)
      = (lam : ℂ) + (Real.sin (Real.arccos lam) : ℂ) * Complex.I := by
    rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  unfold phaseMinus
  rw [phaseMinus_eq_cos_sin (Real.arccos lam), Real.cos_arccos h1 h2, hconj]
  ring

/-- For a normalized Hamiltonian eigenvector with `lam ∈ [-1, 1]`, the plus-phase lift has self
inner product `2 * (1 - lam ^ 2)`. -/
theorem inner_muState_phasePlus (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (hv : Normalized v)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    Inner (muState D v (phasePlus lam)) (muState D v (phasePlus lam))
      = 2 * (1 - (lam : ℂ) ^ 2) := by
  rw [inner_muState_self D lam v hv heig (phasePlus lam), phasePlus_add_conj lam h1 h2]
  rw [show (starRingEnd ℂ) (phasePlus lam) * phasePlus lam = 1 from by
        rw [mul_comm, phasePlus_unit]]
  ring

/-- For a normalized Hamiltonian eigenvector with `lam ∈ [-1, 1]`, the minus-phase lift has self
inner product `2 * (1 - lam ^ 2)`. -/
theorem inner_muState_phaseMinus (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (hv : Normalized v)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    Inner (muState D v (phaseMinus lam)) (muState D v (phaseMinus lam))
      = 2 * (1 - (lam : ℂ) ^ 2) := by
  rw [inner_muState_self D lam v hv heig (phaseMinus lam), phaseMinus_add_conj lam h1 h2]
  rw [show (starRingEnd ℂ) (phaseMinus lam) * phaseMinus lam = 1 from by
        rw [mul_comm, phaseMinus_unit]]
  ring

/-- For `lam ∈ [-1, 1]`, expands `exp(i * arcsin lam)` as `√(1 - lam ^ 2) + i * lam`. -/
theorem exp_I_arcsin (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    Complex.exp (Complex.I * (Real.arcsin lam : ℂ))
      = ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) + Complex.I * (lam : ℂ) := by
  rw [phasePlus_eq_cos_sin (Real.arcsin lam), Real.cos_arcsin, Real.sin_arcsin h1 h2]
  ring

/-- For `lam ∈ [-1, 1]`, expands `exp(-i * arcsin lam)` as `√(1 - lam ^ 2) - i * lam`. -/
theorem exp_neg_I_arcsin (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    Complex.exp (-(Complex.I * (Real.arcsin lam : ℂ)))
      = ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) - Complex.I * (lam : ℂ) := by
  rw [phaseMinus_eq_cos_sin (Real.arcsin lam), Real.cos_arcsin, Real.sin_arcsin h1 h2]
  ring

/-- Identifies the two phase-derived walk eigenvalues with `-exp(-i * arcsin lam)` and `exp(i *
arcsin lam)` for `lam ∈ [-1, 1]`. See [Childs, Theorem 1][Childs2010]. -/
theorem theorem1_eigenvalues_arcsin (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam ≤ 1) :
    Complex.I * phasePlus lam = -Complex.exp (-(Complex.I * (Real.arcsin lam : ℂ)))
      ∧ Complex.I * phaseMinus lam = Complex.exp (Complex.I * (Real.arcsin lam : ℂ)) := by
  refine ⟨?_, ?_⟩
  · rw [phasePlus_eigenvalue_sqrt lam h1 h2, exp_neg_I_arcsin lam h1 h2]; ring
  · rw [phaseMinus_eigenvalue_sqrt lam h1 h2, exp_I_arcsin lam h1 h2]

/-- For a normalized Hamiltonian eigenvector with `lam ^ 2 < 1`, dividing the plus-phase lift by
`√(2 * (1 - lam ^ 2))` gives a normalized state. See [Childs, Theorem 1][Childs2010]. -/
theorem theorem1_normalized_phasePlus (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (hv : Normalized v)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (hlam : lam ^ 2 < 1) :
    Normalized
      ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ) • muState D v (phasePlus lam)) := by
  have h1 : -1 ≤ lam := by nlinarith [hlam, sq_nonneg (lam + 1)]
  have h2 : lam ≤ 1 := by nlinarith [hlam, sq_nonneg (lam - 1)]
  have hpos : (0 : ℝ) < 2 * (1 - lam ^ 2) := by nlinarith
  have hne : Real.sqrt (2 * (1 - lam ^ 2)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hsqC : (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ)) ^ 2
      = 2 * (1 - (lam : ℂ) ^ 2) := by
    have h := Real.sq_sqrt (le_of_lt hpos)
    have hcast : (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ)) ^ 2
        = (((Real.sqrt (2 * (1 - lam ^ 2))) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, h]; push_cast; ring
  have hYne : (2 * (1 - (lam : ℂ) ^ 2)) ≠ 0 := by
    have hc : (2 * (1 - (lam : ℂ) ^ 2)) = ((2 * (1 - lam ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hc]; exact_mod_cast (ne_of_gt hpos)
  have hS : ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ))
      = (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ))⁻¹ := by push_cast; ring
  have hC : ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ))
      * ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ))
      * (2 * (1 - (lam : ℂ) ^ 2)) = 1 := by
    rw [hS]
    have hpp : (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ))⁻¹
        * (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ))⁻¹
        = (2 * (1 - (lam : ℂ) ^ 2))⁻¹ := by
      rw [← mul_inv, ← sq, hsqC]
    rw [hpp, inv_mul_cancel₀ hYne]
  rw [normalized_iff_inner_self,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
    inner_muState_phasePlus D lam v hv heig h1 h2]
  rw [starRingEnd_ofReal, ← mul_assoc]
  exact hC

/-- For a normalized Hamiltonian eigenvector with `lam ^ 2 < 1`, dividing the minus-phase lift
by `√(2 * (1 - lam ^ 2))` gives a normalized state. See [Childs, Theorem 1][Childs2010]. -/
theorem theorem1_normalized_phaseMinus (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (hv : Normalized v)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (hlam : lam ^ 2 < 1) :
    Normalized
      ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ) • muState D v (phaseMinus lam)) := by
  have h1 : -1 ≤ lam := by nlinarith [hlam, sq_nonneg (lam + 1)]
  have h2 : lam ≤ 1 := by nlinarith [hlam, sq_nonneg (lam - 1)]
  have hpos : (0 : ℝ) < 2 * (1 - lam ^ 2) := by nlinarith
  have hne : Real.sqrt (2 * (1 - lam ^ 2)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hsqC : (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ)) ^ 2
      = 2 * (1 - (lam : ℂ) ^ 2) := by
    have h := Real.sq_sqrt (le_of_lt hpos)
    have hcast : (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ)) ^ 2
        = (((Real.sqrt (2 * (1 - lam ^ 2))) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, h]; push_cast; ring
  have hYne : (2 * (1 - (lam : ℂ) ^ 2)) ≠ 0 := by
    have hc : (2 * (1 - (lam : ℂ) ^ 2)) = ((2 * (1 - lam ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hc]; exact_mod_cast (ne_of_gt hpos)
  have hS : ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ))
      = (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ))⁻¹ := by push_cast; ring
  have hC : ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ))
      * ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ))
      * (2 * (1 - (lam : ℂ) ^ 2)) = 1 := by
    rw [hS]
    have hpp : (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ))⁻¹
        * (((Real.sqrt (2 * (1 - lam ^ 2)) : ℝ) : ℂ))⁻¹
        = (2 * (1 - (lam : ℂ) ^ 2))⁻¹ := by
      rw [← mul_inv, ← sq, hsqC]
    rw [hpp, inv_mul_cancel₀ hYne]
  rw [normalized_iff_inner_self,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
    inner_muState_phaseMinus D lam v hv heig h1 h2]
  rw [starRingEnd_ofReal, ← mul_assoc]
  exact hC

/-- For a normalized Hamiltonian eigenvector with `lam ^ 2 < 1`, the rescaled plus-phase lift is
normalized and satisfies the walk eigenvector equation with eigenvalue `i * phasePlus lam`.
See [Childs, Theorem 1][Childs2010]. -/
theorem theorem1_normalized_eigenvector_phasePlus (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (hv : Normalized v)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (hlam : lam ^ 2 < 1) :
    Normalized
        ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ) • muState D v (phasePlus lam))
      ∧ walkOperator D *ᵥ
          ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ) • muState D v (phasePlus lam))
          = (Complex.I * phasePlus lam) •
              ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ) • muState D v (phasePlus lam)) := by
  have h1 : -1 ≤ lam := by nlinarith [hlam, sq_nonneg (lam + 1)]
  have h2 : lam ≤ 1 := by nlinarith [hlam, sq_nonneg (lam - 1)]
  refine ⟨theorem1_normalized_phasePlus D lam v hv heig hlam, ?_⟩
  rw [Matrix.mulVec_smul, walkOperator_muState_phasePlus D lam v heig h1 h2, smul_smul,
    smul_smul]
  congr 1
  ring

/-- For a normalized Hamiltonian eigenvector with `lam ^ 2 < 1`, the rescaled minus-phase lift
is normalized and satisfies the walk eigenvector equation with eigenvalue `i * phaseMinus
lam`. See [Childs, Theorem 1][Childs2010]. -/
theorem theorem1_normalized_eigenvector_phaseMinus (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (hv : Normalized v)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v)
    (hlam : lam ^ 2 < 1) :
    Normalized
        ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ) • muState D v (phaseMinus lam))
      ∧ walkOperator D *ᵥ
          ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ) • muState D v (phaseMinus lam))
          = (Complex.I * phaseMinus lam) •
              ((((Real.sqrt (2 * (1 - lam ^ 2)))⁻¹ : ℝ) : ℂ) • muState D v (phaseMinus lam)) := by
  have h1 : -1 ≤ lam := by nlinarith [hlam, sq_nonneg (lam + 1)]
  have h2 : lam ≤ 1 := by nlinarith [hlam, sq_nonneg (lam - 1)]
  refine ⟨theorem1_normalized_phaseMinus D lam v hv heig hlam, ?_⟩
  rw [Matrix.mulVec_smul, walkOperator_muState_phaseMinus D lam v heig h1 h2, smul_smul,
    smul_smul]
  congr 1
  ring

end Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum
