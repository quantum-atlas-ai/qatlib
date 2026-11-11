/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Weighted invariants and multiplexed matrix expectations

This module defines the phase `sourceAlpha`, the weighted expression `sourceInvariant`, and the
multiplexed matrix expectation used in [GarneroneMarzuoliRasetti2007]. It supplies tensor-state
and tensor-matrix identities, controlled block-diagonal matrices, and the square-root weight
vector `psiFromWeights`.

For a unitary matrix fixing the weight vector, `muxExpectation_eq` reduces the expectation to a
weighted sum of block matrix elements. With normalized nonnegative weights,
`muxExpectation_norm_sub_le` transfers a uniform block-entry approximation bound to the
multiplexed expectation.

## Main statements

* `invariant_mul_alpha_zpow`: Multiplying by the signature phase recovers the weighted sum.
* `muxExpectation_eq`: The multiplexed expectation is a weighted sum of return amplitudes.
* `muxExpectation_norm_sub_le`: Uniform return-amplitude errors bound the expectation error.

## References

* [Garnerone et al., 2007][GarneroneMarzuoliRasetti2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.ManifoldInv07.MainResults.Defs

open Qatlib.Foundations.PureStateMath

/-- The complex phase exp(3πki/(4(k + 2))) at level k. -/
def sourceAlpha (k : ℕ) : ℂ :=
  Complex.exp (((3 * Real.pi * (k : ℝ) / (4 * ((k : ℝ) + 2)) : ℝ)) * Complex.I)

/-- The source phase is nonzero at every natural level. -/
theorem sourceAlpha_ne_zero (k : ℕ) : sourceAlpha k ≠ 0 :=
  Complex.exp_ne_zero _

/-- The weighted sum of supplied polynomial values multiplied by the integer signature
correction α^(−σ). -/
def sourceInvariant {J : Type*} [Fintype J]
    (α : ℂ) (σ : ℤ) (μ : J → ℝ) (Jpoly : J → ℂ) : ℂ :=
  α ^ (-σ) * ∑ j, (μ j : ℂ) * Jpoly j

/-- The vector whose coordinates are the real square roots of the supplied weights, viewed as
complex numbers. -/
def psiFromWeights {J : Type*} (μ : J → ℝ) : QState J := fun j => (Real.sqrt (μ j) : ℂ)

/-- For nonnegative weights, squaring a coordinate of the square-root weight vector recovers
that weight. -/
theorem psiFromWeights_mul_self {J : Type*} (μ : J → ℝ) (hμ : ∀ j, 0 ≤ μ j) (j : J) :
    psiFromWeights μ j * psiFromWeights μ j = (μ j : ℂ) := by
  simp only [psiFromWeights, ← Complex.ofReal_mul, Real.mul_self_sqrt (hμ j)]

/-- Each coordinate of the square-root weight vector is fixed by complex conjugation. -/
theorem star_psiFromWeights {J : Type*} (μ : J → ℝ) (j : J) :
    (starRingEnd ℂ) (psiFromWeights μ j) = psiFromWeights μ j := by
  simp [psiFromWeights]

/-- For nonzero α, multiplying the invariant by α^σ cancels its signature correction and gives
the weighted polynomial sum [GarneroneMarzuoliRasetti2007]. -/
theorem invariant_mul_alpha_zpow {J : Type*} [Fintype J]
    (α : ℂ) (hα : α ≠ 0) (σ : ℤ) (μ : J → ℝ) (Jpoly : J → ℂ) :
    sourceInvariant α σ μ Jpoly * α ^ σ = ∑ j, (μ j : ℂ) * Jpoly j := by
  have hz : α ^ (-σ) * α ^ σ = 1 := by
    rw [← zpow_add₀ hα]
    simp
  unfold sourceInvariant
  set S : ℂ := ∑ j, (μ j : ℂ) * Jpoly j with hS
  calc (α ^ (-σ) * S) * α ^ σ = S * (α ^ (-σ) * α ^ σ) := by ring
    _ = S := by rw [hz, mul_one]

/-- The product-coordinate tensor state with amplitude v(j)w(p) at (j, p). -/
def tensorState {J P : Type*} (v : QState J) (w : QState P) : QState (J × P) :=
  fun a => v a.1 * w a.2

/-- The product-indexed tensor matrix with entries A(j, j′)B(p, p′). -/
def tensorMat {J P : Type*} (A : Matrix J J ℂ) (B : Matrix P P ℂ) :
    Matrix (J × P) (J × P) ℂ :=
  fun a b => A a.1 b.1 * B a.2 b.2

/-- The controlled block-diagonal matrix whose block at color j is `U j`. -/
def blockDiag {J P : Type*} [DecidableEq J] (U : J → Matrix P P ℂ) :
    Matrix (J × P) (J × P) ℂ :=
  fun a b => if a.1 = b.1 then U a.1 a.2 b.2 else 0

/-- Applying a tensor matrix to a tensor state equals the tensor product of the two separately
transformed states. -/
theorem applyGate_tensorMat {J P : Type*} [Fintype J] [Fintype P]
    (A : Matrix J J ℂ) (B : Matrix P P ℂ) (v : QState J) (w : QState P) :
    ApplyGate (tensorMat A B) (tensorState v w)
      = tensorState (ApplyGate A v) (ApplyGate B w) := by
  funext a
  simp only [ApplyGate, tensorMat, tensorState, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- A tensor matrix with identity on the second factor transforms only the first factor of a
tensor state. -/
theorem applyGate_tensorMat_one {J P : Type*} [Fintype J] [Fintype P] [DecidableEq P]
    (A : Matrix J J ℂ) (v : QState J) (w : QState P) :
    ApplyGate (tensorMat A (1 : Matrix P P ℂ)) (tensorState v w)
      = tensorState (ApplyGate A v) w := by
  rw [applyGate_tensorMat, applyGate_one]

/-- Applying the controlled block matrix to a tensor state preserves the first-factor amplitude
and applies the corresponding block to the second factor. -/
theorem applyGate_blockDiag {J P : Type*} [Fintype J] [Fintype P] [DecidableEq J]
    (U : J → Matrix P P ℂ) (v : QState J) (w : QState P) :
    ApplyGate (blockDiag U) (tensorState v w)
      = fun a => v a.1 * ApplyGate (U a.1) w a.2 := by
  funext a
  simp only [ApplyGate, blockDiag, tensorState, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a.1]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [if_pos rfl]
    ring
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ a.1) h

/-- The inner product of tensor states factors as the product of their two component inner
products. -/
theorem inner_tensorState {J P : Type*} [Fintype J] [Fintype P] [DecidableEq J]
    [DecidableEq P] (v v' : QState J) (w w' : QState P) :
    Inner (tensorState v w) (tensorState v' w') = Inner v v' * Inner w w' := by
  simp only [inner_apply, tensorState, Fintype.sum_prod_type]
  simp only [starRingEnd_apply, star_mul]
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The inner product with the basis ket at a equals the a-coordinate of the state. -/
theorem inner_ket_left {I : Type*} [Fintype I] [DecidableEq I] (a : I) (φ : QState I) :
    Inner (Ket a) φ = φ a := by
  rw [inner_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The inner product with a tensor of a color state and `Ket p0` is the sum of conjugated color
amplitudes times the coordinates at `p0`. -/
theorem inner_tensorState_ket_left {J P : Type*} [Fintype J] [Fintype P] [DecidableEq J]
    [DecidableEq P] (ψJ : QState J) (p0 : P) (φ : QState (J × P)) :
    Inner (tensorState ψJ (Ket p0)) φ = ∑ j, (starRingEnd ℂ) (ψJ j) * φ (j, p0) := by
  rw [inner_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single p0]
  · simp [tensorState]
  · intro p _ hp
    simp [tensorState, Ket, hp]
  · intro h
    exact absurd (Finset.mem_univ p0) h

/-- At a fixed second-register label, applying `S0` tensored with identity is the matrix sum
over first-register labels. -/
theorem applyGate_tensorMat_one_apply {J P : Type*} [Fintype J] [Fintype P] [DecidableEq P]
    (S0 : Matrix J J ℂ) (y : QState (J × P)) (j : J) (p0 : P) :
    (ApplyGate (tensorMat S0 (1 : Matrix P P ℂ)) y) (j, p0)
      = ∑ j', S0 j j' * y (j', p0) := by
  simp only [ApplyGate, tensorMat, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro j' _
  rw [Finset.sum_eq_single p0]
  · simp
  · intro p' _ hp'
    simp [show p0 ≠ p' from Ne.symm hp']
  · intro h
    exact absurd (Finset.mem_univ p0) h

/-- The expectation of the controlled block matrix followed by `S0` on the square-root weight
state tensored with `Ket p0`. -/
def muxExpectation {J P : Type*} [Fintype J] [Fintype P] [DecidableEq J] [DecidableEq P]
    (S0 : Matrix J J ℂ) (U : J → Matrix P P ℂ) (μ : J → ℝ) (p0 : P) : ℂ :=
  Inner (tensorState (psiFromWeights μ) (Ket p0))
    (ApplyGate (tensorMat S0 (1 : Matrix P P ℂ) * blockDiag U)
      (tensorState (psiFromWeights μ) (Ket p0)))

/-- If a unitary `S0` fixes a vector, its conjugate coordinate row is also fixed under right
multiplication by `S0`. -/
theorem sum_star_mul_S0 {J : Type*} [Fintype J] [DecidableEq J]
    (S0 : Matrix J J ℂ) (ψJ : QState J)
    (hS0u : S0 ∈ Matrix.unitaryGroup J ℂ) (hS0 : ApplyGate S0 ψJ = ψJ) (j' : J) :
    (∑ j, (starRingEnd ℂ) (ψJ j) * S0 j j') = (starRingEnd ℂ) (ψJ j') := by
  have hmv : ApplyGate S0 (Ket j') = fun k => S0 k j' := by
    funext k
    simp only [ApplyGate, Matrix.mulVec, dotProduct, Ket]
    rw [Finset.sum_eq_single j']
    · simp
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ j') h
  have hstep : Inner ψJ (ApplyGate S0 (Ket j')) = (starRingEnd ℂ) (ψJ j') := by
    have hunit : Inner (ApplyGate S0 ψJ) (ApplyGate S0 (Ket j')) = Inner ψJ (Ket j') :=
      inner_applyGate hS0u ψJ (Ket j')
    rw [hS0] at hunit
    rw [hunit, inner_apply, Finset.sum_eq_single j']
    · simp [Ket]
    · intro i _ hi
      simp [Ket, hi]
    · intro h
      exact absurd (Finset.mem_univ j') h
  rw [← hstep, inner_apply, hmv]

/-- For nonnegative weights and a unitary `S0` fixing their square-root vector, the multiplexed
expectation is the weighted sum of the block return amplitudes
[GarneroneMarzuoliRasetti2007]. -/
theorem muxExpectation_eq {J P : Type*} [Fintype J] [Fintype P]
    [DecidableEq J] [DecidableEq P]
    (S0 : Matrix J J ℂ) (U : J → Matrix P P ℂ) (μ : J → ℝ) (p0 : P)
    (hμ : ∀ j, 0 ≤ μ j)
    (hS0u : S0 ∈ Matrix.unitaryGroup J ℂ)
    (hS0 : ApplyGate S0 (psiFromWeights μ) = psiFromWeights μ) :
    muxExpectation S0 U μ p0
      = ∑ j, (μ j : ℂ) * Inner (Ket p0) (ApplyGate (U j) (Ket p0)) := by
  unfold muxExpectation
  rw [applyGate_mul, applyGate_blockDiag]
  rw [inner_tensorState_ket_left]

  have hinner : ∀ j,
      (ApplyGate (tensorMat S0 (1 : Matrix P P ℂ))
        (fun a => psiFromWeights μ a.1 * ApplyGate (U a.1) (Ket p0) a.2)) (j, p0)
      = ∑ j', S0 j j' * (psiFromWeights μ j' * ApplyGate (U j') (Ket p0) p0) := by
    intro j
    rw [applyGate_tensorMat_one_apply]
  simp only [hinner]

  have hexpand : ∀ j,
      (starRingEnd ℂ) (psiFromWeights μ j) *
        (∑ j', S0 j j' * (psiFromWeights μ j' * ApplyGate (U j') (Ket p0) p0))
      = ∑ j', ((starRingEnd ℂ) (psiFromWeights μ j) * S0 j j'
          * psiFromWeights μ j') * ApplyGate (U j') (Ket p0) p0 := by
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j' _
    ring
  simp only [hexpand]
  rw [Finset.sum_comm]

  apply Finset.sum_congr rfl
  intro j' _
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [sum_star_mul_S0 S0 (psiFromWeights μ) hS0u hS0 j']
  rw [star_psiFromWeights, psiFromWeights_mul_self μ hμ j', inner_ket_left]

/-- For normalized nonnegative weights and a unitary `S0` fixing their square-root vector, a
uniform δ bound on block return-amplitude changes gives a δ bound on the multiplexed
expectation change. -/
theorem muxExpectation_norm_sub_le {J P : Type*} [Fintype J] [Fintype P]
    [DecidableEq J] [DecidableEq P]
    (S0 : Matrix J J ℂ) (U U' : J → Matrix P P ℂ) (μ : J → ℝ) (p0 : P)
    (hμ : ∀ j, 0 ≤ μ j) (hμsum : ∑ j, μ j = 1)
    (hS0u : S0 ∈ Matrix.unitaryGroup J ℂ)
    (hS0 : ApplyGate S0 (psiFromWeights μ) = psiFromWeights μ)
    (δ : ℝ)
    (hδ : ∀ j, ‖(ApplyGate (U' j) (Ket p0)) p0
      - (ApplyGate (U j) (Ket p0)) p0‖ ≤ δ) :
    ‖muxExpectation S0 U' μ p0 - muxExpectation S0 U μ p0‖ ≤ δ := by
  rw [muxExpectation_eq S0 U' μ p0 hμ hS0u hS0,
    muxExpectation_eq S0 U μ p0 hμ hS0u hS0]
  simp only [inner_ket_left]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ j, ((μ j : ℂ) * (ApplyGate (U' j) (Ket p0)) p0
        - (μ j : ℂ) * (ApplyGate (U j) (Ket p0)) p0)‖
        = ‖∑ j, (μ j : ℂ) * ((ApplyGate (U' j) (Ket p0)) p0
            - (ApplyGate (U j) (Ket p0)) p0)‖ := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, ‖(μ j : ℂ) * ((ApplyGate (U' j) (Ket p0)) p0
            - (ApplyGate (U j) (Ket p0)) p0)‖ := norm_sum_le _ _
    _ = ∑ j, μ j * ‖(ApplyGate (U' j) (Ket p0)) p0
            - (ApplyGate (U j) (Ket p0)) p0‖ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul]
          simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ j)]
    _ ≤ ∑ j, μ j * δ := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hδ j) (hμ j)
    _ = δ := by
          rw [← Finset.sum_mul, hμsum, one_mul]

end Qatlib.Papers.ManifoldInv07.MainResults.Defs
