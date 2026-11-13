/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.WalkSpectralResolutionStat

/-!
# Spectral resolution of qubitized walks

This module proves the orthogonal support decomposition and spectral resolution of a reflected
walk associated with a Hermitian unitary compression. It identifies the residual basis, support
and kernel, and normalized walk eigenvectors with phases given by signed arccosines of the
compressed eigenvalues. Related mathematical background is given in [LowSu2026].

## Main statements

* `Clause12WalkSpectralResolution_answer`: The support and walk spectral identities of
  Proposition 18 and Corollary 19.

## References

* [Low and Su, 2026, Proposition 18 and Corollary 19][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
  Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The pure-state density matrix equals the outer-product matrix. -/
private theorem pureDensity_eq_outerProduct {I : Type} (ψ : QState I) :
    pureDensity ψ = outerProduct ψ := rfl

/-- Applying a pure density matrix to a vector gives the defining state scaled by its inner
product with that vector. -/
private theorem pureDensity_mulVec {I : Type} [Fintype I] (ψ φ : QState I) :
    pureDensity ψ *ᵥ φ = (Qatlib.Foundations.PureStateMath.Inner ψ φ) • ψ := by
  rw [pureDensity_eq_outerProduct, outerProduct_mulVec]

/-- The entry of a product of two pure density matrices is their defining states' inner product
times the corresponding cross outer-product entry. -/
private theorem pureDensity_mul_apply {I : Type} [Fintype I] (ψ φ : QState I) (a b : I) :
    (pureDensity ψ * pureDensity φ) a b = Qatlib.Foundations.PureStateMath.Inner ψ φ * (ψ a * star (φ b)) := by
  simp only [Matrix.mul_apply, pureDensity]
  have h : (∑ k, ψ a * star (ψ k) * (φ k * star (φ b)))
      = ψ a * star (φ b) * ∑ k, star (ψ k) * φ k := by
    calc (∑ k, ψ a * star (ψ k) * (φ k * star (φ b)))
        = ∑ k, (ψ a * star (φ b)) * (star (ψ k) * φ k) :=
          Finset.sum_congr rfl fun k _ => by ring
      _ = ψ a * star (φ b) * ∑ k, star (ψ k) * φ k :=
        (Finset.mul_sum _ _ _).symm
  rw [h]
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply]
  ring

/-- The pure density matrix of a state with self-inner-product one is idempotent. -/
private theorem pureDensity_mul_self {I : Type} [Fintype I] (ψ : QState I)
    (h : Qatlib.Foundations.PureStateMath.Inner ψ ψ = 1) : pureDensity ψ * pureDensity ψ = pureDensity ψ := by
  ext a b
  rw [pureDensity_mul_apply, h, one_mul]
  rfl

/-- The pure density matrix is fixed by the matrix star operation. -/
private theorem pureDensity_star {I : Type} (ψ : QState I) :
    star (pureDensity ψ) = pureDensity ψ := by
  ext a b
  simp only [pureDensity, Matrix.star_apply]
  rw [star_mul, star_star]

/-- Evaluating a finite sum of matrices at an entry gives the sum of the corresponding entries. -/
private theorem sum_smul_apply {ι H : Type} [Fintype ι] [Fintype H]
    (f : ι → Matrix H H ℂ) (a b : H) :
    (∑ i, f i) a b = ∑ i, f i a b := by
  rw [Matrix.sum_apply]

/-- Multiplication of a pure density matrix on the left by `M` replaces the first outer-product
factor by `M *ᵥ x`. -/
private theorem mul_pureDensity_apply {H : Type} [Fintype H]
    (M : Matrix H H ℂ) (x : QState H) (a b : H) :
    (M * pureDensity x) a b = (M *ᵥ x) a * star (x b) := by
  simp only [Matrix.mul_apply, pureDensity, Matrix.mulVec, dotProduct]
  have h : (∑ k, M a k * (x k * star (x b)))
      = (∑ k, M a k * x k) * star (x b) := by
    calc (∑ k, M a k * (x k * star (x b)))
        = ∑ k, (M a k * x k) * star (x b) :=
          Finset.sum_congr rfl fun k _ => by ring
      _ = (∑ k, M a k * x k) * star (x b) := (Finset.sum_mul _ _ _).symm
  rw [h]

/-- Two matrices are equal if they have the same action on every vector. -/
private theorem eq_of_mulVec_eq {H : Type} [Fintype H] [DecidableEq H] {A B : Matrix H H ℂ}
    (h : ∀ x : H → ℂ, A *ᵥ x = B *ᵥ x) : A = B :=
  Matrix.ext_of_mulVec_single (fun i => h (Pi.single i 1))

/-- The squared vector norm is the sum of squared coordinate norms. -/
private theorem normVec_sq {H : Type} [Fintype H] (v : H → ℂ) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  show ‖toEuclidean_fromVec v‖ ^ 2 = _
  exact norm_toEuclidean_fromVec_sq v

/-- A normalized state has vector norm one. -/
private theorem normVec_eq_one_of_normalized {I : Type} [Fintype I]
    {φ : QState I} (hφ : Normalized φ) : normVec φ = 1 := by
  have h2 : normVec φ ^ 2 = 1 := by
    rw [normVec_sq, hφ]
  have hn : 0 ≤ normVec φ := norm_nonneg _
  nlinarith

/-- An isometric matrix preserves the vector norm. -/
private theorem normVec_isometry {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I]
    {L : Matrix H I ℂ} (hL : IsIsometry L) (v : QState I) :
    normVec (L *ᵥ v) = normVec v := by
  show ‖toEuclidean_fromVec (L *ᵥ v)‖ = ‖toEuclidean_fromVec v‖
  exact isometry_mulVec_norm hL v

/-- A unitary matrix preserves the vector norm. -/
private theorem normVec_unitary {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) (v : QState H) :
    normVec (U *ᵥ v) = normVec v := by
  have hUHU : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  exact normVec_isometry (show IsIsometry U from hUHU) v

/-- The vector norm of a complex scalar multiple is the scalar norm times the vector norm. -/
private theorem normVec_smul {H : Type} [Fintype H] (c : ℂ) (v : QState H) :
    normVec (c • v) = ‖c‖ * normVec v := by
  show ‖toEuclidean_fromVec (c • v)‖ = ‖c‖ * ‖toEuclidean_fromVec v‖
  have h : toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := rfl
  rw [h, norm_smul]

/-- The pure-state inner product is complex-linear in its second argument under scalar
multiplication. -/
private theorem inner_smul_r {I : Type} [Fintype I] (c : ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (c • φ) = c * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (starRingEnd ℂ) (ψ i) * (c * φ i) = c * ((starRingEnd ℂ) (ψ i) * φ i)
  ring

/-- The pure-state inner product is conjugate-linear in its first argument under scalar
multiplication. -/
private theorem inner_smul_l {I : Type} [Fintype I] (c : ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (c • ψ) φ = star c * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (starRingEnd ℂ) (c * ψ i) * φ i = (starRingEnd ℂ) c * ((starRingEnd ℂ) (ψ i) * φ i)
  rw [map_mul]
  ring

/-- The pure-state inner product distributes over subtraction in its second argument. -/
private theorem inner_sub_r {I : Type} [Fintype I] (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (φ - χ) = Qatlib.Foundations.PureStateMath.Inner ψ φ - Qatlib.Foundations.PureStateMath.Inner ψ χ := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- The pure-state inner product distributes over subtraction in its first argument. -/
private theorem inner_sub_l {I : Type} [Fintype I] (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (ψ - φ) χ = Qatlib.Foundations.PureStateMath.Inner ψ χ - Qatlib.Foundations.PureStateMath.Inner φ χ := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply, map_sub]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Reversing the arguments of the pure-state inner product conjugates its value. -/
private theorem inner_rev' {I : Type} [Fintype I] (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner φ ψ = star (Qatlib.Foundations.PureStateMath.Inner ψ φ) :=
  (inner_conj_symm φ ψ)

/-- The norm of the pure-state inner product is at most the product of the two vector norms. -/
private theorem abs_inner_le {I : Type} [Fintype I] (ψ φ : QState I) :
    ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ ≤ normVec ψ * normVec φ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec ψ) (toEuclidean_fromVec φ)
  rwa [inner_euclidean_fromVec] at h

/-- Pure density matrices of orthogonal states multiply to zero. -/
private theorem pureDensity_mul_zero {I : Type} [Fintype I] (ψ φ : QState I)
    (h : Qatlib.Foundations.PureStateMath.Inner ψ φ = 0) : pureDensity ψ * pureDensity φ = 0 := by
  ext a b
  rw [pureDensity_mul_apply, h, zero_mul, Matrix.zero_apply]

/-- An entry of a scalar multiple of a pure density matrix is the scalar times the corresponding
outer-product entry. -/
private theorem smul_pureDensity_apply {I : Type} (c : ℂ) (x : QState I) (a b : I) :
    (c • pureDensity x) a b = c * (x a * star (x b)) := by
  simp [pureDensity, smul_eq_mul]

/-- Moving a matrix from the first argument of the pure-state inner product to the second
replaces it by its conjugate transpose. -/
private theorem inner_mulVec_adj {I O : Type} [Fintype I] [Fintype O]
    (A : Matrix O I ℂ) (u : QState I) (v : QState O) :
    Qatlib.Foundations.PureStateMath.Inner (A *ᵥ u) v = Qatlib.Foundations.PureStateMath.Inner u (Aᴴ *ᵥ v) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec,
      Matrix.dotProduct_mulVec]

/-- Applying the same unitary matrix to both states preserves their pure-state inner product. -/
private theorem inner_applyGate' {I : Type} [Fintype I] [DecidableEq I]
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (U *ᵥ ψ) (U *ᵥ φ) = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  have hUU : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hUU, Matrix.vecMul_one]

/-- The bilinear expression for a two-dimensional rotation block decomposes into the two complex
terms with factors `m + i * c` and `m - i * c`. -/
private theorem spectral_block (m c A B C D : ℂ) :
    (m * A - c * B) * C + (c * A + m * B) * D
      = (m + Complex.I * c) * ((1 : ℂ) / 2) * (A + Complex.I * B) * (C - Complex.I * D)
        + (m - Complex.I * c) * ((1 : ℂ) / 2) * (A - Complex.I * B) * (C + Complex.I * D) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ring_nf
  rw [hI]
  ring

/-- The self-inner-product of `u + v` expands into its four pairwise inner products. -/
private theorem Inner_add_add' {I : Type} [Fintype I] (u v : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (u + v) (u + v) = Qatlib.Foundations.PureStateMath.Inner u u + Qatlib.Foundations.PureStateMath.Inner u v + Qatlib.Foundations.PureStateMath.Inner v u + Qatlib.Foundations.PureStateMath.Inner v v := by
  rw [inner_apply, inner_apply, inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply, map_add, add_mul, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  module

/-- The pure-state inner product distributes over addition in its second argument. -/
private theorem inner_add_r {I : Type} [Fintype I] (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (φ + χ) = Qatlib.Foundations.PureStateMath.Inner ψ φ + Qatlib.Foundations.PureStateMath.Inner ψ χ := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply]
  conv_lhs => rw [Finset.sum_congr rfl (fun k _ => by
    show (starRingEnd ℂ) (ψ k) * (φ k + χ k) = _
    rw [mul_add])]
  rw [Finset.sum_add_distrib]

/-- Complex conjugation fixes the complex cast of a real number. -/
private theorem star_ofReal_cast (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.conj_ofReal]

/-- A state with zero self-inner-product is the zero state. -/
private theorem inner_self_eq_zero {I : Type} [Fintype I] {ψ : QState I}
    (h : Qatlib.Foundations.PureStateMath.Inner ψ ψ = 0) : ψ = 0 := by
  have hs : (∑ i, (‖ψ i‖ ^ 2 : ℝ)) = 0 := by
    have h1 : ((∑ i, (‖ψ i‖ ^ 2 : ℝ) : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum, ← inner_self ψ, h]
    exact_mod_cast h1
  have h2 : ∀ i : I, ‖ψ i‖ ^ 2 = 0 :=
    fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hs i (Finset.mem_univ i)
  funext i
  have h3 : ‖ψ i‖ = 0 := sq_eq_zero_iff.mp (h2 i)
  exact norm_eq_zero.mp h3

/-- The pure-state inner product distributes over addition in its first argument. -/
private theorem inner_add_l {I : Type} [Fintype I] (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (φ + χ) ψ = Qatlib.Foundations.PureStateMath.Inner φ ψ + Qatlib.Foundations.PureStateMath.Inner χ ψ := by
  rw [inner_rev', inner_add_r, star_add, ← inner_rev', ← inner_rev']

/-- The sum of the pure densities of the columns of `S` is `S * Sᴴ`. -/
private theorem sum_pureDensity_S_cols {I : Type} [Fintype I] (S : Matrix I I ℂ) :
    ∑ i, pureDensity (fun j => S j i) = S * Sᴴ := by
  ext a b
  rw [sum_smul_apply, Matrix.mul_apply]
  simp only [pureDensity, Matrix.conjTranspose_apply]

/-- The pure density of `G *ᵥ w` is `G * pureDensity w * Gᴴ`. -/
private theorem pureDensity_mulVec_eq {H I : Type} [Fintype H] [Fintype I]
    (G : Matrix H I ℂ) (w : QState I) :
    pureDensity (G *ᵥ w) = G * pureDensity w * Gᴴ := by
  ext a b
  simp only [pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hL : (G *ᵥ w) a = ∑ k, G a k * w k := by
    simp only [Matrix.mulVec, dotProduct]
  have hR : (G *ᵥ w) b = ∑ l, G b l * w l := by
    simp only [Matrix.mulVec, dotProduct]
  rw [hL, hR]
  have hstar : star (∑ l, G b l * w l) = ∑ l, star (G b l) * star (w l) := by
    rw [show star (∑ l, G b l * w l) = (starRingEnd ℂ) (∑ l, G b l * w l) from rfl,
      map_sum (starRingEnd ℂ : ℂ →+* ℂ)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  rw [hstar]
  have hRS : (∑ l, (∑ k, G a k * (w k * star (w l))) * star (G b l))
      = ∑ k, ∑ l, G a k * w k * star (w l) * star (G b l) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hRS, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => by ring

/-- If `S * Sᴴ = 1`, the matrix `G * Gᴴ` is the sum of the pure densities of `G` applied to the
columns of `S`. -/
private theorem gg_eq_sum_pureDensity {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I]
    (G : Matrix H I ℂ) (S : Matrix I I ℂ) (hSS : S * Sᴴ = 1) :
    G * Gᴴ = ∑ i, pureDensity (G *ᵥ (fun j => S j i)) := by
  have h1 : ∀ i : I, pureDensity (G *ᵥ (fun j => S j i))
      = G * pureDensity (fun j => S j i) * Gᴴ := fun i => pureDensity_mulVec_eq G _
  calc G * Gᴴ = G * (S * Sᴴ) * Gᴴ := by rw [hSS, Matrix.mul_one]
    _ = G * (∑ i, pureDensity (fun j => S j i)) * Gᴴ := by rw [sum_pureDensity_S_cols]
    _ = (∑ i, G * pureDensity (fun j => S j i)) * Gᴴ := by
      rw [Matrix.mul_sum]
    _ = ∑ i, G * pureDensity (fun j => S j i) * Gᴴ := by
      rw [Matrix.sum_mul]
    _ = ∑ i, pureDensity (G *ᵥ (fun j => S j i)) := Finset.sum_congr rfl fun i _ => (h1 i).symm

/-- The qubitized walk satisfies the stated orthogonality, support-projector, residual-basis,
and spectral-resolution identities, with eigenphases given by signed arccosines of the
compressed eigenvalues. See [Low and Su, Proposition 18 and Corollary 19][LowSu2026]. -/
theorem Clause12WalkSpectralResolution_answer : Clause12WalkSpectralResolution := by
  intro H I _fH _dH _fI _dI U G S lam hU hGiso hS hU2 hUG v e T
  have hUU : U * Uᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUHU : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hSS : S * Sᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hS
    rwa [Matrix.star_eq_conjTranspose] at h
  have hSHS : Sᴴ * S = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hS
    rwa [Matrix.star_eq_conjTranspose] at h
  have hGG : Gᴴ * G = 1 := hGiso

  have hs_inner : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) (fun k => S k j)
      = (Sᴴ * S : Matrix I I ℂ) i j := by
    intro i j
    show (star (fun k => S k i)) ⬝ᵥ (fun k => S k j) = _
    simp only [dotProduct, Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def]
  have hs_orth : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) (fun k => S k j)
      = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [hs_inner, hSHS, Matrix.one_apply]
  have hs_norm : ∀ i : I, Normalized (fun k => S k i) := by
    intro i
    rw [normalized_iff_inner_self, hs_orth i i, ite_eq_left rfl]

  have hv_eq : ∀ i : I, v i = G *ᵥ (fun k => S k i) := fun i => rfl
  have hv_inner : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (v i) (v j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [hv_eq i, hv_eq j,
        (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.inner_mulVec hGiso), hs_orth]
  have hv_norm : ∀ i : I, Normalized (v i) := by
    intro i
    exact (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.normalized_mulVec hGiso)
        (hs_norm i)
  have hv_self : ∀ i : I, Qatlib.Foundations.PureStateMath.Inner (v i) (v i) = 1 := by
    intro i
    rw [hv_inner i i, ite_eq_left rfl]

  have hGUv : ∀ j : I, Gᴴ *ᵥ (U *ᵥ v j) = (lam j : ℂ) • (fun k => S k j) := by
    intro j
    have hkey : Gᴴ *ᵥ (U *ᵥ (G *ᵥ (fun k => S k j)))
        = (Gᴴ * U * G) *ᵥ (fun k => S k j) := by
      conv_lhs => rw [Matrix.mulVec_mulVec]
      conv_lhs => rw [Matrix.mulVec_mulVec]
    have hSadj : (Sᴴ : Matrix I I ℂ) *ᵥ (fun k => S k j) = (Pi.single j (1 : ℂ) : I → ℂ) := by
      have h : (fun k => S k j) = (S : Matrix I I ℂ) *ᵥ (Pi.single j (1 : ℂ) : I → ℂ) := by
        rw [Matrix.mulVec_single_one]; rfl
      conv_lhs => rw [h]
      rw [Matrix.mulVec_mulVec, hSHS, Matrix.one_mulVec]
    have hdiag : (Matrix.diagonal (fun i => (lam i : ℂ)) : Matrix I I ℂ)
        *ᵥ (Pi.single j (1 : ℂ) : I → ℂ) = (lam j : ℂ) • (Pi.single j (1 : ℂ) : I → ℂ) := by
      rw [Matrix.diagonal_mulVec_single, mul_one]
      funext a
      simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    have hSv : (S : Matrix I I ℂ) *ᵥ (Pi.single j (1 : ℂ) : I → ℂ) = fun k => S k j := by
      rw [Matrix.mulVec_single_one]; rfl
    conv_lhs => rw [hv_eq j, hkey, hUG]

    conv_lhs => rw [← Matrix.mulVec_mulVec]
    conv_lhs => rw [← Matrix.mulVec_mulVec]
    rw [hSadj, hdiag, Matrix.mulVec_smul, hSv]
  have hGv : ∀ j : I, Gᴴ *ᵥ v j = fun k => S k j := by
    intro j
    conv_lhs => rw [hv_eq j, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]

  have hU2unit : (U ^ 2)ᴴ * U ^ 2 = 1 := by
    have h : U ^ 2 ∈ Matrix.unitaryGroup H ℂ := (Matrix.unitaryGroup H ℂ).pow_mem hU 2
    have := (Matrix.mem_unitaryGroup_iff').mp h
    rwa [Matrix.star_eq_conjTranspose] at this
  have hU2G : (U ^ 2) * G = G := by
    have hexp : ((U ^ 2 * G - G : Matrix H I ℂ)ᴴ * (U ^ 2 * G - G) : Matrix I I ℂ) = 0 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_sub]
      have a1 : (Gᴴ * (U ^ 2)ᴴ) * (U ^ 2 * G) = 1 := by
        conv_lhs => rw [Matrix.mul_assoc, ← Matrix.mul_assoc (U ^ 2)ᴴ (U ^ 2) G,
          hU2unit, Matrix.one_mul]
        exact hGG
      have a2 : (Gᴴ * (U ^ 2)ᴴ) * G = 1 := by
        have h2eq : (Gᴴ * (U ^ 2)ᴴ) * G = Matrix.conjTranspose (Gᴴ * (U ^ 2) * G) := by
          conv_rhs => rw [Matrix.mul_assoc]
          conv_rhs => rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
        rw [h2eq, hU2, Matrix.conjTranspose_one]
      have a3 : Gᴴ * (U ^ 2 * G) = 1 := by
        conv_lhs => rw [← Matrix.mul_assoc]
        exact hU2
      rw [a1, a2, a3, hGG]
      norm_num
    exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp hexp)
  have hU2v : ∀ i : I, U *ᵥ (U *ᵥ v i) = v i := by
    intro i
    have heq : (U ^ 2) *ᵥ (v i) = v i := by
      conv_lhs => rw [hv_eq i, Matrix.mulVec_mulVec, hU2G]
    calc U *ᵥ (U *ᵥ v i) = (U * U) *ᵥ v i := by rw [← Matrix.mulVec_mulVec]
      _ = (U ^ 2) *ᵥ v i := by rw [pow_two]
      _ = v i := heq
  have hUHv : ∀ i : I, Uᴴ *ᵥ v i = U *ᵥ v i := by
    intro i
    have h1 : Uᴴ *ᵥ (U *ᵥ (U *ᵥ v i)) = U *ᵥ v i := by
      conv_lhs => rw [Matrix.mulVec_mulVec]
      rw [hUHU, Matrix.one_mulVec]
    calc Uᴴ *ᵥ v i = Uᴴ *ᵥ (U *ᵥ (U *ᵥ v i)) := by rw [hU2v i]
      _ = U *ᵥ v i := h1
  have hGGv : ∀ i : I, (G * Gᴴ) *ᵥ v i = v i := by
    intro i
    conv_lhs => rw [hv_eq i]
    conv_lhs => rw [← Matrix.mulVec_mulVec]
    conv_lhs => rw [hGv]
  have hGGw : ∀ i : I, (G * Gᴴ) *ᵥ (U *ᵥ v i) = (lam i : ℂ) • v i := by
    intro i
    conv_lhs => rw [← Matrix.mulVec_mulVec]
    conv_lhs => rw [hGUv]
    rw [Matrix.mulVec_smul, hv_eq i]

  have hlam_eq : ∀ i : I, (lam i : ℂ) = Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i) := by
    intro i
    have hkey : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i) = Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) (Gᴴ *ᵥ (U *ᵥ v i)) := by
      conv_lhs => rw [hv_eq i]
      rw [inner_mulVec_adj]
    rw [hkey, hGUv, inner_smul_r, hs_orth i i, ite_eq_left rfl, mul_one]
  have hlam_le : ∀ i : I, |lam i| ≤ 1 := by
    intro i
    have hcs : ‖Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i)‖ ≤ normVec (v i) * normVec (U *ᵥ v i) :=
      abs_inner_le (v i) (U *ᵥ v i)
    have hnv : normVec (v i) = 1 := normVec_eq_one_of_normalized (hv_norm i)
    have hnu : normVec (U *ᵥ v i) = normVec (v i) := normVec_unitary hU _
    rw [hnv, hnu, hnv, mul_one] at hcs
    have hcast : ‖((lam i : ℂ) : ℂ)‖ = |lam i| := by simp
    rw [← hlam_eq i, hcast] at hcs
    exact hcs
  have hneg1 : ∀ i : I, -1 ≤ lam i := by
    intro i
    have h := abs_le.mp (hlam_le i)
    exact h.1
  have hpos1 : ∀ i : I, lam i ≤ 1 := by
    intro i
    have h := abs_le.mp (hlam_le i)
    exact h.2
  have habs : ∀ i : I, abs (lam i) = |lam i| := fun i => rfl

  have hvU : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v j) = (lam j : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    intro i j
    have hkey : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v j) = Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) (Gᴴ *ᵥ (U *ᵥ v j)) := by
      conv_lhs => rw [hv_eq i]
      rw [inner_mulVec_adj]
    rw [hkey, hGUv, inner_smul_r, hs_orth]
  have hUv : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v j) = (lam i : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    intro i j
    have h := hvU j i
    have hrev :
        Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v j) = star
        (Qatlib.Foundations.PureStateMath.Inner (v j) (U *ᵥ v i)) := inner_rev' _ _
    rw [hrev, h]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hUU_in : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (U *ᵥ v j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [inner_applyGate' hU, hv_inner]

  have he_eq : ∀ i : I,
      e i = (Real.sqrt (1 - (lam i) ^ 2) : ℂ)⁻¹ • (U *ᵥ v i - (lam i : ℂ) • v i) := fun i => rfl
  have hs_nonneg : ∀ i : I, 0 ≤ Real.sqrt (1 - (lam i) ^ 2) := fun i => Real.sqrt_nonneg _
  have hs_sq : ∀ i : I, (Real.sqrt (1 - (lam i) ^ 2) : ℝ) ^ 2 = 1 - (lam i) ^ 2 := by
    intro i
    rw [Real.sq_sqrt]
    have h2 := abs_le.mp (hlam_le i)
    nlinarith [sq_nonneg (lam i)]

  have hlam_eq : ∀ i : I, (lam i : ℂ) = Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i) := by
    intro i
    have hkey : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i) = Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) (Gᴴ *ᵥ (U *ᵥ v i)) := by
      conv_lhs => rw [hv_eq i]
      rw [inner_mulVec_adj]
    rw [hkey, hGUv, inner_smul_r, hs_orth i i, ite_eq_left rfl, mul_one]
  have hlam_le : ∀ i : I, |lam i| ≤ 1 := by
    intro i
    have hcs : ‖Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i)‖ ≤ normVec (v i) * normVec (U *ᵥ v i) :=
      abs_inner_le (v i) (U *ᵥ v i)
    have hnv : normVec (v i) = 1 := normVec_eq_one_of_normalized (hv_norm i)
    have hnu : normVec (U *ᵥ v i) = normVec (v i) := normVec_unitary hU _
    rw [hnv, hnu, hnv, mul_one] at hcs
    have hcast : ‖((lam i : ℂ) : ℂ)‖ = |lam i| := by simp
    rw [← hlam_eq i, hcast] at hcs
    exact hcs
  have hneg1 : ∀ i : I, -1 ≤ lam i := by
    intro i
    have h := abs_le.mp (hlam_le i)
    exact h.1
  have hpos1 : ∀ i : I, lam i ≤ 1 := by
    intro i
    have h := abs_le.mp (hlam_le i)
    exact h.2
  have habs : ∀ i : I, abs (lam i) = |lam i| := fun i => rfl

  have hvU : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v j) = (lam j : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    intro i j
    have hkey : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v j) = Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) (Gᴴ *ᵥ (U *ᵥ v j)) := by
      conv_lhs => rw [hv_eq i]
      rw [inner_mulVec_adj]
    rw [hkey, hGUv, inner_smul_r, hs_orth]
  have hUv : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v j) = (lam i : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    intro i j
    have h := hvU j i
    have hrev :
        Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v j) = star
        (Qatlib.Foundations.PureStateMath.Inner (v j) (U *ᵥ v i)) := inner_rev' _ _
    rw [hrev, h]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hUU_in : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (U *ᵥ v j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [inner_applyGate' hU, hv_inner]

  have he_eq : ∀ i : I,
      e i = (Real.sqrt (1 - (lam i) ^ 2) : ℂ)⁻¹ • (U *ᵥ v i - (lam i : ℂ) • v i) := fun i => rfl
  have hs_nonneg : ∀ i : I, 0 ≤ Real.sqrt (1 - (lam i) ^ 2) := fun i => Real.sqrt_nonneg _
  have hs_sq : ∀ i : I, (Real.sqrt (1 - (lam i) ^ 2) : ℝ) ^ 2 = 1 - (lam i) ^ 2 := by
    intro i
    rw [Real.sq_sqrt]
    have h2 := abs_le.mp (hlam_le i)
    nlinarith [sq_nonneg (lam i)]

  have he_zero : ∀ i : I, abs (lam i) < 1 → e i = (Real.sqrt (1 - (lam i) ^ 2) : ℂ)⁻¹
      • (U *ᵥ v i - (lam i : ℂ) • v i) := fun i _ => he_eq i
  have he_zero_of_ge : ∀ i : I, ¬ (abs (lam i) < 1) → e i = 0 := by
    intro i hni
    rw [he_eq i]
    have hc : Real.sqrt (1 - (lam i) ^ 2) = 0 := by
      have h1 : 1 ≤ |lam i| := le_of_not_gt hni
      have h2 : |lam i| ≤ 1 := hlam_le i
      have h3 : |lam i| = 1 := le_antisymm h2 h1
      have h4 : (lam i) ^ 2 = 1 := by
        have := abs_mul_abs_self (lam i)
        rw [h3] at this
        nlinarith
      have h5 : (1 : ℝ) - (lam i) ^ 2 = 0 := by nlinarith
      rw [h5]
      exact Real.sqrt_zero
    rw [hc]
    simp
  have hUv1 : ∀ i : I, abs (lam i) < 1 →
      U *ᵥ v i = (lam i : ℂ) • v i + (Real.sqrt (1 - (lam i) ^ 2) : ℂ) • e i := by
    intro i hlt
    have hs0 : (0 : ℝ) < Real.sqrt (1 - (lam i) ^ 2) := by
      apply Real.sqrt_pos.mpr
      have h2 := abs_lt.mp hlt
      nlinarith [sq_nonneg (lam i)]
    have hsne : (Real.sqrt (1 - (lam i) ^ 2) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hs0)
    conv_rhs => rw [he_eq i]
    rw [smul_smul, mul_inv_cancel₀ hsne, one_smul]
    module
  have hUe1 : ∀ i : I, abs (lam i) < 1 →
      U *ᵥ e i = (Real.sqrt (1 - (lam i) ^ 2) : ℂ) • v i - (lam i : ℂ) • e i := by
    intro i hlt
    have hs0 : (0 : ℝ) < Real.sqrt (1 - (lam i) ^ 2) := by
      apply Real.sqrt_pos.mpr
      have h2 := abs_lt.mp hlt
      nlinarith [sq_nonneg (lam i)]
    have hsne : (Real.sqrt (1 - (lam i) ^ 2) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hs0)
    have hsne0 : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hs0)
    have hsreal : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) * (Real.sqrt (1 - (lam i) ^ 2) : ℝ)
        = 1 - (lam i) ^ 2 := by
      have := hs_sq i
      nlinarith [sq_nonneg (lam i)]
    set s : ℂ := ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) with hsdef
    have hUv1i : U *ᵥ v i = (lam i : ℂ) • v i + s • e i := by
      rw [hsdef]
      exact hUv1 i hlt
    conv_lhs => rw [he_eq i]
    conv_lhs => rw [Matrix.mulVec_smul]
    have hU2w : U *ᵥ (U *ᵥ v i - (lam i : ℂ) • v i)
        = v i - (lam i : ℂ) • (U *ᵥ v i) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hU2v]
    rw [hU2w, hUv1i]
    have hcalc : v i - (lam i : ℂ) • ((lam i : ℂ) • v i + s • e i)
        = ((1 : ℂ) - (lam i : ℂ) * (lam i : ℂ)) • v i
          - ((lam i : ℂ) * s) • e i := by
      simp only [smul_add]
      module
    rw [hcalc]
    rw [smul_sub, ← mul_smul, ← mul_smul]
    have h1 : s⁻¹ * ((1 : ℂ) - (lam i : ℂ) * (lam i : ℂ)) = s := by
      have h1a : ((1 : ℂ) - (lam i : ℂ) * (lam i : ℂ))
          = ((1 - (lam i) ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
        ring
      rw [h1a, hsdef]
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
      simp only [Complex.ofReal_inj]
      have h1b : (Real.sqrt (1 - (lam i) ^ 2) : ℝ)⁻¹ * (1 - (lam i) ^ 2)
          = Real.sqrt (1 - (lam i) ^ 2) := by
        field_simp [hsne0]
        nlinarith [sq_nonneg (lam i)]
      exact h1b
    have h2 : s⁻¹ * ((lam i : ℂ) * s) = (lam i : ℂ) := by
      rw [hsdef]
      field_simp [hsne]
    rw [h1, h2]
  have hGGe1 : ∀ i : I, (G * Gᴴ) *ᵥ e i = 0 := by
    intro i
    by_cases hlt : abs (lam i) < 1
    · conv_lhs => rw [he_eq i, Matrix.mulVec_smul]
      have hkey : (G * Gᴴ) *ᵥ (U *ᵥ v i - (lam i : ℂ) • v i) = 0 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hGGw, hGGv]
        module
      rw [hkey, smul_zero]
    · rw [he_zero_of_ge i hlt]
      simp
  have hIve : ∀ i : I, Qatlib.Foundations.PureStateMath.Inner (v i) (e i) = 0 := by
    intro i
    by_cases hlt : abs (lam i) < 1
    · conv_lhs => rw [he_eq i, inner_smul_r]
      have hkey : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i - (lam i : ℂ) • v i) = 0 := by
        rw [inner_sub_r, inner_smul_r, hlam_eq i, hv_self]
        ring
      rw [hkey, mul_zero]
    · rw [he_zero_of_ge i hlt, inner_apply]
      simp
  have hNorm : ∀ i : I, abs (lam i) < 1 → Normalized (e i) := by
    intro i hlt
    rw [normalized_iff_inner_self]
    have hsne0 : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) ≠ 0 := by
      have hs0 : (0 : ℝ) < Real.sqrt (1 - (lam i) ^ 2) := by
        apply Real.sqrt_pos.mpr
        have h2 := abs_lt.mp hlt
        nlinarith [sq_nonneg (lam i)]
      exact_mod_cast (ne_of_gt hs0)
    have hsreal : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) * (Real.sqrt (1 - (lam i) ^ 2) : ℝ)
        = 1 - (lam i) ^ 2 := by
      have := hs_sq i
      nlinarith [sq_nonneg (lam i)]
    conv_lhs => rw [he_eq i, inner_smul_l, inner_smul_r]
    have hkey : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i - (lam i : ℂ) • v i) (U *ᵥ v i - (lam i : ℂ) • v i)
        = ((1 - (lam i) ^ 2 : ℝ) : ℂ) := by
      simp only [inner_sub_l, inner_sub_r, inner_smul_r, inner_smul_l]
      rw [hUU_in i i, ite_eq_left rfl, hUv i i, ite_eq_left rfl, hvU i i, ite_eq_left rfl, hv_self]
      simp only [star_ofReal_cast]
      push_cast
      ring
    rw [hkey]
    have hsC : ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsne0
    have hstar : star (((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ)⁻¹)
        = (((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ)⁻¹) := by
      rw [RCLike.star_def, Complex.conj_inv, Complex.conj_ofReal]
    rw [hstar]
    field_simp [hsC]
    push_cast
    have h : (1 - (lam i) ^ 2 : ℝ) = Real.sqrt (1 - (lam i) ^ 2) ^ 2 :=
      hsreal.symm.trans (pow_two _).symm
    exact_mod_cast h
  have hres : ∀ i : I, abs (lam i) < 1 →
      U *ᵥ v i = (lam i : ℂ) • v i + (Real.sqrt (1 - (lam i) ^ 2) : ℂ) • e i ∧
      U *ᵥ e i = (Real.sqrt (1 - (lam i) ^ 2) : ℂ) • v i - (lam i : ℂ) • e i ∧
      (G * Gᴴ) *ᵥ e i = 0 ∧
      Qatlib.Foundations.PureStateMath.Inner (v i) (e i) = 0 ∧ Normalized (e i) := by
    intro i hlt
    exact ⟨hUv1 i hlt, hUe1 i hlt, hGGe1 i, hIve i, hNorm i hlt⟩

  have hwalk : ∀ i : I, abs (lam i) < 1 → ∀ neg : Bool,
      Normalized (walkBranch U (v i) (lam i) neg) ∧
      walk G U *ᵥ walkBranch U (v i) (lam i) neg =
        Complex.exp (Complex.I * (if neg then -Real.arccos (lam i) else Real.arccos (lam i))) •
          walkBranch U (v i) (lam i) neg := by
    intro i hlt neg
    have hNormX : Normalized (e i) := hNorm i hlt
    have hNorm'' := hNormX

    have hNormWB : Normalized (walkBranch U (v i) (lam i) neg) := by
      have hNorm' : Qatlib.Foundations.PureStateMath.Inner (e i) (e i) = 1 :=
          (normalized_iff_inner_self _).1 hNorm''
      have hcross : Qatlib.Foundations.PureStateMath.Inner (v i) (e i) = 0 := hIve i
      have hcross' : Qatlib.Foundations.PureStateMath.Inner (e i) (v i) = 0 := by
        rw [inner_rev', hcross]
        simp
      have hkey : ∀ (t : ℂ), Qatlib.Foundations.PureStateMath.Inner (v i + t • e i) (v i + t • e i) = 1 + star t * t := by
        intro t
        rw [Inner_add_add']
        simp only [inner_smul_r, inner_smul_l]
        rw [hv_self, hNorm', hcross, hcross']
        simp only [mul_zero, add_zero]
        ring
      rw [show walkBranch U (v i) (lam i) neg = (Real.sqrt 2 : ℂ)⁻¹ • (v i + (if neg then -Complex.I else Complex.I) • e i) from rfl, normalized_iff_inner_self]
      rw [inner_smul_l, inner_smul_r]
      have hif : (if neg then -Complex.I else Complex.I) = (if neg = true then -Complex.I else Complex.I) := by
        cases neg <;> simp
      rw [hif]
      by_cases hneg : neg = true
      · rw [ite_eq_left hneg, hkey]
        have h1 : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
          rw [RCLike.star_def, Complex.conj_inv, Complex.conj_ofReal]
        rw [h1]
        have h2 : star (-Complex.I : ℂ) = Complex.I := by
          rw [RCLike.star_def, map_neg, Complex.conj_I]
          simp
        rw [h2]
        have h3 : (1 + Complex.I * (-Complex.I) : ℂ) = 2 := by
          rw [mul_neg, Complex.I_mul_I]
          ring
        rw [h3]
        have h4 : ((Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ * 2) : ℂ) = 1 := by
          have h5 : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = 2 :=
            Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
          have h6 : ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) = ((2 : ℝ) : ℂ) := by
            rw [← Complex.ofReal_mul, h5]
          have h7 : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ : ℂ)
              = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ := by
            rw [_root_.mul_inv_rev]
          rw [← mul_assoc, h7, h6]
          push_cast
          field_simp
        exact h4
      · rw [ite_eq_right hneg, hkey]
        have h1 : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
          rw [RCLike.star_def, Complex.conj_inv, Complex.conj_ofReal]
        rw [h1]
        have h2 : star (Complex.I : ℂ) = -Complex.I := by
          rw [RCLike.star_def, Complex.conj_I]
        rw [h2]
        have h3 : (1 + (-Complex.I) * Complex.I : ℂ) = 2 := by
          rw [neg_mul, Complex.I_mul_I]
          ring
        rw [h3]
        have h4 : ((Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ * 2) : ℂ) = 1 := by
          have h5 : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = 2 :=
            Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
          have h6 : ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) = ((2 : ℝ) : ℂ) := by
            rw [← Complex.ofReal_mul, h5]
          have h7 : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ : ℂ)
              = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ := by
            rw [_root_.mul_inv_rev]
          rw [← mul_assoc, h7, h6]
          push_cast
          field_simp
        exact h4

    have hEigen : walk G U *ᵥ walkBranch U (v i) (lam i) neg
        = Complex.exp (Complex.I * (if neg then -Real.arccos (lam i) else Real.arccos (lam i))) •
            walkBranch U (v i) (lam i) neg := by
      rw [show walkBranch U (v i) (lam i) neg = (Real.sqrt 2 : ℂ)⁻¹ • (v i + (if neg then -Complex.I else Complex.I) • e i) from rfl, Matrix.mulVec_smul]
      have hwalkv : walk G U *ᵥ v i = (lam i : ℂ) • v i - ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) • e i := by
        rw [show walk G U = ((2 • (G * Gᴴ) - 1) * U : Matrix H H ℂ) from rfl]
        rw [← Matrix.mulVec_mulVec, hUv1 i hlt]
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        have hD : (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) *ᵥ v i = v i := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hGGv i, Matrix.one_mulVec]
          module
        have hE : (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) *ᵥ e i = - e i := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hGGe1 i, Matrix.one_mulVec]
          module
        rw [hD, hE]
        module
      have hwalke : walk G U *ᵥ e i = ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) • v i + (lam i : ℂ) • e i := by
        rw [show walk G U = ((2 • (G * Gᴴ) - 1) * U : Matrix H H ℂ) from rfl]
        rw [← Matrix.mulVec_mulVec, hUe1 i hlt]
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
        have hD : (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) *ᵥ v i = v i := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hGGv i, Matrix.one_mulVec]
          module
        have hE : (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) *ᵥ e i = - e i := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hGGe1 i, Matrix.one_mulVec]
          module
        rw [hD, hE]
        module
      cases neg with
      | false =>
        rw [ite_eq_right (by simp : ¬ (false = true)), ite_eq_right (by simp : ¬ (false = true))]
        have hcore : walk G U *ᵥ (v i + Complex.I • e i)
            = Complex.exp (Complex.I * (Real.arccos (lam i) : ℂ)) • (v i + Complex.I • e i) := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, hwalkv, hwalke]
          have hexp : Complex.exp (Complex.I * (Real.arccos (lam i) : ℂ))
              = (lam i : ℂ) + Complex.I * ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) := by
            have h2 : (Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ) : ℂ)
                = ((Real.arccos (lam i) : ℝ) : ℂ) * Complex.I := by ring
            rw [h2]
            have h1 : Complex.exp (((Real.arccos (lam i) : ℝ) : ℂ) * Complex.I)
                = ((Real.cos (Real.arccos (lam i)) : ℝ) : ℂ)
                    + ((Real.sin (Real.arccos (lam i)) : ℝ) : ℂ) * Complex.I :=
              Complex.exp_ofReal_mul_I _
            rw [h1, Real.cos_arccos (hneg1 i) (hpos1 i), Real.sin_arccos]
            have hsreal2 : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) = (Real.sqrt (1 - (lam i) ^ 2) : ℝ) :=
                rfl
            rw [hsreal2]
            ring
          rw [hexp]
          simp only [smul_add, smul_smul]
          have hI : ((↑(lam i) + Complex.I * ↑(Real.sqrt (1 - (lam i) ^ 2))) * Complex.I : ℂ)
              = -(((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ)) + Complex.I * ((lam i : ℂ)) := by
            rw [add_mul]
            ring_nf
            rw [show (Complex.I ^ 2 : ℂ) = -1 by rw [pow_two, Complex.I_mul_I]]
            ring
          rw [hI]
          module
        rw [hcore]
        module
      | true =>
        rw [ite_eq_left (by simp : (true = true)), ite_eq_left (by simp : (true = true))]
        have hcore : walk G U *ᵥ (v i + (-Complex.I) • e i)
            = Complex.exp (Complex.I * (-((Real.arccos (lam i) : ℝ) : ℂ)))
                • (v i + (-Complex.I) • e i) := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, hwalkv, hwalke]
          have hexp : Complex.exp (Complex.I * (-((Real.arccos (lam i) : ℝ) : ℂ)))
              = (lam i : ℂ) - Complex.I * ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) := by
            have h2 : (Complex.I * (-((Real.arccos (lam i) : ℝ) : ℂ)) : ℂ)
                = ((-Real.arccos (lam i) : ℝ) : ℂ) * Complex.I := by
              rw [Complex.ofReal_neg]
              ring
            rw [h2]
            have h1 : Complex.exp (((-Real.arccos (lam i) : ℝ) : ℂ) * Complex.I)
                = ((Real.cos (-Real.arccos (lam i)) : ℝ) : ℂ)
                    + ((Real.sin (-Real.arccos (lam i)) : ℝ) : ℂ) * Complex.I :=
              Complex.exp_ofReal_mul_I _
            rw [h1, Real.cos_neg, Real.cos_arccos (hneg1 i) (hpos1 i), Real.sin_neg,
                Real.sin_arccos]
            have hsreal2 : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) = (Real.sqrt (1 - (lam i) ^ 2) : ℝ) :=
                rfl
            rw [hsreal2, Complex.ofReal_neg]
            ring
          rw [hexp]
          simp only [smul_add, smul_smul]
          have hI : ((↑(lam i) - Complex.I * ↑(Real.sqrt (1 - (lam i) ^ 2))) * -Complex.I : ℂ)
              = -(((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ)) - Complex.I * ((lam i : ℂ)) := by
            rw [mul_neg, sub_mul]
            ring_nf
            rw [show (Complex.I ^ 2 : ℂ) = -1 by rw [pow_two, Complex.I_mul_I]]
            ring
          rw [hI]
          module
        rw [hcore]
        module
    exact ⟨hNormWB, hEigen⟩
  have hT_eq : T = ∑ i, (pureDensity (v i) + (if abs (lam i) < 1 then pureDensity (e i) else 0)) := by
    show walkSupport U G S lam = _
    simp only [walkSupport]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hv_eq, he_eq, residual]
  have hT_mulVec : ∀ x : QState H,
      T *ᵥ x = ∑ i, (Qatlib.Foundations.PureStateMath.Inner (v i) x • v i
        + (if abs (lam i) < 1 then Qatlib.Foundations.PureStateMath.Inner (e i) x • e i else 0)) := by
    intro x
    rw [hT_eq]
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.add_mulVec]
    by_cases hlt : abs (lam i) < 1
    · simp only [ite_eq_left hlt, pureDensity_mulVec]
    · simp only [ite_eq_right hlt, pureDensity_mulVec, Matrix.zero_mulVec, add_zero]

  have he_cross : ∀ i j : I, i ≠ j → Qatlib.Foundations.PureStateMath.Inner (e i) (e j) = 0 := by
    intro i j hij
    by_cases hlti : abs (lam i) < 1
    · by_cases hltj : abs (lam j) < 1
      · rw [he_zero i hlti, he_zero j hltj, inner_smul_l, inner_smul_r]
        have hkey : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i - (lam i : ℂ) • v i)
            (U *ᵥ v j - (lam j : ℂ) • v j) = 0 := by
          simp only [inner_sub_l, inner_sub_r, inner_smul_r, inner_smul_l]
          rw [hUU_in i j, ite_eq_right hij, hUv i j, ite_eq_right hij, hvU i j, ite_eq_right hij,
            hv_inner i j, ite_eq_right hij]
          simp
        rw [hkey]
        ring
      · rw [he_zero_of_ge j hltj, inner_apply]
        simp
    · rw [he_zero_of_ge i hlti, inner_apply]
      simp
  have he_norm : ∀ i : I, abs (lam i) < 1 → Qatlib.Foundations.PureStateMath.Inner (e i) (e i) = 1 := by
    intro i hlt
    exact (normalized_iff_inner_self _).1 (hres i hlt).2.2.2.2
  have he_inner : ∀ i j : I,
      Qatlib.Foundations.PureStateMath.Inner (e i) (e j) = if i = j then (if abs (lam i) < 1 then (1:ℂ) else 0) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      by_cases hlt : abs (lam i) < 1
      · rw [ite_eq_left hlt, he_norm i hlt]
      · rw [ite_eq_right hlt, he_zero_of_ge i hlt, inner_apply]
        simp
    · rw [ite_eq_right hij, he_cross i j hij]
  have he_ve : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (v i) (e j) = 0 := by
    intro i j
    by_cases hlt : abs (lam j) < 1
    · rw [he_zero j hlt, inner_smul_r]
      have hkey : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v j - (lam j : ℂ) • v j) = 0 := by
        simp only [inner_sub_r, inner_smul_r]
        rw [hvU i j, hv_inner i j]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]
      rw [hkey, mul_zero]
    · rw [he_zero_of_ge j hlt, inner_apply]
      simp
  have he_ve' : ∀ i j : I, Qatlib.Foundations.PureStateMath.Inner (e i) (v j) = 0 := by
    intro i j
    rw [inner_rev', he_ve j i]
    simp
  have hTv : ∀ i : I, T *ᵥ v i = v i := by
    intro i
    rw [hT_mulVec]
    rw [Finset.sum_eq_single i]
    · rw [hv_self]
      by_cases hlt : abs (lam i) < 1
      · rw [ite_eq_left hlt, he_ve' i i]
        module
      · rw [ite_eq_right hlt]
        module
    · intro b _ hb
      rw [hv_inner b i, ite_eq_right hb]
      by_cases hlt : abs (lam b) < 1
      · rw [ite_eq_left hlt, he_ve' b i]
        module
      · rw [ite_eq_right hlt]
        module
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hTe : ∀ i : I, abs (lam i) < 1 → T *ᵥ e i = e i := by
    intro i hlt
    rw [hT_mulVec]
    rw [Finset.sum_eq_single i]
    · rw [he_ve i i, he_norm i hlt, ite_eq_left hlt]
      module
    · intro b _ hb
      rw [he_ve b i]
      by_cases hltb : abs (lam b) < 1
      · rw [ite_eq_left hltb, he_cross b i hb]
        module
      · rw [ite_eq_right hltb]
        module
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hTe_zero : ∀ i : I, ¬ (abs (lam i) < 1) → T *ᵥ e i = 0 := by
    intro i hni
    rw [he_zero_of_ge i hni]
    simp

  have h1 : ∀ i : I, -1 ≤ lam i ∧ lam i ≤ 1 ∧ Normalized (v i) := by
    intro i
    exact ⟨hneg1 i, hpos1 i, hv_norm i⟩
  have h2 : ∀ i j : I, i ≠ j →
      Qatlib.Foundations.PureStateMath.Inner (v i) (v j) = 0 ∧ Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v j) = 0 ∧
        Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v j) = 0 ∧ Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (U *ᵥ v j) = 0 := by
    intro i j hij
    have h1 : Qatlib.Foundations.PureStateMath.Inner (v i) (v j) = 0 := by
      rw [hv_inner i j, ite_eq_right hij]
    have h2 : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v j) = 0 := by
      rw [hvU i j, ite_eq_right hij]
      ring
    have h3 : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v j) = 0 := by
      rw [hUv i j, ite_eq_right hij]
      ring
    have h4 : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (U *ᵥ v j) = 0 := by
      rw [hUU_in i j, ite_eq_right hij]
    exact ⟨h1, h2, h3, h4⟩
  have hT_star : star T = T := by
    rw [hT_eq]
    have hsum : star (∑ i, (pureDensity (v i) + (if abs (lam i) < 1 then pureDensity (e i) else 0)))
        = ∑ i, star (pureDensity (v i) + (if abs (lam i) < 1 then pureDensity (e i) else 0)) :=
      map_sum (starAddEquiv : Matrix H H ℂ ≃+ Matrix H H ℂ).toAddMonoidHom _ _
    rw [hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hA : star (pureDensity (v i)) = pureDensity (v i) := pureDensity_star _
    by_cases hlt : abs (lam i) < 1
    · rw [ite_eq_left hlt]
      show star (pureDensity (v i) + pureDensity (e i)) = _
      rw [star_add, hA, pureDensity_star]
    · rw [ite_eq_right hlt]
      show star (pureDensity (v i) + (0 : Matrix H H ℂ)) = _
      rw [add_zero, hA]
  have hTadj : Matrix.conjTranspose T = T := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hT_star
  have hTin : ∀ (y z : QState H), T *ᵥ y = y → Qatlib.Foundations.PureStateMath.Inner y (T *ᵥ z) = Qatlib.Foundations.PureStateMath.Inner y z := by
    intro y z hy
    rw [inner_rev', inner_mulVec_adj]
    rw [show (Matrix.conjTranspose T) = T from hTadj]
    rw [← inner_rev', hy]
  have h3 : IsOrthogonalProjector T := by
    have hT_self : T * T = T := by
      apply eq_of_mulVec_eq
      intro x
      rw [← Matrix.mulVec_mulVec, hT_mulVec]
      conv_rhs => rw [hT_mulVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 :
          Qatlib.Foundations.PureStateMath.Inner (v i)
          (T *ᵥ x) = Qatlib.Foundations.PureStateMath.Inner (v i) x := hTin (v i) x (hTv i)
      rw [h1]
      by_cases hlt : abs (lam i) < 1
      · have h2 : Qatlib.Foundations.PureStateMath.Inner (e i) (T *ᵥ x) = Qatlib.Foundations.PureStateMath.Inner (e i) x := hTin (e i) x (hTe i hlt)
        rw [h2]
      · have hz : e i = 0 := he_zero_of_ge i hlt
        rw [hz]
        simp [hlt]
    exact ⟨hT_self, hT_star⟩
  have hUHw : ∀ i : I, Uᴴ *ᵥ (U *ᵥ v i) = v i := by
    intro i
    rw [Matrix.mulVec_mulVec, hUHU, Matrix.one_mulVec]

  have hUHe : ∀ i : I, Uᴴ *ᵥ e i = U *ᵥ e i := by
    intro i
    by_cases hlt : abs (lam i) < 1
    · rw [he_zero i hlt, Matrix.mulVec_smul, Matrix.mulVec_smul]
      have hkey : Uᴴ *ᵥ (U *ᵥ v i - (lam i : ℂ) • v i)
          = U *ᵥ (U *ᵥ v i - (lam i : ℂ) • v i) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
        rw [hUHw i, hUHv i, hU2v i]
      rw [hkey]
    · rw [he_zero_of_ge i hlt]
      simp
  have h4 : U * T = T * U := by
    apply eq_of_mulVec_eq
    intro x
    rw [← Matrix.mulVec_mulVec]
    conv_rhs => rw [← Matrix.mulVec_mulVec]
    rw [hT_mulVec, hT_mulVec]
    conv_lhs => rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hin : ∀ (y : QState H), Uᴴ *ᵥ y = U *ᵥ y →
        Qatlib.Foundations.PureStateMath.Inner y (U *ᵥ x) = Qatlib.Foundations.PureStateMath.Inner (U *ᵥ y) x := by
      intro y hy
      rw [inner_rev', inner_mulVec_adj, hy, inner_rev', star_star]
    by_cases hlt : abs (lam i) < 1
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      have hsplit : ∀ (a b : ℂ), U *ᵥ (a • v i + b • e i)
          = a • (U *ᵥ v i) + b • (U *ᵥ e i) := by
        intro a b
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      rw [hsplit, hUv1 i hlt, hUe1 i hlt]
      rw [hin (v i) (hUHv i), hin (e i) (hUHe i), hUv1 i hlt, hUe1 i hlt]

      have hR1 : Qatlib.Foundations.PureStateMath.Inner ((lam i : ℂ) • v i
          + ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) • e i) x
          = (lam i : ℂ) * Qatlib.Foundations.PureStateMath.Inner (v i) x
            + ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner (e i) x := by
        rw [inner_add_l, inner_smul_l, inner_smul_l]
        rw [star_ofReal_cast, star_ofReal_cast]
      have hR2 : Qatlib.Foundations.PureStateMath.Inner (((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) • v i
          - (lam i : ℂ) • e i) x
          = ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner (v i) x
            - (lam i : ℂ) * Qatlib.Foundations.PureStateMath.Inner (e i) x := by
        rw [inner_sub_l, inner_smul_l, inner_smul_l]
        rw [star_ofReal_cast, star_ofReal_cast]
      rw [hR1, hR2]
      simp only [smul_add, smul_sub, smul_smul]
      module
    · rw [ite_eq_right hlt, ite_eq_right hlt]
      have hsplit2 : ∀ (a : ℂ), U *ᵥ (a • v i + (0 : QState H))
          = a • (U *ᵥ v i) := by
        intro a
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        simp
      rw [hsplit2, hin (v i) (hUHv i)]
      have hUV : U *ᵥ v i = (lam i : ℂ) • v i := by
        have h1 : abs (lam i) = 1 := by
          have := hlam_le i
          have h2 : 1 ≤ abs (lam i) := le_of_not_gt hlt
          exact le_antisymm this h2
        have h2 : (lam i) ^ 2 = 1 := by
          have : (abs (lam i)) ^ 2 = 1 := by rw [h1, one_pow]
          rwa [sq_abs] at this
        have hw : U *ᵥ v i - (lam i : ℂ) • v i = 0 := by
          have hInner : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i - (lam i : ℂ) • v i) (U *ᵥ v i - (lam i : ℂ) • v i) = 0 := by
            have hUU' : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (U *ᵥ v i) = 1 := by
              rw [hUU_in i i, ite_eq_left rfl]
            have hUV' : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v i) = (lam i : ℂ) := by
              rw [inner_rev', hvU i i, ite_eq_left rfl, mul_one]
              exact star_ofReal_cast _
            have hVV : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i) = (lam i : ℂ) := by
              rw [hvU i i, ite_eq_left rfl, mul_one]
            simp only [inner_sub_l, inner_sub_r, inner_smul_r, inner_smul_l]
            rw [hUU', hUV', hVV, hv_self i]
            have hs1 : star ((lam i : ℂ)) = (lam i : ℂ) := star_ofReal_cast _
            have h2c : ((lam i : ℂ) * (lam i : ℂ) : ℂ) = 1 := by
              have h2' : (lam i * lam i : ℝ) = 1 := by rw [← pow_two]; exact h2
              exact_mod_cast h2'
            rw [hs1, mul_one, h2c]
            ring
          exact inner_self_eq_zero hInner
        have h3 : U *ᵥ v i = (lam i : ℂ) • v i := sub_eq_zero.mp hw
        exact h3
      rw [hUV]
      rw [inner_smul_l, star_ofReal_cast]
      module

  have hGGT : (G * Gᴴ) * T = G * Gᴴ := by
    have hsum : ∑ i : I, pureDensity (v i) = G * Gᴴ :=
      (gg_eq_sum_pureDensity G S hSS).symm
    rw [hT_eq, Matrix.mul_sum]
    have hterm : ∀ i : I,
        (G * Gᴴ) * (pureDensity (v i) + if abs (lam i) < 1 then pureDensity (e i) else 0)
          = pureDensity (v i) := by
      intro i
      rw [Matrix.mul_add]
      have hvG : (G * Gᴴ) * pureDensity (v i) = pureDensity (v i) := by
        ext a b
        rw [mul_pureDensity_apply, hGGv i]
        rfl
      by_cases hlt : abs (lam i) < 1
      · rw [ite_eq_left hlt]
        have heG : (G * Gᴴ) * pureDensity (e i) = 0 := by
          ext a b
          rw [mul_pureDensity_apply, hGGe1 i]
          simp
        rw [hvG, heG, add_zero]
      · rw [ite_eq_right hlt, Matrix.mul_zero, add_zero]
        exact hvG
    rw [Finset.sum_congr rfl fun i _ => hterm i, hsum]
  have h5 : G * Gᴴ * (1 - T) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hGGT, sub_self]

  have hcol_eq : ∀ i : I, (G * S).col i = v i := fun i => rfl
  have hTG : T * G = G := by
    have key : T * (G * S) = G * S := by
      ext a i
      show (T *ᵥ (G * S).col i) a = _
      rw [show (G * S).col i = v i from rfl, hTv i]
      rfl
    have key' : (T * G) * S = G * S := by
      rw [Matrix.mul_assoc, key]
    have h2 : G * (S * Sᴴ) = G := by
      rw [hSS, Matrix.mul_one]
    calc T * G = T * (G * (S * Sᴴ)) := by rw [h2]
      _ = ((T * G) * S) * Sᴴ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = (G * S) * Sᴴ := by rw [key']
      _ = G * (S * Sᴴ) := by rw [Matrix.mul_assoc]
      _ = G := h2

  have hSHS_vec : ∀ w : QState I, Sᴴ *ᵥ (S *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hSHS, Matrix.one_mulVec]
  have hGS : ∀ w : QState I, G *ᵥ (S *ᵥ w) = ∑ i, w i • v i := by
    intro w
    conv_lhs => rw [Matrix.mulVec_mulVec]
    funext k
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    show (∑ j, G k j * S j x) * w x = w x * (G *ᵥ fun j => S j x) k
    simp only [Matrix.mulVec, dotProduct]
    exact mul_comm _ _
  have hG_exp : ∀ x : QState I, G *ᵥ x = ∑ i, ((Sᴴ *ᵥ x) i) • v i := by
    intro x
    conv_lhs => rw [show x = S *ᵥ (Sᴴ *ᵥ x) by
      rw [Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]]
    rw [hGS]

  have hUv_all : ∀ i : I, U *ᵥ v i = (lam i : ℂ) • v i
      + ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) • e i := by
    intro i
    by_cases hlt : abs (lam i) < 1
    · exact hUv1 i hlt
    · have h1 : abs (lam i) = 1 := by
        have := hlam_le i
        have h2 : 1 ≤ abs (lam i) := le_of_not_gt hlt
        exact le_antisymm this h2
      have h2 : (lam i) ^ 2 = 1 := by
        have : (abs (lam i)) ^ 2 = 1 := by rw [h1, one_pow]
        rwa [sq_abs] at this
      have hs : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) = 0 := by
        rw [h2, sub_self, Real.sqrt_zero]
      have he0 : e i = 0 := he_zero_of_ge i hlt
      rw [he0, hs, smul_zero, add_zero]
      have hw : U *ᵥ v i - (lam i : ℂ) • v i = 0 := by
        have hInner : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i - (lam i : ℂ) • v i) (U *ᵥ v i - (lam i : ℂ) • v i) = 0 := by
          have hUU' : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (U *ᵥ v i) = 1 := by
            rw [hUU_in i i, ite_eq_left rfl]
          have hUV' : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) (v i) = (lam i : ℂ) := by
            rw [inner_rev', hvU i i, ite_eq_left rfl, mul_one]
            exact star_ofReal_cast _
          have hVV : Qatlib.Foundations.PureStateMath.Inner (v i) (U *ᵥ v i) = (lam i : ℂ) := by
            rw [hvU i i, ite_eq_left rfl, mul_one]
          have hs1 : star ((lam i : ℂ)) = (lam i : ℂ) := star_ofReal_cast _
          have h2c : ((lam i : ℂ) * (lam i : ℂ) : ℂ) = 1 := by
            have h2' : (lam i * lam i : ℝ) = 1 := by rw [← pow_two]; exact h2
            exact_mod_cast h2'
          simp only [inner_sub_l, inner_sub_r, inner_smul_r, inner_smul_l]
          rw [hUU', hUV', hVV, hv_self i, hs1]
          simp only [mul_one, h2c]
          ring
        exact inner_self_eq_zero hInner
      exact sub_eq_zero.mp hw
  have hUe_all : ∀ i : I, U *ᵥ e i = ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) • v i
      - (lam i : ℂ) • e i := by
    intro i
    by_cases hlt : abs (lam i) < 1
    · exact hUe1 i hlt
    · have h1 : abs (lam i) = 1 := by
        have := hlam_le i
        have h2 : 1 ≤ abs (lam i) := le_of_not_gt hlt
        exact le_antisymm this h2
      have h2 : (lam i) ^ 2 = 1 := by
        have : (abs (lam i)) ^ 2 = 1 := by rw [h1, one_pow]
        rwa [sq_abs] at this
      have hs : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) = 0 := by
        rw [h2, sub_self, Real.sqrt_zero]
      rw [he_zero_of_ge i hlt]
      simp only [smul_zero, sub_zero, Matrix.mulVec_zero]
      rw [hs]
      simp

  have h6 : ∀ ψ : QState H, T *ᵥ ψ = ψ ↔ ∃ a b : QState I, ψ = G *ᵥ a + U *ᵥ (G *ᵥ b) := by
    intro ψ
    constructor
    · intro hψ
      set c : I → ℂ := fun i => Qatlib.Foundations.PureStateMath.Inner (v i) ψ
      set d : I → ℂ := fun i => (if abs (lam i) < 1 then Qatlib.Foundations.PureStateMath.Inner (e i) ψ else 0)
          * ((Real.sqrt (1 - (lam i) ^ 2) : ℂ) : ℂ)⁻¹
      refine ⟨S *ᵥ (fun i => c i - d i * (lam i : ℂ)), S *ᵥ d, ?_⟩
      have hGa : G *ᵥ (S *ᵥ (fun i => c i - d i * (lam i : ℂ)))
          = ∑ i, (c i - d i * (lam i : ℂ)) • v i := hGS _
      have hGb : G *ᵥ (S *ᵥ d) = ∑ i, d i • v i := hGS _
      rw [hGa, hGb]
      have hsplit : ∀ i : I, d i • (U *ᵥ v i) = (d i * (lam i : ℂ)) • v i
          + (if abs (lam i) < 1 then (Qatlib.Foundations.PureStateMath.Inner (e i) ψ) • e i else 0) := by
        intro i
        by_cases hlt : abs (lam i) < 1
        · rw [ite_eq_left hlt, hUv1 i hlt, smul_add, smul_smul, smul_smul]
          have hs0 : (0 : ℝ) < Real.sqrt (1 - (lam i) ^ 2) := by
            apply Real.sqrt_pos.mpr
            have h2 := abs_lt.mp hlt
            nlinarith [sq_nonneg (lam i)]
          have hsne : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) ≠ 0 := ne_of_gt hs0
          have hds : d i * ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ)
              = (Qatlib.Foundations.PureStateMath.Inner (e i) ψ) := by
            simp only [d, ite_eq_left hlt]
            rw [mul_assoc, inv_mul_cancel₀, mul_one]
            exact_mod_cast hsne
          rw [hds]
        · rw [ite_eq_right hlt]
          have hd : d i = 0 := by
            simp only [d, ite_eq_right hlt, zero_mul]
          have hs : ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) = 0 := by
            have h1 : abs (lam i) = 1 := by
              have := hlam_le i
              have h2 : 1 ≤ abs (lam i) := le_of_not_gt hlt
              exact le_antisymm this h2
            have h2 : (lam i) ^ 2 = 1 := by
              have : (abs (lam i)) ^ 2 = 1 := by rw [h1, one_pow]
              rwa [sq_abs] at this
            rw [h2, sub_self]
            simp
          have hUV : U *ᵥ v i = (lam i : ℂ) • v i := by
            rw [hUv_all i, hs]
            simp
          rw [hUV, hd]
          module
      have hUGb : U *ᵥ (∑ i, d i • v i) = ∑ i, (d i * (lam i : ℂ)) • v i
          + ∑ i, (if abs (lam i) < 1 then (Qatlib.Foundations.PureStateMath.Inner (e i) ψ) • e i else 0) := by
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul]
        have hsum : (∑ i, d i • (U *ᵥ v i))
            = ∑ i, ((d i * (lam i : ℂ)) • v i
              + (if abs (lam i) < 1 then (Qatlib.Foundations.PureStateMath.Inner (e i) ψ) • e i else 0)) :=
          Finset.sum_congr rfl fun i _ => hsplit i
        rw [hsum, Finset.sum_add_distrib]
      conv_rhs => rw [hUGb]
      have hcomb : (∑ i, (c i - d i * (lam i : ℂ)) • v i)
          + (∑ i, (d i * (lam i : ℂ)) • v i
              + ∑ i, (if abs (lam i) < 1 then (Qatlib.Foundations.PureStateMath.Inner (e i) ψ) • e i else 0))
          = ∑ i, (c i • v i + (if abs (lam i) < 1 then (Qatlib.Foundations.PureStateMath.Inner (e i) ψ) • e i else 0)) := by
        conv_lhs => rw [← Finset.sum_add_distrib (s := Finset.univ)
          (f := fun i : I => (d i * (lam i : ℂ)) • v i)
          (g := fun i : I => if abs (lam i) < 1 then (Qatlib.Foundations.PureStateMath.Inner (e i) ψ) • e i else 0)]
        conv_lhs => rw [← Finset.sum_add_distrib (s := Finset.univ)
          (f := fun i : I => (c i - d i * (lam i : ℂ)) • v i)
          (g := fun i : I => (d i * (lam i : ℂ)) • v i
            + (if abs (lam i) < 1 then (Qatlib.Foundations.PureStateMath.Inner (e i) ψ) • e i else 0))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_assoc, ← add_smul, sub_add_cancel]
      rw [hcomb]
      exact hψ.symm.trans (hT_mulVec ψ)
    · rintro ⟨a, b, rfl⟩
      rw [Matrix.mulVec_add]
      have h1 : ∀ x : QState I, T *ᵥ (G *ᵥ x) = G *ᵥ x := by
        intro x
        rw [Matrix.mulVec_mulVec, hTG]
      have h2 : ∀ x : QState I, T *ᵥ (U *ᵥ (G *ᵥ x)) = U *ᵥ (G *ᵥ x) := by
        intro x
        rw [Matrix.mulVec_mulVec, ← h4, ← Matrix.mulVec_mulVec, h1]
      rw [h1, h2]

  have hGadj : ∀ x : QState I, (∀ i : I, Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) x = 0) → x = 0 := by
    intro x hx
    have h : Sᴴ *ᵥ x = 0 := by
      funext i
      have h1 : Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) x = (Sᴴ *ᵥ x) i := by
        rw [inner_apply]
        simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
        rfl
      rw [← h1, hx]
      rfl
    have h2 : x = S *ᵥ (Sᴴ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
    rw [h2, h, Matrix.mulVec_zero]
  have h7 : ∀ ψ : QState H, T *ᵥ ψ = 0 ↔ Gᴴ *ᵥ ψ = 0 ∧ Gᴴ *ᵥ (Uᴴ *ᵥ ψ) = 0 := by
    intro ψ
    constructor
    · intro hψ
      have hIv : ∀ j : I, Qatlib.Foundations.PureStateMath.Inner (v j) ψ = 0 := by
        intro j
        have h2 :
            Qatlib.Foundations.PureStateMath.Inner (v j)
            (T *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner (v j) ψ := hTin (v j) ψ (hTv j)
        rw [hψ] at h2
        simp [Qatlib.Foundations.PureStateMath.Inner] at h2
        exact h2.symm
      have hIe : ∀ j : I, Qatlib.Foundations.PureStateMath.Inner (e j) ψ = 0 := by
        intro j
        by_cases hlt : abs (lam j) < 1
        · have h2 : Qatlib.Foundations.PureStateMath.Inner (e j) (T *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner (e j) ψ := hTin (e j) ψ (hTe j hlt)
          rw [hψ] at h2
          simp [Qatlib.Foundations.PureStateMath.Inner] at h2
          exact h2.symm
        · rw [he_zero_of_ge j hlt]
          simp [Qatlib.Foundations.PureStateMath.Inner]
      have hG : Gᴴ *ᵥ ψ = 0 := by
        apply hGadj
        intro i
        have h1 : Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) (Gᴴ *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner (v i) ψ :=
          (inner_mulVec_adj G (fun k => S k i) ψ).symm
        rw [h1, hIv]
      have hGU : Gᴴ *ᵥ (Uᴴ *ᵥ ψ) = 0 := by
        apply hGadj
        intro i
        have h1 : Qatlib.Foundations.PureStateMath.Inner (fun k => S k i) (Gᴴ *ᵥ (Uᴴ *ᵥ ψ)) = Qatlib.Foundations.PureStateMath.Inner (v i) (Uᴴ *ᵥ ψ) :=
          (inner_mulVec_adj G (fun k => S k i) (Uᴴ *ᵥ ψ)).symm
        rw [h1]
        have h2 : Qatlib.Foundations.PureStateMath.Inner (v i) (Uᴴ *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v i) ψ :=
          (inner_mulVec_adj U (v i) ψ).symm
        rw [h2, hUv_all i, inner_add_l, inner_smul_l, inner_smul_l, hIv, hIe]
        rw [star_ofReal_cast]
        simp
      exact ⟨hG, hGU⟩
    · rintro ⟨hG, hGU⟩
      have hIv : ∀ j : I, Qatlib.Foundations.PureStateMath.Inner (v j) ψ = 0 := by
        intro j
        have h1 : Qatlib.Foundations.PureStateMath.Inner (v j) ψ = Qatlib.Foundations.PureStateMath.Inner (fun k => S k j) (Gᴴ *ᵥ ψ) :=
          inner_mulVec_adj G (fun k => S k j) ψ
        rw [h1, hG]
        simp [Qatlib.Foundations.PureStateMath.Inner]
      have hIUv : ∀ j : I, Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v j) ψ = 0 := by
        intro j
        have h3 : Qatlib.Foundations.PureStateMath.Inner (U *ᵥ v j) ψ = Qatlib.Foundations.PureStateMath.Inner (v j) (Uᴴ *ᵥ ψ) :=
          inner_mulVec_adj U (v j) ψ
        have h2 : Qatlib.Foundations.PureStateMath.Inner (v j) (Uᴴ *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner (fun k => S k j) (Gᴴ *ᵥ (Uᴴ *ᵥ ψ)) :=
          inner_mulVec_adj G (fun k => S k j) (Uᴴ *ᵥ ψ)
        rw [h3, h2, hGU]
        simp [Qatlib.Foundations.PureStateMath.Inner]
      have hIe : ∀ j : I, Qatlib.Foundations.PureStateMath.Inner (e j) ψ = 0 := by
        intro j
        by_cases hlt : abs (lam j) < 1
        · rw [he_zero j hlt, inner_smul_l, inner_sub_l, inner_smul_l, hIUv, hIv]
          rw [star_ofReal_cast]
          simp
        · rw [he_zero_of_ge j hlt]
          simp [Qatlib.Foundations.PureStateMath.Inner]
      rw [hT_mulVec]
      apply Finset.sum_eq_zero
      intro i _
      rw [hIv, hIe]
      by_cases hlt : abs (lam i) < 1
      · rw [ite_eq_left hlt]
        simp
      · rw [ite_eq_right hlt]
        simp

  have h8 : ∀ i : I, abs (lam i) < 1 →
      Normalized (e i) ∧ Qatlib.Foundations.PureStateMath.Inner (v i) (e i) = 0 ∧
        U *ᵥ (v i) = (lam i : ℂ) • v i + (Real.sqrt (1-(lam i)^2) : ℂ) • e i ∧
        U *ᵥ (e i) = (Real.sqrt (1-(lam i)^2) : ℂ) • v i - (lam i : ℂ) • e i ∧
        (G*Gᴴ) *ᵥ e i=0 ∧
        (∀ neg : Bool, Normalized (walkBranch U (v i) (lam i) neg) ∧
          walk G U *ᵥ walkBranch U (v i) (lam i) neg=
            Complex.exp (Complex.I*(if neg then -Real.arccos (lam i) else Real.arccos (lam i))) •
              walkBranch U (v i) (lam i) neg) := by
    intro i hlt
    obtain ⟨hUv1i, hUe1i, hGGe1i, hIvei, hNormi⟩ := hres i hlt
    refine ⟨hNormi, hIvei, hUv1i, hUe1i, hGGe1i, ?_⟩
    intro neg
    exact hwalk i hlt neg

  have hwalkv : ∀ i : I, walk G U *ᵥ v i
      = (lam i : ℂ) • v i - ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) • e i := by
    intro i
    rw [show walk G U = ((2 • (G * Gᴴ) - 1) * U : Matrix H H ℂ) from rfl]
    rw [← Matrix.mulVec_mulVec, hUv_all i]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hD : (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) *ᵥ v i = v i := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hGGv i, Matrix.one_mulVec]
      module
    have hE : (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) *ᵥ e i = - e i := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hGGe1 i, Matrix.one_mulVec]
      module
    rw [hD, hE]
    module
  have hwalke : ∀ i : I, walk G U *ᵥ e i
      = ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) • v i + (lam i : ℂ) • e i := by
    intro i
    rw [show walk G U = ((2 • (G * Gᴴ) - 1) * U : Matrix H H ℂ) from rfl]
    rw [← Matrix.mulVec_mulVec, hUe_all i]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hD : (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) *ᵥ v i = v i := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hGGv i, Matrix.one_mulVec]
      module
    have hE : (2 • (G * Gᴴ) - 1 : Matrix H H ℂ) *ᵥ e i = - e i := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hGGe1 i, Matrix.one_mulVec]
      module
    rw [hD, hE]
    module

  have hsqrt2 : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ : ℂ) = 1 / 2 := by
    have h5 : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = 2 :=
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h6 : ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) = ((2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, h5]
    have h7 : ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ : ℂ)
        = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ := by
      rw [_root_.mul_inv_rev]
    rw [h7, h6]
    push_cast
    field_simp
  have hstar_sqrt2 : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [RCLike.star_def, Complex.conj_inv, Complex.conj_ofReal]
  have hexp_cos : ∀ i : I,
      Complex.exp (Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ))
        = (lam i : ℂ) + Complex.I * ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) := by
    intro i
    have h2 : (Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ) : ℂ)
        = ((Real.arccos (lam i) : ℝ) : ℂ) * Complex.I := by ring
    rw [h2]
    have h1 : Complex.exp (((Real.arccos (lam i) : ℝ) : ℂ) * Complex.I)
        = ((Real.cos (Real.arccos (lam i)) : ℝ) : ℂ)
            + ((Real.sin (Real.arccos (lam i)) : ℝ) : ℂ) * Complex.I :=
      Complex.exp_ofReal_mul_I _
    rw [h1, Real.cos_arccos (hneg1 i) (hpos1 i), Real.sin_arccos]
    ring
  have hexp_cos_neg : ∀ i : I,
      Complex.exp (-Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ))
        = (lam i : ℂ) - Complex.I * ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ) := by
    intro i
    have h2 : (-Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ) : ℂ)
        = ((-Real.arccos (lam i) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_neg]
      ring
    rw [h2]
    have h1 : Complex.exp (((-Real.arccos (lam i) : ℝ) : ℂ) * Complex.I)
        = ((Real.cos (-Real.arccos (lam i)) : ℝ) : ℂ)
            + ((Real.sin (-Real.arccos (lam i)) : ℝ) : ℂ) * Complex.I :=
      Complex.exp_ofReal_mul_I _
    rw [h1, Real.cos_neg, Real.cos_arccos (hneg1 i) (hpos1 i), Real.sin_neg, Real.sin_arccos]
    push_cast
    ring

  have hwb_apply : ∀ (i : I) (neg : Bool) (a b : H),
      pureDensity (walkBranch U (v i) (lam i) neg) a b
        = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹)
            * (v i a + (if neg then -Complex.I else Complex.I) * e i a)
            * (star (v i b) + star (if neg then -Complex.I else Complex.I) * star (e i b)) := by
    intro i neg a b
    rw [show walkBranch U (v i) (lam i) neg
        = (Real.sqrt 2 : ℂ)⁻¹ • (v i + (if neg then -Complex.I else Complex.I) • e i) from rfl]
    simp only [pureDensity, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [star_mul, hstar_sqrt2, star_add, star_mul]
    ring
  have h9 : walk G U * T =
      ∑ i, if abs (lam i) = 1 then (lam i : ℂ) • pureDensity (v i)
      else
        Complex.exp (Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ)) •
            pureDensity (walkBranch U (v i) (lam i) false) +
          Complex.exp (-Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ)) •
            pureDensity (walkBranch U (v i) (lam i) true) := by
    ext a b
    rw [hT_eq, Matrix.mul_sum]
    simp only [sum_smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_add]
    by_cases h1 : abs (lam i) = 1
    · have hlt : ¬ abs (lam i) < 1 := by
        intro h
        exact absurd h (by rw [h1]; exact lt_irrefl (1:ℝ))
      rw [ite_eq_right hlt, Matrix.mul_zero, add_zero, ite_eq_left h1]
      have hs : (Real.sqrt (1 - (lam i) ^ 2) : ℝ) = 0 := by
        have h2 : (lam i) ^ 2 = 1 := by
          have : (abs (lam i)) ^ 2 = 1 := by rw [h1, one_pow]
          rwa [sq_abs] at this
        rw [h2, sub_self, Real.sqrt_zero]
      have he0 : e i = 0 := he_zero_of_ge i hlt
      rw [mul_pureDensity_apply, hwalkv i, he0, hs, smul_zero, sub_zero,
        smul_pureDensity_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · have hlt : abs (lam i) < 1 := by
        have h2 : abs (lam i) ≤ 1 := hlam_le i
        exact lt_of_le_of_ne h2 h1
      rw [ite_eq_left hlt, ite_eq_right h1]
      show (walk G U * pureDensity (v i)) a b + (walk G U * pureDensity (e i)) a b = _
      rw [mul_pureDensity_apply, mul_pureDensity_apply]
      rw [hwalkv i, hwalke i]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hR : ((Complex.exp (Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ)) •
              pureDensity (walkBranch U (v i) (lam i) false) +
            Complex.exp (-Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ)) •
              pureDensity (walkBranch U (v i) (lam i) true)) : Matrix H H ℂ) a b
          = Complex.exp (Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ))
              * pureDensity (walkBranch U (v i) (lam i) false) a b
            + Complex.exp (-Complex.I * ((Real.arccos (lam i) : ℝ) : ℂ))
              * pureDensity (walkBranch U (v i) (lam i) true) a b := by
        simp [smul_eq_mul]
      rw [hR, hwb_apply i false a b, hwb_apply i true a b]
      simp only [ite_eq_right (by simp : ¬ (false = true)), ite_true]
      have hsI : star (Complex.I) = -Complex.I := by
        rw [RCLike.star_def, Complex.conj_I]
      have hsI_neg : star (-Complex.I) = Complex.I := by
        rw [RCLike.star_def, map_neg, Complex.conj_I]
        simp
      rw [hexp_cos i, hexp_cos_neg i, hsI, hsI_neg, hsqrt2]
      have hcore := spectral_block (lam i : ℂ)
        ((Real.sqrt (1 - (lam i) ^ 2) : ℝ) : ℂ)
        (v i a) (e i a) (star (v i b)) (star (e i b))
      ring_nf at hcore ⊢
      rw [show (Complex.I ^ 2 : ℂ) = -1 by rw [pow_two, Complex.I_mul_I]] at hcore ⊢
      ring_nf at hcore ⊢
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
