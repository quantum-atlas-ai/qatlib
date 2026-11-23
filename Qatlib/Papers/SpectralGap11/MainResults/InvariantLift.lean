/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.GroundLift
public import Qatlib.Papers.SpectralGap11.MainResults.InvariantBlocks

/-!
# Actual invariant vectors from an eigenvector of the input Hamiltonian

The compression relation is derived from the doubled oracle register.
The residual-vector identities prove invariance under the actual matrix
before normalizing the two-dimensional basis.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.InvariantLift

open Matrix
open AmplifiedRegister
open scoped BigOperators

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Orthogonal residual before dividing by the compression sine. -/
def residual (U : Matrix I I ℂ) (v : I → ℂ) (gamma : ℂ) : I → ℂ :=
  U *ᵥ v - gamma • v

omit [DecidableEq I] in
/-- The residual is annihilated by the original ancilla projection. -/
theorem residual_projected (P U : Matrix I I ℂ) (v : I → ℂ) (gamma : ℂ)
    (hPv : P *ᵥ v = v) (hPUv : P *ᵥ (U *ᵥ v) = gamma • v) :
    P *ᵥ residual U v gamma = 0 := by
  simp only [residual, Matrix.mulVec_sub, Matrix.mulVec_smul, hPUv, hPv, sub_self]

/-- The involution exchanges the lifted vector with its residual according
to the source compression cosine. -/
theorem residual_reflected (U : Matrix I I ℂ) (v : I → ℂ) (gamma : ℂ)
    (hU : U * U = 1) :
    U *ᵥ residual U v gamma =
      (1 - gamma ^ 2) • v - gamma • residual U v gamma := by
  simp only [residual, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  module

/-- The exact penalty construction, with no spectral conclusions in its data. -/
def penaltyH (P U : Matrix I I ℂ) (L delta : ℂ) : Matrix I I ℂ :=
  L • (U * P * U - P) + delta • (1 - P)

/-- The actual penalty Hamiltonian preserves the lifted vector and residual
span and has the stated two-column action there. -/
theorem penalty_invariant (P U : Matrix I I ℂ) (v : I → ℂ) (gamma L delta : ℂ)
    (hU : U * U = 1) (hPv : P *ᵥ v = v)
    (hPUv : P *ᵥ (U *ᵥ v) = gamma • v) :
    penaltyH P U L delta *ᵥ v =
        (L * (gamma ^ 2 - 1)) • v +
          (L * gamma) • residual U v gamma ∧
      penaltyH P U L delta *ᵥ residual U v gamma =
        (L * gamma * (1 - gamma ^ 2)) • v +
          (delta + L * (1 - gamma ^ 2)) • residual U v gamma := by
  have hPw := residual_projected P U v gamma hPv hPUv
  have hUw := residual_reflected U v gamma hU
  have hUv : U *ᵥ v = gamma • v + residual U v gamma := by
    dsimp [residual]
    module
  have hPUw : P *ᵥ (U *ᵥ residual U v gamma) = (1 - gamma ^ 2) • v := by
    rw [hUw, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hPv, hPw]
    simp
  have hUPUv : (U * P * U) *ᵥ v = gamma • (U *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPUv, Matrix.mulVec_smul]
  have hUPUw : (U * P * U) *ᵥ residual U v gamma =
      (1 - gamma ^ 2) • (U *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPUw, Matrix.mulVec_smul]
  constructor
  · simp only [penaltyH, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, hUPUv, hPv, Matrix.one_mulVec, hUv]
    module
  · simp only [penaltyH, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, hUPUw, hPw, Matrix.one_mulVec, hUv]
    module

/-- An actual eigenvector of the input sum yields the lazy cosine after
compression of the actual doubled-register oracle. -/
theorem compressed_eigen_lift (Proj : K → Matrix I I ℂ)
    (hK : 0 < Fintype.card K) (psi : I → ℂ) (lambda : ℂ)
    (heigen : (∑ k, Proj k) *ᵥ psi = lambda • psi) :
    lazyP *ᵥ (lazyOracle Proj *ᵥ
        (uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi)) =
      (1 - (Fintype.card K : ℂ)⁻¹ * lambda) •
        (uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi) := by
  let J := uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K))
  have hcompression : Jᴴ * lazyOracle Proj * J =
      1 - (Fintype.card K : ℂ)⁻¹ • ∑ k, Proj k := lazy_compression Proj hK
  have hmatrix : lazyP * lazyOracle Proj * J =
      J * (1 - (Fintype.card K : ℂ)⁻¹ • ∑ k, Proj k) := by
    change (J * Jᴴ) * lazyOracle Proj * J = _
    calc
      (J * Jᴴ) * lazyOracle Proj * J = J * (Jᴴ * lazyOracle Proj * J) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcompression]
  change lazyP *ᵥ (lazyOracle Proj *ᵥ (J *ᵥ psi)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmatrix,
    ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, heigen, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [Matrix.mulVec_smul]
  dsimp [J]
  module

/-- The input eigenvector determines an invariant two-vector span for the
actual amplified matrix, with its cosine derived from `H`, not supplied as
an unconstrained model field. -/
theorem actual_invariant (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k) (hK : 0 < Fintype.card K)
    (psi : I → ℂ) (lambda delta : ℂ)
    (heigen : (∑ k, Proj k) *ᵥ psi = lambda • psi) :
    let v := uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi
    let gamma := 1 - (Fintype.card K : ℂ)⁻¹ * lambda
    doubledHamiltonian Proj delta *ᵥ v =
        ((Fintype.card K : ℂ) * (gamma ^ 2 - 1)) • v +
          ((Fintype.card K : ℂ) * gamma) • residual (lazyOracle Proj) v gamma ∧
      doubledHamiltonian Proj delta *ᵥ residual (lazyOracle Proj) v gamma =
        ((Fintype.card K : ℂ) * gamma * (1 - gamma ^ 2)) • v +
          (delta + (Fintype.card K : ℂ) * (1 - gamma ^ 2)) •
            residual (lazyOracle Proj) v gamma := by
  dsimp only
  have h := penalty_invariant lazyP (lazyOracle Proj)
    (uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi)
    (1 - (Fintype.card K : ℂ)⁻¹ * lambda) (Fintype.card K : ℂ) delta
    (lazyOracle_sq Proj hproj) (ground_projection_fixed hK psi)
    (compressed_eigen_lift Proj hK psi lambda heigen)
  simpa only [penaltyH, doubledHamiltonian, doubledProjectionDifference] using h

/-- The two-column matrix for a lifted vector and its sine-normalized residual. -/
def spanFrame (U : Matrix I I ℂ) (v : I → ℂ) (gamma sine : ℂ) : Matrix I (Fin 2) ℂ :=
  fun i j => if j = 0 then v i else sine⁻¹ * residual U v gamma i

/-- The actual penalty matrix intertwines the constructed invariant frame
with exactly the source's two-dimensional block. This matrix identity is
proved before any eigenvalue or gap claim. -/
theorem spanFrame_intertwines (P U : Matrix I I ℂ) (v : I → ℂ)
    (gamma sine L delta : ℂ) (hU : U * U = 1) (hPv : P *ᵥ v = v)
    (hPUv : P *ᵥ (U *ᵥ v) = gamma • v)
    (hnorm : gamma ^ 2 + sine ^ 2 = 1) (hsine : sine ≠ 0) :
    penaltyH P U L delta * spanFrame U v gamma sine =
      spanFrame U v gamma sine *
        !![-L * sine ^ 2, L * sine * gamma;
          L * sine * gamma, delta + L * sine ^ 2] := by
  have h := penalty_invariant P U v gamma L delta hU hPv hPUv
  have hgamma : gamma ^ 2 = 1 - sine ^ 2 := (eq_sub_iff_add_eq).2 hnorm
  ext i j
  fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, spanFrame]
    have hv := congrFun h.1 i
    change (penaltyH P U L delta *ᵥ v) i = _
    rw [hv, hgamma]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hsine]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, spanFrame]
    have heq : (∑ k, penaltyH P U L delta i k *
        (sine⁻¹ * residual U v gamma k)) =
          sine⁻¹ * (penaltyH P U L delta *ᵥ residual U v gamma) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [heq, congrFun h.2 i]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hgamma]
    field_simp [hsine]
    ring

end

end Qatlib.Papers.SpectralGap11.MainResults.InvariantLift
