/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.AmplifiedRegister

/-!
# The actual amplified Hamiltonian and its ground-state embedding

The operators use the explicit doubled register constructed in
`AmplifiedRegister`, rather than independent output or spectral fields.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults

open Matrix
open AmplifiedRegister

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- The actual difference of conjugated and original ancilla projections. -/
def doubledProjectionDifference (Proj : K → Matrix I I ℂ) : Matrix (I × (K × Bool)) (I × (K × Bool)) ℂ :=
  lazyOracle Proj * lazyP * lazyOracle Proj - lazyP

/-- The source penalty construction on the repaired doubled register. -/
def doubledHamiltonian (Proj : K → Matrix I I ℂ) (delta : ℂ) :
    Matrix (I × (K × Bool)) (I × (K × Bool)) ℂ :=
  (Fintype.card K : ℂ) • doubledProjectionDifference Proj + delta • (1 - lazyP)

/-- The repaired actual amplified Hamiltonian is Hermitian for Hermitian
input terms and a real penalty. Projector idempotence is unnecessary here. -/
theorem doubled_hamiltonian_hermitian (Proj : K → Matrix I I ℂ)
    (hHerm : ∀ k, (Proj k).IsHermitian) (delta : ℂ) (hdelta : star delta = delta) :
    (doubledHamiltonian Proj delta).IsHermitian := by
  have hU : (lazyOracle Proj)ᴴ = lazyOracle Proj := (lazyOracle_hermitian Proj hHerm).eq
  have hP : (lazyP (I := I) (K := K))ᴴ = lazyP := lazyP_hermitian.eq
  change (doubledHamiltonian Proj delta)ᴴ = doubledHamiltonian Proj delta
  simp only [doubledHamiltonian, doubledProjectionDifference, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hU, hP,
    Matrix.conjTranspose_one, star_natCast, hdelta]
  rw [Matrix.mul_assoc]

omit [Fintype K] [DecidableEq K] in
/-- Applying the uniform-register embedding produces its explicit amplitudes. -/
theorem uniformEmbed_mulVec (rho : ℂ) (psi : I → ℂ) (i : I) (k : K) :
    (uniformEmbed (K := K) rho *ᵥ psi) (i, k) = rho * psi i := by
  simp [uniformEmbed, Matrix.mulVec, dotProduct]

/-- A controlled matrix acts on the physical system in each ancilla branch. -/
theorem blockDiagonal_uniform (B : K → Matrix I I ℂ) (rho : ℂ) (psi : I → ℂ)
    (i : I) (k : K) :
    (Matrix.blockDiagonal B *ᵥ (uniformEmbed rho *ᵥ psi)) (i, k) =
      rho * (B k *ᵥ psi) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply]
  simp [uniformEmbed]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A common zero eigenvector of the input terms is fixed by the actual
controlled oracle after embedding in the uniform doubled ancilla. -/
theorem ground_oracle_fixed (Proj : K → Matrix I I ℂ) (psi : I → ℂ)
    (hground : ∀ k, Proj k *ᵥ psi = 0) :
    lazyOracle Proj *ᵥ (uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi) =
      uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi := by
  funext row
  rcases row with ⟨i, k, b⟩
  rw [lazyOracle, blockDiagonal_uniform, uniformEmbed_mulVec]
  cases b <;> simp [lazyBlocks, termReflection, Matrix.sub_mulVec,
    Matrix.smul_mulVec, hground, Matrix.one_mulVec]

/-- The explicit embedding lies in the range of the ancilla projection. -/
theorem ground_projection_fixed (hK : 0 < Fintype.card K) (psi : I → ℂ) :
    lazyP *ᵥ (uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi) =
      uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi := by
  let J := uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K))
  change (J * Jᴴ) *ᵥ (J *ᵥ psi) = J *ᵥ psi
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec psi Jᴴ J]
  rw [show Jᴴ * J = 1 from lazyEmbed_isometry hK, Matrix.one_mulVec]

/-- The actual repaired amplified Hamiltonian annihilates every lifted
common ground vector, for every choice of the penalty. -/
theorem ground_amplified_zero (Proj : K → Matrix I I ℂ)
    (hK : 0 < Fintype.card K) (psi : I → ℂ)
    (hground : ∀ k, Proj k *ᵥ psi = 0) (delta : ℂ) :
    doubledHamiltonian Proj delta *ᵥ
      (uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi) = 0 := by
  have hU := ground_oracle_fixed Proj psi hground
  have hP := ground_projection_fixed hK psi
  simp only [doubledHamiltonian, doubledProjectionDifference, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hU, hP, Matrix.one_mulVec,
    sub_self, smul_zero, add_zero]

end

end Qatlib.Papers.SpectralGap11.MainResults
