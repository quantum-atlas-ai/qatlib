/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.KernelLift

/-!
# The physical doubled register excludes spurious ground states

The idle branch forces a vector fixed by both register projections to be
fixed by the actual oracle. The active branches then recover the common
input-term kernel. A stacked Gram matrix connects that kernel to `sum Proj`.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.KernelBridge

open Matrix
open AmplifiedRegister
open scoped BigOperators ComplexOrder

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
/-- The uniform doubled ancilla has nonzero amplitude for nonempty term sets. -/
theorem amplitude_ne_zero (hK : 0 < Fintype.card K) : ancAmplitude (K := K) ≠ 0 := by
  have hne : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  have hn : (1 / (2 * (Fintype.card K : ℂ))) ≠ 0 := by
    exact one_div_ne_zero (mul_ne_zero (by norm_num) hne)
  intro hz
  have h := ancAmplitude_norm (K := K)
  rw [hz, star_zero, zero_mul] at h
  exact hn h.symm

/-- The actual oracle leaves the idle half of every vector unchanged. -/
theorem idle_branch (Proj : K → Matrix I I ℂ) (v : I × (K × Bool) → ℂ)
    (i : I) (k : K) : (lazyOracle Proj *ᵥ v) (i, k, true) = v (i, k, true) := by
  simp [lazyOracle, Matrix.mulVec, dotProduct,
    Matrix.blockDiagonal_apply, Fintype.sum_prod_type, lazyBlocks]
  simp [Matrix.one_apply]

/-- A vector in both projection ranges must be fixed by the oracle, because
the idle branch fixes the original system amplitudes. -/
theorem intersection_oracle_fixed (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k) (hK : 0 < Fintype.card K)
    (v : I × (K × Bool) → ℂ) (hP : lazyP *ᵥ v = v)
    (hQ : (lazyOracle Proj * lazyP * lazyOracle Proj) *ᵥ v = v) :
    lazyOracle Proj *ᵥ v = v := by
  let U := lazyOracle Proj
  let J := uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K))
  let psi := Jᴴ *ᵥ v
  let phi := Jᴴ *ᵥ (U *ᵥ v)
  have hUU : U * U = 1 := lazyOracle_sq Proj hproj
  have hUPU : U * (U * lazyP * U) = lazyP * U := by
    calc
      U * (U * lazyP * U) = (U * U) * lazyP * U := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.one_mul]
  have hPU : lazyP *ᵥ (U *ᵥ v) = U *ᵥ v := by
    have h := congrArg (fun x => U *ᵥ x) hQ
    rw [Matrix.mulVec_mulVec, hUPU, ← Matrix.mulVec_mulVec] at h
    exact h
  have hv : v = J *ᵥ psi := by
    dsimp [psi, J]
    rw [Matrix.mulVec_mulVec]
    exact hP.symm
  have hUv : U *ᵥ v = J *ᵥ phi := by
    dsimp [phi]
    rw [Matrix.mulVec_mulVec]
    exact hPU.symm
  obtain ⟨k⟩ : Nonempty K := Fintype.card_pos_iff.1 hK
  have hphi : phi = psi := by
    funext i
    apply mul_left_cancel₀ (amplitude_ne_zero hK)
    calc ancAmplitude (K := K) * phi i = (J *ᵥ phi) (i, k, true) :=
        (uniformEmbed_mulVec _ _ _ _).symm
      _ = (U *ᵥ v) (i, k, true) := congrFun hUv.symm _
      _ = v (i, k, true) := idle_branch Proj v i k
      _ = ancAmplitude (K := K) * psi i := by
        rw [hv]
        exact uniformEmbed_mulVec _ _ _ _
  rw [hUv, hphi, ← hv]

/-- Recovering the original vector from the projection and fixed-oracle
relations yields the common zero eigenspace of all actual input terms. -/
theorem fixed_oracle_common_kernel (Proj : K → Matrix I I ℂ)
    (hK : 0 < Fintype.card K) (v : I × (K × Bool) → ℂ)
    (hP : lazyP *ᵥ v = v) (hU : lazyOracle Proj *ᵥ v = v) :
    ∀ k, Proj k *ᵥ
      ((uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)))ᴴ *ᵥ v) = 0 := by
  let J := uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K))
  let psi := Jᴴ *ᵥ v
  have hv : v = J *ᵥ psi := by
    dsimp [psi, J]
    rw [Matrix.mulVec_mulVec]
    exact hP.symm
  intro k
  have hreflect : termReflection (Proj k) *ᵥ psi = psi := by
    funext i
    apply mul_left_cancel₀ (amplitude_ne_zero hK)
    have h := congrFun hU (i, k, false)
    rw [hv, lazyOracle, blockDiagonal_uniform, uniformEmbed_mulVec] at h
    simpa only [lazyBlocks, Bool.false_eq_true, ↓reduceIte] using h
  rw [termReflection, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hreflect
  have hz : (2 : ℂ) • (Proj k *ᵥ psi) = 0 := sub_eq_self.1 hreflect
  exact (smul_eq_zero.1 hz).resolve_left (by norm_num)

/-- Stack the actual input terms as a rectangular matrix. -/
def termStack (Proj : K → Matrix I I ℂ) : Matrix (I × K) I ℂ :=
  fun row col => Proj row.2 row.1 col

omit [DecidableEq I] [DecidableEq K] in
/-- The Gram matrix of the stacked terms is their sum for orthogonal
projectors, linking the common kernel to the actual input Hamiltonian. -/
theorem termStack_gram (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k)
    (hHerm : ∀ k, (Proj k).IsHermitian) :
    (termStack Proj)ᴴ * termStack Proj = ∑ k, Proj k := by
  have hsum : ∑ k, (Proj k)ᴴ * Proj k = ∑ k, Proj k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [(hHerm k).eq, hproj k]
  rw [← hsum]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, termStack,
    Fintype.sum_prod_type, Matrix.sum_apply]
  rw [Finset.sum_comm]

omit [DecidableEq I] [DecidableEq K] in
/-- The input sum has exactly the common kernel of its projector terms. -/
theorem sum_kernel_iff (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k)
    (hHerm : ∀ k, (Proj k).IsHermitian) (psi : I → ℂ) :
    (∑ k, Proj k) *ᵥ psi = 0 ↔ ∀ k, Proj k *ᵥ psi = 0 := by
  rw [← termStack_gram Proj hproj hHerm,
    Matrix.conjTranspose_mul_self_mulVec_eq_zero]
  constructor
  · intro h k
    funext i
    exact congrFun h (i, k)
  · intro h
    funext row
    exact congrFun (h row.2) row.1

/-- The actual amplified zero eigenspace is exactly the embedded input zero
eigenspace. The idle oracle branch excludes the old endpoint degeneracy. -/
theorem actual_kernel_iff (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k)
    (hHerm : ∀ k, (Proj k).IsHermitian) (hK : 0 < Fintype.card K)
    (delta : ℂ) (hd : delta ≠ 0) (hLd : (Fintype.card K : ℂ) + delta ≠ 0)
    (v : I × (K × Bool) → ℂ) :
    doubledHamiltonian Proj delta *ᵥ v = 0 ↔ ∃ psi : I → ℂ,
      (∑ k, Proj k) *ᵥ psi = 0 ∧
        uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi = v := by
  let U := lazyOracle Proj
  let P := lazyP (I := I) (K := K)
  let Q := U * P * U
  have hU : U * U = 1 := lazyOracle_sq Proj hproj
  have hP : P * P = P := lazyP_sq hK
  have hPH : P.IsHermitian := lazyP_hermitian
  have hUH : U.IsHermitian := lazyOracle_hermitian Proj hHerm
  have hQ : Q * Q = Q := by
    dsimp [Q]
    calc
      (U * P * U) * (U * P * U) = U * P * (U * U) * P * U := by
        simp only [Matrix.mul_assoc]
      _ = U * (P * P) * U := by
        rw [hU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = U * P * U := by rw [hP]
  have hQH : Q.IsHermitian := by
    change (U * P * U)ᴴ = U * P * U
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hUH.eq, hPH.eq,
      Matrix.mul_assoc]
  have hL : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  constructor
  · intro hzero
    have hpair : KernelLift.pairH P Q (Fintype.card K : ℂ) delta *ᵥ v = 0 := hzero
    obtain ⟨hp, hq⟩ := (KernelLift.pairH_kernel P Q _ delta hP hQ hPH hQH
      hL hd hLd v).1 hpair
    have hu := intersection_oracle_fixed Proj hproj hK v hp hq
    let psi := (uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)))ᴴ *ᵥ v
    refine ⟨psi, (sum_kernel_iff Proj hproj hHerm psi).2
      (fixed_oracle_common_kernel Proj hK v hp hu), ?_⟩
    dsimp [psi]
    rw [Matrix.mulVec_mulVec]
    exact hp
  · rintro ⟨psi, hpsi, hv⟩
    rw [← hv]
    exact ground_amplified_zero Proj hK psi ((sum_kernel_iff Proj hproj hHerm psi).1
      hpsi) delta

end

end Qatlib.Papers.SpectralGap11.MainResults.KernelBridge
