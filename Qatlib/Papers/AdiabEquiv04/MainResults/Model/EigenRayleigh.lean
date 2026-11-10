/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.AdiabaticDefs
import Qatlib.Papers.AdiabEquiv04.MainResults.Model.SpectralBasics
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.AdiabEquiv04.MainResults.Model

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def eigVec (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (j : ι) : ι → ℂ :=
  fun i => hA.eigenvectorUnitary i j

theorem eigVec_eq_basis (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (j : ι) :
    eigVec A hA j = ⇑(hA.eigenvectorBasis j) := by
  funext i
  rw [eigVec, ← Matrix.IsHermitian.eigenvectorUnitary_col_eq (hA := hA)]
  rfl

theorem mulVec_eigVec (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (j : ι) :
    A *ᵥ eigVec A hA j = fun i => (hA.eigenvalues j : ℂ) * eigVec A hA j i := by
  have hb := eigVec_eq_basis A hA j
  conv_lhs => rw [hb]
  rw [hA.mulVec_eigenvectorBasis j]
  funext i
  rw [hb]
  simp only [Pi.smul_apply, Complex.real_smul]

theorem unitary_mul_star (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ) * star (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
  exact mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2

theorem unitary_mulVec_star (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ
      ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ ψ) = ψ := by
  rw [mulVec_mulVec, unitary_mul_star, one_mulVec]

theorem unitary_mulVec_eq_sum (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (v : ι → ℂ) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ v = ∑ j, v j • eigVec A hA j := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, eigVec]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem star_unitary_mulVec_apply (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) (j : ι) :
    ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ ψ) j =
      (star (eigVec A hA j)) ⬝ᵥ ψ := by
  simp only [Matrix.mulVec, dotProduct, eigVec, Pi.star_apply, Matrix.star_apply]

theorem spectral_mulVec (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) :
    A *ᵥ ψ = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ
        ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ ψ)) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, mulVec_mulVec, Matrix.mul_assoc]

theorem mulVec_spectral_sum (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) :
    A *ᵥ ψ = ∑ j, ((hA.eigenvalues j : ℂ) * ((star (eigVec A hA j)) ⬝ᵥ ψ)) • eigVec A hA j := by
  rw [spectral_mulVec A hA ψ]
  have hc : ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ ψ) =
      fun j => (star (eigVec A hA j)) ⬝ᵥ ψ := by
    funext j; exact star_unitary_mulVec_apply A hA ψ j
  rw [hc]
  have hd : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ
        (fun j => (star (eigVec A hA j)) ⬝ᵥ ψ)) =
      fun j => (hA.eigenvalues j : ℂ) * ((star (eigVec A hA j)) ⬝ᵥ ψ) := by
    funext j
    rw [mulVec_diagonal]
    rfl
  rw [hd, unitary_mulVec_eq_sum]

theorem dot_star_eigVec (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) (j : ι) :
    (star ψ) ⬝ᵥ eigVec A hA j = star ((star (eigVec A hA j)) ⬝ᵥ ψ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem dotProduct_star_spectral (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) :
    (star ψ) ⬝ᵥ (A *ᵥ ψ) =
      ∑ j, (hA.eigenvalues j : ℂ) * ((Complex.normSq ((star (eigVec A hA j)) ⬝ᵥ ψ) : ℝ) : ℂ) := by
  rw [mulVec_spectral_sum A hA ψ, dotProduct_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dotProduct_smul, dot_star_eigVec A hA ψ j, smul_eq_mul]
  set c : ℂ := (star (eigVec A hA j)) ⬝ᵥ ψ
  have hcc : c * star c = ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.star_def]
    exact Complex.mul_conj c
  calc (hA.eigenvalues j : ℂ) * c * star c
      = (hA.eigenvalues j : ℂ) * (c * star c) := by ring
    _ = (hA.eigenvalues j : ℂ) * ((Complex.normSq c : ℝ) : ℂ) := by rw [hcc]

theorem rayleigh_spectral (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) :
    ((star ψ) ⬝ᵥ (A *ᵥ ψ)).re =
      ∑ j, hA.eigenvalues j * Complex.normSq ((star (eigVec A hA j)) ⬝ᵥ ψ) := by
  rw [dotProduct_star_spectral A hA ψ, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.mul_re]
  simp

omit [DecidableEq ι] in

theorem normSq_eq_re_dotProduct (ψ : ι → ℂ) :
    (∑ i, Complex.normSq (ψ i)) = ((star ψ) ⬝ᵥ ψ).re := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := ψ i))
  simpa [Pi.star_apply, Complex.star_def] using! h.symm

theorem parseval_eigVec (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) :
    ∑ j, Complex.normSq ((star (eigVec A hA j)) ⬝ᵥ ψ) =
      ∑ i, Complex.normSq (ψ i) := by
  have hψ : ψ = ∑ j, ((star (eigVec A hA j)) ⬝ᵥ ψ) • eigVec A hA j := by
    calc ψ = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ
          ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ ψ) :=
          (unitary_mulVec_star A hA ψ).symm
      _ = ∑ j, ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ ψ) j • eigVec A hA j :=
          unitary_mulVec_eq_sum A hA _
      _ = ∑ j, ((star (eigVec A hA j)) ⬝ᵥ ψ) • eigVec A hA j :=
          Finset.sum_congr rfl (fun j _ => by rw [star_unitary_mulVec_apply])
  have hkey : (star ψ) ⬝ᵥ ψ =
      ∑ j, ((Complex.normSq ((star (eigVec A hA j)) ⬝ᵥ ψ) : ℝ) : ℂ) := by
    nth_rw 2 [hψ]
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [dotProduct_smul, dot_star_eigVec A hA ψ j, smul_eq_mul]
    have hcc : ((star (eigVec A hA j)) ⬝ᵥ ψ) * star ((star (eigVec A hA j)) ⬝ᵥ ψ) =
        ((Complex.normSq ((star (eigVec A hA j)) ⬝ᵥ ψ) : ℝ) : ℂ) := by
      rw [Complex.star_def]
      exact Complex.mul_conj _
    exact hcc
  have hre : ((star ψ) ⬝ᵥ ψ).re =
      ∑ j, Complex.normSq ((star (eigVec A hA j)) ⬝ᵥ ψ) := by
    rw [hkey, Complex.re_sum]
    exact Finset.sum_congr rfl (fun j _ => Complex.ofReal_re _)
  rw [← hre, normSq_eq_re_dotProduct]

theorem dot_star_eigVec_eigVec (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (j k : ι) :
    (star (eigVec A hA j)) ⬝ᵥ eigVec A hA k = if j = k then 1 else 0 := by
  have hU : (star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have h := congrFun (congrFun hU j) k
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  simpa [dotProduct, eigVec, Pi.star_apply] using h

theorem normSq_eigVec (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (j : ι) :
    ∑ i, Complex.normSq (eigVec A hA j i) = 1 := by
  have hp := parseval_eigVec A hA (eigVec A hA j)
  rw [← hp, Finset.sum_eq_single j]
  · rw [dot_star_eigVec_eigVec, if_pos rfl, Complex.normSq_one]
  · intro k _ hk
    rw [dot_star_eigVec_eigVec, if_neg hk, Complex.normSq_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem rayleigh_eigVec (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (j : ι) :
    ((star (eigVec A hA j)) ⬝ᵥ (A *ᵥ eigVec A hA j)).re = hA.eigenvalues j := by
  rw [rayleigh_spectral A hA (eigVec A hA j), Finset.sum_eq_single j]
  · rw [dot_star_eigVec_eigVec, if_pos rfl, Complex.normSq_one, mul_one]
  · intro k _ hk
    rw [dot_star_eigVec_eigVec, if_neg hk, Complex.normSq_zero, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

def eigIdx (ι : Type) [Fintype ι] : ι ≃ Fin (Fintype.card ι) :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm

theorem eigenvalues_eq_eigenvalues₀ (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (j : ι) :
    hA.eigenvalues j = hA.eigenvalues₀ (eigIdx ι j) := rfl

theorem groundEnergy_le_eigenvalues (H : Hamiltonian ι) (h : 0 < Fintype.card ι) (j : ι) :
    groundEnergy H h ≤ H.herm.eigenvalues j := by
  rw [groundEnergy, eigvals]
  exact H.herm.eigenvalues₀_antitone (Nat.le_sub_one_of_lt (eigIdx ι j).isLt)

theorem exists_eigenvalues_eq_groundEnergy (H : Hamiltonian ι) (h : 0 < Fintype.card ι) :
    ∃ j : ι, H.herm.eigenvalues j = groundEnergy H h := by
  refine ⟨eigIdx ι |>.symm ⟨Fintype.card ι - 1, by omega⟩, ?_⟩
  rw [eigenvalues_eq_eigenvalues₀, Equiv.apply_symm_apply, groundEnergy, eigvals]

theorem fin_le_pred_of_ne_top {n : ℕ} (hn : 2 ≤ n) (x : Fin n)
    (hx : x ≠ ⟨n - 1, by omega⟩) : x ≤ ⟨n - 2, by omega⟩ := by
  rw [Fin.le_def]
  show x.val ≤ n - 2
  have hv : x.val ≠ n - 1 := fun hv => hx (Fin.ext hv)
  have hlt := x.isLt
  omega

theorem secondLowestEnergy_le_eigenvalues (H : Hamiltonian ι) (h2 : 2 ≤ Fintype.card ι)
    (j : ι) (hj : eigIdx ι j ≠ ⟨Fintype.card ι - 1, by omega⟩) :
    secondLowestEnergy H h2 ≤ H.herm.eigenvalues j := by
  have hx := fin_le_pred_of_ne_top h2 (eigIdx ι j) hj
  have he := H.herm.eigenvalues₀_antitone hx
  rw [secondLowestEnergy, eigvals]
  exact he

theorem groundEnergy_le_secondLowest (H : Hamiltonian ι) (h2 : 2 ≤ Fintype.card ι) :
    groundEnergy H (by omega) ≤ secondLowestEnergy H h2 := by
  have hx : (⟨Fintype.card ι - 2, by omega⟩ : Fin (Fintype.card ι)) ≤
      ⟨Fintype.card ι - 1, by omega⟩ := by
    rw [Fin.le_def]; show Fintype.card ι - 2 ≤ Fintype.card ι - 1; omega
  have he := H.herm.eigenvalues₀_antitone hx
  rw [groundEnergy, secondLowestEnergy, eigvals]
  exact he

theorem groundEnergy_le_rayleigh (H : Hamiltonian ι) (h : 0 < Fintype.card ι)
    (ψ : ι → ℂ) (hψ : IsNormalized ψ) :
    groundEnergy H h ≤ rayleigh H.mat ψ := by
  have hspec := rayleigh_spectral H.mat H.herm ψ
  have hpar := parseval_eigVec H.mat H.herm ψ
  have hnorm : ∑ j, Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ) = 1 := by
    rw [hpar]; exact hψ
  rw [show rayleigh H.mat ψ =
    ∑ j, H.herm.eigenvalues j * Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ)
    from hspec]
  calc groundEnergy H h
      = groundEnergy H h * 1 := (mul_one _).symm
    _ = groundEnergy H h * ∑ j, Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ) := by
          rw [hnorm]
    _ = ∑ j, groundEnergy H h * Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ j, H.herm.eigenvalues j * Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ) :=
          Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (groundEnergy_le_eigenvalues H h j) (Complex.normSq_nonneg _))

theorem exists_groundVec (H : Hamiltonian ι) (h : 0 < Fintype.card ι) :
    ∃ ψ : ι → ℂ, IsGroundVector H ψ := by
  obtain ⟨j, hj⟩ := exists_eigenvalues_eq_groundEnergy H h
  refine ⟨eigVec H.mat H.herm j, ?_, ?_⟩
  · show normSq (eigVec H.mat H.herm j) = 1
    exact normSq_eigVec H.mat H.herm j
  · intro φ hφ
    rw [show rayleigh H.mat (eigVec H.mat H.herm j) = H.herm.eigenvalues j
      from rayleigh_eigVec H.mat H.herm j, hj]
    exact groundEnergy_le_rayleigh H h φ hφ

theorem eigVec_expansion (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (ψ : ι → ℂ) :
    ψ = ∑ k, ((star (eigVec A hA k)) ⬝ᵥ ψ) • eigVec A hA k := by
  calc ψ = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ
        ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ ψ) :=
        (unitary_mulVec_star A hA ψ).symm
    _ = ∑ j, ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ ψ) j • eigVec A hA j :=
        unitary_mulVec_eq_sum A hA _
    _ = ∑ j, ((star (eigVec A hA j)) ⬝ᵥ ψ) • eigVec A hA j :=
        Finset.sum_congr rfl (fun j _ => by rw [star_unitary_mulVec_apply])

theorem rayleigh_of_groundVector (H : Hamiltonian ι) (h : 0 < Fintype.card ι)
    (ψ : ι → ℂ) (hψ : IsGroundVector H ψ) :
    rayleigh H.mat ψ = groundEnergy H h := by
  obtain ⟨j, hj⟩ := exists_eigenvalues_eq_groundEnergy H h
  have hφn : IsNormalized (eigVec H.mat H.herm j) := normSq_eigVec H.mat H.herm j
  have hφr : rayleigh H.mat (eigVec H.mat H.herm j) = groundEnergy H h := by
    rw [show rayleigh H.mat (eigVec H.mat H.herm j) = H.herm.eigenvalues j
      from rayleigh_eigVec H.mat H.herm j, hj]
  exact le_antisymm (hφr ▸ hψ.2 _ hφn) (groundEnergy_le_rayleigh H h ψ hψ.1)

theorem groundVector_coeffs_vanish (H : Hamiltonian ι) (h : 0 < Fintype.card ι)
    (ψ : ι → ℂ) (hψ : IsGroundVector H ψ) (k : ι)
    (hk : groundEnergy H h < H.herm.eigenvalues k) :
    (star (eigVec H.mat H.herm k)) ⬝ᵥ ψ = 0 := by
  have hr := rayleigh_of_groundVector H h ψ hψ
  have hspec := rayleigh_spectral H.mat H.herm ψ
  have hsum1 : ∑ j, Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ) = 1 := by
    rw [parseval_eigVec H.mat H.herm ψ]; exact hψ.1
  have hg : ∑ j, H.herm.eigenvalues j * Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ)
      = groundEnergy H h := by rw [← hspec]; exact hr
  have hzero : ∑ j, (H.herm.eigenvalues j - groundEnergy H h) *
      Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ) = 0 := by
    have h1 : ∑ j, (H.herm.eigenvalues j - groundEnergy H h) *
        Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ)
        = (∑ j, H.herm.eigenvalues j * Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ))
          - ∑ j, groundEnergy H h * Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => sub_mul _ _ _)
    rw [h1, hg, ← Finset.mul_sum, hsum1, mul_one, sub_self]
  have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ (H.herm.eigenvalues j - groundEnergy H h) *
      Complex.normSq ((star (eigVec H.mat H.herm j)) ⬝ᵥ ψ) :=
    fun j _ => mul_nonneg (sub_nonneg.mpr (groundEnergy_le_eigenvalues H h j))
      (Complex.normSq_nonneg _)
  have hterm : (H.herm.eigenvalues k - groundEnergy H h) *
      Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ ψ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero k (Finset.mem_univ k)
  have hpos : 0 < H.herm.eigenvalues k - groundEnergy H h := sub_pos.mpr hk
  have hn0 : Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ ψ) = 0 := by
    rcases mul_eq_zero.mp hterm with hh | hh
    · exact absurd hh (ne_of_gt hpos)
    · exact hh
  exact Complex.normSq_eq_zero.mp hn0

omit [DecidableEq ι] in

theorem dotProduct_star_smul (c : ℂ) (u v : ι → ℂ) :
    (star (c • u)) ⬝ᵥ v = star c * ((star u) ⬝ᵥ v) := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, star_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem secondLowest_le_rayleigh_of_orth_ground (H : Hamiltonian ι)
    (h2 : 2 ≤ Fintype.card ι) (ξ w : ι → ℂ)
    (hξ : IsGroundVector H ξ) (hw : IsNormalized w) (horth : (star ξ) ⬝ᵥ w = 0) :
    secondLowestEnergy H h2 ≤ rayleigh H.mat w := by
  have hg := groundEnergy_le_secondLowest H h2
  rcases eq_or_lt_of_le hg with hEq | hLt
  · rw [← hEq]
    exact groundEnergy_le_rayleigh H (by omega) w hw
  · set jl : ι := eigIdx ι |>.symm ⟨Fintype.card ι - 1, by omega⟩ with hjl
    have hjl_eig : eigIdx ι jl = ⟨Fintype.card ι - 1, by omega⟩ := by
      rw [hjl]; exact Equiv.apply_symm_apply _ _
    have hjl_val : H.herm.eigenvalues jl = groundEnergy H (by omega) := by
      rw [eigenvalues_eq_eigenvalues₀, hjl_eig]
      show H.herm.eigenvalues₀ (⟨Fintype.card ι - 1, by omega⟩ : Fin (Fintype.card ι)) =
        eigvals H ⟨Fintype.card ι - 1, by omega⟩
      rw [eigvals]
    have hcoef : ∀ k ∈ Finset.univ.erase jl,
        (star (eigVec H.mat H.herm k)) ⬝ᵥ ξ = 0 := by
      intro k hk
      have hne : k ≠ jl := Finset.ne_of_mem_erase hk
      apply groundVector_coeffs_vanish H (by omega) ξ hξ k
      rw [← hjl_val]
      have hne' : eigIdx ι k ≠ ⟨Fintype.card ι - 1, by omega⟩ := by
        intro he
        apply hne
        apply (eigIdx ι).injective
        rw [he, hjl_eig]
      exact lt_of_lt_of_le (hjl_val ▸ hLt) (secondLowestEnergy_le_eigenvalues H h2 k hne')
    have hξe : ξ = ((star (eigVec H.mat H.herm jl)) ⬝ᵥ ξ) • eigVec H.mat H.herm jl := by
      conv_lhs => rw [eigVec_expansion H.mat H.herm ξ]
      rw [Finset.sum_eq_single jl]
      · intro k _ hk
        rw [hcoef k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩), zero_smul]
      · intro hj; exact absurd (Finset.mem_univ jl) hj
    have hn1 : Complex.normSq ((star (eigVec H.mat H.herm jl)) ⬝ᵥ ξ) = 1 := by
      have hp := parseval_eigVec H.mat H.herm ξ
      have h1 : ∑ k, Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ ξ) = 1 := by
        rw [hp]; exact hξ.1
      rw [← h1, Finset.sum_eq_single jl]
      · intro k _ hk
        rw [hcoef k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩), Complex.normSq_zero]
      · intro hj; exact absurd (Finset.mem_univ jl) hj
    have hcj : ((star (eigVec H.mat H.herm jl)) ⬝ᵥ ξ) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hn1; exact zero_ne_one hn1
    have hcw : ((star (eigVec H.mat H.herm jl)) ⬝ᵥ w) = 0 := by
      have hcalc : star ξ ⬝ᵥ w = star (((star (eigVec H.mat H.herm jl)) ⬝ᵥ ξ)) *
          ((star (eigVec H.mat H.herm jl)) ⬝ᵥ w) := by
        conv_lhs => rw [hξe]
        rw [dotProduct_star_smul]
      have hz : star (((star (eigVec H.mat H.herm jl)) ⬝ᵥ ξ)) *
          ((star (eigVec H.mat H.herm jl)) ⬝ᵥ w) = 0 := by
        rw [← hcalc]; exact horth
      have hsc : star (((star (eigVec H.mat H.herm jl)) ⬝ᵥ ξ)) ≠ 0 := by
        intro h; exact hcj (star_eq_zero.mp h)
      exact (mul_eq_zero.mp hz).resolve_left hsc
    have hnw : Complex.normSq ((star (eigVec H.mat H.herm jl)) ⬝ᵥ w) = 0 := by
      rw [hcw, Complex.normSq_zero]
    have hsum1w : ∑ k, Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ w) = 1 := by
      rw [parseval_eigVec H.mat H.herm w]; exact hw
    have hspecw := rayleigh_spectral H.mat H.herm w
    rw [show rayleigh H.mat w = ∑ k, H.herm.eigenvalues k *
      Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ w) from hspecw]
    have hsplit : ∑ k, H.herm.eigenvalues k * Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ w)
        = ∑ k ∈ Finset.univ.erase jl, H.herm.eigenvalues k *
            Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ w) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ jl), hnw, mul_zero, add_zero]
    rw [hsplit]
    have hsumErase : ∑ k ∈ Finset.univ.erase jl,
        Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ w) = 1 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ jl), hsum1w, hnw, sub_zero]
    calc secondLowestEnergy H h2
        = secondLowestEnergy H h2 * 1 := (mul_one _).symm
      _ = secondLowestEnergy H h2 * ∑ k ∈ Finset.univ.erase jl,
            Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ w) := by rw [hsumErase]
      _ = ∑ k ∈ Finset.univ.erase jl, secondLowestEnergy H h2 *
            Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ w) := by rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.univ.erase jl, H.herm.eigenvalues k *
            Complex.normSq ((star (eigVec H.mat H.herm k)) ⬝ᵥ w) := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            have hne : k ≠ jl := Finset.ne_of_mem_erase hk
            have hne' : eigIdx ι k ≠ ⟨Fintype.card ι - 1, by omega⟩ := by
              intro he
              apply hne
              apply (eigIdx ι).injective
              rw [he, hjl_eig]
            exact mul_le_mul_of_nonneg_right (secondLowestEnergy_le_eigenvalues H h2 k hne')
              (Complex.normSq_nonneg _)

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem dotProduct_star_mulVec_left {m n : Type} [Fintype m] [Fintype n]
    (V : Matrix m n ℂ) (ξ : n → ℂ) (w : m → ℂ) :
    (star ξ) ⬝ᵥ (Vᴴ *ᵥ w) = (star (V *ᵥ ξ)) ⬝ᵥ w := by
  rw [dotProduct_mulVec, vecMul_conjTranspose, star_star]

omit [DecidableEq ι] in

theorem isometry_mulVec_mulVec (V : Matrix ι σ ℂ) (hV : Vᴴ * V = 1) (ξ : σ → ℂ) :
    Vᴴ *ᵥ (V *ᵥ ξ) = ξ := by
  rw [mulVec_mulVec, hV, one_mulVec]

omit [DecidableEq ι] in

theorem normSq_isometry (V : Matrix ι σ ℂ) (hV : Vᴴ * V = 1) (ξ : σ → ℂ) :
    normSq (V *ᵥ ξ) = normSq ξ := by
  unfold normSq
  rw [normSq_eq_re_dotProduct, normSq_eq_re_dotProduct]
  congr 1
  rw [← dotProduct_star_mulVec_left V ξ (V *ᵥ ξ), isometry_mulVec_mulVec V hV]

theorem rayleigh_isometry (V : Matrix ι σ ℂ) (hV : Vᴴ * V = 1) (H : Hamiltonian ι) (ξ : σ → ℂ) :
    rayleigh (restrict V H hV).mat ξ = rayleigh H.mat (V *ᵥ ξ) := by
  unfold rayleigh restrict
  simp only [← mulVec_mulVec]
  rw [dotProduct_star_mulVec_left]

omit [DecidableEq σ] in

theorem rayleigh_compressed_zero (H₂ : Hamiltonian ι) (V : Matrix ι σ ℂ)
    (hzero : Vᴴ * H₂.mat * V = 0) (ξ : σ → ℂ) : rayleigh H₂.mat (V *ᵥ ξ) = 0 := by
  unfold rayleigh
  have h : (star (V *ᵥ ξ)) ⬝ᵥ (H₂.mat *ᵥ (V *ᵥ ξ))
      = (star ξ) ⬝ᵥ ((Vᴴ * H₂.mat * V) *ᵥ ξ) := by
    rw [← dotProduct_star_mulVec_left V ξ (H₂.mat *ᵥ (V *ᵥ ξ))]
    simp only [← mulVec_mulVec]
  rw [h, hzero, zero_mulVec, dotProduct_zero, Complex.zero_re]

theorem ground_add_le_ground_restrict (V : Matrix ι σ ℂ) (hV : Vᴴ * V = 1)
    (H₁ H₂ : Hamiltonian ι) (hzero : Vᴴ * H₂.mat * V = 0)
    (hcardS : 0 < Fintype.card σ) (hcard : 0 < Fintype.card ι) :
    groundEnergy (H₁.add H₂) hcard ≤ groundEnergy (restrict V H₁ hV) hcardS := by
  obtain ⟨ξ, hξ⟩ := exists_groundVec (restrict V H₁ hV) hcardS
  have hone : IsNormalized (V *ᵥ ξ) := by
    show normSq (V *ᵥ ξ) = 1
    rw [normSq_isometry V hV, hξ.1]
  have hray : rayleigh (H₁.add H₂).mat (V *ᵥ ξ) = groundEnergy (restrict V H₁ hV) hcardS := by
    have hmat : (H₁.add H₂).mat = H₁.mat + H₂.mat := rfl
    rw [hmat, rayleigh_add, rayleigh_compressed_zero H₂ V hzero ξ, add_zero,
      ← rayleigh_isometry V hV H₁ ξ, ← rayleigh_of_groundVector (restrict V H₁ hV) hcardS ξ hξ]
  rw [← hray]
  exact groundEnergy_le_rayleigh (H₁.add H₂) hcard (V *ᵥ ξ) hone

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
