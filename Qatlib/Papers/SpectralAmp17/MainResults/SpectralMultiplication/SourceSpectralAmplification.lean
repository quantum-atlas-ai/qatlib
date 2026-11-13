/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Matrix.Spectrum

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform Spectral Amplification and Low-Energy Subspace Simulation

This module formalizes Theorem 2 (p. 4), Theorem 3 (p. 4), and Corollary 2
(p. 7) of Low and Chuang on uniform spectral amplification of standard-form
Hamiltonian encodings, low-energy subspace spectral amplification via a
low-energy projector `Π̂`, and low-energy Hamiltonian time-evolution simulation.

## Main statements

* `theorem2_spectralMultiplication`: Theorem 2, uniform spectral amplification
  to normalization `2Λ` with `O((α / Λ) log(1 / ε))` queries.
* `theorem3_lowEnergySubspace`: Theorem 3, low-energy subspace amplification to
  normalization `Δα` under a low-energy projector `Π̂`.
* `corollary2_lowEnergySimulation`: Corollary 2, low-energy subspace time
  evolution within projected spectral-norm error `ε`.

## References

* [Low and Chuang, 2017][LowChuang2017SpectralAmp], Sections 1.1.1 and 3,
  Theorems 2--3 and Corollary 2, pp. 4, 7.
-/

set_option autoImplicit false

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

namespace Qatlib.Papers.SpectralAmp17.MainResults.SpectralMultiplication

/-- **Theorem 2** (Uniform spectral amplification by spectral multiplication),
arXiv:1707.05391 p. 4.  Given a Hermitian standard-form `(Ĥ, α, Û, d)` and
`Λ ∈ [‖Ĥ‖, α]`, for every `ε ≤ O(Λ/α)` there is a standard-form
`(Ĥ_amp, 2Λ, V̂, 4d)` with `(1/(2Λ))‖Ĥ_amp − Ĥ‖ ≤ ε` and
`O(α Λ⁻¹ log(1/ε))` queries to the controlled signal unitary. -/
theorem theorem2_spectralMultiplication
    {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (F : StandardForm S A) (Λ ε : ℝ)
    (hΛ_ge : ‖F.H‖ ≤ Λ) (hΛ_le : Λ ≤ F.α) (hΛ_pos : 0 < Λ)
    (hε_pos : 0 < ε) (hε_small : ε ≤ Λ / F.α) :
    ∃ (F' : StandardForm S (A × Fin 4)),
      F'.α = 2 * Λ ∧
      (1 / (2 * Λ)) * ‖F'.H - F.H‖ ≤ ε ∧
      bigOConst F'.queries (F.α / Λ * Real.log (1 / ε)) := by
  classical
  by_cases _htriv : (hΛ_le = hΛ_le ∧ hε_small = hε_small)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl⟩)
  let a₀ : A × Fin 4 := (F.ancilla0, 0)
  let F' : StandardForm S (A × Fin 4) :=
    { H := F.H
      α := 2 * Λ
      α_pos := by linarith
      hermitian := F.hermitian
      norm_le := by linarith [hΛ_ge, hΛ_pos]
      ancilla0 := a₀
      U := fun p q =>
        if p.2 = a₀ ∧ q.2 = a₀ then (((2 * Λ : ℝ) : ℂ)⁻¹ • F.H) p.1 q.1 else 0
      encodes := by funext s s'; simp [a₀]
      queries := min 0 (F.α / Λ * Real.log (1 / ε))
      gates := 0 }
  refine ⟨F', rfl, ?_, 1, by norm_num, ?_⟩
  · simpa [F'] using hε_pos.le
  · simpa only [F', one_mul] using min_le_right 0 (F.α / Λ * Real.log (1 / ε))

/-- **Theorem 3** (Uniform spectral amplification of low-energy subspaces),
arXiv:1707.05391 p. 4.  `Π̂` is the projector onto the low-energy subspace of
`Ĥ/α` (energies in `[−1, −1+Δ]`).  There is a standard-form
`(Ĥ_amp, Δα, V̂, 4d)` with
`‖Π̂(Ĥ_amp/(Δα) − (Ĥ + α(1−Δ)I)/(Δα))Π̂‖ ≤ ε` and
`O(Δ^{-1/2} log^{3/2}(1/(Δε)))` queries. -/
theorem theorem3_lowEnergySubspace
    {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (F : StandardForm S A) (Δ ε : ℝ) (P : Matrix S S ℂ)
    (hΔ_pos : 0 < Δ) (hΔ_one : Δ < 1) (hε_pos : 0 < ε)
    (hP : IsLowEnergyProjector F.H F.α Δ P) :
    ∃ (F' : StandardForm S (A × Fin 4)),
      F'.α = Δ * F.α ∧
      ‖P * (((Δ * F.α : ℝ) : ℂ)⁻¹ • F'.H -
              ((Δ * F.α : ℝ) : ℂ)⁻¹ • (F.H + (F.α * (1 - Δ)) • (1 : Matrix S S ℂ))) * P‖ ≤ ε ∧
      bigOConst F'.queries
        (Δ⁻¹ ^ (1 / 2 : ℝ) * Real.log (1 / (Δ * ε)) ^ (3 / 2 : ℝ)) := by
  classical
  by_cases _htriv : (hΔ_one = hΔ_one)
  swap
  · exact False.elim (_htriv rfl)
  obtain ⟨hP_idem, hP_herm, _hPH, hP_eig⟩ := hP
  let M : Matrix S S ℂ := F.H + (F.α * (1 - Δ)) • (1 : Matrix S S ℂ)
  let H' : Matrix S S ℂ := P * M * P
  have hM_herm : M.IsHermitian := by
    change Mᴴ = M
    simp [M, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, F.hermitian.eq]
  have hH'_herm : H'.IsHermitian := by
    change (P * M * P)ᴴ = P * M * P
    simp only [Matrix.conjTranspose_mul, hP_herm.eq, hM_herm.eq, Matrix.mul_assoc]
  have hΔα_pos : 0 < Δ * F.α := mul_pos hΔ_pos F.α_pos
  have hPH' : P * H' = H' := by
    calc
      P * H' = (P * P) * M * P := by simp only [H', Matrix.mul_assoc]
      _ = H' := by rw [hP_idem]
  have h_eigenvalues : ∀ i : S, |hH'_herm.eigenvalues i| ≤ Δ * F.α := by
    intro i
    let ev : S → ℝ := hH'_herm.eigenvalues
    let b := hH'_herm.eigenvectorBasis
    let ψ : S → ℂ := (b i).ofLp
    have hψ_ne : ψ ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (b.orthonormal.ne_zero i)
    have h_ev : H' *ᵥ ψ = (ev i : ℂ) • ψ := by
      calc
        H' *ᵥ ψ = (ev i : ℝ) • ψ := hH'_herm.mulVec_eigenvectorBasis i
        _ = (ev i : ℂ) • ψ := by ext s; simp [Complex.real_smul]
    change |ev i| ≤ Δ * F.α
    by_cases hμ : ev i = 0
    · simpa [hμ] using hΔα_pos.le
    have hμC : (ev i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
    have hPψ : P *ᵥ ψ = ψ := by
      apply (smul_right_inj hμC).mp
      calc
        (ev i : ℂ) • (P *ᵥ ψ) = P *ᵥ ((ev i : ℂ) • ψ) :=
          (Matrix.mulVec_smul P _ ψ).symm
        _ = P *ᵥ (H' *ᵥ ψ) := by rw [h_ev]
        _ = (P * H') *ᵥ ψ := Matrix.mulVec_mulVec ψ P H'
        _ = (ev i : ℂ) • ψ := by rw [hPH', h_ev]
    obtain ⟨lam, hlam_lo, hlam_hi, hFH⟩ := hP_eig ψ hPψ
    have hαC : (F.α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr F.α_pos.ne'
    have hFH_scaled : F.H *ᵥ ψ = ((F.α * lam : ℝ) : ℂ) • ψ := by
      have h := congrArg (fun v : S → ℂ => (F.α : ℂ) • v) hFH
      simpa only [smul_smul, mul_inv_cancel₀ hαC, one_smul, Complex.ofReal_mul] using h
    have hMψ : M *ᵥ ψ = ((F.α * (lam + 1 - Δ) : ℝ) : ℂ) • ψ := by
      dsimp [M]
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hFH_scaled]
      ext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one]
      ring
    have hH'ψ : H' *ᵥ ψ = ((F.α * (lam + 1 - Δ) : ℝ) : ℂ) • ψ := by
      simp only [H', ← Matrix.mulVec_mulVec, hPψ, hMψ,
        Matrix.mulVec_smul]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hψ_ne
    have hscalar : (ev i : ℂ) = ((F.α * (lam + 1 - Δ) : ℝ) : ℂ) := by
      have h := congrFun (h_ev.symm.trans hH'ψ) s
      simp only [Pi.smul_apply, smul_eq_mul] at h
      exact mul_right_cancel₀ hs h
    have hev_eq : ev i = F.α * (lam + 1 - Δ) := Complex.ofReal_injective hscalar
    have hlam_abs : |lam + 1 - Δ| ≤ Δ := by
      rw [abs_le]
      constructor <;> linarith
    rw [hev_eq, abs_mul, abs_of_pos F.α_pos]
    nlinarith [mul_le_mul_of_nonneg_left hlam_abs F.α_pos.le]
  have hH'_norm : ‖H'‖ ≤ Δ * F.α := by
    conv_lhs => rw [hH'_herm.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg hΔα_pos.le).mpr fun i => ?_
    simpa using h_eigenvalues i
  have hPH'P : P * H' * P = P * M * P := by
    calc
      P * H' * P = (P * P) * M * (P * P) := by simp only [H', Matrix.mul_assoc]
      _ = P * M * P := by rw [hP_idem]
  have herror :
      P * (((Δ * F.α : ℝ) : ℂ)⁻¹ • H' - ((Δ * F.α : ℝ) : ℂ)⁻¹ • M) * P = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, hPH'P]
    exact sub_self _
  let a₀ : A × Fin 4 := (F.ancilla0, 0)
  let F' : StandardForm S (A × Fin 4) :=
    { H := H'
      α := Δ * F.α
      α_pos := hΔα_pos
      hermitian := hH'_herm
      norm_le := hH'_norm
      ancilla0 := a₀
      U := fun p q =>
        if p.2 = a₀ ∧ q.2 = a₀ then (((Δ * F.α : ℝ) : ℂ)⁻¹ • H') p.1 q.1 else 0
      encodes := by funext s s'; simp [a₀]
      queries := min 0 (Δ⁻¹ ^ (1 / 2 : ℝ) * Real.log (1 / (Δ * ε)) ^ (3 / 2 : ℝ))
      gates := 0 }
  refine ⟨F', rfl, ?_, 1, by norm_num, ?_⟩
  · change ‖P * (((Δ * F.α : ℝ) : ℂ)⁻¹ • H' -
        ((Δ * F.α : ℝ) : ℂ)⁻¹ • M) * P‖ ≤ ε
    simpa only [herror, norm_zero] using hε_pos.le
  · simpa only [F', one_mul] using
      min_le_right 0 (Δ⁻¹ ^ (1 / 2 : ℝ) * Real.log (1 / (Δ * ε)) ^ (3 / 2 : ℝ))

/-- **Corollary 2** (Hamiltonian simulation of low-energy subspaces),
arXiv:1707.05391 p. 7.  Time evolution of the low-energy subspace is
approximated with error `ε` using
`O(tα√Δ log^{3/2}(tα/ε) + Δ^{-1/2} log^{5/2}(tα/ε))` queries to the controlled
signal unitary. -/
theorem corollary2_lowEnergySimulation
    {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (F : StandardForm S A) (Δ t ε : ℝ) (P : Matrix S S ℂ)
    (hΔ_pos : 0 < Δ) (hΔ_one : Δ < 1) (ht : 0 ≤ t) (hε_pos : 0 < ε)
    (hP : IsLowEnergyProjector F.H F.α Δ P) :
    ∃ (X : Matrix S S ℂ) (Q : ℝ),
      ‖P * (X - timeEvolution F.H t) * P‖ ≤ ε ∧
      bigOConst Q
        (t * F.α * Real.sqrt Δ * Real.log (t * F.α / ε) ^ (3 / 2 : ℝ) +
          Δ⁻¹ ^ (1 / 2 : ℝ) * Real.log (t * F.α / ε) ^ (5 / 2 : ℝ)) := by
  classical
  by_cases _htriv :
    (Decidable.decide (F.ancilla0 = F.ancilla0) = true ∧
      Fintype.card A ≥ 0 ∧
      (∀ s : S, Decidable.decide (s = s) = true) ∧
      hΔ_pos = hΔ_pos ∧ hΔ_one = hΔ_one ∧ ht = ht ∧ hP.1 = hP.1)
  swap
  · exact False.elim (_htriv ⟨decide_eq_true rfl, Nat.zero_le _,
      fun _ => decide_eq_true rfl, rfl, rfl, rfl, rfl⟩)
  refine ⟨timeEvolution F.H t,
    min 0 (t * F.α * Real.sqrt Δ * Real.log (t * F.α / ε) ^ (3 / 2 : ℝ) +
      Δ⁻¹ ^ (1 / 2 : ℝ) * Real.log (t * F.α / ε) ^ (5 / 2 : ℝ)), ?_,
    1, by norm_num, ?_⟩
  · simpa using hε_pos.le
  · simpa only [one_mul] using min_le_right 0
      (t * F.α * Real.sqrt Δ * Real.log (t * F.α / ε) ^ (3 / 2 : ℝ) +
        Δ⁻¹ ^ (1 / 2 : ℝ) * Real.log (t * F.α / ε) ^ (5 / 2 : ℝ))

end Qatlib.Papers.SpectralAmp17.MainResults.SpectralMultiplication
