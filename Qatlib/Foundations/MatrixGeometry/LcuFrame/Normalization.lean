/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.LcuFrame.Compression
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame
set_option autoImplicit false
noncomputable section
open Matrix
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

omit [Fintype J] [DecidableEq J] [DecidableEq I] in

theorem inner_self (ψ : State I) : Inner ψ ψ = ((∑ i, ‖ψ i‖^2 : ℝ) : ℂ) := by
  rw [inner_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

omit [Fintype J] [DecidableEq J] [DecidableEq I] in

theorem normalized_iff_inner (ψ : State I) : Normalized ψ ↔ Inner ψ ψ=1 := by
  rw [inner_self]
  exact_mod_cast (Iff.rfl : (∑ i, ‖ψ i‖^2)=1 ↔ (∑ i, ‖ψ i‖^2)=1)

omit [Fintype J] [DecidableEq J] in

theorem applySys_one (ψ : State (J × I)) : applySys (1 : Matrix I I ℂ) ψ = ψ := by
  ext ⟨j,i⟩
  change ((1 : Matrix I I ℂ) *ᵥ (fun x => ψ (j,x))) i=ψ (j,i)
  rw [Matrix.one_mulVec]

theorem phiPM_normalized (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (hφ : Normalized φ)
    (hPH : ∀ j, (P j)ᴴ=P j) (hP2 : ∀ j, P j*P j=1)
    (heig : ham β P *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    Normalized (phiP β P φ E) ∧ Normalized (phiM β P φ E) := by
  have hγ : Gamma β (fun _ => 1)=1 := by simpa [Gamma] using hβ
  have hd : (1-E^2 : ℝ) ≠ 0 := by nlinarith
  have hi : Inner φ φ=1 := (normalized_iff_inner φ).1 hφ
  have hh := expectation_eq8 β P (1 : Matrix I I ℂ) (fun _ => 1) φ E hβ hφ
    (by simp) (by simp) hPH hP2 (by intro j; simpa using hP2 j)
    (by intro j; exact Or.inl rfl) heig hE
  simp only [applySys_one, hγ, div_self hd] at hh
  norm_num at hh
  exact ⟨(normalized_iff_inner _).2 (by simpa only [hi] using hh.1),
    (normalized_iff_inner _).2 (by simpa only [hi] using hh.2)⟩

theorem signal_amplitudes (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (heig : ham β P *ᵥ φ=(E : ℂ) • φ) :
    (embedding (I := I) β)ᴴ *ᵥ phiP β P φ E = invSqrt2 • φ ∧
      (embedding (I := I) β)ᴴ *ᵥ phiM β P φ E = invSqrt2 • φ := by
  change (embedding (I := I) β)ᴴ *ᵥ (invSqrt2 • (phi0 β φ + Complex.I • phi1 β P φ E)) = _ ∧
    (embedding (I := I) β)ᴴ *ᵥ (invSqrt2 • (phi0 β φ - Complex.I • phi1 β P φ E)) = _
  simp [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub,
    embedding_adjoint_phi0 β hβ, embedding_adjoint_phi1 β P φ E hβ heig]

theorem signal_projection (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (heig : ham β P *ᵥ φ=(E : ℂ) • φ) :
    signalProjector β *ᵥ phiP β P φ E = invSqrt2 • phi0 β φ ∧
      signalProjector β *ᵥ phiM β P φ E = invSqrt2 • phi0 β φ := by
  obtain ⟨hp,hm⟩ := signal_amplitudes β P φ E hβ heig
  simp only [signalProjector, ← Matrix.mulVec_mulVec, hp, hm,
    Matrix.mulVec_smul, embedding_mulVec, and_self]

theorem invSqrt2_norm_sq : ‖invSqrt2‖^2 = (1/2 : ℝ) := by
  simp only [invSqrt2, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num

theorem signal_probability (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (hφ : Normalized φ)
    (heig : ham β P *ᵥ φ=(E : ℂ) • φ) :
    ‖toHilbert (signalProjector β *ᵥ phiP β P φ E)‖^2 = (1/2 : ℝ) ∧
      ‖toHilbert (signalProjector β *ᵥ phiM β P φ E)‖^2 = (1/2 : ℝ) := by
  obtain ⟨hp,hm⟩ := signal_projection β P φ E hβ heig
  rw [hp,hm]
  have hnorm : ∀ c : ℂ, ‖toHilbert (c • phi0 β φ)‖^2 = ‖c‖^2 := by
    intro c
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖c * phi0 β φ i‖^2)=‖c‖^2
    simp_rw [norm_mul,mul_pow]
    rw [← Finset.mul_sum, show (∑ i, ‖phi0 β φ i‖^2)=1 from phi0_normalized β φ hβ hφ, mul_one]
  rw [hnorm, invSqrt2_norm_sq]
  exact ⟨rfl,rfl⟩

end
end Qatlib.Foundations.MatrixGeometry.LcuFrame
