/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma5EndpointsStat

/-!
# General-phase amplitude amplification at the endpoints

The phase-modified amplification iterate has explicit action on the good and
bad components of a prepared unit vector. This proof includes success
probabilities zero and one, where one component vanishes, and combines them
with the interior case. The formulation uses a Hilbert basis and a closed good
subspace, without assuming the Hilbert space is finite dimensional.

The two-component identities come from [BrassardEtAl2002]; see
[Brassard et al., Lemma 5][BrassardEtAl2002] for the general-phase formulas.
-/
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore

/-- The generalized phase iterate maps the zero vector to zero. -/
private lemma bhmt5_endpoint_iterate_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H ≃ₗᵢ[ℂ] H) (e₀ : H) (G : ClosedSubmodule ℂ H) (φ ϕ : ℝ) :
    amplitudeEstimationPhaseIterate A e₀ G φ ϕ 0 = 0 := by
  have hp0 : G.toSubmodule.starProjection 0 = 0 := map_zero _
  simp only [amplitudeEstimationPhaseIterate, hp0, smul_zero, add_zero, map_zero,
    inner_zero_right, mul_zero, zero_smul, neg_zero]

/-- The squared norm of the orthogonal projection of a unit vector onto a closed subspace is at
most one. -/
private lemma bhmt5_endpoint_norm_sq_le_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ClosedSubmodule ℂ H) (ψ : H) (hψ : ‖ψ‖ = 1) :
    ‖G.toSubmodule.starProjection ψ‖ ^ 2 ≤ 1 := by
  have hn : ‖G.toSubmodule.starProjection ψ‖ ≤ ‖ψ‖ :=
    Submodule.norm_starProjection_apply_le G.toSubmodule ψ
  rw [hψ] at hn
  rw [pow_two]
  exact (mul_le_mul hn hn (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

/-- The general-phase formulas of [Brassard et al., Lemma 5][BrassardEtAl2002]
hold also when the good-component squared norm is zero or one. -/
theorem lemma5_endpoints_unrestricted :
    ∀ (ι H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (basis : HilbertBasis ι ℂ H) (zeroIndex : ι)
      (A : H ≃ₗᵢ[ℂ] H) (χ : ι → Bool) (φ ϕ : ℝ),
    0 ≤ φ → φ < 2 * Real.pi →
    0 ≤ ϕ → ϕ < 2 * Real.pi →
    let G := amplitudeEstimationGoodSubspace basis χ;
    let ψ : H := A (basis zeroIndex);
    let ψ₁ : H := G.toSubmodule.starProjection ψ;
    let ψ₀ : H := ψ - ψ₁;
    let a : ℝ := ‖ψ₁‖ ^ 2;
    let p : ℂ := Complex.exp ((φ : ℂ) * Complex.I);
    let q : ℂ := Complex.exp ((ϕ : ℂ) * Complex.I);
    let Q : H → H := amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ;
    Q ψ₁ =
        (q * ((1 - p) * (a : ℂ) - 1)) • ψ₁ +
        (q * (1 - p) * (a : ℂ)) • ψ₀ ∧
    Q ψ₀ =
        ((1 - p) * (1 - (a : ℂ))) • ψ₁ -
        ((1 - p) * (a : ℂ) + p) • ψ₀ := by
  intro ι H _ _ _ basis zeroIndex A χ φ ϕ _hφ₀ _hφ₂π _hϕ₀ _hϕ₂π
  (try dsimp only)
  have hψ : ‖A (basis zeroIndex)‖ = 1 :=
    (A.norm_map _).trans (basis.orthonormal.norm_eq_one zeroIndex)
  set G := amplitudeEstimationGoodSubspace basis χ with hGdef
  set ψ := A (basis zeroIndex) with hψdef
  set ψ₁ := G.toSubmodule.starProjection ψ with hψ₁def
  set ψ₀ := ψ - ψ₁ with hψ₀def
  set a : ℝ := ‖ψ₁‖ ^ 2 with hadef
  set p : ℂ := Complex.exp ((φ : ℂ) * Complex.I) with hpdef
  set q : ℂ := Complex.exp ((ϕ : ℂ) * Complex.I) with hqdef
  obtain ⟨hP₁, _hP₀, hinner₁, _hinner₀⟩ :=
    zoo_amplitude_estimation_general_phase_action_projection G ψ hψ
  change G.toSubmodule.starProjection ψ₁ = ψ₁ at hP₁
  change inner ℂ ψ ψ₁ = ((‖ψ₁‖ ^ 2 : ℝ) : ℂ) at hinner₁
  have hale : a ≤ 1 := by
    rw [hadef]
    exact bhmt5_endpoint_norm_sq_le_one G ψ hψ
  by_cases hzero : a = 0
  · have h1 : ψ₁ = 0 := by
      have hn : ‖ψ₁‖ = 0 := (pow_eq_zero_iff (two_ne_zero)).mp (by rw [← hadef, hzero])
      exact norm_eq_zero.mp hn
    have hψ₀ψ : ψ₀ = ψ := by rw [hψ₀def, h1, sub_zero]
    have hQ0 : amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ 0 = 0 :=
      bhmt5_endpoint_iterate_zero A (basis zeroIndex) G φ ϕ
    have hPψ : G.toSubmodule.starProjection ψ = 0 := by rw [← hψ₁def, h1]
    have he : A.symm ψ = basis zeroIndex := A.symm_apply_apply _
    have hin : inner ℂ (basis zeroIndex) (basis zeroIndex) = 1 := by
      rw [@inner_self_eq_norm_sq_to_K ℂ, basis.orthonormal.norm_eq_one zeroIndex]
      norm_num
    have hkey : amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ ψ
        = -(p • ψ) := by
      show -(A (A.symm (ψ + (q - 1) • G.toSubmodule.starProjection ψ) +
          ((p - 1) * inner ℂ (basis zeroIndex)
            (A.symm (ψ + (q - 1) • G.toSubmodule.starProjection ψ))) • basis zeroIndex))
        = -(p • ψ)
      rw [hPψ, smul_zero, add_zero, he, hin, mul_one]
      have hco : basis zeroIndex + (p - 1) • basis zeroIndex = p • basis zeroIndex := by
        module
      rw [hco, map_smul, ← hψdef]
    rw [h1]
    constructor
    · rw [hQ0, hzero]
      simp
    · rw [hψ₀ψ, hkey, hzero]
      simp
  by_cases hone : a = 1
  · have hsq1 : ‖ψ₁‖ ^ 2 = 1 := by rw [← hadef, hone]
    have hn1 : ‖ψ₁‖ = 1 := by
      have hfac : (‖ψ₁‖ - 1) * (‖ψ₁‖ + 1) = 0 := by
        have hexp : (‖ψ₁‖ - 1) * (‖ψ₁‖ + 1) = ‖ψ₁‖ ^ 2 - 1 := by ring
        rw [hexp, hsq1]
        ring
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h (by nlinarith [norm_nonneg ψ₁])
    have hin11 : inner ℂ ψ₁ ψ₁ = 1 := by
      rw [@inner_self_eq_norm_sq_to_K ℂ, hn1]
      norm_num
    have hinψ1 : inner ℂ ψ ψ₁ = 1 := by
      rw [hinner₁, hn1]
      norm_num
    have hin1ψ : inner ℂ ψ₁ ψ = 1 := by
      rw [← inner_conj_symm, hinψ1]
      norm_num
    have hinψψ : inner ℂ ψ ψ = 1 := by
      rw [@inner_self_eq_norm_sq_to_K ℂ, hψ]
      norm_num
    have hnorm0 : ‖ψ - ψ₁‖ ^ 2 = 0 := by
      have hin2 : inner ℂ (ψ - ψ₁) (ψ - ψ₁) = 0 := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right, hinψψ, hinψ1, hin1ψ,
          hin11]
        ring
      have hcast : ((‖ψ - ψ₁‖ : ℝ) : ℂ) ^ 2 = 0 :=
        (@inner_self_eq_norm_sq_to_K ℂ _ _ _ _ (ψ - ψ₁)).symm.trans hin2
      have hreal : ‖ψ - ψ₁‖ = 0 := by
        have hcz : ((‖ψ - ψ₁‖ : ℝ) : ℂ) = 0 :=
          (pow_eq_zero_iff (two_ne_zero)).mp hcast
        have : Complex.ofReal (‖ψ - ψ₁‖) = Complex.ofReal 0 := by
          rw [Complex.ofReal_zero]
          exact hcz
        exact Complex.ofReal_injective this
      rw [hreal]
      norm_num
    have hzerobad : ψ₀ = 0 := by
      rw [hψ₀def]
      exact norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hnorm0)
    have hψ₁ψ : ψ₁ = ψ := (sub_eq_zero.mp hzerobad).symm
    have hQ0 : amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ 0 = 0 :=
      bhmt5_endpoint_iterate_zero A (basis zeroIndex) G φ ϕ
    have hPψ : G.toSubmodule.starProjection ψ = ψ := by rw [← hψ₁def, hψ₁ψ]
    have he : A.symm ψ = basis zeroIndex := A.symm_apply_apply _
    have hin : inner ℂ (basis zeroIndex) (basis zeroIndex) = 1 := by
      rw [@inner_self_eq_norm_sq_to_K ℂ, basis.orthonormal.norm_eq_one zeroIndex]
      norm_num
    have hkey : amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ ψ
        = -((p * q) • ψ) := by
      have hco : ψ + (q - 1) • ψ = q • ψ := by module
      have hco2 : q • (basis zeroIndex) + ((p - 1) * q) • (basis zeroIndex)
          = (p * q) • (basis zeroIndex) := by module
      show -(A (A.symm (ψ + (q - 1) • G.toSubmodule.starProjection ψ) +
          ((p - 1) * inner ℂ (basis zeroIndex)
            (A.symm (ψ + (q - 1) • G.toSubmodule.starProjection ψ))) • basis zeroIndex))
        = -((p * q) • ψ)
      rw [hPψ, hco, A.symm.map_smul, he, inner_smul_right, hin, mul_one, hco2, map_smul,
        ← hψdef]
    constructor
    · rw [hψ₁ψ, hkey, hzerobad, hone]
      simp only [Complex.ofReal_one, smul_zero, add_zero]
      module
    · rw [hzerobad, hQ0, hone]
      simp
  · have hann : (0:ℝ) ≤ a := by rw [hadef]; exact sq_nonneg ‖ψ₁‖
    have hpos : 0 < a := by
      rcases eq_or_lt_of_le hann with h | h
      · exact absurd h.symm hzero
      · exact h
    have hlt : a < 1 := by
      rcases eq_or_lt_of_le hale with h | h
      · exact absurd h hone
      · exact h
    exact @zoo_amplitude_estimation_general_phase_action ι H _ _ _ basis zeroIndex A χ
      φ ϕ _hφ₀ _hφ₂π _hϕ₀ _hϕ₂π hpos hlt

/-- The general phase component action satisfies `Lemma5EndpointsSpec.expected`, including zero
and unit success probability. -/
theorem lemma5_endpoints_unrestricted_contract :
    Lemma5EndpointsSpec.expected :=
  lemma5_endpoints_unrestricted

end Qatlib.Concepts.AmplitudeCore.AmplifyCore
