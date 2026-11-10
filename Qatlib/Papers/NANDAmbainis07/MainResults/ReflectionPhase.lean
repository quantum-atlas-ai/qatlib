/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NANDAmbainis07.MainResults

open scoped ComplexConjugate ComplexInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def refl (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) : V :=
  v - 2 • S.starProjection v

lemma refl_def (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) :
    refl S v = v - 2 • S.starProjection v := rfl

lemma refl_eq_neg_reflection (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) :
    refl S v = -(S.reflection v) := by
  rw [refl_def, Submodule.reflection_apply, neg_sub]

lemma norm_refl (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) :
    ‖refl S v‖ = ‖v‖ := by
  rw [refl_eq_neg_reflection, norm_neg]
  exact LinearIsometryEquiv.norm_map S.reflection v

lemma refl_self_adjoint (S : Submodule ℂ V) [S.HasOrthogonalProjection] (x y : V) :
    ⟪refl S x, y⟫ = ⟪x, refl S y⟫ := by
  rw [refl_def, refl_def, two_smul, two_smul, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, Submodule.inner_starProjection_left_eq_right S x y]

lemma refl_refl (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) :
    refl S (refl S v) = v := by
  have hidem : S.starProjection (S.starProjection v) = S.starProjection v :=
    Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem v)
  have hproj : S.starProjection (refl S v) = -S.starProjection v := by
    rw [refl_def, two_smul, map_sub, map_add, hidem]
    abel
  rw [refl_def, hproj, smul_neg, refl_def, two_smul]
  abel

lemma refl_inner (S : Submodule ℂ V) [S.HasOrthogonalProjection] (x y : V) :
    ⟪refl S x, refl S y⟫ = ⟪x, y⟫ := by
  rw [refl_self_adjoint, refl_refl]

lemma inner_self_eq (v : V) : ⟪v, v⟫ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow ‖v‖ 2).symm

lemma inner_starProjection_eq (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) :
    ⟪v, S.starProjection v⟫ = ((‖S.starProjection v‖ ^ 2 : ℝ) : ℂ) := by
  have hidem : S.starProjection (S.starProjection v) = S.starProjection v :=
    Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem v)
  calc ⟪v, S.starProjection v⟫
      = ⟪v, S.starProjection (S.starProjection v)⟫ := by rw [hidem]
    _ = ⟪S.starProjection v, S.starProjection v⟫ := by
          rw [Submodule.inner_starProjection_left_eq_right]
    _ = ((‖S.starProjection v‖ ^ 2 : ℝ) : ℂ) := inner_self_eq _

lemma refl_inner_self_eq (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) :
    ⟪v, refl S v⟫ = ((‖v‖ ^ 2 : ℝ) : ℂ) - 2 * ((‖S.starProjection v‖ ^ 2 : ℝ) : ℂ) := by
  rw [refl_def, two_smul, inner_sub_right, inner_add_right, inner_starProjection_eq, inner_self_eq,
    ← two_mul]

lemma refl_inner_self_re (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) :
    (⟪v, refl S v⟫).re = ‖v‖ ^ 2 - 2 * ‖S.starProjection v‖ ^ 2 := by
  rw [refl_inner_self_eq, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re,
    Complex.ofReal_im]
  norm_num

lemma composite_re_of_orth (S1 S2 : Submodule ℂ V) [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] {p q : V} (hp : p ∈ S1) (hq : q ∈ S1ᗮ) :
    (⟪p + q, refl S2 (refl S1 (p + q))⟫).re
      = ‖q‖ ^ 2 - ‖p‖ ^ 2
        + 2 * (‖S2.starProjection p‖ ^ 2 - ‖S2.starProjection q‖ ^ 2) := by
  have hpq : ⟪p, q⟫ = 0 := by
    rw [Submodule.mem_orthogonal'] at hq
    rw [← inner_conj_symm, hq p hp, map_zero]
  have hqp : ⟪q, p⟫ = 0 := by rw [← inner_conj_symm, hpq, map_zero]
  have hpp : ⟪p, p⟫ = ((‖p‖ ^ 2 : ℝ) : ℂ) := inner_self_eq p
  have hqq : ⟪q, q⟫ = ((‖q‖ ^ 2 : ℝ) : ℂ) := inner_self_eq q
  have hP1p : S1.starProjection p = p := Submodule.starProjection_eq_self_iff.mpr hp
  have hP1q : S1.starProjection q = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := S1)).mpr hq
  have hU1 : refl S1 (p + q) = q - p := by
    rw [refl_def, two_smul, map_add, hP1p, hP1q]
    abel
  have hU2 : refl S2 (q - p) = (q - p) - (S2.starProjection q - S2.starProjection p)
      - (S2.starProjection q - S2.starProjection p) := by
    rw [refl_def, two_smul, map_sub]
    abel
  have hcomp : ⟪p + q, refl S2 (refl S1 (p + q))⟫
      = ⟪p + q, (q - p) - (S2.starProjection q - S2.starProjection p)
          - (S2.starProjection q - S2.starProjection p)⟫ := by
    rw [hU1, hU2]
  have e1 : (⟪p + q, q - p⟫).re = ‖q‖ ^ 2 - ‖p‖ ^ 2 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, hpq, hqp, hpp, hqq, Complex.add_re,
      Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
    ring
  have hAB : (⟪p + q, S2.starProjection q - S2.starProjection p⟫).re
      = ‖S2.starProjection q‖ ^ 2 - ‖S2.starProjection p‖ ^ 2 := by
    have h1 : ⟪p, S2.starProjection q⟫ = conj ⟪q, S2.starProjection p⟫ := by
      rw [← inner_conj_symm, Submodule.inner_starProjection_left_eq_right]
    have hAq : ⟪q, S2.starProjection q⟫ = ((‖S2.starProjection q‖ ^ 2 : ℝ) : ℂ) :=
      inner_starProjection_eq S2 q
    have hBp : ⟪p, S2.starProjection p⟫ = ((‖S2.starProjection p‖ ^ 2 : ℝ) : ℂ) :=
      inner_starProjection_eq S2 p
    have h : ⟪p + q, S2.starProjection q - S2.starProjection p⟫
        = ((‖S2.starProjection q‖ ^ 2 : ℝ) : ℂ) - ((‖S2.starProjection p‖ ^ 2 : ℝ) : ℂ)
          + (conj ⟪q, S2.starProjection p⟫ - ⟪q, S2.starProjection p⟫) := by
      rw [inner_add_left, inner_sub_right, inner_sub_right, h1, hAq, hBp]
      ring
    rw [h, Complex.add_re, Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re,
      Complex.conj_re]
    ring
  rw [hcomp, inner_sub_right, inner_sub_right, Complex.sub_re, Complex.sub_re, e1, hAB]
  ring

lemma refl_inner_self_eq' (S : Submodule ℂ V) [S.HasOrthogonalProjection] (v : V) :
    ⟪v, refl S v⟫ = ((‖v‖ ^ 2 - 2 * ‖S.starProjection v‖ ^ 2 : ℝ) : ℂ) := by
  rw [refl_inner_self_eq]
  push_cast
  ring

lemma eigen_inner_relation (S1 S2 : Submodule ℂ V) [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] {ψ : V} {lam : ℂ}
    (heig : refl S2 (refl S1 ψ) = lam • ψ) :
    ⟪ψ, refl S1 ψ⟫ = lam * conj ⟪ψ, refl S2 ψ⟫ := by
  calc ⟪ψ, refl S1 ψ⟫ = conj ⟪refl S1 ψ, ψ⟫ := (inner_conj_symm _ _).symm
    _ = conj ⟪refl S2 (refl S1 ψ), refl S2 ψ⟫ := by
          rw [refl_inner S2]
    _ = conj ⟪lam • ψ, refl S2 ψ⟫ := by rw [heig]
    _ = conj (conj lam * ⟪ψ, refl S2 ψ⟫) := by rw [inner_smul_left]
    _ = lam * conj ⟪ψ, refl S2 ψ⟫ := by rw [map_mul, Complex.conj_conj]

lemma eigen_norm_one {S1 S2 : Submodule ℂ V} [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] {ψ : V} (hψ : ψ ≠ 0) {lam : ℂ}
    (heig : refl S2 (refl S1 ψ) = lam • ψ) : ‖lam‖ = 1 := by
  have hψn : (0 : ℝ) < ‖ψ‖ := norm_pos_iff.mpr hψ
  have h : ‖lam • ψ‖ = ‖ψ‖ := by
    rw [← heig, norm_refl, norm_refl]
  rw [norm_smul] at h
  exact mul_right_cancel₀ hψn.ne' (by rw [one_mul]; exact h)

lemma refl_refl_inner_re (S1 S2 : Submodule ℂ V) [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] (ψ : V) :
    (⟪ψ, refl S2 (refl S1 ψ)⟫).re
      = ‖ψ - S1.starProjection ψ‖ ^ 2 - ‖S1.starProjection ψ‖ ^ 2
        + 2 * (‖S2.starProjection (S1.starProjection ψ)‖ ^ 2
          - ‖S2.starProjection (ψ - S1.starProjection ψ)‖ ^ 2) := by
  have h := composite_re_of_orth S1 S2 (p := S1.starProjection ψ)
    (q := ψ - S1.starProjection ψ) (S1.starProjection_apply_mem ψ)
    (S1.sub_starProjection_mem_orthogonal ψ)
  rwa [show S1.starProjection ψ + (ψ - S1.starProjection ψ) = ψ from by abel] at h

lemma eigen_re_le (S1 S2 : Submodule ℂ V) [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] {ε : ℝ} (hε1 : ε ≤ 1)
    (hsep : ∀ x ∈ S1, ε * ‖x‖ ^ 2 ≤ ‖x - S2.starProjection x‖ ^ 2)
    (hdisj : S1 ⊓ S2 = ⊥) {ψ : V} (hψU : ψ ∈ S1 ⊔ S2) (hψ : ψ ≠ 0) {lam : ℂ}
    (heig : refl S2 (refl S1 ψ) = lam • ψ) : lam.re ≤ 1 - ε := by
  have hψpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by
    have := norm_pos_iff.mpr hψ
    positivity
  have hP2 : ‖S2.starProjection (S1.starProjection ψ)‖ ^ 2
      ≤ (1 - ε) * ‖S1.starProjection ψ‖ ^ 2 := by
    have hx := hsep (S1.starProjection ψ) (S1.starProjection_apply_mem ψ)
    have hpy := S2.norm_sq_eq_add_norm_sq_starProjection (S1.starProjection ψ)
    rw [Submodule.starProjection_orthogonal_val] at hpy
    nlinarith [hx, hpy]
  have hinrel := eigen_inner_relation S1 S2 heig
  by_cases hq : ⟪ψ, refl S2 ψ⟫ = 0
  · have hU1zero : ⟪ψ, refl S1 ψ⟫ = 0 := by rw [hinrel, hq, map_zero, mul_zero]
    have hpn : ‖S1.starProjection ψ‖ ^ 2 = ‖ψ‖ ^ 2 / 2 := by
      have h := refl_inner_self_re S1 ψ
      rw [hU1zero] at h
      norm_num at h
      linarith
    have hqn : ‖ψ - S1.starProjection ψ‖ ^ 2 = ‖ψ‖ ^ 2 / 2 := by
      have h := S1.norm_sq_eq_add_norm_sq_starProjection ψ
      rw [Submodule.starProjection_orthogonal_val] at h
      linarith
    have hray : (⟪ψ, refl S2 (refl S1 ψ)⟫).re = lam.re * ‖ψ‖ ^ 2 := by
      rw [heig, inner_smul_right, inner_self_eq, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    have hrepr := refl_refl_inner_re S1 S2 ψ
    rw [hray] at hrepr
    have hnonneg : 0 ≤ ‖S2.starProjection (ψ - S1.starProjection ψ)‖ ^ 2 := sq_nonneg _
    nlinarith [hrepr, hpn, hqn, hP2, hnonneg, hψpos]
  · have hlam1 := eigen_norm_one (S1 := S1) (S2 := S2) hψ heig
    have hconjq : conj ⟪ψ, refl S2 ψ⟫ = ((‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [refl_inner_self_eq', Complex.conj_ofReal]
    have hpreal : ⟪ψ, refl S1 ψ⟫ = ((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2 : ℝ) : ℂ) :=
      refl_inner_self_eq' S1 ψ
    have hqne : ((‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hq
      have h2 : conj ⟪ψ, refl S2 ψ⟫ = 0 := by rw [hconjq, h]
      exact (map_eq_zero (starRingEnd ℂ)).mp h2
    have hlameq : lam = (((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2)
        * (‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
      have h : ((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2 : ℝ) : ℂ)
          = lam * ((‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hconjq, ← hpreal]; exact hinrel
      have h' : ((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2 : ℝ) : ℂ)
            * (((‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2 : ℝ) : ℂ))⁻¹ = lam := by
        rw [h, mul_assoc, mul_inv_cancel₀ hqne, mul_one]
      rw [← h']
      simp [Complex.ofReal_mul, Complex.ofReal_inv]
    have hlampm : lam = 1 ∨ lam = -1 := by
      have hsq : ((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2)
          * (‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2)⁻¹) ^ 2 = 1 := by
        have h2 : Complex.normSq lam = 1 := by
          rw [Complex.normSq_eq_norm_sq, hlam1]
          norm_num
        rw [hlameq, Complex.normSq_ofReal] at h2
        simpa [pow_two] using h2
      have hfac : (((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2)
          * (‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2)⁻¹) - 1)
          * (((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2)
          * (‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2)⁻¹) + 1) = 0 := by
        nlinarith [hsq]
      rcases mul_eq_zero.mp hfac with h | h
      · left
        rw [hlameq, show ((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2)
          * (‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2)⁻¹) = 1 by linarith]
        norm_num
      · right
        rw [hlameq, show ((‖ψ‖ ^ 2 - 2 * ‖S1.starProjection ψ‖ ^ 2)
          * (‖ψ‖ ^ 2 - 2 * ‖S2.starProjection ψ‖ ^ 2)⁻¹) = -1 by linarith]
        norm_num
    rcases hlampm with h | h
    · have hcontra : False := by
        have h1 : refl S1 ψ = refl S2 ψ := by
          have h' : refl S2 (refl S1 ψ) = ψ := by rw [heig, h, one_smul]
          calc refl S1 ψ = refl S2 (refl S2 (refl S1 ψ)) := by rw [refl_refl]
            _ = refl S2 ψ := by rw [h']
        rw [refl_def, refl_def] at h1
        have h2 : 2 • S1.starProjection ψ = 2 • S2.starProjection ψ := by
          have hc := congrArg (fun z => ψ - z) h1
          simpa using hc
        have h2' : (2 : ℂ) • S1.starProjection ψ = (2 : ℂ) • S2.starProjection ψ := by
          rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Nat.cast_smul_eq_nsmul,
            Nat.cast_smul_eq_nsmul]
          exact h2
        have hp_eq : S1.starProjection ψ = S2.starProjection ψ := by
          have hc := congrArg (fun z => (2 : ℂ)⁻¹ • z) h2'
          simpa [smul_smul] using hc
        have hpbot : S1.starProjection ψ = 0 := by
          have h1 := S1.starProjection_apply_mem ψ
          have h2 : S1.starProjection ψ ∈ S2 := hp_eq ▸ S2.starProjection_apply_mem ψ
          have hmem : S1.starProjection ψ ∈ S1 ⊓ S2 := ⟨h1, h2⟩
          rw [hdisj] at hmem
          exact hmem
        have hpbot2 : S2.starProjection ψ = 0 := hp_eq ▸ hpbot
        have horth : ψ ∈ (S1 ⊔ S2)ᗮ := by
          rw [← Submodule.inf_orthogonal]
          exact ⟨(Submodule.starProjection_apply_eq_zero_iff (K := S1)).mp hpbot,
            (Submodule.starProjection_apply_eq_zero_iff (K := S2)).mp hpbot2⟩
        have hzz : ⟪ψ, ψ⟫ = 0 := (Submodule.mem_orthogonal' (K := (S1 ⊔ S2)) ψ).mp horth ψ hψU
        exact hψ (inner_self_eq_zero.mp hzz)
      exact absurd hcontra (by simp)
    · rw [h]
      norm_num
      linarith

theorem eigenphase_bounds (S1 S2 : Submodule ℂ V) [S1.HasOrthogonalProjection]
    [S2.HasOrthogonalProjection] {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hdisj : S1 ⊓ S2 = ⊥)
    (hsep : ∀ x ∈ S1, ε * ‖x‖ ^ 2 ≤ ‖x - S2.starProjection x‖ ^ 2)
    {ψ : V} (hψU : ψ ∈ S1 ⊔ S2) (hψ : ψ ≠ 0) {lam : ℂ}
    (heig : refl S2 (refl S1 ψ) = lam • ψ) :
    ∃ θ : ℝ, θ ∈ Set.Icc (Real.sqrt ε) (2 * Real.pi - Real.sqrt ε) ∧
      lam = Complex.exp ((θ : ℂ) * Complex.I) := by
  have hre : lam.re ≤ 1 - ε := eigen_re_le (S1 := S1) (S2 := S2) hε1 hsep hdisj hψU hψ heig
  have hsqrt_le_pi : Real.sqrt ε ≤ Real.pi := by
    have h1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
    have h2 : (1 : ℝ) ≤ Real.pi := by linarith [Real.one_le_pi_div_two, Real.pi_pos]
    linarith
  have hcos_le : lam.re ≤ Real.cos (Real.sqrt ε) := by
    have h1 : 1 - ε ≤ Real.cos (Real.sqrt ε) := by
      have h := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt ε)
      rw [Real.sq_sqrt hε0] at h
      linarith
    linarith
  have hlam1 : ‖lam‖ = 1 := eigen_norm_one (S1 := S1) (S2 := S2) hψ heig
  have hexp : lam = Complex.exp ((lam.arg : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I lam
    rw [hlam1] at h
    simpa using h.symm
  have hcos : Real.cos lam.arg = lam.re := by
    nth_rw 2 [hexp]
    rw [Complex.exp_ofReal_mul_I_re]
  have hargle : lam.arg ≤ Real.pi := Complex.arg_le_pi lam
  by_cases harg : 0 ≤ lam.arg
  · refine ⟨lam.arg, ⟨?_, ?_⟩, hexp⟩
    · by_contra hcon
      rw [not_le] at hcon
      have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi harg hsqrt_le_pi hcon
      linarith
    · linarith
  · rw [not_le] at harg
    refine ⟨2 * Real.pi + lam.arg, ⟨?_, ?_⟩, ?_⟩
    · have h1 : -Real.pi < lam.arg := Complex.neg_pi_lt_arg lam
      linarith
    · have hge : Real.sqrt ε ≤ -lam.arg := by
        by_contra hcon
        rw [not_le] at hcon
        have hc2 : Real.cos (-lam.arg) = lam.re := by rw [Real.cos_neg]; exact hcos
        have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (x := -lam.arg) (y := Real.sqrt ε)
          (by linarith) hsqrt_le_pi hcon
        rw [hc2] at hlt
        linarith
      linarith
    · have hexp2 : Complex.exp ((((2 * Real.pi + lam.arg : ℝ)) : ℂ) * Complex.I)
          = Complex.exp ((lam.arg : ℂ) * Complex.I) := by
        have hsplit : (((2 * Real.pi + lam.arg : ℝ)) : ℂ) * Complex.I
            = ((2 * Real.pi : ℝ) : ℂ) * Complex.I + (lam.arg : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hsplit, Complex.exp_add]
        have hpi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
          simp
        rw [hpi, one_mul]
      rw [hexp2, ← hexp]

end Qatlib.Papers.NANDAmbainis07.MainResults
