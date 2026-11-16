/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.SpectralAmp17.MainResults.PhaseBoundary

open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

/-- An odd natural number cannot satisfy the legacy pointwise complexity relation with zero budget. -/
theorem odd_no_zero_budget :
    ¬ ∃ n : ℕ, Odd n ∧ bigOConst (n : ℝ) 0 := by
  rintro ⟨n, hn, hcost⟩
  obtain ⟨C, hC, hbound⟩ := hcost
  have hnpos : 0 < n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  simp only [mul_zero] at hbound
  linarith

/-- The Gaussian-based degree budget in the source erf claims vanishes at the allowed tolerance one. -/
theorem erf_unit_tolerance_impossible (k : ℝ) :
    ¬ ∃ n : ℕ, Odd n ∧
      bigOConst (n : ℝ)
        (Real.sqrt ((k ^ 2 + Real.log (1 / (1 : ℝ))) * Real.log (1 / (1 : ℝ)))) := by
  simpa using odd_no_zero_budget

/-- The source arcsine degree claim also has an impossible zero budget at tolerance one. -/
theorem arcsin_unit_tolerance_impossible :
    ¬ ∃ n : ℕ, Odd n ∧ bigOConst (n : ℝ) (Real.log (1 / (1 : ℝ))) := by
  simpa using odd_no_zero_budget

/-- The legacy amplitude predicate forgets the target-vector phase and therefore admits both signs. -/
theorem hasAmplitude_neg {d : ℕ} [NeZero d]
    {G : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ} {lam : ℝ}
    (h : HasAmplitude G lam) : HasAmplitude G (-lam) := by
  obtain ⟨v, hv, hact⟩ := h
  refine ⟨-v, ?_, ?_⟩
  · simpa only [Pi.neg_apply, norm_neg] using hv
  · intro i
    rw [hact i]
    simp

/-- The identity matrix on one system coordinate satisfies the source amplitude predicate at one. -/
theorem identity_hasAmplitude :
    HasAmplitude (1 : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ) 1 := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · norm_num
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi, Matrix.one_apply]

/-- A single scalar cannot equal the odd identity response at both source amplitude witnesses. -/
theorem identity_no_odd_response :
    ¬ ∃ z : ℂ, ∀ lam : ℝ,
      HasAmplitude (1 : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ) lam →
        z = (((Polynomial.X : Polynomial ℝ).eval lam : ℝ) : ℂ) := by
  rintro ⟨z, hz⟩
  have hp := hz 1 identity_hasAmplitude
  have hn := hz (-1) (hasAmplitude_neg identity_hasAmplitude)
  norm_num at hp hn
  have hbad : (1 : ℂ) = -1 := hp.symm.trans hn
  norm_num at hbad

/-- The identity polynomial meets the degree, oddness, and unit-interval premises of source Theorem 8. -/
theorem identity_polynomial_hypotheses :
    IsOddPoly (Polynomial.X : Polynomial ℝ) ∧
      (Polynomial.X : Polynomial ℝ).natDegree ≤ 2 * 0 + 1 ∧
      (∀ lam ∈ Set.Icc (-1 : ℝ) 1,
        (Polynomial.X : Polynomial ℝ).eval lam ^ 2 ≤ 1) := by
  refine ⟨?_, by simp, ?_⟩
  · intro x
    simp
  · intro lam hlam
    simp only [Polynomial.eval_X]
    rcases hlam with ⟨hlo, hhi⟩
    nlinarith

/-- Zero and the identity polynomial also meet the two-polynomial premises of source Theorem 10. -/
theorem identity_flexible_hypotheses :
    IsOddPoly (0 : Polynomial ℝ) ∧ IsOddPoly (Polynomial.X : Polynomial ℝ) ∧
      (0 : Polynomial ℝ).natDegree ≤ 2 * 0 + 1 ∧
      (Polynomial.X : Polynomial ℝ).natDegree ≤ 2 * 0 + 1 ∧
      (∀ lam ∈ Set.Icc (-1 : ℝ) 1,
        (0 : Polynomial ℝ).eval lam ^ 2 + (Polynomial.X : Polynomial ℝ).eval lam ^ 2 ≤ 1) ∧
      (∀ lam : ℝ, 1 ≤ lam →
        1 ≤ (0 : Polynomial ℝ).eval lam ^ 2 + (Polynomial.X : Polynomial ℝ).eval lam ^ 2) := by
  refine ⟨?_, identity_polynomial_hypotheses.1, by simp, by simp, ?_, ?_⟩
  · intro x
    simp
  · intro lam hlam
    simpa using identity_polynomial_hypotheses.2.2 lam hlam
  · intro lam hlam
    simp only [Polynomial.eval_zero, Polynomial.eval_X, zero_pow (by norm_num : 2 ≠ 0), zero_add]
    nlinarith

/-- The legacy model admits an explicit half-amplitude matrix on a one-coordinate system. -/
theorem half_hasAmplitude :
    HasAmplitude (((1 / 2 : ℂ)) •
      (1 : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ)) (1 / 2) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · norm_num
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi, Matrix.smul_apply]

/-- The two radius-one-eighth disks around positive and negative one-half do not intersect. -/
theorem half_disks_disjoint (z : ℂ) :
    ¬ (‖z - (1 / 2 : ℂ)‖ ≤ (1 / 8 : ℝ) ∧
      ‖z - (-1 / 2 : ℂ)‖ ≤ (1 / 8 : ℝ)) := by
  rintro ⟨hp, hn⟩
  have heq : (z - (-1 / 2 : ℂ)) - (z - (1 / 2 : ℂ)) = 1 := by ring
  have htri := norm_sub_le (z - (-1 / 2 : ℂ)) (z - (1 / 2 : ℂ))
  rw [heq] at htri
  norm_num at hp hn htri
  linarith

/-- No scalar satisfies the exact necessary amplitude conclusion of source Lemma 4 at Gamma one-half. -/
theorem half_no_linear_response :
    ¬ ∃ z : ℂ, ∀ lam : ℝ, |lam| ≤ 1 / 2 →
      HasAmplitude (((1 / 2 : ℂ)) •
        (1 : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ)) lam →
      ‖z - (((lam / (2 * (1 / 2 : ℝ)) : ℝ)) : ℂ)‖ ≤
        |lam| / (2 * (1 / 2 : ℝ)) * (1 / 4 : ℝ) := by
  rintro ⟨z, hz⟩
  have hp := hz (1 / 2) (by norm_num) half_hasAmplitude
  have hn := hz (-(1 / 2)) (by norm_num) (hasAmplitude_neg half_hasAmplitude)
  norm_num at hp hn
  apply half_disks_disjoint z
  norm_num
  exact ⟨hp, hn⟩

end Qatlib.Papers.SpectralAmp17.MainResults.PhaseBoundary
