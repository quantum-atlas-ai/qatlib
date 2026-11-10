/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreRefined
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCore
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial
open scoped Classical BigOperators
open Qatlib.Concepts.QsvtCore.ApproxToolkit
set_option warningAsError false

noncomputable def printedRectanglePolynomial (S : Polynomial ℝ) (ε₀ t : ℝ) : Polynomial ℝ :=
  Polynomial.C ((1 - ε₀ / 2) / 2) *
    (S.comp (Polynomial.X + Polynomial.C t) +
      S.comp (Polynomial.C t - Polynomial.X)) +
    Polynomial.C (ε₀ / 2)

lemma printedRectanglePolynomial_eval (S : Polynomial ℝ) (ε₀ t x : ℝ) :
    (printedRectanglePolynomial S ε₀ t).eval x =
      ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x)) + ε₀ / 2 := by
  simp only [printedRectanglePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [Polynomial.eval_comp, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]

lemma printedRectanglePolynomial_even (S : Polynomial ℝ) (ε₀ t x : ℝ) :
    (printedRectanglePolynomial S ε₀ t).eval (-x) = (printedRectanglePolynomial S ε₀ t).eval x := by
  rw [printedRectanglePolynomial_eval, printedRectanglePolynomial_eval]
  have h1 : -x + t = t - x := by ring
  have h2 : t - (-x) = x + t := by ring
  rw [h1, h2]
  ring

lemma printedRectanglePolynomial_natDegree_le (S : Polynomial ℝ) (ε₀ t : ℝ) :
    (printedRectanglePolynomial S ε₀ t).natDegree ≤ S.natDegree := by
  have h1 : (S.comp (Polynomial.X + Polynomial.C t)).natDegree ≤ S.natDegree := by
    refine le_trans Polynomial.natDegree_comp_le ?_
    rw [natDegree_X_add_C]
    simp
  have h2 : (S.comp (Polynomial.C t - Polynomial.X)).natDegree ≤ S.natDegree := by
    refine le_trans Polynomial.natDegree_comp_le ?_
    have hsub : Polynomial.C t - Polynomial.X = -(Polynomial.X - Polynomial.C t) := by ring
    rw [hsub, Polynomial.natDegree_neg, natDegree_X_sub_C]
    simp
  have hsum : (S.comp (Polynomial.X + Polynomial.C t) +
      S.comp (Polynomial.C t - Polynomial.X)).natDegree ≤ S.natDegree :=
    le_trans (Polynomial.natDegree_add_le _ _) (max_le h1 h2)
  have hz1 : (Polynomial.C ((1 - ε₀ / 2) / 2)).natDegree ≤ 0 := by
    rw [Polynomial.natDegree_C]
  have hz2 : (Polynomial.C (ε₀ / 2)).natDegree ≤ 0 := by
    rw [Polynomial.natDegree_C]
  have hmul : (Polynomial.C ((1 - ε₀ / 2) / 2) *
      (S.comp (Polynomial.X + Polynomial.C t) +
        S.comp (Polynomial.C t - Polynomial.X))).natDegree ≤ S.natDegree :=
    le_trans Polynomial.natDegree_mul_le (by simpa using! add_le_add hz1 hsum)
  exact le_trans (Polynomial.natDegree_add_le _ _)
    (by simpa using! add_le_add hmul hz2)

theorem printedRectangle_bands {S : Polynomial ℝ} {ε₀ δ' t σ : ℝ}
    (hε0 : 0 < ε₀) (hε01 : ε₀ < 1) (hδ' : 0 < δ') (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hbudget : (1 - ε₀ / 2) * σ ≤ ε₀ / 2)
    (hS : SignApproximation S δ' σ) :
    (∀ x : ℝ, |x| ≤ 1 → |(printedRectanglePolynomial S ε₀ t).eval x| ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → -(t - δ') ≤ x → x ≤ t - δ' →
      1 - ε₀ ≤ (printedRectanglePolynomial S ε₀ t).eval x ∧
        (printedRectanglePolynomial S ε₀ t).eval x ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → (x ≤ -(t + δ') ∨ t + δ' ≤ x) →
      0 ≤ (printedRectanglePolynomial S ε₀ t).eval x ∧
        (printedRectanglePolynomial S ε₀ t).eval x ≤ ε₀) := by
  have hcpos : 0 < (1 - ε₀ / 2) / 2 := by
    have h : (1:ℝ) - ε₀ / 2 > 0 := by linarith
    linarith
  have hc : 0 ≤ (1 - ε₀ / 2) / 2 := le_of_lt hcpos
  have hε : (0:ℝ) ≤ ε₀ / 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
    have hxt : |x + t| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have htx : |t - x| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have h1 : |S.eval (x + t)| ≤ 1 := hS.1 (x + t) hxt
    have h2 : |S.eval (t - x)| ≤ 1 := hS.1 (t - x) htx
    have hsum : |S.eval (x + t)| + |S.eval (t - x)| ≤ 2 := by linarith
    rw [printedRectanglePolynomial_eval]
    calc |((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x)) + ε₀ / 2|
        ≤ |((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x))| + |ε₀ / 2| := abs_add_le _ _
      _ = |(1 - ε₀ / 2) / 2| * |S.eval (x + t) + S.eval (t - x)| + |ε₀ / 2| := by
          rw [abs_mul, abs_of_nonneg hc, abs_of_nonneg hε]
      _ ≤ ((1 - ε₀ / 2) / 2) * (|S.eval (x + t)| + |S.eval (t - x)|) + ε₀ / 2 := by
          rw [abs_of_nonneg hc, abs_of_nonneg hε]
          exact add_le_add (mul_le_mul_of_nonneg_left (abs_add_le _ _) hc) (le_refl _)
      _ ≤ ((1 - ε₀ / 2) / 2) * 2 + ε₀ / 2 := by
          exact add_le_add (mul_le_mul_of_nonneg_left hsum hc) (le_refl _)
      _ = 1 := by ring
  · intro x hx hleft hright
    have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
    have hxtpos : 0 < x + t := by linarith
    have htxpos : 0 < t - x := by linarith
    have hxtδ : δ' ≤ |x + t| := by
      rw [abs_of_nonneg (le_of_lt hxtpos)]
      linarith
    have htxδ : δ' ≤ |t - x| := by
      rw [abs_of_nonneg (le_of_lt htxpos)]
      linarith
    have hxt2 : |x + t| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have htx2 : |t - x| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have h1 := signApprox_pos hS hxt2 hxtδ hxtpos
    have h2 := signApprox_pos hS htx2 htxδ htxpos
    have h1u : S.eval (x + t) ≤ 1 := (abs_le.mp (hS.1 (x + t) hxt2)).2
    have h2u : S.eval (t - x) ≤ 1 := (abs_le.mp (hS.1 (t - x) htx2)).2
    have hsumlo : 2 - 2 * σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
    have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ 2 := by linarith
    rw [printedRectanglePolynomial_eval]
    constructor
    · have hlo : ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x)) ≥
          (1 - ε₀ / 2) - ((1 - ε₀ / 2) * σ) := by
          calc ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x))
              ≥ ((1 - ε₀ / 2) / 2) * (2 - 2 * σ) := mul_le_mul_of_nonneg_left hsumlo hc
            _ = (1 - ε₀ / 2) - ((1 - ε₀ / 2) * σ) := by ring
      have hb : (1 - ε₀ / 2) * σ ≤ ε₀ / 2 := hbudget
      linarith
    · have hhi : ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x)) ≤ 1 - ε₀ / 2 := by
          calc ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x))
              ≤ ((1 - ε₀ / 2) / 2) * 2 := mul_le_mul_of_nonneg_left hsumhi hc
            _ = 1 - ε₀ / 2 := by ring
      linarith
  · intro x hx hband
    have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
    rcases hband with hleft | hright
    · have hxtneg : x + t < 0 := by linarith
      have htxpos : 0 < t - x := by linarith
      have hxtδ : δ' ≤ |x + t| := by
        rw [abs_of_nonpos (le_of_lt hxtneg)]
        linarith
      have htxδ : δ' ≤ |t - x| := by
        rw [abs_of_nonneg (le_of_lt htxpos)]
        linarith
      have hxt2 : |x + t| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      have htx2 : |t - x| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      have h1 := signApprox_neg hS hxt2 hxtδ hxtneg
      have h2 := signApprox_pos hS htx2 htxδ htxpos
      have h1u : -1 ≤ S.eval (x + t) := (abs_le.mp (hS.1 (x + t) hxt2)).1
      have h2u : S.eval (t - x) ≤ 1 := (abs_le.mp (hS.1 (t - x) htx2)).2
      have hsumlo : -σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
      have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ σ := by linarith
      rw [printedRectanglePolynomial_eval]
      have hlo : ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x)) ≥
            -((1 - ε₀ / 2) * σ) / 2 := by
          calc ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x))
              ≥ ((1 - ε₀ / 2) / 2) * (-σ) := mul_le_mul_of_nonneg_left hsumlo hc
            _ = -((1 - ε₀ / 2) * σ) / 2 := by ring
      have hhi : ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x)) ≤
            ((1 - ε₀ / 2) * σ) / 2 := by
          calc ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x))
              ≤ ((1 - ε₀ / 2) / 2) * σ := mul_le_mul_of_nonneg_left hsumhi hc
            _ = ((1 - ε₀ / 2) * σ) / 2 := by ring
      have hb : (1 - ε₀ / 2) * σ ≤ ε₀ / 2 := hbudget
      constructor <;> linarith
    · have htxneg : t - x < 0 := by linarith
      have hxtpos : 0 < x + t := by linarith
      have htxδ : δ' ≤ |t - x| := by
        rw [abs_of_nonpos (le_of_lt htxneg)]
        linarith
      have hxtδ : δ' ≤ |x + t| := by
        rw [abs_of_nonneg (le_of_lt hxtpos)]
        linarith
      have hxt2 : |x + t| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      have htx2 : |t - x| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      have h1 := signApprox_pos hS hxt2 hxtδ hxtpos
      have h2 := signApprox_neg hS htx2 htxδ htxneg
      have h1u : S.eval (x + t) ≤ 1 := (abs_le.mp (hS.1 (x + t) hxt2)).2
      have h2u : -1 ≤ S.eval (t - x) := (abs_le.mp (hS.1 (t - x) htx2)).1
      have hsumlo : -σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
      have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ σ := by linarith
      rw [printedRectanglePolynomial_eval]
      have hlo : ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x)) ≥
            -((1 - ε₀ / 2) * σ) / 2 := by
          calc ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x))
              ≥ ((1 - ε₀ / 2) / 2) * (-σ) := mul_le_mul_of_nonneg_left hsumlo hc
            _ = -((1 - ε₀ / 2) * σ) / 2 := by ring
      have hhi : ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x)) ≤
            ((1 - ε₀ / 2) * σ) / 2 := by
          calc ((1 - ε₀ / 2) / 2) * (S.eval (x + t) + S.eval (t - x))
              ≤ ((1 - ε₀ / 2) / 2) * σ := mul_le_mul_of_nonneg_left hsumhi hc
            _ = ((1 - ε₀ / 2) * σ) / 2 := by ring
      have hb : (1 - ε₀ / 2) * σ ≤ ε₀ / 2 := hbudget
      constructor <;> linarith

theorem printedRectangle_bands_abs {S : Polynomial ℝ} {ε₀ δ' t σ : ℝ}
    (hε0 : 0 < ε₀) (hε01 : ε₀ < 1) (hδ' : 0 < δ') (ht : |t| ≤ 1)
    (hbudget : (1 - ε₀ / 2) * σ ≤ ε₀ / 2)
    (hS : SignApproximation S δ' σ) :
    (∀ x : ℝ, |x| ≤ 1 → |(printedRectanglePolynomial S ε₀ |t|).eval x| ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → -(|t| - δ') ≤ x → x ≤ |t| - δ' →
      1 - ε₀ ≤ (printedRectanglePolynomial S ε₀ |t|).eval x ∧
        (printedRectanglePolynomial S ε₀ |t|).eval x ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → (x ≤ -(|t| + δ') ∨ |t| + δ' ≤ x) →
      0 ≤ (printedRectanglePolynomial S ε₀ |t|).eval x ∧
        (printedRectanglePolynomial S ε₀ |t|).eval x ≤ ε₀) := by
  have htabs : 0 ≤ |t| := abs_nonneg t
  have htabs1 : |t| ≤ 1 := ht
  exact printedRectangle_bands hε0 hε01 hδ' htabs htabs1 hbudget hS

theorem frontier2 {S : Polynomial ℝ} (δ' ε' t : ℝ) (hδ' : 0 < δ') (hε' : 0 < ε')
    (hε'2 : ε' ≤ 1 / 2) (ht : |t| ≤ 1) (hS : SignApproximation S δ' (ε' / 2)) :
    (∀ x : ℝ, |x| ≤ 1 → |(printedRectanglePolynomial S ε' |t|).eval x| ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → -(|t| - δ') ≤ x → x ≤ |t| - δ' →
      1 - ε' ≤ (printedRectanglePolynomial S ε' |t|).eval x ∧
        (printedRectanglePolynomial S ε' |t|).eval x ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → (x ≤ -(|t| + δ') ∨ |t| + δ' ≤ x) →
      0 ≤ (printedRectanglePolynomial S ε' |t|).eval x ∧
        (printedRectanglePolynomial S ε' |t|).eval x ≤ ε') := by
  have hbudget : (1 - ε' / 2) * (ε' / 2) ≤ ε' / 2 := by
    calc (1 - ε' / 2) * (ε' / 2) = (ε' / 2) * (1 - ε' / 2) := by ring
      _ ≤ (ε' / 2) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = ε' / 2 := by ring
  exact printedRectangle_bands_abs (ε₀ := ε') (δ' := δ') (σ := ε' / 2)
    (by linarith) (by linarith) (by linarith) ht hbudget hS

theorem frontier2_gapSign (K : ℕ) (δ σ t : ℝ)
    (hδ : 0 < δ) (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8) (ht : |t| ≤ 1)
    (hbudget : gapSignError K δ ≤ σ) :
    (∀ x : ℝ, |x| ≤ 1 → |(printedRectanglePolynomial (gapSignPolynomial K) (4 * σ) |t|).eval x| ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → -(|t| - δ) ≤ x → x ≤ |t| - δ →
      1 - 4 * σ ≤ (printedRectanglePolynomial (gapSignPolynomial K) (4 * σ) |t|).eval x ∧
        (printedRectanglePolynomial (gapSignPolynomial K) (4 * σ) |t|).eval x ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 1 → (x ≤ -(|t| + δ) ∨ |t| + δ ≤ x) →
      0 ≤ (printedRectanglePolynomial (gapSignPolynomial K) (4 * σ) |t|).eval x ∧
        (printedRectanglePolynomial (gapSignPolynomial K) (4 * σ) |t|).eval x ≤ 4 * σ) := by
  have hS : SignApproximation (gapSignPolynomial K) δ σ := by
    have h := gapSign_approximation K δ hδ
    refine ⟨h.1, ?_, h.2.2⟩
    intro x hx hgap
    exact le_trans (h.2.1 x hx hgap) hbudget
  have hbudget' : (1 - 4 * σ / 2) * σ ≤ 4 * σ / 2 := by
    nlinarith [sq_nonneg σ]
  exact printedRectangle_bands_abs (S := gapSignPolynomial K) (ε₀ := 4 * σ) (δ' := δ) (σ := σ)
    (by positivity) (by linarith) (by linarith) ht hbudget' hS

theorem middle_band_empty {t δ' : ℝ} (h : t < δ') :
    ¬ (∃ x : ℝ, |x| ≤ 1 ∧ -(t - δ') ≤ x ∧ x ≤ t - δ') := by
  rintro ⟨x, _, hleft, hright⟩
  have : -(t - δ') ≤ t - δ' := le_trans hleft hright
  linarith

theorem outer_band_empty {t δ' : ℝ} (h : 1 < t + δ') :
    ¬ (∃ x : ℝ, |x| ≤ 1 ∧ (x ≤ -(t + δ') ∨ t + δ' ≤ x)) := by
  rintro ⟨x, hx, hband⟩
  have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
  rcases hband with hleft | hright
  · linarith
  · linarith

theorem outer_band_nonempty_iff {t δ' : ℝ} :
    (∃ x : ℝ, |x| ≤ 1 ∧ (x ≤ -(t + δ') ∨ t + δ' ≤ x)) ↔ t + δ' ≤ 1 := by
  constructor
  · rintro ⟨x, hx, hband⟩
    have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
    rcases hband with hleft | hright
    · linarith
    · linarith
  · intro h
    by_cases hc : -1 ≤ t + δ'
    · refine ⟨t + δ', ⟨abs_le.mpr ⟨hc, h⟩, Or.inr (le_refl _)⟩⟩
    · refine ⟨-1, ⟨abs_le.mpr ⟨by norm_num, by norm_num⟩, Or.inl (by linarith)⟩⟩

theorem middle_band_nonempty_iff {t δ' : ℝ} :
    (∃ x : ℝ, |x| ≤ 1 ∧ -(t - δ') ≤ x ∧ x ≤ t - δ') ↔ δ' ≤ t := by
  constructor
  · rintro ⟨x, hx, hleft, hright⟩
    have hmid : -(t - δ') ≤ t - δ' := le_trans hleft hright
    linarith
  · intro h
    refine ⟨0, ⟨abs_le.mpr ⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩⟩⟩
    · have : -(t - δ') ≤ 0 := by linarith
      exact this
    · have : 0 ≤ t - δ' := by linarith
      exact this

end Qatlib.Concepts.QsvtCore.PhaseExistence
