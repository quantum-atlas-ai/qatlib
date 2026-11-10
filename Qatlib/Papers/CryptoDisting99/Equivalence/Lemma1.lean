/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition2
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition5.Proposition5ClassicalInequalities
import Mathlib.Analysis.SpecificLimits.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open Filter
open scoped BigOperators

variable {X : Type} [Fintype X]

lemma expSmall_of_le_const_mul {d : ℕ → ℝ} {C ε : ℝ} (_hC : 0 < C)
    (hε0 : 0 < ε) (hε1 : ε < 1) (N0 : ℕ)
    (h : ∀ n, N0 ≤ n → d n ≤ C * ε ^ n) : ExpSmall d := by
  obtain ⟨e, hεe, he1⟩ : ∃ e : ℝ, ε < e ∧ e < 1 := ⟨(ε + 1) / 2, by linarith, by linarith⟩
  have hr : 1 < e / ε := by rw [lt_div_iff₀ hε0]; linarith
  have htend : Tendsto (fun n : ℕ => (e / ε) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  have hev : ∀ᶠ n : ℕ in atTop, C ≤ (e / ε) ^ n :=
    htend.eventually (eventually_ge_atTop C)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max N0 N, e, hε0.trans hεe, he1, fun n hn => ?_⟩
  have h1 : d n ≤ C * ε ^ n := h n (le_trans (le_max_left _ _) hn)
  have h2 : C ≤ (e / ε) ^ n := hN n (le_trans (le_max_right _ _) hn)
  calc d n ≤ C * ε ^ n := h1
    _ ≤ (e / ε) ^ n * ε ^ n := mul_le_mul_of_nonneg_right h2 (pow_nonneg hε0.le n)
    _ = e ^ n := by rw [← mul_pow, div_mul_cancel₀ e hε0.ne']

lemma classicalKolmogorov_nonneg (p0 p1 : FinDist X) : 0 ≤ classicalKolmogorov p0 p1 := by
  unfold classicalKolmogorov tv
  positivity

lemma bhattacharyya_le_one (p0 p1 : FinDist X) : bhattacharyya p0 p1 ≤ 1 := by
  have hB := bhattacharyya_eq_sum_sqrt_mul p0 p1
  have hnn : 0 ≤ ∑ x, Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (∑ x, Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x)) ^ 2 ≤ 1 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset X)
      (fun x => Real.sqrt (p0.prob x)) (fun x => Real.sqrt (p1.prob x))
    have h0 : (∑ x, (Real.sqrt (p0.prob x)) ^ 2) = 1 := by
      rw [Finset.sum_congr rfl (fun x _ => by rw [sq, Real.mul_self_sqrt (p0.nonneg x)])]
      exact p0.sum_one
    have h1 : (∑ x, (Real.sqrt (p1.prob x)) ^ 2) = 1 := by
      rw [Finset.sum_congr rfl (fun x _ => by rw [sq, Real.mul_self_sqrt (p1.nonneg x)])]
      exact p1.sum_one
    rw [h0, h1, mul_one] at hcs
    exact hcs
  have hs := sq_nonneg (∑ x, Real.sqrt (p0.prob x) * Real.sqrt (p1.prob x) - 1)
  rw [hB]
  nlinarith

lemma sqrt_pow_eq (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    Real.sqrt (ε ^ n) = (Real.sqrt ε) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hε k), ih, pow_succ]

lemma classExpK_imp_classExpPE (P Q : ℕ → FinDist X) (h : ClassExpK P Q) :
    ClassExpPE P Q := by
  unfold ClassExpK ExpSmall at h
  obtain ⟨n0, ε, hε0, hε1, hb⟩ := h
  refine ⟨n0, ε, hε0, hε1, fun n hn => ?_⟩
  have hK := hb n hn
  simp only [] at hK
  have hPE := proposition2_error_eq_kolmogorov (P n) (Q n)
  have hnn := classicalKolmogorov_nonneg (P n) (Q n)
  simp only []
  have habs : |classicalErrProb (P n) (Q n) - 1 / 2| =
      classicalKolmogorov (P n) (Q n) / 2 := by
    rw [hPE]
    rw [show (1 : ℝ) / 2 - classicalKolmogorov (P n) (Q n) / 2 - 1 / 2
        = -(classicalKolmogorov (P n) (Q n) / 2) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
  rw [habs]
  linarith

lemma classExpPE_imp_classExpK (P Q : ℕ → FinDist X) (h : ClassExpPE P Q) :
    ClassExpK P Q := by
  unfold ClassExpPE ExpNear at h
  obtain ⟨n0, ε, hε0, hε1, hb⟩ := h
  unfold ClassExpK
  refine expSmall_of_le_const_mul (C := 2) (ε := ε) (by norm_num) hε0 hε1 n0 ?_
  intro n hn
  have hPE := hb n hn
  have hEq := proposition2_error_eq_kolmogorov (P n) (Q n)
  have hnn := classicalKolmogorov_nonneg (P n) (Q n)
  have habs : |classicalErrProb (P n) (Q n) - 1 / 2| =
      classicalKolmogorov (P n) (Q n) / 2 := by
    rw [hEq]
    rw [show (1 : ℝ) / 2 - classicalKolmogorov (P n) (Q n) / 2 - 1 / 2
        = -(classicalKolmogorov (P n) (Q n) / 2) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
  rw [habs] at hPE
  linarith

lemma classExpK_imp_classExpB (P Q : ℕ → FinDist X) (h : ClassExpK P Q) :
    ClassExpB P Q := by
  unfold ClassExpK ExpSmall at h
  obtain ⟨n0, ε, hε0, hε1, hb⟩ := h
  refine ⟨n0, ε, hε0, hε1, fun n hn => ?_⟩
  have hK := hb n hn
  have h43 := proposition5_43_left (P n) (Q n)
  have hBle := bhattacharyya_le_one (P n) (Q n)
  have habs : |bhattacharyya (P n) (Q n) - 1| = 1 - bhattacharyya (P n) (Q n) := by
    rw [abs_of_nonpos (by linarith), neg_sub]
  rw [habs]
  linarith

lemma classExpB_imp_classExpK (P Q : ℕ → FinDist X) (h : ClassExpB P Q) :
    ClassExpK P Q := by
  unfold ClassExpB ExpNear at h
  obtain ⟨n0, ε, hε0, hε1, hb⟩ := h
  have hεs0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε0
  have hεs1 : Real.sqrt ε < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hε0.le hε1
  unfold ClassExpK
  refine expSmall_of_le_const_mul (C := Real.sqrt 2) (ε := Real.sqrt ε)
    (Real.sqrt_pos.mpr (by norm_num)) hεs0 hεs1 n0 ?_
  intro n hn
  have hB := hb n hn
  have h43 := proposition5_43_right (P n) (Q n)
  have hBle := bhattacharyya_le_one (P n) (Q n)
  have h1B : 1 - bhattacharyya (P n) (Q n) ≤ ε ^ n := by
    have habs : |bhattacharyya (P n) (Q n) - 1| = 1 - bhattacharyya (P n) (Q n) := by
      rw [abs_of_nonpos (by linarith), neg_sub]
    rw [habs] at hB
    exact hB
  have h2 : 1 - (bhattacharyya (P n) (Q n)) ^ 2 ≤ 2 * (1 - bhattacharyya (P n) (Q n)) := by
    nlinarith
  have h3 : Real.sqrt (1 - (bhattacharyya (P n) (Q n)) ^ 2) ≤
      Real.sqrt (2 * (1 - bhattacharyya (P n) (Q n))) := Real.sqrt_le_sqrt h2
  have h4 : Real.sqrt (2 * (1 - bhattacharyya (P n) (Q n))) ≤ Real.sqrt (2 * ε ^ n) :=
    Real.sqrt_le_sqrt (by linarith)
  have h5 : Real.sqrt (2 * ε ^ n) = Real.sqrt 2 * (Real.sqrt ε) ^ n := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), sqrt_pow_eq ε hε0.le n]
  linarith

lemma classExpK_imp_classExpSD (P Q : ℕ → FinDist X) (h : ClassExpK P Q) :
    ClassExpSD P Q := by
  unfold ClassExpK ExpSmall at h
  obtain ⟨n0, ε, hε0, hε1, hb⟩ := h
  refine ⟨n0, ε, hε0, hε1, fun n hn => ?_⟩
  have hK := hb n hn
  have h44 := proposition5_44_right (P n) (Q n)
  have hPE := proposition2_error_eq_kolmogorov (P n) (Q n)
  rw [hPE] at h44
  linarith

lemma classExpSD_imp_classExpK (P Q : ℕ → FinDist X) (h : ClassExpSD P Q) :
    ClassExpK P Q := by
  unfold ClassExpSD ExpSmall at h
  obtain ⟨n0, ε, hε0, hε1, hb⟩ := h
  have hεs0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε0
  have hεs1 : Real.sqrt ε < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hε0.le hε1
  unfold ClassExpK
  refine expSmall_of_le_const_mul (C := Real.sqrt 2) (ε := Real.sqrt ε)
    (Real.sqrt_pos.mpr (by norm_num)) hεs0 hεs1 n0 ?_
  intro n hn
  have hSD := hb n hn
  have h45 := proposition5_45_left (P n) (Q n)
  have h43 := proposition5_43_right (P n) (Q n)
  have hBle := bhattacharyya_le_one (P n) (Q n)
  have h1B : 1 - bhattacharyya (P n) (Q n) ≤ ε ^ n := by linarith
  have h2 : 1 - (bhattacharyya (P n) (Q n)) ^ 2 ≤ 2 * (1 - bhattacharyya (P n) (Q n)) := by
    nlinarith
  have h3 : Real.sqrt (1 - (bhattacharyya (P n) (Q n)) ^ 2) ≤
      Real.sqrt (2 * (1 - bhattacharyya (P n) (Q n))) := Real.sqrt_le_sqrt h2
  have h4 : Real.sqrt (2 * (1 - bhattacharyya (P n) (Q n))) ≤ Real.sqrt (2 * ε ^ n) :=
    Real.sqrt_le_sqrt (by linarith)
  have h5 : Real.sqrt (2 * ε ^ n) = Real.sqrt 2 * (Real.sqrt ε) ^ n := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), sqrt_pow_eq ε hε0.le n]
  linarith

lemma classExpSD_imp_classExpB (P Q : ℕ → FinDist X) (h : ClassExpSD P Q) :
    ClassExpB P Q := by
  unfold ClassExpSD ExpSmall at h
  obtain ⟨n0, ε, hε0, hε1, hb⟩ := h
  refine ⟨n0, ε, hε0, hε1, fun n hn => ?_⟩
  have hSD := hb n hn
  have h45 := proposition5_45_left (P n) (Q n)
  have hBle := bhattacharyya_le_one (P n) (Q n)
  have habs : |bhattacharyya (P n) (Q n) - 1| = 1 - bhattacharyya (P n) (Q n) := by
    rw [abs_of_nonpos (by linarith), neg_sub]
  rw [habs]
  linarith

lemma classExpSD_imp_classExpPE (P Q : ℕ → FinDist X) (h : ClassExpSD P Q) :
    ClassExpPE P Q :=
  classExpK_imp_classExpPE P Q (classExpSD_imp_classExpK P Q h)

theorem lemma1_classical_exponential_equivalence (P Q : ℕ → FinDist X) :
    (ClassExpK P Q ↔ ClassExpPE P Q) ∧
    (ClassExpK P Q ↔ ClassExpB P Q) ∧
    (ClassExpK P Q ↔ ClassExpSD P Q) :=
  ⟨⟨classExpK_imp_classExpPE P Q, classExpPE_imp_classExpK P Q⟩,
   ⟨classExpK_imp_classExpB P Q, classExpB_imp_classExpK P Q⟩,
   ⟨classExpK_imp_classExpSD P Q, classExpSD_imp_classExpK P Q⟩⟩

end Qatlib.Papers.CryptoDisting99.Equivalence
