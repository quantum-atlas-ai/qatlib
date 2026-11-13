/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSStatePrep24.SpectralLeak.FiveSuccessProbabilitiesStat

/-!
# Comparison of five spectral success weights

This module proves `Clause31FiveSuccessProbabilities`, comparing the single-band, inverse-band,
near-band, full-band, and perturbed state weights. Continuation products, stopping-mass
telescoping, and geometric error bounds provide the quantitative estimates. See [LowSu2026] for
the paper context.

## Main statements

* `stopMass_telescope`: For a positive number of normalized rows with a deterministic terminal
  stop, the squared norms of the stopping coefficients sum to one.
* `Clause31FiveSuccessProbabilities_answer`: The five success weights satisfy the bounds
  specified by `Clause31FiveSuccessProbabilities`, including near-band leakage control and the
  `4 * εbm` perturbation estimate.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.QLSStatePrep24.SpectralLeak

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators

/-- The squared norms of the two components of a normalized state sum to one. -/
private theorem normalized_two_eq {ψ : QState (Fin 2)} (h : Normalized ψ) :
    ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 = 1 := by
  have h2 : ∑ i : Fin 2, ‖ψ i‖ ^ 2 = 1 := h
  rwa [Fin.sum_univ_two] at h2

/-- Each component of a normalized two-component state has squared norm at most one. -/
private theorem normalized_two_le {ψ : QState (Fin 2)} (h : Normalized ψ) (b : Fin 2) :
    ‖ψ b‖ ^ 2 ≤ 1 := by
  have hs := normalized_two_eq h
  have h0 : ‖ψ 0‖ ^ 2 ≤ 1 := by linarith [sq_nonneg (‖ψ 1‖)]
  have h1 : ‖ψ 1‖ ^ 2 ≤ 1 := by linarith [sq_nonneg (‖ψ 0‖)]
  fin_cases b
  · exact h0
  · exact h1

/-- The product of squared continuation amplitudes through the first `t` steps for label `u`. -/
private def contMass {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (t : ℕ) : ℝ :=
  ∏ l : Fin t, ‖ξ (l.val + 1) u 1‖ ^ 2

/-- The continuation mass before any steps is one. -/
private theorem contMass_zero {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) :
    contMass ξ u 0 = 1 := by
  show (∏ l : Fin 0, ‖ξ (l.val + 1) u 1‖ ^ 2) = 1
  simp

/-- The continuation mass equals the product over `i < t` of the squared continuation amplitude
at step `i + 1`. -/
private theorem contMass_eq_prod_range {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (t : ℕ) :
    contMass ξ u t = ∏ i ∈ Finset.range t, ‖ξ (i + 1) u 1‖ ^ 2 :=
  Fin.prod_univ_eq_prod_range (fun k : ℕ => ‖ξ (k + 1) u 1‖ ^ 2) t

/-- The continuation mass through step `t + 1` is the previous mass times the squared
continuation amplitude at that step. -/
private theorem contMass_succ {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (t : ℕ) :
    contMass ξ u (t + 1) = contMass ξ u t * ‖ξ (t + 1) u 1‖ ^ 2 := by
  rw [contMass_eq_prod_range, contMass_eq_prod_range, Finset.prod_range_succ]

/-- The continuation mass is nonnegative. -/
private theorem contMass_nonneg {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (t : ℕ) :
    0 ≤ contMass ξ u t := by
  apply Finset.prod_nonneg
  intro i _
  exact sq_nonneg _

/-- If the first `n` rows are normalized and `t ≤ n`, the continuation mass through `t` steps is
at most one. -/
private theorem contMass_le_one {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I)
    {n t : ℕ} (ht : t ≤ n) (hnorm : ∀ j : ℕ, j < n → Normalized (ξ (j + 1) u)) :
    contMass ξ u t ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i _
    exact sq_nonneg _
  · intro i _
    exact normalized_two_le (hnorm i.val (by omega)) 1

/-- At a positive step `j`, the squared stopping amplitude is the squared stop component times
the continuation mass through `j - 1` steps. -/
private theorem stopCoefficient_sq {I : Type} {ξ : ℕ → I → QState (Fin 2)}
    (u : I) {j : ℕ} (hj : 0 < j) :
    ‖stopCoefficient ξ j u‖ ^ 2 = ‖ξ j u 0‖ ^ 2 * contMass ξ u (j - 1) := by
  have hj0 : j ≠ 0 := Nat.pos_iff_ne_zero.mp hj
  have hsc : stopCoefficient ξ j u = ξ j u 0 * ∏ l : Fin (j - 1), ξ (l.val + 1) u 1 := by
    simp [stopCoefficient, hj0]
  rw [hsc, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  rfl

/-- Reindexing the sum of `f(i + 1)` over `i < n` gives the sum of `f` over the integers from
one to `n`. -/
private theorem sum_range_add_one {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∑ i ∈ Finset.range n, f (i + 1)) = ∑ l ∈ Finset.Icc 1 n, f l := by
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro i₁ _ i₂ _ h
    exact Nat.succ.inj h
  · intro l hl
    simp only [Finset.mem_Icc] at hl
    refine ⟨l - 1, by simp only [Finset.mem_range]; omega, ?_⟩
    show (l - 1) + 1 = l
    omega
  · intro i hi
    rfl

/-- The sum of `f(j + 1)` over `Fin m` equals the sum of `f` over the natural interval from one
to `m`. -/
private theorem sum_fin_add_one {α : Type} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    (∑ j : Fin m, f (j.val + 1)) = ∑ l ∈ Finset.Icc 1 m, f l :=
  (Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k + 1)) m).trans (sum_range_add_one m f)

/-- For a positive number of normalized rows with a deterministic terminal stop, the squared
norms of the stopping coefficients sum to one. -/
private theorem stopMass_telescope {I : Type} (ξ : ℕ → I → QState (Fin 2)) (u : I) (m : ℕ)
    (hm : 0 < m) (hnorm : ∀ j : ℕ, j < m → Normalized (ξ (j + 1) u))
    (hstop : ξ m u = (fun b => if b = 0 then 1 else 0)) :
    (∑ j : Fin m, ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2) = 1 := by
  have hz : ∀ j : Fin m, ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2
      = contMass ξ u j.val - contMass ξ u (j.val + 1) := by
    intro j
    have hj : 0 < j.val + 1 := Nat.succ_pos _
    rw [stopCoefficient_sq u hj, Nat.add_sub_cancel]
    have h01 := normalized_two_eq (hnorm j.val j.is_lt)
    have hc := contMass_succ ξ u j.val
    have hre : ‖ξ (j.val + 1) u 0‖ ^ 2 = 1 - ‖ξ (j.val + 1) u 1‖ ^ 2 := by linarith
    rw [hre, hc]
    ring
  have h2 : (∑ j : Fin m, ‖stopCoefficient ξ (j.val + 1) u‖ ^ 2)
      = ∑ i ∈ Finset.range m, (contMass ξ u i - contMass ξ u (i + 1)) :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖stopCoefficient ξ (i + 1) u‖ ^ 2) m).trans
      (Finset.sum_congr rfl (fun i hi => hz ⟨i, Finset.mem_range.mp hi⟩))
  rw [h2, Finset.sum_range_sub', contMass_zero]
  have hm0 : contMass ξ u m = 0 := by
    rw [contMass_eq_prod_range]
    have hmem : m - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
    refine Finset.prod_eq_zero hmem ?_
    have hsu : ξ m u 1 = 0 := by
      rw [hstop]
      simp
    have hfactor : ‖ξ ((m - 1) + 1) u 1‖ ^ 2 = 0 := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hsu]
      simp
    exact hfactor
  rw [hm0]
  ring

/-- If every `d t` lies in `[0, 1/3]`, the sum of `9^t` times the initial product of squared `d`
values is at most the square of their sum. -/
private theorem sum_pow_prod_sq_le_sq {T : ℕ} (d : ℕ → ℝ)
    (hd : ∀ t < T, 0 ≤ d t ∧ d t ≤ 1 / 3) :
    (∑ t ∈ Finset.range T, (9 : ℝ) ^ t * ∏ l ∈ Finset.range (t + 1), (d l) ^ 2)
      ≤ (∑ t ∈ Finset.range T, d t) ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hd' : ∀ t < T, 0 ≤ d t ∧ d t ≤ 1 / 3 := fun t ht => hd t (by omega)
    have ih' := ih hd'
    have hdT := hd T (by omega)
    have hsum : (∑ t ∈ Finset.range (T + 1), (9 : ℝ) ^ t * ∏ l ∈ Finset.range (t + 1), (d l) ^ 2)
        = (∑ t ∈ Finset.range T, (9 : ℝ) ^ t * ∏ l ∈ Finset.range (t + 1), (d l) ^ 2)
          + (9 : ℝ) ^ T * ∏ l ∈ Finset.range (T + 1), (d l) ^ 2 := by
      rw [Finset.sum_range_succ]
    have hfac : (9 : ℝ) ^ T * ∏ l ∈ Finset.range (T + 1), (d l) ^ 2
        = ((9 : ℝ) ^ T * ∏ l ∈ Finset.range T, (d l) ^ 2) * (d T) ^ 2 := by
      rw [Finset.prod_range_succ, mul_assoc]
    have hbound : (9 : ℝ) ^ T * ∏ l ∈ Finset.range T, (d l) ^ 2 ≤ 1 := by
      have hper : ∀ l ∈ Finset.range T, (9 : ℝ) * (d l) ^ 2 ≤ 1 := by
        intro l hl
        have := hd' l (Finset.mem_range.mp hl)
        nlinarith [this.2]
      have hprod : (∏ l ∈ Finset.range T, (9 : ℝ) * (d l) ^ 2) ≤ 1 := by
        apply Finset.prod_le_one₀
        · intro l _
          exact mul_nonneg (by norm_num) (sq_nonneg _)
        · intro l hl
          exact hper l hl
      rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
      simpa [Finset.card_range] using! hprod
    have hextra : ((9 : ℝ) ^ T * ∏ l ∈ Finset.range T, (d l) ^ 2) * (d T) ^ 2 ≤ (d T) ^ 2 := by
      nlinarith [sq_nonneg (d T)]
    have hsum_nonneg : 0 ≤ ∑ t ∈ Finset.range T, d t :=
      Finset.sum_nonneg fun t ht => (hd' t (Finset.mem_range.mp ht)).1
    rw [hsum, hfac, Finset.sum_range_succ]
    nlinarith

/-- Under the normalization and early-stop hypotheses, the squared stopping amplitude at step `j
+ 1` is at most `δ(j + 1)²`. -/
private theorem stop_before_le {I : Type} {ξ : ℕ → I → QState (Fin 2)}
    (δ : ℕ → ℝ) (m : ℕ) (u : I)
    (hδ : ∀ j : ℕ, j < m → 0 ≤ δ (j + 1) ∧ δ (j + 1) ≤ 1 / 3)
    (hnorm : ∀ j : ℕ, j < m → Normalized (ξ (j + 1) u))
    (hbefore : ∀ j : ℕ, j < m → ‖ξ (j + 1) u 0‖ ≤ δ (j + 1))
    {j : ℕ} (hj : j < m) :
    ‖stopCoefficient ξ (j + 1) u‖ ^ 2 ≤ δ (j + 1) ^ 2 := by
  have hj0 : 0 < j + 1 := Nat.succ_pos _
  rw [stopCoefficient_sq u hj0, Nat.add_sub_cancel]
  have hb := hbefore j hj
  have hc : contMass ξ u j ≤ 1 :=
    contMass_le_one ξ u (Nat.le_of_lt hj) (fun l hl => hnorm l hl)
  have hd0 : 0 ≤ δ (j + 1) := (hδ j hj).1
  have hp2 : ‖ξ (j + 1) u 0‖ ^ 2 ≤ δ (j + 1) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hd0]
    exact hb
  have hnn : 0 ≤ contMass ξ u j := contMass_nonneg ξ u j
  have hstep : ‖ξ (j + 1) u 0‖ ^ 2 * contMass ξ u j
      ≤ ‖ξ (j + 1) u 0‖ ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  linarith

/-- Under the stated late-continuation hypotheses, a stopping step strictly beyond `k′ + 1` has
squared amplitude at most `δ j²`. -/
private theorem stop_after_le {I : Type} {ξ : ℕ → I → QState (Fin 2)}
    (δ : ℕ → ℝ) (m k' : ℕ) (u : I)
    (hδ : ∀ j : ℕ, j < m → 0 ≤ δ (j + 1) ∧ δ (j + 1) ≤ 1 / 3)
    (hnorm : ∀ j : ℕ, j < m → Normalized (ξ (j + 1) u))
    (hafter : ∀ j : ℕ, j < m → k' + 1 ≤ j + 1 → ‖ξ (j + 1) u 1‖ ≤ δ (j + 1))
    {j : ℕ} (hj : j < m) (hband : k' + 1 < j + 1) :
    ‖stopCoefficient ξ (j + 1) u‖ ^ 2 ≤ (δ j) ^ 2 := by
  have hj0 : 0 < j + 1 := Nat.succ_pos _
  have hge : k' + 1 ≤ j := by omega
  rw [stopCoefficient_sq u hj0, Nat.add_sub_cancel]
  have hnorm0 : ‖ξ (j + 1) u 0‖ ^ 2 ≤ 1 :=
    normalized_two_le (hnorm j hj) 0
  have hnn : 0 ≤ contMass ξ u j := contMass_nonneg ξ u j
  have hstep : ‖ξ (j + 1) u 0‖ ^ 2 * contMass ξ u j ≤ 1 * contMass ξ u j :=
    mul_le_mul_of_nonneg_right hnorm0 hnn
  have hcm : contMass ξ u j ≤ δ j ^ 2 := by
    have hsplit : contMass ξ u j
        = contMass ξ u k' * ∏ i ∈ Finset.Ico k' j, ‖ξ (i + 1) u 1‖ ^ 2 := by
      have hsp : (∏ i ∈ Finset.range j, ‖ξ (i + 1) u 1‖ ^ 2)
          = (∏ i ∈ Finset.range k', ‖ξ (i + 1) u 1‖ ^ 2)
            * (∏ i ∈ Finset.Ico k' j, ‖ξ (i + 1) u 1‖ ^ 2) :=
        (Finset.prod_range_mul_prod_Ico _ (by omega : k' ≤ j)).symm
      rw [contMass_eq_prod_range ξ u j, contMass_eq_prod_range ξ u k', hsp]
    rw [hsplit]
    have hn1 : contMass ξ u k' ≤ 1 :=
      contMass_le_one ξ u (Nat.le_refl k') (fun l hl => hnorm l (by omega))
    have hle : (∏ i ∈ Finset.Ico k' j, ‖ξ (i + 1) u 1‖ ^ 2)
        ≤ ∏ i ∈ Finset.Ico k' j, δ (i + 1) ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact sq_nonneg _
      · intro i hi
        have hi' : k' ≤ i ∧ i < j := Finset.mem_Ico.mp hi
        have hlt : i < m := by omega
        have ha := hafter i hlt (by omega)
        have hd : 0 ≤ δ (i + 1) := (hδ i hlt).1
        have hsq : ‖ξ (i + 1) u 1‖ ^ 2 ≤ δ (i + 1) ^ 2 := by
          apply sq_le_sq.mpr
          rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hd]
          exact ha
        exact hsq
    have hstep1 : contMass ξ u k' * ∏ i ∈ Finset.Ico k' j, ‖ξ (i + 1) u 1‖ ^ 2
        ≤ 1 * ∏ i ∈ Finset.Ico k' j, δ (i + 1) ^ 2 := by
      apply mul_le_mul hn1 hle
      · exact Finset.prod_nonneg fun i _ => sq_nonneg _
      · exact zero_le_one
    have hreIco : (∏ i ∈ Finset.Ico k' j, δ (i + 1) ^ 2)
        = ∏ l ∈ Finset.Ico (k' + 1) (j + 1), δ l ^ 2 := by
      refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Ico] at hi ⊢
        omega
      · intro i₁ _ i₂ _ h
        exact Nat.succ.inj h
      · intro l hl
        simp only [Finset.mem_Ico] at hl
        refine ⟨l - 1, by simp only [Finset.mem_Ico]; omega, ?_⟩
        show (l - 1) + 1 = l
        omega
      · intro i hi
        rfl
    have hle2 : (∏ l ∈ Finset.Ico (k' + 1) (j + 1), δ l ^ 2) ≤ δ j ^ 2 := by
      rw [Finset.prod_Ico_succ_top (by omega : k' + 1 ≤ j)]
      have hle3 : (∏ l ∈ Finset.Ico (k' + 1) j, δ l ^ 2) ≤ 1 := by
        apply Finset.prod_le_one₀
        · intro i _
          exact sq_nonneg _
        · intro i hi
          have hi' : k' + 1 ≤ i ∧ i < j := Finset.mem_Ico.mp hi
          have hlt : i < m := by omega
          have hge1 : 1 ≤ i := by omega
          have hd' := hδ (i - 1) (by omega)
          have hd : 0 ≤ δ i ∧ δ i ≤ 1 / 3 := by
            rwa [Nat.sub_add_cancel hge1] at hd'
          nlinarith
      have hd : 0 ≤ δ j ^ 2 := sq_nonneg _
      nlinarith
    have hstep2 : (1 : ℝ) * ∏ i ∈ Finset.Ico k' j, δ (i + 1) ^ 2
        = ∏ l ∈ Finset.Ico (k' + 1) (j + 1), δ l ^ 2 := by
      rw [hreIco, one_mul]
    have hstep3 : (1 : ℝ) * ∏ i ∈ Finset.Ico k' j, δ (i + 1) ^ 2 ≤ δ j ^ 2 := by
      rw [hstep2]
      exact hle2
    exact hstep1.trans hstep3
  linarith

/-- Squaring `3^a / 3^b` gives `9^a / 9^b` over the reals. -/
private theorem three_pow_div_sq (a b : ℕ) :
    ((3:ℝ)^a / (3:ℝ)^b) ^ 2 = (9:ℝ)^a / (9:ℝ)^b := by
  rw [div_pow, pow_two, pow_two, ← mul_pow, ← mul_pow]
  norm_num

/-- Squaring the `n`th power of the reciprocal of three gives the `n`th power of the reciprocal
of nine. -/
private theorem inv_three_sq (n : ℕ) :
    ((3:ℝ)⁻¹ ^ n) ^ 2 = (9:ℝ)⁻¹ ^ n := by
  rw [pow_two, ← mul_pow, (by norm_num : (3:ℝ)⁻¹ * 3⁻¹ = 9⁻¹)]

/-- The reciprocal of the `n`th power of the reciprocal of nine equals `9^n`. -/
private theorem inv_pow_eq (n : ℕ) :
    1 / ((9:ℝ)⁻¹ ^ n) = (9:ℝ) ^ n := by
  rw [inv_pow, one_div, inv_inv]

/-- For nonnegative terms on a finite set, the sum of squares is at most the square of the sum. -/
private theorem sum_sq_le_sq_sum {α : Type} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) : (∑ a ∈ s, f a ^ 2) ≤ (∑ a ∈ s, f a) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self _ _)
    have ih' : (∑ b ∈ s, f b ^ 2) ≤ (∑ b ∈ s, f b) ^ 2 :=
      ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    have hsum0 : 0 ≤ ∑ b ∈ s, f b :=
      Finset.sum_nonneg fun b hb => hf b (Finset.mem_insert_of_mem hb)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith

/-- For a nonempty tail of errors in `[0, 1/3]`, multiplying their squared product by `9^(b +
1)` is bounded by `9^(n + 2) * δ b²`. -/
private theorem tail_prod_weighted_le (δ : ℕ → ℝ) (n b : ℕ)
    (hδ : ∀ l, n + 1 ≤ l → l ≤ b → 0 ≤ δ l ∧ δ l ≤ 1 / 3) (hge : n + 1 ≤ b) :
    (∏ l ∈ Finset.Ico (n + 1) (b + 1), δ l ^ 2) * (9 : ℝ) ^ (b + 1)
      ≤ (9 : ℝ) ^ (n + 2) * δ b ^ 2 := by
  have hsp : (∏ l ∈ Finset.Ico (n + 1) (b + 1), δ l ^ 2)
      = δ b ^ 2 * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2 := by
    rw [Finset.prod_Ico_succ_top hge]
    ring
  have hle9 : (∏ l ∈ Finset.Ico (n + 1) b, (9 : ℝ) * δ l ^ 2) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _
      exact mul_nonneg (by norm_num) (sq_nonneg _)
    · intro i hi
      have hi' : n + 1 ≤ i ∧ i < b := Finset.mem_Ico.mp hi
      have hd := hδ i hi'.1 (by omega)
      nlinarith [hd.1, hd.2]
  have hkey : (9 : ℝ) ^ (b - (n + 1)) * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2 ≤ 1 := by
    have h1 : (∏ l ∈ Finset.Ico (n + 1) b, (9 : ℝ) * δ l ^ 2)
        = (9 : ℝ) ^ (b - (n + 1)) * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
    rw [← h1]
    exact hle9
  have hexp : (9 : ℝ) ^ (b + 1)
      = (9 : ℝ) ^ (n + 2) * (9 : ℝ) ^ (b - (n + 1)) := by
    have : b + 1 = n + 2 + (b - (n + 1)) := by omega
    rw [this, pow_add]
  calc (∏ l ∈ Finset.Ico (n + 1) (b + 1), δ l ^ 2) * (9 : ℝ) ^ (b + 1)
      = (δ b ^ 2 * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2) * (9 : ℝ) ^ (b + 1) := by rw [hsp]
    _ = δ b ^ 2 * ((9 : ℝ) ^ (b + 1) * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2) := by ring
    _ = δ b ^ 2 *
        ((9 : ℝ) ^ (n + 2) * ((9 : ℝ) ^ (b - (n + 1)) * ∏ l ∈ Finset.Ico (n + 1) b, δ l ^ 2)) := by
        rw [hexp]
        ring
    _ ≤ δ b ^ 2 * ((9 : ℝ) ^ (n + 2) * 1) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left hkey (pow_nonneg (by positivity) _)
    _ = (9 : ℝ) ^ (n + 2) * δ b ^ 2 := by ring

/-- The five success weights satisfy the bounds specified by `Clause31FiveSuccessProbabilities`,
including near-band leakage control and the `4 * εbm` perturbation estimate. See
[LowSu2026]. -/
theorem Clause31FiveSuccessProbabilities_answer : Clause31FiveSuccessProbabilities := by
  intro I _ m k σ γ ξ δ χ εbm hiv hγ hleg hε hχ hdiff
  obtain ⟨hm, hk, hδ, hstop, hnorm, hbefore, hafter⟩ := hleg
  have hδ' : ∀ j : ℕ, j < m → 0 ≤ δ (j + 1) ∧ δ (j + 1) ≤ 1 / 3 :=
    fun j hj => hδ ⟨j, hj⟩
  have hnorm' : ∀ j : ℕ, j < m → ∀ v : I, Normalized (ξ (j + 1) v) :=
    fun j hj v => hnorm ⟨j, hj⟩ v
  have hbefore' : ∀ j : ℕ, j < m → ∀ v : I, j + 1 < k v → ‖ξ (j + 1) v 0‖ ≤ δ (j + 1) :=
    fun j hj v h => hbefore ⟨j, hj⟩ v h
  have hafter' : ∀ j : ℕ, j < m → ∀ v : I, k v + 1 ≤ j + 1 → ‖ξ (j + 1) v 1‖ ≤ δ (j + 1) :=
    fun j hj v h => hafter ⟨j, hj⟩ v h
  have hstop' : ∀ v : I, ξ m v = (fun b => if b = 0 then 1 else 0) := hstop
  have hiv' : ∀ u : I, k u < m ∧ (3:ℝ)⁻¹^(k u + 1) ≤ abs (σ u) ∧ abs (σ u) < (3:ℝ)⁻¹^(k u) :=
    hiv
  set ζ : ℕ → I → ℂ := stopCoefficient ξ with hζ
  intro he hlt

  have hparseval : ∀ u : I, (∑ j : Fin m, ‖ζ (j.val + 1) u‖ ^ 2) = 1 := by
    intro u
    rw [hζ]
    exact stopMass_telescope ξ u m hm (fun j hj => hnorm' j hj u) (hstop' u)

  have hterm : ∀ u : I,
      ‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m
        ≤ ‖γ u‖ ^ 2 / ((3:ℝ)^m * σ u) ^ 2 ∧
      ‖γ u‖ ^ 2 / ((3:ℝ)^m * σ u) ^ 2
        ≤ ‖γ u‖ ^ 2 * (9:ℝ)^(k u + 1) / (9:ℝ)^m := by
    intro u
    have hiv_u := hiv' u
    have h1 : (3:ℝ)⁻¹^(k u + 1) ≤ abs (σ u) := hiv_u.2.1
    have h2 : abs (σ u) < (3:ℝ)⁻¹^(k u) := hiv_u.2.2
    have hσ2a : ((3:ℝ)⁻¹^(k u + 1)) ^ 2 ≤ abs (σ u) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (by norm_num : (0:ℝ) ≤ 3)) (k u + 1)),
        abs_abs]
      exact h1
    have hσ2b : abs (σ u) ^ 2 < ((3:ℝ)⁻¹^(k u)) ^ 2 := by
      have : abs (abs (σ u)) < abs ((3:ℝ)⁻¹^(k u)) := by
        rw [abs_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (by norm_num : (0:ℝ) ≤ 3)) (k u))]
        exact h2
      exact sq_lt_sq.mpr this
    have hσ2a' : (9:ℝ)⁻¹^(k u + 1) ≤ σ u ^ 2 := by
      have h := hσ2a
      rw [inv_three_sq, sq_abs] at h
      exact h
    have hσ2b' : σ u ^ 2 < (9:ℝ)⁻¹^(k u) := by
      have h := hσ2b
      rw [inv_three_sq, sq_abs] at h
      exact h
    have hσpos : 0 < σ u ^ 2 := by
      have hσn : σ u ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at h1
        have : (0:ℝ) < (3:ℝ)⁻¹^(k u + 1) := pow_pos (inv_pos.mpr (by norm_num)) _
        linarith
      exact sq_pos_of_ne_zero hσn
    have hden : ((3:ℝ)^m * σ u) ^ 2 = (9:ℝ)^m * σ u ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul,
        (by norm_num : (3:ℝ)^2 = 9)]
    have h9m : (0:ℝ) < (9:ℝ)^m := pow_pos (by norm_num) _
    have h9k : (0:ℝ) < (9:ℝ)^(k u) := pow_pos (by norm_num) _
    have h9k1 : (0:ℝ) < (9:ℝ)^(k u + 1) := pow_pos (by norm_num) _
    constructor
    · rw [hden]
      by_cases hg : ‖γ u‖ = 0
      · have hz : ‖γ u‖ ^ 2 = (0:ℝ) := by rw [hg]; norm_num
        rw [hz, zero_mul, zero_div, zero_div]
      · have hg0 : 0 < ‖γ u‖ ^ 2 := sq_pos_of_ne_zero hg
        have hkey : (9:ℝ)^(k u) / (9:ℝ)^m ≤ 1 / ((9:ℝ)^m * σ u ^ 2) := by
          have hlt : σ u ^ 2 < (9:ℝ)⁻¹^(k u) := hσ2b'
          have hpos : 0 < (9:ℝ)^(k u) := h9k
          have h9 : (9:ℝ)^(k u) * (9:ℝ)⁻¹^(k u) = 1 := by
            rw [← mul_pow, (by norm_num : (9:ℝ) * 9⁻¹ = 1), one_pow]
          have hcross : (9:ℝ)^(k u) * σ u ^ 2 < 1 := by
            have := mul_lt_mul_of_pos_left hlt hpos
            rw [h9] at this
            exact this
          rw [le_div_iff₀ (mul_pos h9m hσpos)]
          have heq : (9:ℝ)^(k u) / (9:ℝ)^m * ((9:ℝ)^m * σ u ^ 2)
              = (9:ℝ)^(k u) * σ u ^ 2 := by
            rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt h9m)]
          rw [heq]
          exact le_of_lt hcross
        have hmul : ‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m
            ≤ ‖γ u‖ ^ 2 / ((9:ℝ)^m * σ u ^ 2) := by
          have h := mul_le_mul_of_nonneg_left hkey (sq_nonneg (‖γ u‖))
          rw [mul_one_div, ← mul_div_assoc] at h
          exact h
        exact hmul
    · rw [hden]
      by_cases hg : ‖γ u‖ = 0
      · have hz : ‖γ u‖ ^ 2 = (0:ℝ) := by rw [hg]; norm_num
        rw [hz, zero_mul, zero_div, zero_div]
      · have hg0 : 0 < ‖γ u‖ ^ 2 := sq_pos_of_ne_zero hg
        have hkey : 1 / ((9:ℝ)^m * σ u ^ 2) ≤ (9:ℝ)^(k u + 1) / (9:ℝ)^m := by
          have hge : (9:ℝ)⁻¹^(k u + 1) ≤ σ u ^ 2 := hσ2a'
          have hpos : 0 < (9:ℝ)^(k u + 1) := h9k1
          have h9 : (9:ℝ)^(k u + 1) * (9:ℝ)⁻¹^(k u + 1) = 1 := by
            rw [← mul_pow, (by norm_num : (9:ℝ) * 9⁻¹ = 1), one_pow]
          have hcross : (1:ℝ) ≤ (9:ℝ)^(k u + 1) * σ u ^ 2 := by
            have := mul_le_mul_of_nonneg_left hge (le_of_lt hpos)
            rw [h9] at this
            exact this
          rw [le_div_iff₀ h9m]

          have heq : (1:ℝ) / ((9:ℝ)^m * σ u ^ 2) * (9:ℝ)^m
              = 1 / σ u ^ 2 := by
            rw [div_mul_eq_mul_div, one_mul, ← div_div,
              div_self (ne_of_gt h9m)]
          rw [heq]

          rw [div_le_iff₀ hσpos]
          exact hcross
        have hmul : ‖γ u‖ ^ 2 / ((9:ℝ)^m * σ u ^ 2)
            ≤ ‖γ u‖ ^ 2 * (9:ℝ)^(k u + 1) / (9:ℝ)^m := by
          have h := mul_le_mul_of_nonneg_left hkey (sq_nonneg (‖γ u‖))
          rw [mul_one_div, ← mul_div_assoc] at h
          exact h
        exact hmul
  have h_p_le_p1 : inverseBandProbability m σ γ ≤ singleBandProbability m k γ := by
    unfold inverseBandProbability singleBandProbability
    exact Finset.sum_le_sum fun u _ => (hterm u).2
  have h_p1_9_le_p : singleBandProbability m k γ / 9 ≤ inverseBandProbability m σ γ := by
    unfold inverseBandProbability singleBandProbability
    have h1 : (∑ u : I, ‖γ u‖ ^ 2 * (9:ℝ)^(k u + 1) / (9:ℝ)^m) / 9
        = ∑ u : I, ‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun u _ => by
        have : (‖γ u‖ ^ 2 * (9:ℝ)^(k u + 1) / (9:ℝ)^m) / 9
            = ‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m := by
          field_simp
          rw [pow_succ]
          ring
        exact this
    rw [h1]
    exact Finset.sum_le_sum fun u _ => (hterm u).1

  have hδ'' : ∀ r : ℕ, 1 ≤ r → r < m → 0 ≤ δ r ∧ δ r ≤ 1 / 3 := by
    intro r hr1 hr2
    have := hδ' (r - 1) (by omega)
    rwa [Nat.sub_add_cancel hr1] at this
  have hnorm'' : ∀ r : ℕ, 1 ≤ r → r < m → ∀ v : I, Normalized (ξ r v) := by
    intro r hr1 hr v
    have := hnorm' (r - 1) (by omega) v
    rwa [Nat.sub_add_cancel hr1] at this
  have hafter'' : ∀ r : ℕ, 1 ≤ r → r < m → ∀ v : I, k v + 1 ≤ r → ‖ξ r v 1‖ ≤ δ r := by
    intro r hr1 hr v h
    have := hafter' (r - 1) (by omega) v (by omega)
    rwa [Nat.sub_add_cancel hr1] at this

  have hsplit : ∀ (n : ℕ) (f : Fin m → ℝ),
      (∑ j : Fin m, (if j.val + 1 ≠ n ∧ j.val + 1 ≠ n + 1 then f j else 0))
        = (∑ j : Fin m, (if j.val + 1 < n then f j else 0))
          + (∑ j : Fin m, (if n + 1 < j.val + 1 then f j else 0)) := by
    intro n f
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> first | (exfalso; omega) | ring

  have hbefore_w : ∀ (u : I) (j : Fin m), j.val + 1 < k u →
      ‖ζ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1)
        ≤ (9 : ℝ) ^ (k u + 2) * δ (j.val + 1) ^ 2 := by
    intro u j hj
    have hj' : 0 < j.val + 1 := Nat.succ_pos _
    rw [hζ, stopCoefficient_sq u hj', Nat.add_sub_cancel]
    have hb := hbefore' j.val j.is_lt u hj
    have hc : contMass ξ u j.val ≤ 1 :=
      contMass_le_one ξ u j.is_lt.le (fun l hl => hnorm' l (by omega) u)
    have hd0 : 0 ≤ δ (j.val + 1) := (hδ' j.val j.is_lt).1
    have hp2 : ‖ξ (j.val + 1) u 0‖ ^ 2 ≤ δ (j.val + 1) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hd0]
      exact hb
    have hnn : 0 ≤ contMass ξ u j.val := contMass_nonneg ξ u j.val
    have hstep : ‖ξ (j.val + 1) u 0‖ ^ 2 * contMass ξ u j.val
        ≤ ‖ξ (j.val + 1) u 0‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    have h9 : (9 : ℝ) ^ (j.val + 1) ≤ (9 : ℝ) ^ (k u + 2) := by
      apply pow_le_pow_right₀
      · norm_num
      · omega
    have hd : 0 ≤ δ (j.val + 1) ^ 2 := sq_nonneg _
    have hp : 0 ≤ (9 : ℝ) ^ (j.val + 1) := pow_nonneg (by norm_num) _
    have h3 : ‖ξ (j.val + 1) u 0‖ ^ 2 * contMass ξ u j.val * (9 : ℝ) ^ (j.val + 1)
        ≤ δ (j.val + 1) ^ 2 * (9 : ℝ) ^ (j.val + 1) := by
      nlinarith
    have h4 : δ (j.val + 1) ^ 2 * (9 : ℝ) ^ (j.val + 1)
        ≤ δ (j.val + 1) ^ 2 * (9 : ℝ) ^ (k u + 2) :=
      mul_le_mul_of_nonneg_left h9 hd
    have h4' : δ (j.val + 1) ^ 2 * (9 : ℝ) ^ (k u + 2)
        = (9 : ℝ) ^ (k u + 2) * δ (j.val + 1) ^ 2 := by ring
    linarith

  have hafter_w : ∀ (u : I) (j : Fin m), k u + 1 < j.val + 1 →
      ‖ζ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1)
        ≤ (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 := by
    intro u j hj
    have hj' : 0 < j.val + 1 := Nat.succ_pos _
    have hn : k u < m := hk u
    have hge : k u + 1 ≤ j.val := by omega
    rw [hζ, stopCoefficient_sq u hj', Nat.add_sub_cancel]
    have hnorm0 : ‖ξ (j.val + 1) u 0‖ ^ 2 ≤ 1 :=
      normalized_two_le (hnorm' j.val j.is_lt u) 0
    have hcm : contMass ξ u j.val ≤ ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2 := by
      have hsplitP : contMass ξ u j.val
          = contMass ξ u (k u) * ∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2 := by
        rw [contMass_eq_prod_range ξ u j.val, contMass_eq_prod_range ξ u (k u),
          ← Finset.prod_range_mul_prod_Ico _ (by omega : k u ≤ j.val)]
      rw [hsplitP]
      have hn1 : contMass ξ u (k u) ≤ 1 :=
        contMass_le_one ξ u (Nat.le_refl _) (fun l hl => hnorm' l (by omega) u)
      have hle : (∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
          ≤ ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2 := by
        have h1 : (∏ i ∈ Finset.Ico (k u) j.val, ‖ξ (i + 1) u 1‖ ^ 2)
            = ∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), ‖ξ l u 1‖ ^ 2 := by
          refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_Ico] at hi ⊢
            omega
          · intro i₁ _ i₂ _ h
            exact Nat.succ.inj h
          · intro l hl
            simp only [Finset.mem_Ico] at hl
            refine ⟨l - 1, by simp only [Finset.mem_Ico]; omega, ?_⟩
            show (l - 1) + 1 = l
            omega
          · intro i hi
            rfl
        rw [h1]
        apply Finset.prod_le_prod₀
        · intro i _
          exact sq_nonneg _
        · intro i hi
          have hi' : k u + 1 ≤ i ∧ i < j.val + 1 := Finset.mem_Ico.mp hi
          have hlt : i < m := by omega
          have ha := hafter'' i (by omega) hlt u (by omega)
          rw [pow_two, pow_two]
          exact mul_self_le_mul_self (norm_nonneg _) ha
      have hstep := mul_le_mul hn1 hle
        (Finset.prod_nonneg fun i _ => sq_nonneg _) zero_le_one
      rwa [one_mul] at hstep
    have hbound' : (∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2) * (9 : ℝ) ^ (j.val + 1)
        ≤ (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 :=
      tail_prod_weighted_le δ (k u) j.val
        (fun l hl hl' => hδ'' l (by omega) (by omega)) hge
    have hp : 0 ≤ (9 : ℝ) ^ (j.val + 1) := pow_nonneg (by norm_num) _
    calc ‖ξ (j.val + 1) u 0‖ ^ 2 * contMass ξ u j.val * (9 : ℝ) ^ (j.val + 1)
        ≤ 1 * contMass ξ u j.val * (9 : ℝ) ^ (j.val + 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hnorm0 (contMass_nonneg ξ u j.val)) hp
      _ = contMass ξ u j.val * (9 : ℝ) ^ (j.val + 1) := by ring
      _ ≤ (∏ l ∈ Finset.Ico (k u + 1) (j.val + 1), δ l ^ 2) * (9 : ℝ) ^ (j.val + 1) :=
          mul_le_mul_of_nonneg_right hcm hp
      _ ≤ (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 := hbound'

  have hsum_split : ∀ (n : ℕ), n < m →
      (∑ j : Fin m, (if j.val + 1 < n then δ (j.val + 1) ^ 2 else 0))
        + (∑ j : Fin m, (if n + 1 < j.val + 1 then δ j.val ^ 2 else 0))
        ≤ (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
    intro n hn
    have hA : (∑ j : Fin m, (if j.val + 1 < n then δ (j.val + 1) ^ 2 else 0))
        = ∑ l ∈ Finset.Icc 1 (n - 1), δ l ^ 2 := by
      have h2 : (∑ j : Fin m, (if j.val + 1 < n then δ (j.val + 1) ^ 2 else 0))
          = ∑ i ∈ Finset.range m, (if i + 1 < n then δ (i + 1) ^ 2 else 0) :=
        Fin.sum_univ_eq_sum_range (fun k : ℕ => if k + 1 < n then δ (k + 1) ^ 2 else 0) m
      have h3 : (∑ i ∈ Finset.range m, (if i + 1 < n then δ (i + 1) ^ 2 else 0))
          = ∑ l ∈ Finset.Icc 1 m, (if l < n then δ l ^ 2 else 0) :=
        sum_range_add_one m (fun l => if l < n then δ l ^ 2 else 0)
      have h4 : (∑ l ∈ Finset.Icc 1 m, (if l < n then δ l ^ 2 else 0))
          = ∑ l ∈ Finset.Icc 1 (n - 1), δ l ^ 2 := by
        rw [← Finset.sum_filter]
        congr 1
        ext l
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, by omega⟩
        · intro ⟨h1, h2⟩
          exact ⟨⟨h1, by omega⟩, by omega⟩
      exact h2.trans (h3.trans h4)
    have hB : (∑ j : Fin m, (if n + 1 < j.val + 1 then δ j.val ^ 2 else 0))
        = ∑ l ∈ Finset.Icc (n + 1) (m - 1), δ l ^ 2 := by
      have h2 : (∑ j : Fin m, (if n + 1 < j.val + 1 then δ j.val ^ 2 else 0))
          = ∑ i ∈ Finset.range m, (if n + 1 < i + 1 then δ i ^ 2 else 0) :=
        Fin.sum_univ_eq_sum_range (fun k : ℕ => if n + 1 < k + 1 then δ k ^ 2 else 0) m
      have h3 : (∑ i ∈ Finset.range m, (if n + 1 < i + 1 then δ i ^ 2 else 0))
          = ∑ i ∈ Finset.range m, (if n + 1 ≤ i then δ i ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : n + 1 < i + 1 <;> by_cases h' : n + 1 ≤ i <;> simp [h, h'] <;> omega
      have h4 : (∑ i ∈ Finset.range m, (if n + 1 ≤ i then δ i ^ 2 else 0))
          = ∑ l ∈ Finset.Icc (n + 1) (m - 1), δ l ^ 2 := by
        rw [← Finset.sum_filter]
        congr 1
        ext l
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        constructor
        · intro ⟨h1, h2⟩
          exact ⟨h2, by omega⟩
        · intro ⟨h1, h2⟩
          exact ⟨by omega, h1⟩
      exact h2.trans (h3.trans h4)
    have hdisj : Disjoint (Finset.Icc 1 (n - 1)) (Finset.Icc (n + 1) (m - 1)) := by
      apply Finset.disjoint_left.mpr
      intro l hl1 hl2
      simp only [Finset.mem_Icc] at hl1 hl2
      omega
    have hsub : Finset.Icc 1 (n - 1) ∪ Finset.Icc (n + 1) (m - 1) ⊆ Finset.Icc 1 m := by
      intro l hl
      simp only [Finset.mem_union, Finset.mem_Icc] at hl ⊢
      omega
    have hle : (∑ l ∈ Finset.Icc 1 (n - 1), δ l ^ 2)
        + (∑ l ∈ Finset.Icc (n + 1) (m - 1), δ l ^ 2)
        ≤ ∑ l ∈ Finset.Icc 1 m, δ l ^ 2 := by
      rw [← Finset.sum_union hdisj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => sq_nonneg _)
    have hfinal : (∑ l ∈ Finset.Icc 1 m, δ l ^ 2) ≤ (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
      have h := sum_sq_le_sq_sum (s := (Finset.univ : Finset (Fin m)))
        (f := fun j => δ (j.val + 1)) (fun j _ => (hδ' j.val j.is_lt).1)
      have h2 : (∑ l ∈ Finset.Icc 1 m, δ l ^ 2) = ∑ j : Fin m, δ (j.val + 1) ^ 2 :=
        (sum_fin_add_one m (fun l => δ l ^ 2)).symm
      rw [h2]
      exact h
    rw [hA, hB]
    exact hle.trans hfinal

  have hbefore_le : ∀ (u : I) (j : Fin m), j.val + 1 < k u →
      ‖ζ (j.val + 1) u‖ ^ 2 ≤ δ (j.val + 1) ^ 2 := by
    intro u j hj
    have hj' : 0 < j.val + 1 := Nat.succ_pos _
    rw [hζ, stopCoefficient_sq u hj', Nat.add_sub_cancel]
    have hb := hbefore' j.val j.is_lt u hj
    have hc : contMass ξ u j.val ≤ 1 :=
      contMass_le_one ξ u j.is_lt.le (fun l hl => hnorm' l (by omega) u)
    have hd0 : 0 ≤ δ (j.val + 1) := (hδ' j.val j.is_lt).1
    have hp2 : ‖ξ (j.val + 1) u 0‖ ^ 2 ≤ δ (j.val + 1) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hd0]
      exact hb
    have hnn : 0 ≤ contMass ξ u j.val := contMass_nonneg ξ u j.val
    have hstep : ‖ξ (j.val + 1) u 0‖ ^ 2 * contMass ξ u j.val
        ≤ ‖ξ (j.val + 1) u 0‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    linarith
  have hafter_le : ∀ (u : I) (j : Fin m), k u + 1 < j.val + 1 →
      ‖ζ (j.val + 1) u‖ ^ 2 ≤ δ j.val ^ 2 := by
    intro u j hj
    exact stop_after_le δ m (k u) u (fun l hl => hδ' l hl)
      (fun l hl => hnorm' l hl u) (fun l hl h' => hafter' l hl u h') j.is_lt hj
  have key_uw : ∀ u : I,
      (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
        ‖ζ (j.val + 1) u‖ ^ 2 else 0))
        ≤ (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
    intro u
    have hn : k u < m := hk u
    rw [hsplit (k u) (fun j => ‖ζ (j.val + 1) u‖ ^ 2)]
    have h1 : (∑ j : Fin m, (if j.val + 1 < k u then
        ‖ζ (j.val + 1) u‖ ^ 2 else 0))
        ≤ ∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j.val + 1 < k u
      · simp [h]
        exact hbefore_le u j h
      · simp [h]
    have h2 : (∑ j : Fin m, (if k u + 1 < j.val + 1 then
        ‖ζ (j.val + 1) u‖ ^ 2 else 0))
        ≤ ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : k u + 1 < j.val + 1
      · simp [h]
        exact hafter_le u j h
      · simp [h]
    exact (add_le_add h1 h2).trans (hsum_split (k u) hn)

  have key_w : ∀ u : I,
      (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
        ‖ζ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
        ≤ (9 : ℝ) ^ (k u + 2) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
    intro u
    have hn : k u < m := hk u
    rw [hsplit (k u) (fun j => ‖ζ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1))]
    have h1 : (∑ j : Fin m, (if j.val + 1 < k u then
        ‖ζ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
        ≤ (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0) := by
      have h1a : (∑ j : Fin m, (if j.val + 1 < k u then
          ‖ζ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
          ≤ ∑ j : Fin m, (if j.val + 1 < k u then
            (9 : ℝ) ^ (k u + 2) * δ (j.val + 1) ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : j.val + 1 < k u
        · simp [h]
          exact hbefore_w u j h
        · simp [h]
      have h1b : (∑ j : Fin m, (if j.val + 1 < k u then
          (9 : ℝ) ^ (k u + 2) * δ (j.val + 1) ^ 2 else 0))
          = (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by
          by_cases h : j.val + 1 < k u <;> simp [h])
      exact h1a.trans (le_of_eq h1b)
    have h2 : (∑ j : Fin m, (if k u + 1 < j.val + 1 then
        ‖ζ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
        ≤ (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0) := by
      have h2a : (∑ j : Fin m, (if k u + 1 < j.val + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * (9 : ℝ) ^ (j.val + 1) else 0))
          ≤ ∑ j : Fin m, (if k u + 1 < j.val + 1 then
            (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : k u + 1 < j.val + 1
        · simp [h]
          exact hafter_w u j h
        · simp [h]
      have h2b : (∑ j : Fin m, (if k u + 1 < j.val + 1 then
          (9 : ℝ) ^ (k u + 2) * δ j.val ^ 2 else 0))
          = (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by
          by_cases h : k u + 1 < j.val + 1 <;> simp [h])
      exact h2a.trans (le_of_eq h2b)
    have h3 := add_le_add h1 h2
    have h4 : (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0)
        + (9 : ℝ) ^ (k u + 2) * ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0)
        = (9 : ℝ) ^ (k u + 2) *
          ((∑ j : Fin m, (if j.val + 1 < k u then δ (j.val + 1) ^ 2 else 0))
            + ∑ j : Fin m, (if k u + 1 < j.val + 1 then δ j.val ^ 2 else 0)) := by
      ring
    rw [h4] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (hsum_split (k u) hn)
      (pow_nonneg (by positivity) _))

  intro p1 p pn pf pbm
  have hn2 (H : Type) [Fintype H] (v : QState H) : (normVec v) ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
    norm_toEuclidean_fromVec_sq v

  have hpoint : ∀ p : Fin m × I,
      ‖nearBandState m k γ ζ p‖ ^ 2 ≤ ‖weightedBandState m γ ζ p‖ ^ 2 := by
    intro p
    simp only [nearBandState]
    split_ifs with h
    · exact @le_refl ℝ _ _
    · have : ‖(0 : ℂ)‖ ^ 2 = 0 := by simp [norm_zero]
      rw [this]
      exact sq_nonneg _

  have h5 : pn ≤ pf := by
    show (normVec (nearBandState m k γ ζ)) ^ 2 ≤ (normVec (weightedBandState m γ ζ)) ^ 2
    have h1 : (normVec (nearBandState m k γ ζ)) ^ 2
        = ∑ p : Fin m × I, ‖nearBandState m k γ ζ p‖ ^ 2 :=
      norm_toEuclidean_fromVec_sq _
    have h2 : (normVec (weightedBandState m γ ζ)) ^ 2
        = ∑ p : Fin m × I, ‖weightedBandState m γ ζ p‖ ^ 2 :=
      norm_toEuclidean_fromVec_sq _
    rw [h1, h2]
    exact Finset.sum_le_sum fun p _ => hpoint p

  have hpf_eq : pf = ∑ u : I, ‖γ u‖ ^ 2 * ∑ j : Fin m,
      ‖ζ (j.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (j.val + 1) / (9 : ℝ) ^ m) := by
    show (normVec (weightedBandState m γ ζ)) ^ 2 = _
    have hn : (normVec (weightedBandState m γ ζ)) ^ 2
        = ∑ p : Fin m × I, ‖weightedBandState m γ ζ p‖ ^ 2 :=
      norm_toEuclidean_fromVec_sq _
    rw [hn]
    simp only [weightedBandState]
    have hterm : ∀ p : Fin m × I,
        ‖γ p.2 * ζ (p.1.val + 1) p.2 * ((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m : ℂ)‖ ^ 2
        = ‖γ p.2‖ ^ 2 * ‖ζ (p.1.val + 1) p.2‖ ^ 2 * ((9 : ℝ) ^ (p.1.val + 1) / (9 : ℝ) ^ m) := by
      intro p
      have h1 : ‖γ p.2 * ζ (p.1.val + 1) p.2 * ((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m : ℂ)‖
          = ‖γ p.2‖ * ‖ζ (p.1.val + 1) p.2‖ * ‖((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m : ℂ)‖ :=
        by rw [norm_mul, norm_mul]
      have h2 : ‖((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m : ℂ)‖
          = (3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m := by
        have h : (0:ℝ) ≤ (3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m :=
          div_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_div]
        exact Complex.norm_of_nonneg h
      rw [h1, h2, mul_pow, mul_pow, three_pow_div_sq]
    rw [Finset.sum_congr rfl (fun p _ => hterm p)]

    have hsplit_pf : (∑ p : Fin m × I, ‖γ p.2‖ ^ 2 * ‖ζ (p.1.val + 1) p.2‖ ^ 2
          * ((9 : ℝ) ^ (p.1.val + 1) / (9 : ℝ) ^ m))
        = ∑ u : I, ‖γ u‖ ^ 2 * ∑ j : Fin m,
          ‖ζ (j.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (j.val + 1) / (9 : ℝ) ^ m) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      calc (∑ x : Fin m, ‖γ u‖ ^ 2 * ‖ζ (x.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (x.val + 1) / (9 : ℝ) ^ m))
          = ∑ x : Fin m, ‖γ u‖ ^ 2 * (‖ζ (x.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (x.val + 1) / (9 : ℝ) ^ m)) :=
            Finset.sum_congr rfl (fun x _ => by rw [mul_assoc])
        _ = ‖γ u‖ ^ 2 * ∑ x : Fin m, ‖ζ (x.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (x.val + 1) / (9 : ℝ) ^ m) :=
            (Finset.mul_sum _ _ _).symm
    rw [hsplit_pf]

  have hpn_eq : pn = ∑ u : I, ‖γ u‖ ^ 2 * ∑ j : Fin m,
      (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then
        ‖ζ (j.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (j.val + 1) / (9 : ℝ) ^ m) else 0) := by
    show (normVec (nearBandState m k γ ζ)) ^ 2 = _
    have hn : (normVec (nearBandState m k γ ζ)) ^ 2
        = ∑ p : Fin m × I, ‖nearBandState m k γ ζ p‖ ^ 2 :=
      norm_toEuclidean_fromVec_sq _
    rw [hn]
    simp only [nearBandState]
    have hterm : ∀ p : Fin m × I,
        ‖(if p.1.val + 1 = k p.2 ∨ p.1.val + 1 = k p.2 + 1 then
          weightedBandState m γ ζ p else 0)‖ ^ 2
        = (if p.1.val + 1 = k p.2 ∨ p.1.val + 1 = k p.2 + 1 then
          ‖weightedBandState m γ ζ p‖ ^ 2 else 0) := by
      intro p
      split_ifs with h
      · rfl
      · simp
    rw [Finset.sum_congr rfl (fun p _ => hterm p)]
    have hterm2 : ∀ p : Fin m × I,
        (if p.1.val + 1 = k p.2 ∨ p.1.val + 1 = k p.2 + 1 then
          ‖weightedBandState m γ ζ p‖ ^ 2 else 0)
        = (if p.1.val + 1 = k p.2 ∨ p.1.val + 1 = k p.2 + 1 then
          ‖γ p.2‖ ^ 2 * ‖ζ (p.1.val + 1) p.2‖ ^ 2 * ((9 : ℝ) ^ (p.1.val + 1) / (9 : ℝ) ^ m) else 0) := by
      intro p
      split_ifs with h
      · simp only [weightedBandState]
        have h1 : ‖γ p.2 * ζ (p.1.val + 1) p.2 * ((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m : ℂ)‖
            = ‖γ p.2‖ * ‖ζ (p.1.val + 1) p.2‖ * ‖((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m : ℂ)‖ :=
          by rw [norm_mul, norm_mul]
        have h2 : ‖((3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m : ℂ)‖
            = (3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m := by
          have h : (0:ℝ) ≤ (3 : ℝ) ^ (p.1.val + 1) / (3 : ℝ) ^ m :=
            div_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)
          rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_div]
          exact Complex.norm_of_nonneg h
        rw [h1, h2, mul_pow, mul_pow, three_pow_div_sq]
      · rfl
    rw [Finset.sum_congr rfl (fun p _ => hterm2 p)]
    have hsplit_pn : (∑ p : Fin m × I,
          (if p.1.val + 1 = k p.2 ∨ p.1.val + 1 = k p.2 + 1 then
            ‖γ p.2‖ ^ 2 * ‖ζ (p.1.val + 1) p.2‖ ^ 2 * ((9 : ℝ) ^ (p.1.val + 1) / (9 : ℝ) ^ m) else 0))
        = ∑ u : I, ‖γ u‖ ^ 2 * ∑ j : Fin m,
          (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then
            ‖ζ (j.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (j.val + 1) / (9 : ℝ) ^ m) else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      calc (∑ x : Fin m, (if x.val + 1 = k u ∨ x.val + 1 = k u + 1 then
            ‖γ u‖ ^ 2 * ‖ζ (x.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (x.val + 1) / (9 : ℝ) ^ m) else 0))
          = ∑ x : Fin m, ‖γ u‖ ^ 2 * (if x.val + 1 = k u ∨ x.val + 1 = k u + 1 then
            ‖ζ (x.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (x.val + 1) / (9 : ℝ) ^ m) else 0) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            by_cases h : x.val + 1 = k u ∨ x.val + 1 = k u + 1
            · rw [ite_eq_left h, ite_eq_left h]; exact @mul_assoc ℝ _ _ _ _
            · rw [ite_eq_right h, ite_eq_right h]; ring
        _ = ‖γ u‖ ^ 2 * ∑ x : Fin m, (if x.val + 1 = k u ∨ x.val + 1 = k u + 1 then
            ‖ζ (x.val + 1) u‖ ^ 2 * ((9 : ℝ) ^ (x.val + 1) / (9 : ℝ) ^ m) else 0) :=
            (Finset.mul_sum _ _ _).symm
    rw [hsplit_pn]

  have hpf_pn : pf - pn = bandLeakage m k γ ζ true := by
    rw [hpf_eq, hpn_eq]
    simp only [bandLeakage]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← mul_sub]
    refine congr_arg₂ _ rfl ?_
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : j.val + 1 = k u ∨ j.val + 1 = k u + 1
    · have h2 : ¬(j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1) := by
        intro hne
        exact absurd (h1.resolve_right hne.2) hne.1
      rw [ite_eq_left h1, ite_eq_right h2]
      exact sub_self _
    · have h2 : j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 := by
        constructor
        · intro h; exact h1 (Or.inl h)
        · intro h; exact h1 (Or.inr h)
      rw [ite_eq_right h1, ite_eq_left h2, mul_div_assoc]
      simp only [ite_true]
      exact sub_zero _

  have hleak_nonneg : 0 ≤ bandLeakage m k γ ζ true := by
    simp only [bandLeakage]
    apply Finset.sum_nonneg
    intro u _
    apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) _))
        (pow_nonneg (by positivity) _)
    · exact le_rfl

  have h_pn_le_pf : pn ≤ pf := by
    have := hleak_nonneg
    linarith [hpf_pn]

  have hout_nonneg : ∀ u : I,
      0 ≤ ∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0) := by
    intro u
    apply Finset.sum_nonneg
    intro j _
    by_cases h : j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1
    · rw [ite_eq_left h]; exact sq_nonneg _
    · rw [ite_eq_right h]

  have hcompl : ∀ (u : I) (f : Fin m → ℝ),
      (∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then f j else 0))
      + (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then f j else 0))
      = ∑ j : Fin m, f j := by
    intro u f
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j.val + 1 = k u ∨ j.val + 1 = k u + 1
    · have h2 : ¬(j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1) := by
        intro hne
        exact absurd (h.resolve_right hne.2) hne.1
      rw [ite_eq_left h, ite_eq_right h2]
      exact add_zero _
    · have h2 : j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 :=
        ⟨fun heq => h (Or.inl heq), fun heq => h (Or.inr heq)⟩
      rw [ite_eq_right h, ite_eq_left h2]
      exact zero_add _

  have hin_out : ∀ u : I,
      (∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0))
      + (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0))
      = 1 := fun u => (hcompl u fun j => ‖ζ (j.val + 1) u‖ ^ 2).trans (hparseval u)

  have hin_ge : ∀ u : I,
      1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2
        ≤ ∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0) := by
    intro u; linarith [hin_out u, key_uw u]

  have hin_le : ∀ u : I,
      (∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0)) ≤ 1 := by
    intro u; linarith [hin_out u, hout_nonneg u]

  have hpt_ge : ∀ (u : I) (j : Fin m), (j.val + 1 = k u ∨ j.val + 1 = k u + 1) →
      (9:ℝ)^(k u) ≤ (9:ℝ)^(j.val + 1) := by
    intro u j hj
    have hle : k u ≤ j.val + 1 := by omega
    exact pow_le_pow_right₀ (by norm_num) hle
  have hpt_le : ∀ (u : I) (j : Fin m), (j.val + 1 = k u ∨ j.val + 1 = k u + 1) →
      (9:ℝ)^(j.val + 1) ≤ (9:ℝ)^(k u + 1) := by
    intro u j hj
    have hle : j.val + 1 ≤ k u + 1 := by omega
    exact pow_le_pow_right₀ (by norm_num) hle

  have hS_ge : ∀ u : I,
      ((9:ℝ)^(k u) / (9:ℝ)^m) *
        (∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0))
      ≤ ∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then
        ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(j.val + 1) / (9:ℝ)^m) else 0) := by
    intro u
    have h1 : ((9:ℝ)^(k u) / (9:ℝ)^m) *
        (∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0))
        = ∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(k u) / (9:ℝ)^m) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j.val + 1 = k u ∨ j.val + 1 = k u + 1
      · rw [ite_eq_left h, ite_eq_left h]; ring
      · rw [ite_eq_right h, ite_eq_right h]; ring
    rw [h1]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : j.val + 1 = k u ∨ j.val + 1 = k u + 1
    · rw [ite_eq_left h, ite_eq_left h]
      exact mul_le_mul_of_nonneg_left
        (by rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (hpt_ge u j h)
              (inv_nonneg.mpr (pow_nonneg (by norm_num) _))) (sq_nonneg _)
    · rw [ite_eq_right h, ite_eq_right h]

  have hS_le : ∀ u : I,
      ∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then
        ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(j.val + 1) / (9:ℝ)^m) else 0)
      ≤ ((9:ℝ)^(k u + 1) / (9:ℝ)^m) *
        (∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0)) := by
    intro u
    have h1 : ((9:ℝ)^(k u + 1) / (9:ℝ)^m) *
        (∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then ‖ζ (j.val + 1) u‖ ^ 2 else 0))
        = ∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(k u + 1) / (9:ℝ)^m) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j.val + 1 = k u ∨ j.val + 1 = k u + 1
      · rw [ite_eq_left h, ite_eq_left h]; ring
      · rw [ite_eq_right h, ite_eq_right h]; ring
    rw [h1]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : j.val + 1 = k u ∨ j.val + 1 = k u + 1
    · rw [ite_eq_left h, ite_eq_left h]
      exact mul_le_mul_of_nonneg_left
        (by rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (hpt_le u j h)
              (inv_nonneg.mpr (pow_nonneg (by norm_num) _))) (sq_nonneg _)
    · rw [ite_eq_right h, ite_eq_right h]

  have hp1_div : p1 / 9 = ∑ u : I, ‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m := by
    show (singleBandProbability m k γ) / 9 = _
    unfold singleBandProbability
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun u _ => by
      have : (‖γ u‖ ^ 2 * (9:ℝ)^(k u + 1) / (9:ℝ)^m) / 9
          = ‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m := by
        field_simp
        rw [pow_succ]
        ring
      exact this

  have hE_nonneg : 0 ≤ ∑ j : Fin m, δ (j.val + 1) :=
    Finset.sum_nonneg fun j _ => (hδ' j.val j.is_lt).1
  have hlt' : (∑ j : Fin m, δ (j.val + 1)) < 1 := hlt
  have hE2_pos : 0 < 1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by nlinarith [hE_nonneg, hlt']

  have h_part3 : p1 / 9 * (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2) ≤ pn := by
    rw [hp1_div, hpn_eq, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro u _
    have hg : 0 ≤ ‖γ u‖ ^ 2 := sq_nonneg _
    have hpow : 0 ≤ (9:ℝ)^(k u) / (9:ℝ)^m :=
      div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
    have hchain : ((9:ℝ)^(k u) / (9:ℝ)^m) * (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)
        ≤ ∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(j.val + 1) / (9:ℝ)^m) else 0) :=
      (mul_le_mul_of_nonneg_left (hin_ge u) hpow).trans (hS_ge u)
    have hrearr : ‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m * (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)
        = ‖γ u‖ ^ 2 * (((9:ℝ)^(k u) / (9:ℝ)^m) * (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)) := by
      rw [mul_div_assoc, mul_assoc]
    rw [hrearr]
    exact mul_le_mul_of_nonneg_left hchain hg

  have h_part4 : pn ≤ p1 := by
    rw [hpn_eq]
    show _ ≤ singleBandProbability m k γ
    unfold singleBandProbability
    apply Finset.sum_le_sum
    intro u _
    have hg : 0 ≤ ‖γ u‖ ^ 2 := sq_nonneg _
    have hpow : 0 ≤ (9:ℝ)^(k u + 1) / (9:ℝ)^m :=
      div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
    have hchain : ∑ j : Fin m, (if j.val + 1 = k u ∨ j.val + 1 = k u + 1 then
        ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(j.val + 1) / (9:ℝ)^m) else 0)
        ≤ (9:ℝ)^(k u + 1) / (9:ℝ)^m :=
      (hS_le u).trans (by
        have := mul_le_mul_of_nonneg_left (hin_le u) hpow
        rwa [mul_one] at this)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hchain hg

  have hleakW : bandLeakage m k γ ζ true
      ≤ (9:ℝ) * p1 * (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
    show (∑ u : I, ‖γ u‖ ^ 2 * ∑ j : Fin m,
        (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * (9:ℝ)^(j.val + 1) / (9:ℝ)^m else 0))
      ≤ (9:ℝ) * p1 * (∑ j : Fin m, δ (j.val + 1)) ^ 2
    have hinner : ∀ u : I,
        (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * (9:ℝ)^(j.val + 1) / (9:ℝ)^m else 0))
        = (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * (9:ℝ)^(j.val + 1) else 0)) / (9:ℝ)^m := by
      intro u
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h]
        exact (zero_div _).symm
    have hrew : (∑ u : I, ‖γ u‖ ^ 2 * ∑ j : Fin m,
        (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * (9:ℝ)^(j.val + 1) / (9:ℝ)^m else 0))
        = ∑ u : I, ‖γ u‖ ^ 2 *
          ((∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
            ‖ζ (j.val + 1) u‖ ^ 2 * (9:ℝ)^(j.val + 1) else 0)) / (9:ℝ)^m) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hinner]
    rw [hrew]
    have hstep : ∀ u : I,
        ‖γ u‖ ^ 2 *
          ((∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
            ‖ζ (j.val + 1) u‖ ^ 2 * (9:ℝ)^(j.val + 1) else 0)) / (9:ℝ)^m)
        ≤ ‖γ u‖ ^ 2 * ((9:ℝ)^(k u + 2) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 / (9:ℝ)^m) := by
      intro u
      have hg : 0 ≤ ‖γ u‖ ^ 2 := sq_nonneg _
      have hdiv : (∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
          ‖ζ (j.val + 1) u‖ ^ 2 * (9:ℝ)^(j.val + 1) else 0)) / (9:ℝ)^m
          ≤ (9:ℝ)^(k u + 2) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 / (9:ℝ)^m := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (key_w u)
          (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
      exact mul_le_mul_of_nonneg_left hdiv hg
    have h1 : (∑ u : I, ‖γ u‖ ^ 2 *
          ((∑ j : Fin m, (if j.val + 1 ≠ k u ∧ j.val + 1 ≠ k u + 1 then
            ‖ζ (j.val + 1) u‖ ^ 2 * (9:ℝ)^(j.val + 1) else 0)) / (9:ℝ)^m))
        ≤ ∑ u : I, ‖γ u‖ ^ 2 * ((9:ℝ)^(k u + 2) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 / (9:ℝ)^m) :=
      Finset.sum_le_sum fun u _ => hstep u
    have hrearr : ∀ u : I,
        ‖γ u‖ ^ 2 * ((9:ℝ)^(k u + 2) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 / (9:ℝ)^m)
        = (‖γ u‖ ^ 2 * (9:ℝ)^(k u + 2) / (9:ℝ)^m) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
      intro u
      field_simp
    have h2 : (∑ u : I, ‖γ u‖ ^ 2 * ((9:ℝ)^(k u + 2) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 / (9:ℝ)^m))
        = (∑ u : I, ‖γ u‖ ^ 2 * (9:ℝ)^(k u + 2) / (9:ℝ)^m) * (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => hrearr u
    rw [h2] at h1
    have hsum9 : (∑ u : I, ‖γ u‖ ^ 2 * (9:ℝ)^(k u + 2) / (9:ℝ)^m) = (9:ℝ) * p1 := by
      have h1' : ∀ u : I, ‖γ u‖ ^ 2 * (9:ℝ)^(k u + 2) / (9:ℝ)^m
          = (81:ℝ) * (‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m) := by
        intro u
        have hpow : (9:ℝ)^(k u + 2) = (81:ℝ) * (9:ℝ)^(k u) := by
          rw [pow_add, show (9:ℝ)^2 = 81 by norm_num]
          ring
        rw [hpow]
        field_simp
      rw [show (∑ u : I, ‖γ u‖ ^ 2 * (9:ℝ)^(k u + 2) / (9:ℝ)^m)
          = ∑ u : I, (81:ℝ) * (‖γ u‖ ^ 2 * (9:ℝ)^(k u) / (9:ℝ)^m) by
        exact Finset.sum_congr rfl fun u _ => h1' u]
      rw [← Finset.mul_sum, ← hp1_div]
      field_simp; try ring
    rw [hsum9] at h1
    exact h1

  have hp1_le : p1 ≤ (9:ℝ) * pn / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2) := by
    have h := h_part3
    have h9pos : (0:ℝ) < 9 := by norm_num
    have hmul : p1 * (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2) ≤ (9:ℝ) * pn := by
      have := mul_le_mul_of_nonneg_left h (le_of_lt h9pos)
      have h9 : (9:ℝ) * (p1 / 9 * (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2))
          = p1 * (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2) := by
        field_simp
      rw [← h9]
      exact this
    rw [le_div_iff₀ hE2_pos]
    exact hmul

  have h_part6 : pf ≤ pn * (1 + (9:ℝ)^3 * (∑ j : Fin m, δ (j.val + 1)) ^ 2
      / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2) := by
    have hpf_eq2 : pf = pn + bandLeakage m k γ ζ true := by linarith [hpf_pn]
    have hE2 : 0 ≤ (∑ j : Fin m, δ (j.val + 1)) ^ 2 := sq_nonneg _
    have h1epos : 0 < (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2 := by nlinarith [hE_nonneg, hlt']
    have h1e_le : (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2
        ≤ 1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2 := by nlinarith [hE_nonneg, hlt']

    have hleak_bound : bandLeakage m k γ ζ true
        ≤ (81:ℝ) * pn * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2) := by
      have h1 := hleakW
      have h2 := hp1_le
      have hinner := mul_le_mul_of_nonneg_right h2 hE2
      have houter := mul_le_mul_of_nonneg_left hinner (by norm_num : 0 ≤ (9:ℝ))
      rw [← mul_assoc, ← mul_assoc] at houter
      have h4 : (9:ℝ) * ((9:ℝ) * pn / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2))
          * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          = (81:ℝ) * pn * (∑ j : Fin m, δ (j.val + 1)) ^ 2
            / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2) := by
        field_simp; try ring
      exact le_trans h1 (le_trans houter (le_of_eq h4))
    have hre : pn + (81:ℝ) * pn * (∑ j : Fin m, δ (j.val + 1)) ^ 2
        / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)
        = pn * (1 + (81:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)) := by
      field_simp
    have hstep1 : pf ≤ pn * (1 + (81:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
        / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)) := by
      have hpf_eq2' : pf = pn + bandLeakage m k γ ζ true := by linarith [hpf_pn]
      rw [hpf_eq2', ← hre]
      linarith [hleak_bound]

    have hkey6 : (81:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
        / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)
        ≤ (729:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2 := by
      have hdiv : (81:ℝ) / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)
          ≤ (81:ℝ) / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num : 0 ≤ (81:ℝ)) h1epos h1e_le
      have hdiv2 : (81:ℝ) / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2
          ≤ (729:ℝ) / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2 := by
        gcongr; norm_num
      have h6 := hdiv.trans hdiv2
      have := mul_le_mul_of_nonneg_left h6 hE2
      have hr1 : (81:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)
          = (∑ j : Fin m, δ (j.val + 1)) ^ 2
            * ((81:ℝ) / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)) := by
        rw [mul_comm, mul_div_assoc]
      have hr2 : (729:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2
          = (∑ j : Fin m, δ (j.val + 1)) ^ 2
            * ((729:ℝ) / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2) := by
        rw [mul_comm, mul_div_assoc]
      rw [hr1, hr2]
      exact this
    have hmulpos : 0 ≤ pn := by
      rw [hpn_eq]
      exact Finset.sum_nonneg fun u _ => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => by
        by_cases h : j.val + 1 = k u ∨ j.val + 1 = k u + 1
        · rw [ite_eq_left h]; positivity
        · rw [ite_eq_right h])
    have hre2 : pn * (1 + (729:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
        / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2)
        = pn * (1 + (9:ℝ)^3 * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2) := by
      rw [show (9:ℝ)^3 = 729 by norm_num]
    have h : (1:ℝ) + (81:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
        / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)
        ≤ 1 + (729:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2 := by
      linarith [hkey6]
    calc pf ≤ pn * (1 + (81:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1)) ^ 2)) := hstep1
      _ ≤ pn * (1 + (729:ℝ) * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2) :=
        mul_le_mul_of_nonneg_left h hmulpos
      _ = pn * (1 + (9:ℝ)^3 * (∑ j : Fin m, δ (j.val + 1)) ^ 2
          / (1 - (∑ j : Fin m, δ (j.val + 1))) ^ 2) := hre2

  have hpf_le1 : pf ≤ 1 := by
    rw [hpf_eq]
    have hinner : ∀ u : I,
        (∑ j : Fin m, ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(j.val + 1) / (9:ℝ)^m))
        ≤ 1 := by
      intro u
      have h1 : (∑ j : Fin m, ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(j.val + 1) / (9:ℝ)^m))
          ≤ ∑ j : Fin m, ‖ζ (j.val + 1) u‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hp : 0 ≤ ‖ζ (j.val + 1) u‖ ^ 2 := sq_nonneg _
        have hd : (9:ℝ)^(j.val + 1) / (9:ℝ)^m ≤ 1 :=
          (div_le_one (pow_pos (by norm_num) _)).mpr (pow_le_pow_right₀ (by norm_num) (by omega))
        have h := mul_le_mul_of_nonneg_left hd hp
        rw [mul_one] at h
        exact h
      have h2 : ∑ j : Fin m, ‖ζ (j.val + 1) u‖ ^ 2 = 1 := hparseval u
      linarith
    have hstep : (∑ u : I, ‖γ u‖ ^ 2 * ∑ j : Fin m, ‖ζ (j.val + 1) u‖ ^ 2 * ((9:ℝ)^(j.val + 1) / (9:ℝ)^m))
        ≤ ∑ u : I, ‖γ u‖ ^ 2 * 1 := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left (hinner u) (sq_nonneg _)
    have hrew : (∑ u : I, ‖γ u‖ ^ 2 * 1) = ∑ u : I, ‖γ u‖ ^ 2 :=
      Finset.sum_congr rfl fun u _ => mul_one _
    have hγ1 : ∑ u : I, ‖γ u‖ ^ 2 = 1 := hγ
    rw [hrew, hγ1] at hstep
    exact hstep

  have hw_le1 : normVec (weightedBandState m γ ζ) ≤ 1 := by
    have hnn : 0 ≤ normVec (weightedBandState m γ ζ) := norm_nonneg _
    have hsq : (normVec (weightedBandState m γ ζ)) ^ 2 ≤ 1 := by
      show pf ≤ 1
      exact hpf_le1
    nlinarith [sq_nonneg (normVec (weightedBandState m γ ζ) - 1)]

  have hsub : abs (normVec (weightedBandState m γ ζ) - normVec χ)
      ≤ normVec (χ - weightedBandState m γ ζ) := by
    rw [abs_sub_comm]
    have h := abs_norm_sub_norm_le (toEuclidean_fromVec χ)
      (toEuclidean_fromVec (weightedBandState m γ ζ))
    have h2 : toEuclidean_fromVec (χ - weightedBandState m γ ζ)
        = toEuclidean_fromVec χ - toEuclidean_fromVec (weightedBandState m γ ζ) := rfl
    unfold normVec at h ⊢
    rw [h2]
    exact h

  have h_part7 : abs (pf - pbm) ≤ 4 * εbm := by
    show abs ((normVec (weightedBandState m γ ζ)) ^ 2 - (normVec χ) ^ 2) ≤ 4 * εbm
    have hsq : abs ((normVec (weightedBandState m γ ζ)) ^ 2 - (normVec χ) ^ 2)
        = abs (normVec (weightedBandState m γ ζ) - normVec χ) *
          (normVec (weightedBandState m γ ζ) + normVec χ) := by
      have h1 : (normVec (weightedBandState m γ ζ)) ^ 2 - (normVec χ) ^ 2
          = (normVec (weightedBandState m γ ζ) + normVec χ) *
            (normVec (weightedBandState m γ ζ) - normVec χ) := sq_sub_sq _ _
      rw [h1, abs_mul]
      have h2 : |normVec (weightedBandState m γ ζ) + normVec χ|
          = normVec (weightedBandState m γ ζ) + normVec χ :=
        abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      rw [h2, mul_comm]
    rw [hsq]
    have hsum : normVec (weightedBandState m γ ζ) + normVec χ ≤ 2 := by linarith
    have hnn : 0 ≤ normVec (weightedBandState m γ ζ) + normVec χ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hnn2 : 0 ≤ normVec (χ - weightedBandState m γ ζ) := norm_nonneg _
    have h1 : abs (normVec (weightedBandState m γ ζ) - normVec χ) *
        (normVec (weightedBandState m γ ζ) + normVec χ)
        ≤ normVec (χ - weightedBandState m γ ζ) *
          (normVec (weightedBandState m γ ζ) + normVec χ) :=
      mul_le_mul_of_nonneg_right hsub hnn
    have h2 : normVec (χ - weightedBandState m γ ζ) *
        (normVec (weightedBandState m γ ζ) + normVec χ)
        ≤ normVec (χ - weightedBandState m γ ζ) * 2 :=
      mul_le_mul_of_nonneg_left hsum hnn2
    have h3 : normVec (χ - weightedBandState m γ ζ) * 2 ≤ 2 * εbm * 2 := by
      linarith [hdiff]
    linarith

  exact ⟨h_p1_9_le_p, h_p_le_p1, h_part3, h_part4, h_pn_le_pf, h_part6, h_part7⟩

end Qatlib.Papers.QLSStatePrep24.SpectralLeak
