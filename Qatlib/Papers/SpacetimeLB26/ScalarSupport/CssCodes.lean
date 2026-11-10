/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes

open scoped BigOperators
open Finset

def binomPMF (N : ℕ) (p : ℝ) (x : ℕ) : ℝ :=
  (N.choose x : ℝ) * p ^ x * (1 - p) ^ (N - x)

def binomTail (N : ℕ) (p Δ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N p x

theorem binaryKL_pos (p Δ : ℝ) (hp : 0 < p) (hpΔ : p < Δ) (hΔ1 : Δ < 1) :
    0 < binaryKL Δ p := by
  have hΔp : 0 < Δ := lt_trans hp hpΔ
  have h1p : 0 < 1 - p := by linarith
  have h1Δ : 0 < 1 - Δ := by linarith
  have hpΔ1 : p / Δ ≠ 1 := by
    intro h
    rw [div_eq_iff (ne_of_gt hΔp)] at h
    linarith

  have hneglog : Real.log (Δ / p) = -Real.log (p / Δ) := by
    rw [Real.log_div (ne_of_gt hΔp) (ne_of_gt hp),
        Real.log_div (ne_of_gt hp) (ne_of_gt hΔp)]
    ring
  have hlt : Real.log (p / Δ) < p / Δ - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos hp hΔp) hpΔ1
  have hstrict1 : Δ - p < Δ * Real.log (Δ / p) := by
    have hloglb : Real.log (Δ / p) > 1 - p / Δ := by
      rw [hneglog]
      have : -(p / Δ - 1) = 1 - p / Δ := by ring
      linarith
    have hfield : Δ * (1 - p / Δ) = Δ - p := by
      field_simp [ne_of_gt hΔp]
    nlinarith

  have hneg2 : Real.log ((1 - Δ) / (1 - p)) = -Real.log ((1 - p) / (1 - Δ)) := by
    rw [Real.log_div (ne_of_gt h1Δ) (ne_of_gt h1p),
        Real.log_div (ne_of_gt h1p) (ne_of_gt h1Δ)]
    ring
  have hloglb2 : p - Δ ≤ (1 - Δ) * Real.log ((1 - Δ) / (1 - p)) := by
    have hlb : 1 - (1 - p) / (1 - Δ) ≤ Real.log ((1 - Δ) / (1 - p)) := by
      rw [hneg2]
      linarith [Real.log_le_sub_one_of_pos (div_pos h1p h1Δ)]
    have hkey : (1 - Δ) * (1 - (1 - p) / (1 - Δ)) = p - Δ := by
      field_simp [ne_of_gt h1Δ]
      ring
    calc p - Δ = (1 - Δ) * (1 - (1 - p) / (1 - Δ)) := hkey.symm
      _ ≤ (1 - Δ) * Real.log ((1 - Δ) / (1 - p)) :=
          mul_le_mul_of_nonneg_left hlb h1Δ.le
  show 0 < Δ * Real.log (Δ / p) + (1 - Δ) * Real.log ((1 - Δ) / (1 - p))
  linarith [hstrict1, hloglb2]

theorem binomial_chernoff_tail (N : ℕ) (p Δ : ℝ) (hp : 0 < p)
    (hpΔ : p < Δ) (hΔ1 : Δ < 1) :
    binomTail N p Δ ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) := by
  have hΔp : 0 < Δ := lt_trans hp hpΔ
  have h1p : 0 < 1 - p := by linarith
  have h1Δ : 0 < 1 - Δ := by linarith
  have hr₁01 : 0 < p / Δ ∧ p / Δ < 1 :=
    ⟨div_pos hp hΔp, (div_lt_one hΔp).2 hpΔ⟩
  have hr₂gt1 : 1 < (1 - p) / (1 - Δ) := by
    rw [one_lt_div h1Δ]
    linarith
  have hlogr₂ : 0 ≤ Real.log ((1 - p) / (1 - Δ)) := (Real.log_pos hr₂gt1).le

  have hexp : Real.exp (-(N : ℝ) * binaryKL Δ p)
      = (p / Δ) ^ (Δ * (N : ℝ)) * ((1 - p) / (1 - Δ)) ^ ((1 - Δ) * (N : ℝ)) := by
    have hneg1 : Real.log (Δ / p) = -Real.log (p / Δ) := by
      rw [Real.log_div (ne_of_gt hΔp) (ne_of_gt hp),
          Real.log_div (ne_of_gt hp) (ne_of_gt hΔp)]
      ring
    have hneg2 : Real.log ((1 - Δ) / (1 - p)) = -Real.log ((1 - p) / (1 - Δ)) := by
      rw [Real.log_div (ne_of_gt h1Δ) (ne_of_gt h1p),
          Real.log_div (ne_of_gt h1p) (ne_of_gt h1Δ)]
      ring
    rw [Real.rpow_def_of_pos (div_pos hp hΔp), Real.rpow_def_of_pos (div_pos h1p h1Δ),
      ← Real.exp_add, Real.exp_eq_exp]
    simp only [binaryKL, hneg1, hneg2]
    ring

  have hmono2 : ∀ a b : ℝ, a ≤ b →
      ((1 - p) / (1 - Δ)) ^ a ≤ ((1 - p) / (1 - Δ)) ^ b := by
    intro a b hab
    rw [Real.rpow_def_of_pos (div_pos h1p h1Δ), Real.rpow_def_of_pos (div_pos h1p h1Δ)]
    exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left hab hlogr₂)

  have hpoint : ∀ x : ℕ, x ≤ N → Δ * (N : ℝ) ≤ (x : ℝ) →
      binomPMF N p x ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) * binomPMF N Δ x := by
    intro x hxn hx
    have hx1 : (p / Δ) ^ x ≤ (p / Δ) ^ (Δ * (N : ℝ)) := by
      rw [← Real.rpow_natCast (p / Δ) x]
      exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hr₁01.1 hr₁01.2).2 hx
    have hsub : (((N - x : ℕ) : ℝ)) = (N : ℝ) - (x : ℝ) := by
      rw [Nat.cast_sub hxn]
    have hle2 : ((N - x : ℕ) : ℝ) ≤ (1 - Δ) * (N : ℝ) := by
      rw [hsub]
      have hexp : (N : ℝ) - (x : ℝ) ≤ (N : ℝ) - Δ * (N : ℝ) := by linarith
      have hring : (N : ℝ) - Δ * (N : ℝ) = (1 - Δ) * (N : ℝ) := by ring
      linarith
    have hxr2 : ((1 - p) / (1 - Δ)) ^ ((N - x : ℕ) : ℝ)
        ≤ ((1 - p) / (1 - Δ)) ^ ((1 - Δ) * (N : ℝ)) := hmono2 _ _ hle2
    have hprodle : (p / Δ) ^ x * ((1 - p) / (1 - Δ)) ^ ((N - x : ℕ) : ℝ)
        ≤ (p / Δ) ^ (Δ * (N : ℝ)) * ((1 - p) / (1 - Δ)) ^ ((1 - Δ) * (N : ℝ)) :=
      mul_le_mul hx1 hxr2
        (Real.rpow_nonneg (div_pos h1p h1Δ).le _)
        (Real.rpow_nonneg (div_pos hp hΔp).le _)
    have hnnΔ : 0 ≤ binomPMF N Δ x := by
      unfold binomPMF
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hΔp.le _))
        (pow_nonneg h1Δ.le _)
    calc binomPMF N p x
        = binomPMF N Δ x * ((p / Δ) ^ x * ((1 - p) / (1 - Δ)) ^ ((N - x : ℕ) : ℝ)) := by
          unfold binomPMF
          rw [Real.rpow_natCast, div_pow, div_pow]
          field_simp [pow_ne_zero _ (ne_of_gt hΔp), pow_ne_zero _ (ne_of_gt h1Δ)]
      _ ≤ binomPMF N Δ x * ((p / Δ) ^ (Δ * (N : ℝ)) *
            ((1 - p) / (1 - Δ)) ^ ((1 - Δ) * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hprodle hnnΔ
      _ = Real.exp (-(N : ℝ) * binaryKL Δ p) * binomPMF N Δ x := by
          rw [← hexp]
          ring

  have hnnΔall : ∀ x : ℕ, 0 ≤ binomPMF N Δ x := by
    intro x
    unfold binomPMF
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hΔp.le _))
      (pow_nonneg h1Δ.le _)
  have hsum : binomTail N p Δ
      ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) *
          (∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x) := by
    have hpt : ∀ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N,
        binomPMF N p x ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) * binomPMF N Δ x := by
      intro x hx
      have hmem := Finset.mem_Icc.mp hx
      have hceil : Δ * (N : ℝ) ≤ (x : ℝ) := by
        have hc := Nat.le_ceil (Δ * (N : ℝ))
        have hx' : ((Nat.ceil (Δ * (N : ℝ)) : ℕ) : ℝ) ≤ (x : ℝ) := by
          exact_mod_cast hmem.1
        linarith
      exact hpoint x hmem.2 hceil
    rw [binomTail, Finset.mul_sum]
    exact Finset.sum_le_sum hpt

  have htailΔ : (∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x) ≤ 1 := by
    have hsub : Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N ⊆ Finset.range (N + 1) := by
      intro x hx
      have hmem := Finset.mem_Icc.mp hx
      simp only [Finset.mem_range]
      omega
    have hsd : (∑ x ∈ Finset.range (N + 1) \ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N,
          binomPMF N Δ x) +
          ∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x =
        ∑ x ∈ Finset.range (N + 1), binomPMF N Δ x :=
      Finset.sum_sdiff hsub
    have hextra : (0 : ℝ) ≤ ∑ x ∈ Finset.range (N + 1) \
        Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x :=
      Finset.sum_nonneg (fun x _ => hnnΔall x)
    have htotal : (∑ x ∈ Finset.range (N + 1), binomPMF N Δ x) = 1 := by
      have hbinom : (Δ + (1 - Δ)) ^ N
          = ∑ m ∈ Finset.range (N + 1), Δ ^ m * (1 - Δ) ^ (N - m) * ↑(N.choose m) :=
        Commute.add_pow (Commute.all Δ (1 - Δ)) N
      have hone : Δ + (1 - Δ) = 1 := by ring
      calc ∑ x ∈ Finset.range (N + 1), binomPMF N Δ x
          = ∑ m ∈ Finset.range (N + 1), Δ ^ m * (1 - Δ) ^ (N - m) * ↑(N.choose m) := by
            unfold binomPMF
            apply Finset.sum_congr rfl
            intro m _
            ring
        _ = (Δ + (1 - Δ)) ^ N := hbinom.symm
        _ = 1 := by rw [hone, one_pow]
    calc ∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x
        ≤ (∑ x ∈ Finset.range (N + 1) \ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N,
              binomPMF N Δ x) +
            ∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x :=
          le_add_of_nonneg_left hextra
      _ = ∑ x ∈ Finset.range (N + 1), binomPMF N Δ x := hsd
      _ = 1 := htotal
  refine le_trans hsum ?_
  have h1 : Real.exp (-(N : ℝ) * binaryKL Δ p) *
      (∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x)
      ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) * 1 :=
    mul_le_mul_of_nonneg_left htailΔ (Real.exp_nonneg _)
  rw [mul_one] at h1
  exact h1

theorem binomial_chernoff
    (N : ℕ) (p Δ : ℝ) (_hN : 1 ≤ N) (hp : 0 < p) (hpΔ : p < Δ) (hΔ1 : Δ < 1) :
    binomTail N p Δ ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) ∧ 0 < binaryKL Δ p :=
  ⟨binomial_chernoff_tail N p Δ hp hpΔ hΔ1, binaryKL_pos p Δ hp hpΔ hΔ1⟩

theorem css_gilbert_varshamov
    (Δ R δGV : ℝ) (RealizableCss : ℕ → ℕ → ℕ → Prop)
    (_hΔ0 : 0 < Δ) (_hΔ : Δ < δGV) (_hGV : IsGilbertVarshamovRate δGV)
    (hR0 : 0 < R) (_hR : R < 1 - 2 * h2 Δ)
    (hF2 : ∃ Δ' : ℝ, Δ < Δ' ∧ Δ' < δGV ∧ R < 1 - 2 * h2 Δ')    (hRef24 : ∀ Δ' R'' : ℝ, 0 < R'' → R'' < 1 - 2 * h2 Δ' →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∃ KN dN : ℕ,
        RealizableCss N KN dN ∧ (KN : ℝ) ≥ R'' * (N : ℝ) ∧ (dN : ℝ) ≥ Δ' * (N : ℝ)) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N → ∃ KN dN : ℕ,
      RealizableCss N KN dN ∧ (KN : ℝ) ≥ R * (N : ℝ) ∧ (dN : ℝ) ≥ Δ * (N : ℝ) := by
  obtain ⟨Δ', hΔlt', hΔ'GV, hRlt'⟩ := hF2
  set R'' : ℝ := (R + (1 - 2 * h2 Δ')) / 2 with hR''def
  have hR''0 : 0 < R'' := by
    rw [hR''def]
    exact div_pos (by linarith) two_pos
  have hR''lt : R'' < 1 - 2 * h2 Δ' := by
    rw [div_lt_iff₀ two_pos]
    linarith
  have hR''ge : R ≤ R'' := by
    rw [hR''def]
    linarith
  obtain ⟨N0, hN0⟩ := hRef24 Δ' R'' hR''0 hR''lt
  refine ⟨max 1 N0, lt_of_lt_of_le zero_lt_one (le_max_left 1 N0), ?_⟩
  intro N hN
  obtain ⟨KN, dN, hreal, hKN, hdN⟩ := hN0 N (le_trans (le_max_right 1 N0) hN)
  refine ⟨KN, dN, hreal, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right hR''ge (Nat.cast_nonneg N)) hKN
  · exact le_trans (mul_le_mul_of_nonneg_right (le_of_lt hΔlt') (Nat.cast_nonneg N)) hdN

theorem css_erasure_construction
    (p Δ R δGV : ℝ) (RealizableCss : ℕ → ℕ → ℕ → Prop)
    (hp : 0 < p) (hpΔ : p < Δ) (hΔ : Δ < δGV) (hGV : IsGilbertVarshamovRate δGV)
    (hR0 : 0 < R) (_hR : R < 1 - 2 * h2 Δ)
    (hF1 : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∃ KN dN : ℕ,
      RealizableCss N KN dN ∧ (KN : ℝ) ≥ R * (N : ℝ) ∧ (dN : ℝ) ≥ Δ * (N : ℝ))
    (K S : ℕ) (hK : 1 ≤ K) (hS : 1 ≤ S) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (N0' N KN dN : ℕ) (c0 err : ℝ),
      0 < c0 ∧ N0' ≤ N ∧ RealizableCss N KN dN ∧ (KN : ℝ) ≥ R * (N : ℝ) ∧
      (dN : ℝ) ≥ Δ * (N : ℝ) ∧ (KN : ℝ) ≥ (K : ℝ) + 1 ∧
      err ≤ 2 * (S : ℝ) * Real.exp (-(binaryKL Δ p) * (N : ℝ)) ∧ err ≤ ε ∧
      (N : ℝ) ≤ c0 * ((K : ℝ) + 1 + Real.log (2 * (S : ℝ) / ε)) := by
  obtain ⟨N0, hN0⟩ := hF1
  have ha : 0 < binaryKL Δ p :=
      binaryKL_pos p Δ hp hpΔ (lt_trans (lt_trans hΔ hGV.2.2) (by norm_num : (1 / 2 : ℝ) < 1))
  have hlog2S : 0 < Real.log (2 * (S : ℝ) / ε) := by
    apply Real.log_pos
    have h2 : (1 : ℝ) < 2 * (S : ℝ) / ε := by
      rw [one_lt_div hε0]
      have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
      linarith
    exact h2

  set x : ℝ := max (max ((N0 : ℝ)) (((K : ℝ) + 1) / R))
      ((1 / binaryKL Δ p) * Real.log (2 * (S : ℝ) / ε)) with hxdef
  set N := Nat.ceil x with hNdef
  have hNx : x ≤ (N : ℝ) := by
    rw [hNdef]
    exact Nat.le_ceil _
  have hmax1 : ((N0 : ℝ)) ≤ x := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmax2 : ((K : ℝ) + 1) / R ≤ x := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmax3 : (1 / binaryKL Δ p) * Real.log (2 * (S : ℝ) / ε) ≤ x :=
    le_trans (le_refl _) (le_max_right _ _)
  have hx0 : (0 : ℝ) ≤ x :=
    le_trans (show (0 : ℝ) ≤ (N0 : ℝ) by exact_mod_cast Nat.zero_le N0) hmax1
  have hNceil : (N : ℝ) < x + 1 := by
    rw [hNdef]
    exact_mod_cast Nat.ceil_lt_add_one hx0
  have hN0' : N0 ≤ N := by
    have : ((N0 : ℝ)) ≤ (N : ℝ) := le_trans hmax1 hNx
    exact_mod_cast this
  obtain ⟨KN, dN, hreal, hKN, hdN⟩ := hN0 N hN0'

  have hcap : (K : ℝ) + 1 ≤ R * (N : ℝ) := by
    have h2 : (K : ℝ) + 1 ≤ R * x := by
      rw [mul_comm]
      exact (div_le_iff₀ hR0).mp hmax2
    have h3 : R * x ≤ R * (N : ℝ) := mul_le_mul_of_nonneg_left hNx hR0.le
    linarith

  have hexpbound : 2 * (S : ℝ) * Real.exp (-(binaryKL Δ p) * (N : ℝ)) ≤ ε := by
    have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
    have h2Spos : (0 : ℝ) < 2 * (S : ℝ) := by linarith
    have h2Sε : (0 : ℝ) < 2 * (S : ℝ) / ε := div_pos h2Spos hε0
    have hNlog : Real.log (2 * (S : ℝ) / ε) ≤ binaryKL Δ p * (N : ℝ) := by
      have hadj : binaryKL Δ p * ((1 / binaryKL Δ p) * Real.log (2 * (S : ℝ) / ε))
          = Real.log (2 * (S : ℝ) / ε) := by
        field_simp [ne_of_gt ha]
      calc Real.log (2 * (S : ℝ) / ε)
          = binaryKL Δ p * ((1 / binaryKL Δ p) * Real.log (2 * (S : ℝ) / ε)) := hadj.symm
        _ ≤ binaryKL Δ p * x := mul_le_mul_of_nonneg_left hmax3 ha.le
        _ ≤ binaryKL Δ p * (N : ℝ) := mul_le_mul_of_nonneg_left hNx ha.le
    have hexpl : Real.exp (-(Real.log (2 * (S : ℝ) / ε))) = ε / (2 * (S : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log h2Sε, inv_div]
    have hexp : Real.exp (-(binaryKL Δ p) * (N : ℝ))
        ≤ ε / (2 * (S : ℝ)) := by
      rw [← hexpl]
      apply Real.exp_le_exp_of_le
      linarith
    calc 2 * (S : ℝ) * Real.exp (-(binaryKL Δ p) * (N : ℝ))
        ≤ 2 * (S : ℝ) * (ε / (2 * (S : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp h2Spos.le
      _ = ε := mul_div_cancel₀ ε (ne_of_gt h2Spos)

  set W : ℝ := (K : ℝ) + 1 + Real.log (2 * (S : ℝ) / ε) with hWdef
  have hW2 : 2 ≤ W := by
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith [hlog2S]
  set c0 : ℝ := (N0 : ℝ) + 1 / R + 1 / binaryKL Δ p + 1 with hc0def
  have hc0pos : 0 < c0 := by
    have h1 : (0 : ℝ) < 1 / R := one_div_pos.mpr hR0
    have h2 : (0 : ℝ) < 1 / binaryKL Δ p := one_div_pos.mpr ha
    have h3 : (0 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast Nat.zero_le N0
    rw [hc0def]
    linarith
  have hW1 : 1 ≤ W := by linarith
  have hxle : x ≤ (N0 : ℝ) + ((K : ℝ) + 1) / R + (1 / binaryKL Δ p) * Real.log (2 * (S : ℝ) / ε) := by
    have hN0nn : (0 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast Nat.zero_le N0
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hBnn : (0 : ℝ) ≤ ((K : ℝ) + 1) / R := by
      have : (0 : ℝ) ≤ (K : ℝ) + 1 := by linarith
      exact div_nonneg this hR0.le
    have hCnn : (0 : ℝ) ≤ (1 / binaryKL Δ p) * Real.log (2 * (S : ℝ) / ε) :=
      mul_nonneg (div_nonneg zero_le_one ha.le) hlog2S.le
    have h1 : x ≤ (N0 : ℝ) +
        (((K : ℝ) + 1) / R + (1 / binaryKL Δ p) * Real.log (2 * (S : ℝ) / ε)) := by
      rw [hxdef]
      apply max_le
      · apply max_le <;> linarith
      · linarith
    linarith
  have hwidth : (N : ℝ) ≤ c0 * W := by
    have hstep : x + 1 ≤ c0 * W := by
      have hN0nn : (0 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast Nat.zero_le N0
      have h1 : ((N0 : ℝ)) ≤ (N0 : ℝ) * W := by
        calc ((N0 : ℝ)) = (N0 : ℝ) * 1 := (mul_one _).symm
          _ ≤ (N0 : ℝ) * W := mul_le_mul_of_nonneg_left hW1 hN0nn
      have h2 : ((K : ℝ) + 1) / R ≤ (1 / R) * W := by
        have : ((K : ℝ) + 1) / R = (1 / R) * ((K : ℝ) + 1) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (by linarith : ((K : ℝ) + 1) ≤ W) (one_div_pos.mpr hR0).le
      have h3 : (1 / binaryKL Δ p) * Real.log (2 * (S : ℝ) / ε)
          ≤ (1 / binaryKL Δ p) * W :=
        mul_le_mul_of_nonneg_left (by linarith : Real.log (2 * (S : ℝ) / ε) ≤ W)
          (one_div_pos.mpr ha).le
      have h4 : (1 : ℝ) ≤ 1 * W := by linarith
      have hc0split : c0 * W = ((N0 : ℝ)) * W + (1 / R) * W + (1 / binaryKL Δ p) * W + 1 * W := by
        rw [hc0def]; ring
      rw [hc0split]
      linarith
    linarith
  exact ⟨N0, N, KN, dN, c0, 2 * (S : ℝ) * Real.exp (-(binaryKL Δ p) * (N : ℝ)),
    hc0pos, hN0', hreal, hKN, hdN, le_trans hcap hKN, le_refl _, hexpbound, hwidth⟩

theorem optimal_worst_case_circuit_size
    (p ε0 : ℝ) (hp : 0 < p) (hp1 : p < 1) (_hε0 : 0 < ε0) (hε01 : ε0 < 1)
    (Cmin : ℕ → ℕ → ℝ → ℝ)
    (cl cup : ℝ) (hcl : 0 < cl) (hcup : 0 < cup)
    (hlower : ∀ (K S : ℕ) (ε : ℝ), 1 ≤ K → 1 ≤ S → 0 < ε → ε ≤ ε0 →
      cl * ((S : ℝ) * ((K : ℝ) + Real.log ((S : ℝ) / ε))) ≤ Cmin K S ε)
    (hupper : ∀ (K S : ℕ) (ε : ℝ), 1 ≤ K → 1 ≤ S → 0 < ε → ε ≤ ε0 →
      Cmin K S ε ≤ cup * ((S : ℝ) * ((K : ℝ) + 1 + Real.log (2 * (S : ℝ) / ε)))) :
    ∃ cminus cplus : ℝ, 0 < cminus ∧ 0 < cplus ∧ ∃ S0 : ℕ, 0 < S0 ∧
      ∀ (K S : ℕ) (ε : ℝ), 1 ≤ K → S0 ≤ S → 0 < ε → ε ≤ ε0 →
        cminus * ((S : ℝ) * ((K : ℝ) + Real.log ((S : ℝ) / ε))) ≤ Cmin K S ε ∧
        Cmin K S ε ≤ cplus * ((S : ℝ) * ((K : ℝ) + Real.log ((S : ℝ) / ε))) := by
  refine ⟨cl, 2 * cup, hcl, mul_pos (by norm_num) hcup, 2, by norm_num, ?_⟩
  intro K S ε hK hS hε hεle
  refine ⟨hlower K S ε hK (by omega) hε hεle, ?_⟩

  have hSε : (2 : ℝ) ≤ (S : ℝ) / ε := by
    rw [le_div_iff₀ hε]
    have hS2 : (2 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
    have hεle1 : ε ≤ 1 := le_trans hεle (le_of_lt hε01)
    linarith
  have hlog2 : Real.log 2 ≤ Real.log ((S : ℝ) / ε) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) hSε
  have hsplit : Real.log (2 * (S : ℝ) / ε) = Real.log 2 + Real.log ((S : ℝ) / ε) := by
    have hSεpos : (0 : ℝ) < (S : ℝ) / ε := div_pos (by
      have : (2 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
      linarith) hε
    have hmul : 2 * (S : ℝ) / ε = 2 * ((S : ℝ) / ε) := by ring
    rw [hmul, Real.log_mul two_ne_zero (ne_of_gt hSεpos)]
  have hbound : (K : ℝ) + 1 + Real.log (2 * (S : ℝ) / ε)
      ≤ 2 * ((K : ℝ) + Real.log ((S : ℝ) / ε)) := by
    rw [hsplit]
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    nlinarith [hK1, hlog2]
  have hSnonneg : 0 ≤ (S : ℝ) := Nat.cast_nonneg S
  calc Cmin K S ε
      ≤ cup * ((S : ℝ) * ((K : ℝ) + 1 + Real.log (2 * (S : ℝ) / ε))) :=
        hupper K S ε hK (by omega) hε hεle
    _ ≤ cup * ((S : ℝ) * (2 * ((K : ℝ) + Real.log ((S : ℝ) / ε)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound hSnonneg) (le_of_lt hcup)
    _ = (2 * cup) * ((S : ℝ) * ((K : ℝ) + Real.log ((S : ℝ) / ε))) := by ring

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes
