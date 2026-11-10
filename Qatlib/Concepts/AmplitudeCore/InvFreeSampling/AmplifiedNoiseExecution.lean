/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedNoiseExecutionDefs
import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.BernoulliTail
import Qatlib.Concepts.AmpTransform.NoiseMoments.NoiseSequenceMoments
import Mathlib.NumberTheory.DiophantineApproximation.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.ErrorStream

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.InvFreeSampling

open Qatlib
open scoped Classical BigOperators

theorem aq_envelope_bound_m1 (N : ℕ) (L : ℝ) :
    aqEnvelopeBound (N : ℝ) 1 L = aqM1Envelope (N : ℝ) L ∨ L = -1 := by
  by_cases h : L = -1
  · exact Or.inr h
  · refine Or.inl ?_
    unfold aqEnvelopeBound aqM1Envelope
    simp only [one_pow]
    have hne : L + 1 ≠ 0 := by
      intro hc
      apply h
      linarith
    by_cases hz : (N : ℝ) - L - 1 = 0
    · simp [hz]
    · have hne2 : ((N : ℝ) - L - 1) * (L + 1) ≠ 0 := mul_ne_zero hz hne
      apply (div_eq_div_iff hne2 hz).mpr
      ring

theorem aq_envelope_bound_m1_open {N : ℕ} {L : ℝ} (h : aqM1OpenWindow N L) :
    aqEnvelopeBound (N : ℝ) 1 L = aqM1Envelope (N : ℝ) L := by
  have hne : L ≠ -1 := by
    intro hc
    subst hc
    exact (lt_irrefl (-1 : ℝ)) h.1
  exact (aq_envelope_bound_m1 N L).resolve_right hne

theorem aq_m1_envelope_strictly_increasing {N : ℕ} (hN : 0 < N) {L₁ L₂ : ℝ}
    (h₁ : aqM1OpenWindow N L₁) (h₂ : aqM1OpenWindow N L₂) (hlt : L₁ < L₂) :
    aqM1Envelope (N : ℝ) L₁ < aqM1Envelope (N : ℝ) L₂ := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos₂ : 0 < (N : ℝ) - L₂ - 1 := by linarith [h₂.2]
  have hlt' : (N : ℝ) - L₂ - 1 < (N : ℝ) - L₁ - 1 := by linarith
  unfold aqM1Envelope
  exact one_div_lt_one_div_of_lt hpos₂ hlt'

theorem aq_m1_envelope_gt_inv_N {N : ℕ} (hN : 0 < N) {L : ℝ} (h : aqM1OpenWindow N L) :
    (1 : ℝ) / N < aqM1Envelope (N : ℝ) L := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) - L - 1 := by linarith [h.2]
  have hlt : (N : ℝ) - L - 1 < N := by linarith [h.1]
  unfold aqM1Envelope
  exact one_div_lt_one_div_of_lt hpos hlt

theorem aq_m1_envelope_infimum_approach {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ L, aqM1OpenWindow N L ∧ aqM1Envelope (N : ℝ) L < (1 : ℝ) / N + ε := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set δ : ℝ := min (ε * N / 2) (N / 4) with hδ
  have hδpos : 0 < δ := by
    have h1 : (0 : ℝ) < ε * N / 2 := by positivity
    have h2 : (0 : ℝ) < N / 4 := by positivity
    exact lt_min h1 h2
  have hδle : δ ≤ N / 4 := min_le_right _ _
  have hδε : δ ≤ ε * N / 2 := min_le_left _ _
  have hpos : 0 < N - δ := by linarith
  have hgap : N * 3 / 4 ≤ N - δ := by linarith
  refine ⟨-1 + δ, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · linarith
    · linarith
  · have hkey : 1 / (N - δ) - 1 / N = δ / (N * (N - δ)) := by
      have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hN'
      have hNd : (N - δ : ℝ) ≠ 0 := ne_of_gt hpos
      field_simp
      ring
    have h1 : 0 < N * (N - δ) := by positivity
    have hbound : δ / (N * (N - δ)) < ε := by
      rw [div_lt_iff₀ h1]
      have h4 : N * (N * 3 / 4) ≤ N * (N - δ) := by nlinarith
      have h2 := mul_le_mul_of_nonneg_left h4 (by positivity)
      nlinarith [h2, hδε, hN', hN1]
    unfold aqM1Envelope
    have hform : (N : ℝ) - (-1 + δ) - 1 = N - δ := by ring
    rw [hform]
    have hsplit : 1 / (N - δ) = 1 / N + δ / (N * (N - δ)) := by linarith [hkey]
    rw [hsplit]
    linarith

theorem aq_m1_envelope_no_optimal {N : ℕ} (hN : 0 < N) {L : ℝ} (h : aqM1OpenWindow N L) :
    ∃ L', aqM1OpenWindow N L' ∧ aqM1Envelope (N : ℝ) L' < aqM1Envelope (N : ℝ) L := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hhalf : (0 : ℝ) < (L + 1) / 2 := by linarith [h.1]
  have hlt : L - (L + 1) / 2 < L := by linarith
  refine ⟨L - (L + 1) / 2, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · linarith
    · linarith [h.2]
  · exact aq_m1_envelope_strictly_increasing hN
      (L₁ := L - (L + 1) / 2) (L₂ := L)
      ⟨by linarith, by linarith [h.2]⟩ h hlt

theorem aq_m1_envelope_physical_minimum {N : ℕ} (hN : 1 < N) {L : ℝ}
    (hL : 0 ≤ L) (hL' : L < (N : ℝ) - 1) :
    (1 : ℝ) / (N - 1) ≤ aqM1Envelope (N : ℝ) L ∧
      (aqM1Envelope (N : ℝ) L = (1 : ℝ) / (N - 1) ↔ L = 0) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ N by omega)
  have hpos : 0 < (N : ℝ) - L - 1 := by linarith
  have hle : (N : ℝ) - L - 1 ≤ (N : ℝ) - 1 := by linarith
  have hpos0 : 0 < (N : ℝ) - 1 := by linarith
  constructor
  · unfold aqM1Envelope
    exact one_div_le_one_div_of_le hpos hle
  · constructor
    · intro heq
      unfold aqM1Envelope at heq
      have hz := (div_eq_div_iff (by linarith : ((N : ℝ) - L - 1) ≠ 0)
        (by linarith : ((N : ℝ) - 1) ≠ 0)).mp heq
      linarith
    · intro hL0
      subst hL0
      unfold aqM1Envelope
      rw [show (N : ℝ) - 0 - 1 = N - 1 by ring]

theorem aq_legendre_integer_window (ξ : ℝ) (u : ℤ) (h : |ξ - (u : ℝ)| ≤ 1 / 2) :
    (∃ n : ℕ, (u : ℚ) = ξ.convergent n) ∨ ξ = (u : ℝ) - 1 / 2 := by
  by_cases htie : ξ = (u : ℝ) - 1 / 2
  · exact Or.inr htie
  · have hab := abs_le.mp h
    have hlo : (u : ℝ) - 1 / 2 < ξ := by
      have h1 : (u : ℝ) - 1 / 2 ≤ ξ := by linarith [hab.1]
      refine lt_of_le_of_ne h1 ?_
      intro hc
      apply htie
      linarith
    have hAss : Real.ContfracLegendre.Ass ξ u ((1 : ℕ) : ℤ) := by
      refine ⟨Int.isCoprime_iff_nat_coprime.mpr (Nat.coprime_one_right _), ?_, ?_⟩
      · intro hb1
        have : -(1 / 2) < ξ - ↑u := by linarith [hlo]
        exact this
      · simp only [Int.cast_natCast]
        norm_num
        linarith [h]
    obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent' (ξ := ξ) (v := 1) (u := u) hAss
    refine Or.inl ⟨n, ?_⟩
    have hq : ((u : ℤ) : ℚ) / ((1 : ℕ) : ℚ) = (u : ℚ) := by norm_num
    rw [hq] at hn
    exact hn

theorem aq_legendre_nonstrict_den_ge_two (ξ : ℝ) (a : ℤ) (b : ℕ) (hb : 2 ≤ b)
    (hc : Nat.Coprime b a.natAbs)
    (h : |ξ - (a : ℝ) / (b : ℝ)| ≤ 1 / (2 * (b : ℝ) ^ 2)) :
    ∃ n : ℕ, ((a : ℚ) / (b : ℚ)) = ξ.convergent n := by
  have hAss : Real.ContfracLegendre.Ass ξ a ((b : ℕ) : ℤ) := by
    refine ⟨Int.isCoprime_iff_nat_coprime.mpr (by simpa using! hc.symm), ?_, ?_⟩
    · intro hb1
      omega
    · have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show (0 : ℕ) < b by omega)
      simp only [Int.cast_natCast]
      have hconv : |ξ - ↑a / ↑b| = |ξ - (a : ℝ) / (b : ℝ)| := by rfl
      rw [hconv]
      have hkey : (b : ℝ) * (2 * (b : ℝ) - 1) < 2 * (b : ℝ) ^ 2 := by
        nlinarith [hbR, hbpos]
      have hpos : (0 : ℝ) < (b : ℝ) * (2 * (b : ℝ) - 1) := by nlinarith [hbR, hbpos]
      refine lt_of_le_of_lt h ?_
      rw [← one_div]
      exact one_div_lt_one_div_of_lt hpos hkey
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent' (ξ := ξ) (v := b) (u := a) hAss
  refine ⟨n, ?_⟩
  have hq : ((a : ℤ) : ℚ) / ((b : ℕ) : ℚ) = (a : ℚ) / (b : ℚ) := by norm_num
  rw [hq] at hn
  exact hn

theorem aq_legendre_nonstrict_complete (ξ : ℝ) (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hc : Nat.Coprime b a.natAbs)
    (h : |ξ - (a : ℝ) / (b : ℝ)| ≤ 1 / (2 * (b : ℝ) ^ 2)) :
    (∃ n : ℕ, ((a : ℚ) / (b : ℚ)) = ξ.convergent n) ∨
      (b = 1 ∧ ξ = (a : ℝ) - 1 / 2) := by
  by_cases h1 : b = 1
  · have hhalf : |ξ - (a : ℝ)| ≤ 1 / 2 := by
      rw [h1] at h
      norm_num at h ⊢
      exact h
    rcases aq_legendre_integer_window ξ a hhalf with ⟨⟨n, hn⟩⟩ | htie
    · refine Or.inl ⟨n, ?_⟩
      rw [h1]
      simpa using! hn
    · refine Or.inr ⟨h1, ?_⟩
      exact htie
  · have h2 : 2 ≤ b := by omega
    exact Or.inl (aq_legendre_nonstrict_den_ge_two ξ a b h2 hc h)

theorem aq_legendre_nonstrict_complete_rat (ξ : ℝ) (q : ℚ)
    (h : |ξ - (q : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2)) :
    (∃ n : ℕ, q = ξ.convergent n) ∨ (q.den = 1 ∧ ξ = (q : ℝ) - 1 / 2) := by
  by_cases hd1 : q.den = 1
  · have hhalf : |ξ - (q : ℝ)| ≤ 1 / 2 := by
      have htwo : (2 : ℝ) * (q.den : ℝ) ^ 2 = 2 := by
        rw [hd1]
        norm_num
      rw [htwo] at h
      norm_num at h ⊢
      exact h
    have hqd := q.num_div_den
    rw [hd1] at hqd
    norm_num at hqd
    have hq : (q.num : ℚ) = q := hqd
    have hu : (q : ℝ) = (q.num : ℝ) := by
      have := congrArg (fun r : ℚ => (r : ℝ)) hq
      push_cast at this
      rw [this]
    have hhalf' : |ξ - (q.num : ℝ)| ≤ 1 / 2 := by rw [← hu]; exact hhalf
    rcases aq_legendre_integer_window ξ q.num hhalf' with ⟨⟨n, hn⟩⟩ | htie
    · refine Or.inl ⟨n, ?_⟩
      rw [← hq]
      exact hn
    · refine Or.inr ⟨hd1, ?_⟩
      rw [hu]
      exact htie
  · have hdenpos : 0 < q.den := q.den_pos
    have hd2 : 2 ≤ q.den := by omega
    have hnum : q.num ≠ 0 := by
      intro hz
      have hz' : q = 0 := by
        have hqd := q.num_div_den
        rw [hz] at hqd
        norm_num at hqd
        exact hqd.symm
      have hden : q.den = 1 := by
        rw [hz']
        norm_num
      omega
    have hcop : Nat.Coprime q.den q.num.natAbs :=
      (Int.natAbs_natCast q.den ▸ q.reduced).symm
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden2 : (2 : ℝ) ≤ q.den := by exact_mod_cast hd2
    have hqd := q.num_div_den
    have hq : (q.num : ℚ) / (q.den : ℚ) = q := hqd
    have hqR : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      have := congrArg (fun r : ℚ => (r : ℝ)) hq
      push_cast at this
      rw [this]
    have hdist : |ξ - (q.num : ℝ) / (q.den : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2) := by
      rw [hqR]
      exact h
    obtain ⟨n, hn⟩ := aq_legendre_nonstrict_den_ge_two ξ q.num q.den hd2 hcop hdist
    refine Or.inl ⟨n, ?_⟩
    rw [hq] at hn
    exact hn

theorem aq_bernoulli_stream_independent (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (g : Fin N → Bool → ℝ) :
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ * ∏ i, g i (σ i))
      = ∏ i, ∑ b : Bool, (bernoulliSiteLaw p hp hp1).prob b * g i b := by
  have h :=
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_prod
      (p := bernoulliSiteLaw p hp hp1) (L := N) g
  simpa only [bernoulliStreamLaw] using! h

private theorem aq_prod_ite_indicator (N : ℕ) (D : Finset (Fin N)) (σ : Fin N → Bool) :
    (∏ j : Fin N, (if j ∈ D then (if σ j then 1 else 0) else 1))
      = (if D ⊆ Finset.filter (fun i : Fin N => σ i = true) Finset.univ then (1 : ℝ) else 0) := by
  classical
  by_cases h : D ⊆ Finset.filter (fun i : Fin N => σ i = true) Finset.univ
  · have hall : ∀ j ∈ D, σ j = true := fun j hj => (Finset.mem_filter.mp (h hj)).2
    have h1 : (∏ j : Fin N, (if j ∈ D then (if σ j then 1 else 0) else 1)) = (1 : ℝ) := by
      refine Finset.prod_eq_one ?_
      intro j _
      by_cases hjD : j ∈ D
      · simp [hjD, hall j hjD]
      · simp [hjD]
    rw [h1]
    simp [h]
  · obtain ⟨j, hj, hjne⟩ := Finset.not_subset.mp h
    have hne' : σ j ≠ true := by simpa using! hjne
    have h0 : (∏ j : Fin N, (if j ∈ D then (if σ j then 1 else 0) else 1)) = (0 : ℝ) :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj, hne'])
    rw [h0]
    simp [h]

theorem aq_bernoulli_all_marked (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (Fin N)) :
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if D ⊆ Finset.filter (fun i : Fin N => σ i = true) Finset.univ then 1 else 0))
      = p ^ D.card := by
  have hsum (j : Fin N) :
      (∑ b : Bool, (bernoulliSiteLaw p hp hp1).prob b *
        (if j ∈ D then (if b then 1 else 0) else 1)) = if j ∈ D then p else 1 := by
    by_cases hj : j ∈ D
    · rw [Fintype.sum_bool]
      simp [bernoulliSiteLaw, hj] <;> linarith
    · rw [Fintype.sum_bool]
      simp [bernoulliSiteLaw, hj] <;> linarith
  have h := aq_bernoulli_stream_independent N p hp hp1
    (fun j b => if j ∈ D then (if b then 1 else 0) else 1)
  calc
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if D ⊆ Finset.filter (fun i : Fin N => σ i = true) Finset.univ then 1 else 0))
        = ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
            (∏ j : Fin N, (if j ∈ D then (if σ j then 1 else 0) else 1)) := by
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      exact (aq_prod_ite_indicator N D σ).symm
    _ = ∏ j : Fin N, ∑ b : Bool, (bernoulliSiteLaw p hp hp1).prob b *
          (if j ∈ D then (if b then 1 else 0) else 1) := h
    _ = p ^ D.card := by
      simp_rw [hsum]
      have hprod : ∏ j : Fin N, (if j ∈ D then p else 1) = p ^ D.card := by
        rw [← Finset.prod_filter (s := (Finset.univ : Finset (Fin N))) (p := fun j => j ∈ D)
          (f := fun _ => p)]
        simp
      rw [hprod]

theorem aq_bernoulli_site_marginal (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin N) :
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if σ i then 1 else 0)) = p := by
  have hconv (σ : Fin N → Bool) :
      ({i} : Finset (Fin N)) ⊆ Finset.filter (fun j : Fin N => σ j = true) Finset.univ
        ↔ σ i = true := by
    simp
  have h := aq_bernoulli_all_marked N p hp hp1 ({i} : Finset (Fin N))
  calc
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if σ i then 1 else 0))
        = ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
            (if ({i} : Finset (Fin N)) ⊆
                Finset.filter (fun j : Fin N => σ j = true) Finset.univ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hc : ({i} : Finset (Fin N)) ⊆
          Finset.filter (fun j : Fin N => σ j = true) Finset.univ
      · have hc' : σ i = true := (hconv σ).mp hc
        simp [hc, hc']
      · have hc' : σ i ≠ true := fun h => hc ((hconv σ).mpr h)
        simp [hc, hc']
    _ = p ^ ({i} : Finset (Fin N)).card := h
    _ = p := by simp

private theorem aq_subset_union_iff {α : Type} [DecidableEq α] (s t u : Finset α) :
    s ⊆ t ∪ u ↔ s \ t ⊆ u := by
  constructor
  · intro hsub x hx
    have hxm : x ∈ s := (Finset.mem_sdiff.mp hx).1
    have hx' := hsub hxm
    rcases Finset.mem_union.mp hx' with hleft | hright
    · exact absurd hleft (Finset.mem_sdiff.mp hx).2
    · exact hright
  · intro hsub x hx
    apply Finset.mem_union.2
    by_cases hx' : x ∈ t
    · exact Or.inl hx'
    · exact Or.inr (hsub (Finset.mem_sdiff.mpr ⟨hx, hx'⟩))

theorem aq_fresh_consistency_probability (N s M P P' : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0))
      = p ^ (aqCandidateSeparation N s M P P') := by
  set D : Finset (Fin N) := aqProgressionSet N s M P' \ aqProgressionSet N s M P with hD
  have hcard : D.card = aqCandidateSeparation N s M P P' := by
    rfl
  have hconv (σ : Fin N → Bool) :
      aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) ↔
        D ⊆ Finset.filter (fun i : Fin N => σ i = true) Finset.univ := by
    unfold aqCandidateConsistent aqFreshMarked
    have h := aq_subset_union_iff (aqProgressionSet N s M P')
      (aqProgressionSet N s M P) (Finset.filter (fun i : Fin N => σ i = true) Finset.univ)
    rw [h]
  have hsum : (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0))
      = (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
        (if D ⊆ Finset.filter (fun i : Fin N => σ i = true) Finset.univ then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hc : aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)
    · have hc' : D ⊆ Finset.filter (fun i : Fin N => σ i = true) Finset.univ := (hconv σ).mp hc
      simp [hc, hc']
    · have hc' : ¬ (D ⊆ Finset.filter (fun i : Fin N => σ i = true) Finset.univ) := by
        intro h
        exact absurd ((hconv σ).mpr h) hc
      simp [hc, hc']
  rw [hsum, aq_bernoulli_all_marked N p hp hp1 D, hcard]

theorem aq_true_period_always_consistent (N s M P : ℕ) (σ : Fin N → Bool) :
    aqCandidateConsistent N s M P (aqFreshMarked N s M P σ) := by
  unfold aqCandidateConsistent aqFreshMarked
  exact Finset.subset_union_left

theorem aq_fresh_disambiguation_succeeds (N s M P : ℕ) (p : ℝ) (cands : Finset ℕ)
    (hP : P ∈ cands) (σ : Fin N → Bool)
    (hrefute : ∀ P' ∈ cands \ {P},
      ¬ aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)) :
    aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) = {P} ∧
      aqFreshDisambiguate N s M cands p (aqFreshMarked N s M P σ) = some P := by
  have hcompat : aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) = {P} := by
    ext P'
    constructor
    · intro hP'
      have hmem : P' ∈ cands := (Finset.mem_filter.mp hP').1
      have hcons : aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) :=
        (Finset.mem_filter.mp hP').2
      by_cases heq : P' = P
      · exact Finset.mem_singleton.mpr heq
      · have hnot : ¬ aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) :=
          hrefute P' (Finset.mem_sdiff.mpr ⟨hmem, by simpa using! heq⟩)
        exact absurd hcons hnot
    · intro hP'
      have hEq : P' = P := Finset.mem_singleton.mp hP'
      rw [hEq]
      exact Finset.mem_filter.mpr ⟨hP, aq_true_period_always_consistent N s M P σ⟩
  refine ⟨hcompat, ?_⟩
  unfold aqFreshDisambiguate
  rw [hcompat]
  simp [aqCandidateLikelihood]

theorem aq_fresh_failure_contained (N s M P : ℕ) (cands : Finset ℕ) (hP : P ∈ cands)
    (σ : Fin N → Bool)
    (hne : aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) ≠ {P}) :
    ∃ P' ∈ cands \ {P}, aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) := by
  by_cases hex : ∃ P' ∈ cands \ {P},
      aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)
  · obtain ⟨P', hP', hc⟩ := hex
    exact ⟨P', hP', hc⟩
  · exfalso
    have hcompat : aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) = {P} := by
      ext P'
      constructor
      · intro hP'
        have hmem : P' ∈ cands := (Finset.mem_filter.mp hP').1
        have hcons : aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) :=
          (Finset.mem_filter.mp hP').2
        by_cases heq : P' = P
        · exact Finset.mem_singleton.mpr heq
        · have hnot : ¬ aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) := by
            intro hh
            exact hex ⟨P', Finset.mem_sdiff.mpr ⟨hmem, by simpa using! heq⟩, hh⟩
          exact absurd hcons hnot
      · intro hP'
        have hEq : P' = P := Finset.mem_singleton.mp hP'
        rw [hEq]
        exact Finset.mem_filter.mpr ⟨hP, aq_true_period_always_consistent N s M P σ⟩
    exact hne hcompat

end Qatlib.Concepts.AmplitudeCore.InvFreeSampling
