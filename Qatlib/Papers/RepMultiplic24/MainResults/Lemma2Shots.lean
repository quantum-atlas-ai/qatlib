/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepMultiplic24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# RepMultiplic24.MainResults.Lemma2Shots

Paper: *Quantum Algorithms for Representation-Theoretic Multiplicities*,
fixed arXiv:2407.17649 (2024), Claim `c005` = Lemma 2 (main text p. 7, proof in
Supp. Mat. Eq. (94)-(97)).

Lemma 2: Algorithm 1 finds `mult(r_H^β, r_G^α↓_H^G)` with constant probability
after `O((d_α/d_β)²)` shots.

The proof route of the paper is:

* each shot is a Bernoulli trial with success probability `p = mult · d_β / d_α`
  (Eq. (10)); so an estimator of `p`, divided by `d_β/d_α`, estimates the
  multiplicity;
* the empirical mean of `N` shots is within `ε` of `p` except with probability
  `≤ Var/(N ε²) ≤ p/(N ε²)` (Chebyshev / Chernoff-Hoeffding, Eq. (94)-(97))
  with `ε = d_β/d_α`;
* `N = Θ(1/ε²)` therefore gives the multiplicity exactly after rounding, with
  constant success probability.

The formalisation below follows exactly this route. The rounding step uses an
`ε/4` margin (instead of the paper's `ε/2`) so that the half-integer boundary
never has to be decided; this changes only the universal constant (`32/ε²`
shots instead of the paper's `4/ε²`), not the asymptotic `Θ(1/ε²)`.

Everything in this file is fully proved; there is no `sorry` here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.RepMultiplic24.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators unitInterval

/-! ## Finite-probability helpers -/

/-- The probability of an event and of its complement add to one. -/
theorem probEvent_add_compl {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (E : (Fin L → X) → Prop) [DecidablePred E] :
    probEvent p E + probEvent p (fun ω => ¬ E ω) = 1 := by
  classical
  have hdisj : Disjoint (Finset.univ.filter E) (Finset.univ.filter (fun ω => ¬ E ω)) :=
    Finset.disjoint_filter_filter_not _ _ _
  have hunion : (Finset.univ.filter E) ∪ (Finset.univ.filter (fun ω => ¬ E ω))
      = (Finset.univ : Finset (Fin L → X)) := by
    simpa using
      (Finset.filter_union_filter_not_eq E (Finset.univ : Finset (Fin L → X)))
  unfold probEvent
  rw [← Finset.sum_union hdisj, hunion]
  simpa using p.sum_probOf L

/-- Event probability is monotone in the event. -/
theorem probEvent_mono {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) {E F : (Fin L → X) → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) :
    probEvent p E ≤ probEvent p F := by
  classical
  unfold probEvent
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω
  · intro ω _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-! ## The single-shot success probability -/

/-- The success probability of one shot of the restriction algorithm of
Theorem 1 / Lemma 2, Eq. (10): `p = mult · d_β / d_α`. Its being `≤ 1` is the
hypothesis `mult · d_β ≤ d_α`. -/
noncomputable def restrictionProb (dα dβ mult : ℕ) (hdα : 0 < dα)
    (hm : mult * dβ ≤ dα) : I :=
  ⟨(mult : ℝ) * (dβ : ℝ) / (dα : ℝ),
    by
      have hα : (0 : ℝ) < (dα : ℝ) := by exact_mod_cast hdα
      exact div_nonneg (by positivity) (le_of_lt hα),
    by
      rw [div_le_one (show (0 : ℝ) < (dα : ℝ) by exact_mod_cast hdα)]
      exact_mod_cast hm⟩

/-- The success probability of one shot of the induction algorithm of
Theorem 3, Eq. (17): `p = mult · |H| d_α / (|G| d_β)`. -/
noncomputable def inductionProb (dα dβ mult GH HH : ℕ) (hGH : 0 < GH) (hdβ : 0 < dβ)
    (hm : mult * (HH * dα) ≤ GH * dβ) : I :=
  ⟨(mult : ℝ) * ((HH : ℝ) * (dα : ℝ)) / ((GH : ℝ) * (dβ : ℝ)),
    by
      have hG : (0 : ℝ) < (GH : ℝ) := by exact_mod_cast hGH
      have hβ : (0 : ℝ) < (dβ : ℝ) := by exact_mod_cast hdβ
      exact div_nonneg (by positivity) (le_of_lt (mul_pos hG hβ)),
    by
      have hG : (0 : ℝ) < (GH : ℝ) := by exact_mod_cast hGH
      have hβ : (0 : ℝ) < (dβ : ℝ) := by exact_mod_cast hdβ
      rw [div_le_one (by positivity)]
      exact_mod_cast hm⟩

/-! ## The shot-count engine -/

/-- **Constant-probability shot count.** If `p = m · ε` with `0 < ε ≤ 1` and `p` a
probability, then with `N = ⌈32/ε²⌉` shots the rounded frequency estimator returns
the integer `m` with probability at least `1/2`. This is `Θ(1/ε²)` shots, as in
Supp. Mat. Eq. (97). -/
theorem shots_constant_probability (p : I) {ε : ℝ} {m : ℕ}
    (hε : 0 < ε) (hpm : (p : ℝ) = (m : ℝ) * ε) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 32 / ε ^ 2 + 1 ∧
      probEvent (bernoulliLaw p)
        (fun ω : Fin N → Bool => frequencyEstimate ε ω = m) ≥ 1 / 2 := by
  classical
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  refine ⟨Nat.ceil (32 / ε ^ 2), ?_, ?_, ?_⟩
  · -- positivity of the shot count
    have h1 : 1 ≤ Nat.ceil (32 / ε ^ 2) := Nat.one_le_ceil_iff.mpr (by positivity)
    omega
  · -- `⌈32/ε²⌉ ≤ 32/ε² + 1`
    have hceil := Nat.ceil_lt_add_one (a := 32 / ε ^ 2) (by positivity)
    have hcast : ((Nat.ceil (32 / ε ^ 2) : ℕ) : ℝ) < 32 / ε ^ 2 + 1 := hceil
    linarith
  · -- concentration: `16 p ≤ (1/2) ε² N`
    have hNpos : 0 < Nat.ceil (32 / ε ^ 2) := by
      have h1 : 1 ≤ Nat.ceil (32 / ε ^ 2) := Nat.one_le_ceil_iff.mpr (by positivity)
      omega
    have hp1 : (p : ℝ) ≤ 1 := p.2.2
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
    have hle : 32 / ε ^ 2 ≤ ((Nat.ceil (32 / ε ^ 2) : ℕ) : ℝ) := Nat.le_ceil _
    have hbound : 16 * (p : ℝ) ≤ (1 / 2 : ℝ) * ε ^ 2 * (Nat.ceil (32 / ε ^ 2) : ℝ) := by
      have h32 : (32 : ℝ) ≤ ε ^ 2 * (Nat.ceil (32 / ε ^ 2) : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left hle (le_of_lt hε2)
        have heq : ε ^ 2 * (32 / ε ^ 2) = 32 := by
          rw [mul_comm, div_mul_cancel₀ _ hε2.ne']
        linarith
      nlinarith [hp0, hp1, h32]
    obtain ⟨hbad, hgood⟩ :=
      shot_estimation_bound p hε hNpos hpm (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hbound
    -- `P(estimate = m) + P(estimate ≠ m) = 1` and `P(≠) ≤ P(bad)`
    have hmono : probEvent (bernoulliLaw p)
        (fun ω : Fin (Nat.ceil (32 / ε ^ 2)) → Bool =>
          ¬ (frequencyEstimate ε ω = m)) ≤
        probEvent (bernoulliLaw p)
          (fun ω : Fin (Nat.ceil (32 / ε ^ 2)) → Bool => frequencyBad (p := (p : ℝ)) ε ω) := by
      apply probEvent_mono
      intro ω hω
      by_contra hb
      exact hω (hgood ω hb)
    have hcompl := probEvent_add_compl (bernoulliLaw p)
      (fun ω : Fin (Nat.ceil (32 / ε ^ 2)) → Bool => frequencyEstimate ε ω = m)
    have hbad' : probEvent (bernoulliLaw p)
        (fun ω : Fin (Nat.ceil (32 / ε ^ 2)) → Bool => frequencyBad (p := (p : ℝ)) ε ω) ≤ 1 / 2 := by
      simpa only [FinDist.probEvent] using hbad
    linarith

/-! ## Lemma 2 -/

/-- **Lemma 2 (c005).** For `d_α, d_β > 0` and `1 ≤ mult ≤ d_α/d_β`, the restriction
algorithm (`p = mult · d_β/d_α`, Eq. (10)) determines `mult` with probability at
least `1/2` using at most `33 (d_α/d_β)²` shots.

Paper: fixed arXiv:2407.17649, Lemma 2 (main text), proof in Supp. Mat.
Eq. (94)-(97). The paper's Chernoff-Hoeffding constant `4` is replaced by `32`
for the `ε/4` rounding margin (same `Θ((d_α/d_β)²)` complexity). -/
theorem lemma2_shots (dα dβ mult : ℕ) (hdα : 0 < dα) (hdβ : 0 < dβ)
    (hmult : 0 < mult) (hm : mult * dβ ≤ dα) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 33 * ((dα : ℝ) / (dβ : ℝ)) ^ 2 ∧
      probEvent (bernoulliLaw (restrictionProb dα dβ mult hdα hm))
        (fun ω : Fin N → Bool => frequencyEstimate ((dβ : ℝ) / (dα : ℝ)) ω = mult) ≥ 1 / 2 := by
  have hα : (0 : ℝ) < (dα : ℝ) := by exact_mod_cast hdα
  have hβ : (0 : ℝ) < (dβ : ℝ) := by exact_mod_cast hdβ
  have hε : (0 : ℝ) < (dβ : ℝ) / (dα : ℝ) := by positivity
  have hε1 : (dβ : ℝ) / (dα : ℝ) ≤ 1 := by
    rw [div_le_one hα]
    have hmul1 : 1 ≤ mult := hmult
    have hle0 : dβ ≤ mult * dβ := by
      calc dβ = 1 * dβ := by ring
        _ ≤ mult * dβ := Nat.mul_le_mul_right dβ hmul1
    have hle : dβ ≤ dα := le_trans hle0 hm
    exact_mod_cast hle
  have hpm : ((restrictionProb dα dβ mult hdα hm : I) : ℝ) =
      (mult : ℝ) * ((dβ : ℝ) / (dα : ℝ)) := by
    simp only [restrictionProb]
    ring
  obtain ⟨N, hN, hbound, hprob⟩ :=
    shots_constant_probability (restrictionProb dα dβ mult hdα hm) hε hpm
  refine ⟨N, hN, ?_, hprob⟩
  have hratio : (33 : ℝ) / ((dβ : ℝ) / (dα : ℝ)) ^ 2 =
      33 * ((dα : ℝ) / (dβ : ℝ)) ^ 2 := by
    field_simp
  have hεsq : (1 : ℝ) ≤ 1 / ((dβ : ℝ) / (dα : ℝ)) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hs := mul_self_le_mul_self (le_of_lt hε) hε1
    nlinarith [hs]
  have hstep : (32 : ℝ) / ((dβ : ℝ) / (dα : ℝ)) ^ 2 + 1 ≤
      33 * ((dα : ℝ) / (dβ : ℝ)) ^ 2 := by
    rw [← hratio]
    set t : ℝ := 1 / ((dβ : ℝ) / (dα : ℝ)) ^ 2 with ht
    have ht1 : (1 : ℝ) ≤ t := by rw [ht]; exact hεsq
    have h32 : (32 : ℝ) / ((dβ : ℝ) / (dα : ℝ)) ^ 2 = 32 * t := by rw [ht]; ring
    have h33 : (33 : ℝ) / ((dβ : ℝ) / (dα : ℝ)) ^ 2 = 33 * t := by rw [ht]; ring
    rw [h32, h33]
    linarith
  linarith

end Qatlib.Papers.RepMultiplic24.MainResults
