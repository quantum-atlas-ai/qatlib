/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.Convergence — Lemma 5: lower bound on the accepted effective step

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Lemma 5 and Eq. (B3), p. 15.

At a nonstationary iterate of Algorithm 2 the Armijo backtracking test is
`Q(t) ≥ q + c·t·γ·G`, where `Q(t) = f(R_U^(5)(t γ g_U))`, `G = ‖g_U‖²_F`, and the Riemannian
Lipschitz estimate Eq. (B2) gives the quadratic lower bound
`Q(t) ≥ q + tγG - (L_Rie/2)(tγ)²G` for every `t ≥ 0`.

Lemma 5 proves (i) the backtracking loop terminates after finitely many reductions, and
(ii) any accepted effective step with the *smallest* admissible `m` satisfies
`t_k γ_k ≥ σ := min{1, 2ρ(1-c)/L_Rie}` (Eq. (B3)).

This file formalizes the scalar core of that argument.  The algorithmic quantities are exposed
as the real numbers `q, G, γ, L, c, ρ` and the trial-objective function `stepQ`; the two
hypotheses `hTaylor` and the backtracking facts are exactly the paper's Eq. (B2) and Algorithm
2's line-search rule.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchPrec26.RmSearch.Convergence

/-- The Armijo acceptance test of Algorithm 2 at trial step `t`, with scaling `γ`, squared
gradient norm `G` and Armijo constant `c`. -/
def armijo (stepQ : ℝ → ℝ) (q γ G c t : ℝ) : Prop :=
  q + c * t * γ * G ≤ stepQ t

/-- **Lemma 5** (arXiv:2603.26039v3, Lemma 5 / Eq. (B3), p. 15).  Assume `γ ≥ 1`, `L > 0`,
`G > 0`, `0 < c < 1`, `0 < ρ < 1`, and the Eq. (B2) quadratic lower bound
`Q(t) ≥ q + tγG - (L/2)(tγ)²G` for all `t ≥ 0`.  Then

* the Armijo backtracking loop accepts some trial step `ρ^m` after finitely many reductions;
* if `ρ^m` is the *first* accepted trial step (all `ρ^j`, `j < m`, rejected), then the accepted
  effective step satisfies `ρ^m γ ≥ min{1, 2ρ(1-c)/L}`.

The constant `min{1, 2ρ(1-c)/L}` is `σ` of Eq. (B3), with `L = L_Rie`. -/
theorem lemma5_effective_step_lower_bound
    (q G γ L c ρ : ℝ)
    (hγ1 : 1 ≤ γ) (hL : 0 < L) (hG : 0 < G)
    (hc : 0 < c) (hc1 : c < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (stepQ : ℝ → ℝ)
    (hTaylor : ∀ t, 0 ≤ t → q + t * γ * G - L / 2 * (t * γ) ^ 2 * G ≤ stepQ t) :
    (∃ m : ℕ, armijo stepQ q γ G c (ρ ^ m)) ∧
      (∀ m : ℕ, (∀ j, j < m → ¬ armijo stepQ q γ G c (ρ ^ j)) →
        armijo stepQ q γ G c (ρ ^ m) →
        ρ ^ m * γ ≥ min 1 (2 * ρ * (1 - c) / L)) := by
  have hγpos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ1
  have hLγ : 0 < L * γ := mul_pos hL hγpos
  constructor
  · -- Finite termination: a trial step below `B_k = 2(1-c)/(Lγ)` satisfies Armijo.
    have hBpos : 0 < 2 * (1 - c) / (L * γ) := by
      have : 0 < 1 - c := by linarith
      positivity
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hBpos hρ1
    refine ⟨m, ?_⟩
    have ht0 : 0 ≤ ρ ^ m := (pow_pos hρ0 m).le
    have hT := hTaylor _ ht0
    -- `ρ^m γ < 2(1-c)/L`.
    have hsmall : ρ ^ m * γ < 2 * (1 - c) / L := by
      have := (lt_div_iff₀ hLγ).mp hm
      exact (lt_div_iff₀ hL).mpr (by nlinarith [this])
    have htγ : 0 < ρ ^ m * γ := mul_pos (pow_pos hρ0 m) hγpos
    have hLt : L * (ρ ^ m * γ) < 2 * (1 - c) := by
      have := (lt_div_iff₀ hL).mp hsmall
      nlinarith [this]
    have hbound : L / 2 * (ρ ^ m * γ) ^ 2 * G ≤ (1 - c) * (ρ ^ m * γ) * G := by
      have h1 : L / 2 * (ρ ^ m * γ) ≤ 1 - c := by nlinarith [hLt]
      have h2 : L / 2 * (ρ ^ m * γ) * (ρ ^ m * γ) ≤ (1 - c) * (ρ ^ m * γ) :=
        mul_le_mul_of_nonneg_right h1 htγ.le
      have h3 : L / 2 * (ρ ^ m * γ) * (ρ ^ m * γ) * G
          ≤ (1 - c) * (ρ ^ m * γ) * G :=
        mul_le_mul_of_nonneg_right h2 hG.le
      nlinarith [h3]
    unfold armijo
    nlinarith [hT, hbound]
  · intro m hrej hacc
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst m
      simp only [pow_zero, one_mul]
      exact le_trans (min_le_left _ _) hγ1
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hk : ¬ armijo stepQ q γ G c (ρ ^ k) := hrej k (Nat.lt_succ_self k)
      have htpos : 0 < ρ ^ k := pow_pos hρ0 k
      have hT := hTaylor (ρ ^ k) htpos.le
      unfold armijo at hk
      have hlt : stepQ (ρ ^ k) < q + c * ρ ^ k * γ * G := lt_of_not_ge hk
      -- Dividing the strict inequality gives `2(1-c)/L < ρ^k γ`.
      have hkey : 2 * (1 - c) / L < ρ ^ k * γ := by
        have htγ : 0 < ρ ^ k * γ := mul_pos htpos hγpos
        have hmid : (1 - c) * (ρ ^ k * γ) * G < L / 2 * (ρ ^ k * γ) ^ 2 * G := by
          nlinarith [hT, hlt]
        have huG : 0 < (ρ ^ k * γ) * G := mul_pos htγ hG
        have h' : (1 - c) * ((ρ ^ k * γ) * G) < (L / 2 * (ρ ^ k * γ)) * ((ρ ^ k * γ) * G) := by
          nlinarith [hmid]
        have hdiv : 1 - c < L / 2 * (ρ ^ k * γ) :=
          lt_of_mul_lt_mul_right (by nlinarith [h']) huG.le
        have h2c : 2 * (1 - c) < (ρ ^ k * γ) * L := by
          have h2 := mul_lt_mul_of_pos_left hdiv (by norm_num : (0 : ℝ) < 2)
          nlinarith [h2]
        exact (div_lt_iff₀ hL).mpr h2c
      have hgoal : 2 * ρ * (1 - c) / L ≤ ρ ^ (k + 1) * γ := by
        have hstep : 2 * ρ * (1 - c) / L < ρ * (ρ ^ k * γ) := by
          calc 2 * ρ * (1 - c) / L = ρ * (2 * (1 - c) / L) := by ring
            _ < ρ * (ρ ^ k * γ) := mul_lt_mul_of_pos_left hkey hρ0
        rw [pow_succ]
        nlinarith [hstep]
      exact le_trans (min_le_right _ _) hgoal

end Qatlib.Papers.QSearchPrec26.RmSearch.Convergence
