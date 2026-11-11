/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.Multilevel.Theorem3

set_option backward.isDefEq.respectTransparency false

/-!
# Corollaries 3, 4 and 5: Black-Scholes, local volatility and Malliavin Greeks

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

* Corollary 3 (p. 19, (5.11)--(5.12)): Black-Scholes GBM (5.1) with the zeroth-order
  oracle (5.7), QA-MLMC cost `Õ(ε^{-1})` for `r > 2`, `Õ(ε^{-1/2-1/r-o(1)})` for `r ≤ 2`,
  and `Õ(ε^{-1})` / `Õ(ε^{-1/r})` for globally Lipschitz payoffs with `r ≥ 1` / `r < 1`.
* Corollary 4 (p. 20, (6.4)--(6.5)): the same cost profile for the local-volatility SDE
  (6.1).
* Corollary 5 (p. 22, (7.8)--(7.10)): the same cost profile for the Delta computed by the
  Malliavin-weight estimator (7.8) of the extended process `(X_t, Y_t)`.

Each corollary is an instantiation of Theorem 3/Corollary 2 to the model in question.
The hypotheses `hGen`, `hLip` are the cost statements of Theorem 2 at the exponents
supplied by Proposition 2 (general piecewise-Lipschitz payoff, respectively the improved
global-Lipschitz rates) for the corresponding model.  The generic theorem
`qamlc_regimes` performs the substitution once.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- The cost profile shared by Corollaries 3, 4 and 5 (displays (5.11)--(5.12),
(6.4)--(6.5), (7.9)--(7.10)), in `Õ` form. -/
theorem qamlc_regimes {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ}
    (hGen : ∀ δ : ℝ, 0 < δ →
      CostTildeClass (quantumMLMCExponent (r - δ) ((r - δ) / 2) 1) cost)
    (hLip : CostTildeClass (quantumMLMCExponent r r 1) cost) :
    (2 < r → CostTildeClass 1 cost) ∧
      (r ≤ 2 → ∀ δ : ℝ, 0 < δ → CostTildeClass (1 / 2 + 1 / r + δ) cost) ∧
      (1 ≤ r → CostTildeClass 1 cost) ∧ (r < 1 → CostTildeClass (1 / r) cost) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hr2
    have hδ : 0 < (r - 2) / 2 := by linarith
    have hexp : quantumMLMCExponent (r - (r - 2) / 2) ((r - (r - 2) / 2) / 2) 1 = 1 := by
      unfold quantumMLMCExponent
      rw [if_pos (show (1 : ℝ) < (r - (r - 2) / 2) / 2 by linarith)]
    have hh := hGen ((r - 2) / 2) hδ
    rwa [hexp] at hh
  · intro hr2 δ hδ
    obtain ⟨η, hη0, hηr, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ r / 2 ∧ η ≤ δ * r ^ 2 / 2 :=
      ⟨min (r / 2) (min (δ * r ^ 2 / 2) (r / 2)), lt_min (by linarith)
          (lt_min (by positivity) (by linarith)),
        (min_le_right _ _).trans (min_le_right _ _),
        (min_le_right _ _).trans (min_le_left _ _)⟩
    have hrδ : 0 < r - η := by linarith
    have hlt : ¬ (1 < (r - η) / 2) := by nlinarith
    have hexp : quantumMLMCExponent (r - η) ((r - η) / 2) 1 = 1 / 2 + 1 / (r - η) := by
      unfold quantumMLMCExponent
      rw [if_neg hlt]
      have hrη0 : r - η ≠ 0 := ne_of_gt hrδ
      field_simp
      ring
    have hbound : 1 / (r - η) ≤ 1 / r + δ := by
      have hdiff : 1 / (r - η) - 1 / r = η / (r * (r - η)) := by
        have hr0 : r ≠ 0 := ne_of_gt hr
        have hrη0 : r - η ≠ 0 := ne_of_gt hrδ
        field_simp
        ring
      have hden : 0 < r * (r - η) := by positivity
      have hle : η / (r * (r - η)) ≤ δ := by
        rw [div_le_iff₀ hden]
        nlinarith [sq_nonneg r, hr]
      linarith
    have hclass := hGen η hη0
    rw [hexp] at hclass
    exact costTildeClass_mono_exp (by linarith) hclass
  · intro hr1
    by_cases hrne : r = 1
    · subst hrne
      have hexp : quantumMLMCExponent 1 1 1 = 1 := by
        unfold quantumMLMCExponent
        rw [if_neg (by norm_num : ¬ (1 : ℝ) < 1)]
        norm_num
      rw [← hexp]
      exact hLip
    · have hlt : (1 : ℝ) < r := lt_of_le_of_ne hr1 (Ne.symm hrne)
      have hexp : quantumMLMCExponent r r 1 = 1 := by
        unfold quantumMLMCExponent
        rw [if_pos hlt]
      rw [← hexp]
      exact hLip
  · intro hr1
    have hexp : quantumMLMCExponent r r 1 = 1 / r := by
      unfold quantumMLMCExponent
      rw [if_neg (not_lt.mpr (by linarith))]
      have hr0 : r ≠ 0 := ne_of_gt hr
      field_simp
      ring
    rw [← hexp]
    exact hLip

/-- Corollary 3 (p. 19, (5.11)--(5.12)): Black-Scholes GBM with a zeroth-order oracle. -/
theorem corollary3 {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ}
    (hGen : ∀ δ : ℝ, 0 < δ →
      CostTildeClass (quantumMLMCExponent (r - δ) ((r - δ) / 2) 1) cost)
    (hLip : CostTildeClass (quantumMLMCExponent r r 1) cost) :
    (2 < r → CostTildeClass 1 cost) ∧
      (r ≤ 2 → ∀ δ : ℝ, 0 < δ → CostTildeClass (1 / 2 + 1 / r + δ) cost) ∧
      (1 ≤ r → CostTildeClass 1 cost) ∧ (r < 1 → CostTildeClass (1 / r) cost) :=
  qamlc_regimes hr hGen hLip

/-- Corollary 4 (p. 20, (6.4)--(6.5)): local-volatility SDE with a zeroth-order oracle. -/
theorem corollary4 {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ}
    (hGen : ∀ δ : ℝ, 0 < δ →
      CostTildeClass (quantumMLMCExponent (r - δ) ((r - δ) / 2) 1) cost)
    (hLip : CostTildeClass (quantumMLMCExponent r r 1) cost) :
    (2 < r → CostTildeClass 1 cost) ∧
      (r ≤ 2 → ∀ δ : ℝ, 0 < δ → CostTildeClass (1 / 2 + 1 / r + δ) cost) ∧
      (1 ≤ r → CostTildeClass 1 cost) ∧ (r < 1 → CostTildeClass (1 / r) cost) :=
  qamlc_regimes hr hGen hLip

/-- Corollary 5 (p. 22, (7.9)--(7.10)): the Malliavin Delta estimator (7.8). -/
theorem corollary5 {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ}
    (hGen : ∀ δ : ℝ, 0 < δ →
      CostTildeClass (quantumMLMCExponent (r - δ) ((r - δ) / 2) 1) cost)
    (hLip : CostTildeClass (quantumMLMCExponent r r 1) cost) :
    (2 < r → CostTildeClass 1 cost) ∧
      (r ≤ 2 → ∀ δ : ℝ, 0 < δ → CostTildeClass (1 / 2 + 1 / r + δ) cost) ∧
      (1 ≤ r → CostTildeClass 1 cost) ∧ (r < 1 → CostTildeClass (1 / r) cost) :=
  qamlc_regimes hr hGen hLip

end Qatlib.Papers.MultilevelMC20.MainResults
