/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.CostModel.CostAsymptotics

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3: complexity of QA-MLMC for SDEs

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

Paper Theorem 3 (p. 15, display (4.14)--(4.15)):

> Under Assumptions 1--3, QA-MLMC with a scheme of strong order `r` estimates `E[P]` up to
> additive error `ε` with probability at least `0.99` in cost `O(ε^{-1}(log 1/ε)^{3/2}
> (log log 1/ε)²)` for `r > 2`, and `O(ε^{-1/2-1/r-o(1)}(log 1/ε)^{3/2}(log log 1/ε)²)`
> for `r ≤ 2`.  If `P` is globally Lipschitz, `O(ε^{-1}(log 1/ε)^{3/2}(log log 1/ε)²)`
> for `r > 1`, `O(ε^{-1}(log 1/ε)^{7/2}(log log 1/ε)²)` for `r = 1`, and
> `O(ε^{-1/r}(log 1/ε)^{3/2}(log log 1/ε)²)` for `r < 1`.

The proof is "a straightforward result from Theorem 2 and Proposition 2".  With
`γ = 1` and `β̂ = r/2` for a strong-order-`r` scheme (recall `β = 2β̂ = r`), Theorem 2's
three cases give the polynomial exponent

* `1` when `β̂ > γ`, i.e. `r > 2`;
* `1 + (γ - β̂)/α = 1/2 + 1/r` when `β̂ < γ`, i.e. `r ≤ 2`,

matching (4.14).  `quantumMLMCExponent` records the first two cases of Theorem 2's
display (3.8) as a function of the exponents; the definitions and the substitution are
proved below.  The global-Lipschitz branch `β̂ = r` gives (4.15).
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- The polynomial exponent of the QA-MLMC cost (Theorem 2, display (3.8)) for a level
model with exponents `α`, `β̂`, `γ`. -/
def quantumMLMCExponent (α bhat γ : ℝ) : ℝ :=
  if γ < bhat then 1 else 1 + (γ - bhat) / α

/-- Theorem 3, general payoff (p. 15, (4.14)).  The hypothesis `h` is Theorem 2's cost
statement at the rate `(α, β̂) = (r - δ, (r - δ)/2)` supplied by Proposition 2 for
arbitrarily small `δ > 0`; the conclusion is the display (4.14). -/
theorem theorem3_general {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ} {q s : ℝ}
    (h : ∀ δ : ℝ, 0 < δ →
      CostClass (quantumMLMCExponent (r - δ) ((r - δ) / 2) 1) q s cost) :
    (2 < r → CostClass 1 q s cost) ∧
      (r ≤ 2 → ∀ δ : ℝ, 0 < δ → CostClass (1 / 2 + 1 / r + δ) q s cost) := by
  constructor
  · intro hr2
    have hδ : 0 < (r - 2) / 2 := by linarith
    have hexp : quantumMLMCExponent (r - (r - 2) / 2) ((r - (r - 2) / 2) / 2) 1 = 1 := by
      unfold quantumMLMCExponent
      rw [if_pos]
      ring_nf
      nlinarith
    have hh := h ((r - 2) / 2) hδ
    rwa [hexp] at hh
  · intro hr2 δ hδ
    -- choose a rate slack `η` small enough that `1/(r-η) ≤ 1/r + δ`.
    obtain ⟨η, hη0, hηsmall⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ r / 2 ∧ η ≤ δ * r ^ 2 / 2 := by
      refine ⟨min (r / 2) (min (δ * r ^ 2 / 2) (r / 2)), ?_, ?_, ?_⟩
      · exact lt_min (by linarith) (lt_min (by positivity) (by linarith))
      · exact (min_le_right _ _).trans (min_le_right _ _)
      · exact (min_le_right _ _).trans (min_le_left _ _)
    have hrδ : 0 < r - η := by linarith
    have hlt : ¬ (1 < (r - η) / 2) := by nlinarith
    have hexp : quantumMLMCExponent (r - η) ((r - η) / 2) 1 = 1 / 2 + 1 / (r - η) := by
      unfold quantumMLMCExponent
      rw [if_neg hlt]
      field_simp
      ring
    have hbound : 1 / (r - η) ≤ 1 / r + δ := by
      have hdiff : 1 / (r - η) - 1 / r = η / (r * (r - η)) := by
        field_simp
        ring
      have hden : 0 < r * (r - η) := by positivity
      have hle : η / (r * (r - η)) ≤ δ := by
        rw [div_le_iff₀ hden]
        nlinarith [sq_nonneg r, hr]
      linarith
    have hclass := h η hη0
    rw [hexp] at hclass
    exact costClass_mono (by linarith) le_rfl le_rfl hclass

/-- Theorem 3, global-Lipschitz improvement (p. 15, (4.15)): with `α = r`, `β̂ = r`,
`γ = 1`, the QA-MLMC cost is `O(ε^{-1})` for `r > 1`, `O(ε^{-1}(log 1/ε)^{7/2}
(log log 1/ε)²)` for `r = 1`, and `O(ε^{-1/r})` for `r < 1`. -/
theorem theorem3_lipschitz {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ} {q s : ℝ}
    (h : CostClass (quantumMLMCExponent r r 1) q s cost) :
    (1 < r → CostClass 1 q s cost) ∧ (r ≤ 1 → CostClass (1 / r) q s cost) := by
  constructor
  · intro hr1
    have hexp : quantumMLMCExponent r r 1 = 1 := by
      unfold quantumMLMCExponent
      rw [if_pos hr1]
    rwa [hexp] at h
  · intro hr1
    have hexp : quantumMLMCExponent r r 1 = 1 / r := by
      unfold quantumMLMCExponent
      rw [if_neg (not_lt.mpr hr1)]
      field_simp
      ring
    rw [hexp] at h
    exact h

end Qatlib.Papers.MultilevelMC20.MainResults
