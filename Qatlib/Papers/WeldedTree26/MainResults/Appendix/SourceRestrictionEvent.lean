/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# WeldedTree26 — Lemma A.3 (restriction to an event), fully proved

Fixed source: arXiv:2609.26712v1, Lemma A.3, p.33, eq. (106).

> Let `F_{i,*}` be the restriction of `F_i` to a collection of allowed anchors involving `ℓ`
> distinct core vertices.  If `Pr_{μ_i}[B | X_{i,a}=v] ≤ p` for every anchor in this
> collection, then `‖1_B F_{i,*}‖² ≤ ℓ p`.  The same bound holds for a restriction of
> `F_i ⊗ F_j` to a collection of pairs of anchors in distinct cores.

This file formalises the finite weighted-`L²` content of the lemma, which is the whole
mathematical substance of the paper's proof (eq. (107)): within each anchor summand the
indicators have disjoint supports, so the event norm is bounded by the conditional probability;
Cauchy–Schwarz over the `ℓ` summands gives the factor `ℓ`.

`μ` is the placement measure (`μ_i` or `μ_i ⊗ μ_j`), `f a` is the anchor component
`f_a ∈ L²(X_{i,a})`, `B` is the event, and `p` the conditional-probability bound.  The
conclusion is exactly `‖1_B ∑_a f_a‖² ≤ ℓ p ∑_a ‖f_a‖²`, i.e. the operator-norm-squared bound
for the restriction `F_{i,*}`.  The proof is complete (no `sorry`).
-/

open Qatlib.Foundations.InstrumentCore.Measurement
set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeldedTree26.MainResults.Appendix

open scoped BigOperators

/-- **Lemma A.3 (Restriction to an event)** — arXiv:2609.26712v1 p.33, eq. (106).

For a finite collection `ι` of allowed anchors and a finite outcome space `Ω` with nonnegative
weights `μ`, if the conditional event probability obeys
`∑_{ω∈B} μ ω ‖f a ω‖² ≤ p ∑_ω μ ω ‖f a ω‖²` for every anchor `a`, then
`∑_{ω∈B} μ ω ‖∑_a f a ω‖² ≤ ℓ p ∑_a ∑_ω μ ω ‖f a ω‖²`, `ℓ = card ι`.

Paper proof (eq. (107)): pointwise `‖∑_a f_a‖² ≤ ℓ ∑_a ‖f_a‖²` (Cauchy–Schwarz), then
sum the per-anchor conditional-probability bound. -/
theorem restriction_to_event
    {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (f : ι → Ω → ℂ) (B : Ω → Prop) [DecidablePred B]
    (p : ℝ)
    (hp : ∀ a, (∑ ω, if B ω then μ ω * ‖f a ω‖ ^ 2 else 0)
        ≤ p * ∑ ω, μ ω * ‖f a ω‖ ^ 2) :
    (∑ ω, if B ω then μ ω * ‖∑ a, f a ω‖ ^ 2 else 0)
      ≤ (Fintype.card ι : ℝ) * p * ∑ a, ∑ ω, μ ω * ‖f a ω‖ ^ 2 := by
  set L : ℝ := (Fintype.card ι : ℝ) with hL
  have hL0 : 0 ≤ L := by positivity
  -- Pointwise Cauchy–Schwarz: `‖∑ a, f a ω‖² ≤ L ∑ a, ‖f a ω‖²`.
  have hpoint : ∀ ω, ‖∑ a, f a ω‖ ^ 2 ≤ L * ∑ a, ‖f a ω‖ ^ 2 := by
    intro ω
    have h1 : ‖∑ a, f a ω‖ ≤ ∑ a, ‖f a ω‖ := norm_sum_le _ _
    have h2 : 0 ≤ ∑ a, ‖f a ω‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h3 : 0 ≤ ‖∑ a, f a ω‖ := norm_nonneg _
    have hsq : ‖∑ a, f a ω‖ ^ 2 ≤ (∑ a, ‖f a ω‖) ^ 2 := by
      exact pow_le_pow_left₀ h3 h1 2
    have hcs : (∑ a, ‖f a ω‖) ^ 2 ≤ (∑ a, ‖f a ω‖ ^ 2) * (∑ _a : ι, (1 : ℝ) ^ 2) := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun a => ‖f a ω‖) (fun _ => (1 : ℝ))
    have hcard : (∑ _a : ι, (1 : ℝ) ^ 2) = L := by
      simp [L]
    rw [hcard] at hcs
    calc ‖∑ a, f a ω‖ ^ 2 ≤ (∑ a, ‖f a ω‖) ^ 2 := hsq
      _ ≤ (∑ a, ‖f a ω‖ ^ 2) * L := hcs
      _ = L * ∑ a, ‖f a ω‖ ^ 2 := by ring
  -- Termwise bound after inserting the pointwise estimate.
  have hstep : (∑ ω, if B ω then μ ω * ‖∑ a, f a ω‖ ^ 2 else 0)
      ≤ ∑ ω, if B ω then μ ω * (L * ∑ a, ‖f a ω‖ ^ 2) else 0 := by
    apply Finset.sum_le_sum
    intro ω _
    by_cases hB : B ω
    · simp only [hB, if_true]
      exact mul_le_mul_of_nonneg_left (hpoint ω) (hμ ω)
    · simp [hB]
  -- Move `L` out, interchange the two sums, and apply the per-anchor hypothesis.
  have hrewrite :
      (∑ ω, if B ω then μ ω * (L * ∑ a, ‖f a ω‖ ^ 2) else 0)
        = L * ∑ a, ∑ ω, if B ω then μ ω * ‖f a ω‖ ^ 2 else 0 := by
    have h1 : ∀ ω, (if B ω then μ ω * (L * ∑ a, ‖f a ω‖ ^ 2) else 0)
        = if B ω then L * (μ ω * ∑ a, ‖f a ω‖ ^ 2) else 0 := by
      intro ω
      by_cases hB : B ω
      · simp only [hB, if_true]; ring
      · simp [hB]
    simp only [h1]
    have hLout : (∑ x, if B x then L * (μ x * ∑ a, ‖f a x‖ ^ 2) else 0)
        = L * ∑ x, if B x then μ x * ∑ a, ‖f a x‖ ^ 2 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hB : B x
      · simp only [hB, if_true]
      · simp [hB]
    have hswap : (∑ x, if B x then μ x * ∑ a, ‖f a x‖ ^ 2 else 0)
        = ∑ a, ∑ ω, if B ω then μ ω * ‖f a ω‖ ^ 2 else 0 := by
      have h2 : ∀ x, (if B x then μ x * ∑ a, ‖f a x‖ ^ 2 else 0)
          = ∑ a, if B x then μ x * ‖f a x‖ ^ 2 else 0 := by
        intro x
        by_cases hB : B x
        · simp only [hB, if_true]
          rw [Finset.mul_sum]
        · simp [hB]
      simp only [h2]
      exact Finset.sum_comm
    rw [hLout, hswap]
  calc (∑ ω, if B ω then μ ω * ‖∑ a, f a ω‖ ^ 2 else 0)
      ≤ ∑ ω, if B ω then μ ω * (L * ∑ a, ‖f a ω‖ ^ 2) else 0 := hstep
    _ = L * ∑ a, ∑ ω, if B ω then μ ω * ‖f a ω‖ ^ 2 else 0 := hrewrite
    _ ≤ L * ∑ a, p * ∑ ω, μ ω * ‖f a ω‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hL0
        exact Finset.sum_le_sum fun a _ => hp a
    _ = L * p * ∑ a, ∑ ω, μ ω * ‖f a ω‖ ^ 2 := by
        rw [← Finset.mul_sum, mul_assoc]

/-- **Lemma A.3, two distinct cores** — arXiv:2609.26712v1 p.33, after eq. (106).
The same estimate for a restriction of `F_i ⊗ F_j`: the anchor index is a pair `(a,b)`, the
measure is `μ_i ⊗ μ_j`, `p` bounds the conditional probability given both anchors, and `ℓ`
counts the distinct pairs of core vertices. -/
theorem restriction_to_event_pair
    {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (f : ι → κ → Ω → ℂ) (B : Ω → Prop) [DecidablePred B]
    (p : ℝ)
    (hp : ∀ a b, (∑ ω, if B ω then μ ω * ‖f a b ω‖ ^ 2 else 0)
        ≤ p * ∑ ω, μ ω * ‖f a b ω‖ ^ 2) :
    (∑ ω, if B ω then μ ω * ‖∑ a, ∑ b, f a b ω‖ ^ 2 else 0)
      ≤ (Fintype.card (ι × κ) : ℝ) * p * ∑ a, ∑ b, ∑ ω, μ ω * ‖f a b ω‖ ^ 2 := by
  -- Collapse the pair index and reuse the single-index statement.
  let g : ι × κ → Ω → ℂ := fun q ω => f q.1 q.2 ω
  have hg : ∀ q : ι × κ, (∑ ω, if B ω then μ ω * ‖g q ω‖ ^ 2 else 0)
      ≤ p * ∑ ω, μ ω * ‖g q ω‖ ^ 2 := by
    rintro ⟨a, b⟩
    exact hp a b
  have h := restriction_to_event (ι := ι × κ) μ hμ g B p hg
  have hsum : (∑ a, ∑ b, ∑ ω, μ ω * ‖f a b ω‖ ^ 2)
      = ∑ q : ι × κ, ∑ ω, μ ω * ‖g q ω‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hpoint : (∑ ω, if B ω then μ ω * ‖∑ a, ∑ b, f a b ω‖ ^ 2 else 0)
      = ∑ ω, if B ω then μ ω * ‖∑ q : ι × κ, g q ω‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro ω _
    have hvec : (∑ a, ∑ b, f a b ω) = ∑ q : ι × κ, g q ω := by
      simpa [g] using (Fintype.sum_prod_type (f := fun q => g q ω)).symm
    rw [hvec]
  rw [hpoint, hsum]
  exact h

end Qatlib.Papers.WeldedTree26.MainResults.Appendix
