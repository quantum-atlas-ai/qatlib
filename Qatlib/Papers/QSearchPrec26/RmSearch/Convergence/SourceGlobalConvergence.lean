/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.Convergence — Proposition 1: global monotone convergence

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Proposition 1 and Eq. (B6), p. 15–16.

Let `q_k = f(U_k) = Tr(Hψ_k) ∈ [0,1]` be the success probability produced by Algorithm 2 with
the 5-factor retraction, `G_k = ‖g_k‖²_F = 2q_k(1-q_k)`, `t_k` the accepted Armijo step and
`γ_k` the modified-Newton scaling.  Lemma 5 gives `t_k γ_k ≥ σ` with
`σ = min{1, 2ρ(1-c)/L_Rie}` (Eq. (B3)), and the Armijo condition gives
`q_{k+1} ≥ q_k + c t_k γ_k G_k`.  Proposition 1 then proves
`q_{k+1} ≥ q_k + 2cσ q_k(1-q_k)` (Eq. (B6)), hence `{q_k}` is monotone nondecreasing and
converges to `1`.

This file formalizes the sequence-theoretic core: the Armijo and effective-step facts enter as
explicit hypotheses (they are the conclusions of Lemma 5), and the conclusion is the paper's
global monotone convergence.
-/

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology

namespace Qatlib.Papers.QSearchPrec26.RmSearch.Convergence

/-- **Proposition 1** (arXiv:2603.26039v3, Proposition 1, p. 15–16).  Suppose the success
probabilities `q : ℕ → ℝ` satisfy `0 ≤ q_k ≤ 1`, the Armijo recurrence
`q_{k+1} ≥ q_k + c·t_k·γ_k·G_k`, the Lemma 5 effective-step bound `t_k·γ_k ≥ σ` with
`σ = min{1, 2ρ(1-c)/L_Rie}`, and `G_k = 2q_k(1-q_k)`, for parameters `0 < δ ≤ 1`,
`0 < c ≤ 1/2`, `0 < ρ < 1` and `L_Rie > 0`, with `q_0 > 0` (`q_0 = M/N`).
Then `q_k` is monotonically nondecreasing and converges to `1`. -/
theorem proposition1_global_monotone_convergence
    (q : ℕ → ℝ) (t γ G : ℕ → ℝ) (L c ρ δ σ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L)
    (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hσ : σ = min 1 (2 * ρ * (1 - c) / L))
    (hq0 : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (hqpos : 0 < q 0)
    (hArmijo : ∀ k, q (k + 1) ≥ q k + c * (t k * γ k) * G k)
    (hStep : ∀ k, t k * γ k ≥ σ)
    (hG : ∀ k, G k = 2 * q k * (1 - q k)) :
    (∀ k, q k ≤ q (k + 1)) ∧ Tendsto q atTop (𝓝 1) := by
  -- `σ > 0`.
  have hσpos : 0 < σ := by
    rw [hσ]
    apply lt_min one_pos
    have h1c : 0 < 1 - c := by linarith
    positivity
  -- Eq. (B6): `q(k+1) - q k ≥ 2cσ q_k(1-q_k)`.
  have hB6 : ∀ k, q (k + 1) - q k ≥ 2 * c * σ * (q k * (1 - q k)) := by
    intro k
    have hGk := hG k
    have hqk := hq0 k
    have hGnonneg : 0 ≤ G k := by rw [hGk]; nlinarith [hqk.1, hqk.2]
    have hcG : 0 ≤ c * σ * G k := mul_nonneg (mul_nonneg hc.le hσpos.le) hGnonneg
    have h1 : c * (t k * γ k) * G k ≥ c * σ * G k := by
      have hcG' : 0 ≤ c * G k := mul_nonneg hc.le hGnonneg
      nlinarith [hStep k, hcG']
    have h3 : c * σ * G k = 2 * c * σ * (q k * (1 - q k)) := by
      rw [hGk]; ring
    linarith [hArmijo k, h1, h3]
  have hmonoStep : ∀ k, q k ≤ q (k + 1) := by
    intro k
    have hqk := hq0 k
    have hnn : 0 ≤ 2 * c * σ * (q k * (1 - q k)) := by
      have : 0 ≤ q k * (1 - q k) := mul_nonneg hqk.1 (by linarith [hqk.2])
      positivity
    linarith [hB6 k, hnn]
  have hmono : Monotone q := monotone_nat_of_le_succ hmonoStep
  have hbdd : BddAbove (Set.range q) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (hq0 k).2
  -- Monotone bounded sequence has a limit `l = ⨆ q`.
  have htend : Tendsto q atTop (𝓝 (⨆ k, q k)) := tendsto_atTop_ciSup hmono hbdd
  set l := ⨆ k, q k with hl
  -- `q_0 ≤ l` and `l ≤ 1`.
  have hq0le : q 0 ≤ l := by
    rw [hl]
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend
      (Eventually.of_forall fun k => hmono (Nat.zero_le k))
  have hlpos : 0 < l := lt_of_lt_of_le hqpos hq0le
  have hl1 : l ≤ 1 := by
    rw [hl]
    exact le_of_tendsto_of_tendsto htend tendsto_const_nhds
      (Eventually.of_forall fun k => (hq0 k).2)
  -- Passing Eq. (B6) to the limit: `2cσ l(1-l) ≤ 0`.
  have hshift : Tendsto (fun k => q (k + 1)) atTop (𝓝 l) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun k => q (k + 1) - q k) atTop (𝓝 (l - l)) :=
    hshift.sub htend
  have hright : Tendsto (fun k => 2 * c * σ * (q k * (1 - q k))) atTop
      (𝓝 (2 * c * σ * (l * (1 - l)))) := by
    have hinner : Tendsto (fun k => q k * (1 - q k)) atTop (𝓝 (l * (1 - l))) :=
      htend.mul (tendsto_const_nhds.sub htend)
    exact tendsto_const_nhds.mul hinner
  have hlimle : 2 * c * σ * (l * (1 - l)) ≤ 0 := by
    have h := le_of_tendsto_of_tendsto hright hdiff
      (Eventually.of_forall fun k => hB6 k)
    simpa using h
  -- Hence `l = 1`.
  have hlge1 : 1 ≤ l := by
    have hfac : l * (1 - l) ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have hpos : 0 < 2 * c * σ := by positivity
      nlinarith [hlimle, hpos, hcon]
    by_contra hcon
    push_neg at hcon
    nlinarith [hfac, hlpos, hcon]
  have hl_eq : l = 1 := le_antisymm hl1 hlge1
  refine ⟨hmonoStep, ?_⟩
  rw [hl_eq] at htend
  exact htend

end Qatlib.Papers.QSearchPrec26.RmSearch.Convergence
