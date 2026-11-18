/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Lemma 4 — the multiproduct order boost by moment cancellation

Fixed source: Childs and Wiebe, arXiv:1202.5822v1, Lemma 4, Eq. (18):
for a multiproduct `M_{k,χ}(λ) = Σ_q C_q S_χ(λ/ℓ_q)^{ℓ_q}` built according to
Definition 1, `‖M_{k,χ}(λ) − U(λ)‖ ∈ O(λ^{2(k+χ)+1})` as `λ → 0`.

The source proof reduces the claim to the moment system (the matrix equation
with rows `ℓ_q^{-2χ-2j}`, `j < k`, already formalized from the frozen
`multiproductMoment` identity in `Qatlib.Papers.HamLCUSim12.TaylorBounds.MomentBridge`): if each node
word `W_q(λ) = S_χ(λ/ℓ_q)^{ℓ_q}` differs from the evolution by the
node-uniform defect polynomial with terms
`λ^{2χ+1+2j} / ℓ_q^{2χ+2j} • D_j`, then all error terms up to order `2(k+χ)-1` cancel in
`Σ_q C_q W_q(λ) − U(λ)`, leaving order `2(k+χ)+1`.

This module proves exactly that cancellation step for abstract node words in
any real normed space: given the moment rows and the defect expansion with a
remainder of order `2(k+χ)+1`, the multi-product defect obeys the printed
order with constant `‖C‖₁ · B`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Node-uniform defect expansion of the symmetric order-`2χ` integrator words:
each word `W q lam` at node `ℓ q` differs from the evolution `U lam` by the explicit
polynomial `Σ_j lam^{2χ+1+2j} / (ℓ q)^{2χ+2j} • D j` with common coefficients
`D j`, up to a remainder bounded by `B lam^{2(k+χ)+1}`. -/
def NodeDefects (k χ : ℕ) (ℓ : Fin (k + 1) → ℝ) (U : ℝ → E)
    (W : Fin (k + 1) → ℝ → E) (D : ℕ → E)
    (B t₀ : ℝ) : Prop :=
  0 < t₀ ∧ ∀ (q : Fin (k + 1)) (lam : ℝ), lam ∈ Set.Ico 0 t₀ →
    ‖W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
        (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ))‖ ≤
      B * lam ^ (2 * (χ + k) + 1)

/-- Lemma 4, Eq. (18) — the order boost: if the coefficients `C` satisfy the
moment system of order `χ` (`Σ_q C_q = 1` and `Σ_q C_q / ℓ_q^{2χ+2j} = 0` for
`j < k`) and each node word has the node-uniform defect expansion
`NodeDefects`, then the multiproduct `Σ_q C_q • W_q(lam)` approximates `U(lam)`
to order `2(k+χ)+1` with constant `‖C‖₁ · B`. -/
theorem multiproduct_order_at (k χ : ℕ) (C : Fin (k + 1) → ℝ) (ℓ : Fin (k + 1) → ℝ)
    (hmom₁ : ∑ q, C q = 1)
    (hmom : ∀ j : ℕ, j < k → (∑ q, C q / ℓ q ^ (2 * χ + 2 * j)) = 0)
    (U : ℝ → E) (W : Fin (k + 1) → ℝ → E) (D : ℕ → E) (B lam : ℝ)
    (hd : ∀ q : Fin (k + 1),
      ‖W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
        (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ))‖ ≤
        B * lam ^ (2 * (χ + k) + 1)) :
    ‖(∑ q, C q • W q lam) - U lam‖ ≤ (∑ q, |C q|) * B * lam ^ (2 * (χ + k) + 1) := by
  have hddef : ∀ q : Fin (k + 1), ‖W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
        (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ))‖ ≤
        B * lam ^ (2 * (χ + k) + 1) := hd
  have hU : U lam = ∑ q, C q • U lam := by
    rw [← Finset.sum_smul, hmom₁, one_smul]
  have hsplit : (∑ q, C q • W q lam) - U lam = ∑ q, C q • (W q lam - U lam) := by
    conv_lhs => rw [hU]
    rw [← Finset.sum_sub_distrib]
    simp only [smul_sub]
  have hzero : (∑ q, C q • ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
      (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ))) = 0 := by
    have hterm : ∀ q : Fin (k + 1),
        C q • ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
          (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ)) =
        ∑ j : Fin k, ((C q / ℓ q ^ (2 * χ + 2 * (j : ℕ))) *
          lam ^ (2 * χ + 1 + 2 * (j : ℕ))) • (D (j : ℕ)) := by
      intro q
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]; congr 1; ring
    rw [Finset.sum_congr rfl fun q _ => hterm q]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul, ← Finset.sum_mul,
      hmom (j : ℕ) j.isLt, zero_mul, zero_smul]
  rw [hsplit]
  have hdecomp : ∀ q : Fin (k + 1),
      C q • (W q lam - U lam) =
      C q • (W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
        (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ))) +
      C q • ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
        (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ)) := by
    intro q
    rw [← smul_add, sub_add_cancel]
  rw [Finset.sum_congr rfl fun q _ => hdecomp q, Finset.sum_add_distrib, hzero,
    add_zero]
  calc ‖∑ q, C q • (W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
        (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ)))‖
      ≤ ∑ q, ‖C q • (W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
          (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ)))‖ := norm_sum_le _ _
    _ ≤ ∑ q, |C q| * (B * lam ^ (2 * (χ + k) + 1)) := by
        refine Finset.sum_le_sum fun q _ => ?_
        have hq := hddef q
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hq (abs_nonneg (C q))
    _ = (∑ q, |C q|) * (B * lam ^ (2 * (χ + k) + 1)) := (Finset.sum_mul _ _ _).symm
    _ = (∑ q, |C q|) * B * lam ^ (2 * (χ + k) + 1) := (mul_assoc _ _ _).symm

/-- Bundled form of `multiproduct_order_at` on the interval `Ico 0 t₀`. -/
theorem multiproduct_order (k χ : ℕ) (C : Fin (k + 1) → ℝ) (ℓ : Fin (k + 1) → ℝ)
    (hmom₁ : ∑ q, C q = 1)
    (hmom : ∀ j : ℕ, j < k → (∑ q, C q / ℓ q ^ (2 * χ + 2 * j)) = 0)
    (U : ℝ → E) (W : Fin (k + 1) → ℝ → E) (D : ℕ → E) (B t₀ : ℝ)
    (hd : NodeDefects k χ ℓ U W D B t₀) (lam : ℝ) (hlam : lam ∈ Set.Ico 0 t₀) :
    ‖(∑ q, C q • W q lam) - U lam‖ ≤ (∑ q, |C q|) * B * lam ^ (2 * (χ + k) + 1) :=
  multiproduct_order_at k χ C ℓ hmom₁ hmom U W D B lam (hd.2 · lam hlam)

end Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder
