/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic
public import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
public import Qatlib.Papers.TrotterError19.MainResults.SourceModel

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Matrix Filter Asymptotics
open scoped Matrix.Norms.L2Operator BigOperators ContDiff Topology

open Qatlib.Papers.TrotterError19.MainResults

namespace Qatlib.Papers.TrotterError19.MainResults.Appendices

section

/-- **Lemma B.1, Eq. (172), first sentence** (arXiv:1912.08854v3, p. 47):
a continuous operator-valued function satisfies the order condition
`F(τ) = O(1)` near zero. -/
theorem lemmaB1_continuous_orderCondition {E : Type*} [NormedAddCommGroup E]
    (F : ℝ → E) (hF : Continuous F) : OrderCondition F 0 := by
  have hbdd : ∀ᶠ τ in 𝓝 (0 : ℝ), ‖F τ‖ ≤ ‖F 0‖ + 1 := by
    have hball : ∀ᶠ τ in 𝓝 (0 : ℝ), F τ ∈ Metric.ball (F 0) 1 :=
      hF.continuousAt (Metric.ball_mem_nhds _ zero_lt_one)
    filter_upwards [hball] with τ hτ
    have hdist : dist (F τ) (F 0) < 1 := Metric.mem_ball.mp hτ
    rw [dist_eq_norm] at hdist
    calc ‖F τ‖ = ‖F 0 + (F τ - F 0)‖ := by congr 1; abel
      _ ≤ ‖F 0‖ + ‖F τ - F 0‖ := norm_add_le _ _
      _ ≤ ‖F 0‖ + 1 := by linarith
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp hbdd
  refine ⟨‖F 0‖ + 1, δ / 2, by positivity, by positivity, ?_⟩
  intro t ht
  have hmem : t ∈ Metric.ball (0 : ℝ) δ := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith [abs_nonneg t]
  simpa using hδb hmem

/-- **Lemma B.1, Eq. (172), equivalence** (arXiv:1912.08854v3, p. 47):
for a smooth matrix-valued function, `F = O(τ^p)` iff
`F(0) = F'(0) = ⋯ = F^{(p-1)}(0) = 0`.

Reuses the frozen FQN
`Qatlib.Concepts.TrotterFormula.GeneralOrder.trotter_matrix_order_jets`.
The paper assumes `p` continuous derivatives; the frozen theorem (and hence
this bridge) assumes `C^∞`, which covers every function appearing in the paper
(products of matrix exponentials and their derivatives). -/
theorem lemmaB1_derivative_condition {I : Type} [Fintype I] [DecidableEq I]
    (F : ℝ → Matrix I I ℂ) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    OrderCondition F p ↔ ∀ j : ℕ, j < p → iteratedDeriv j F 0 = 0 :=
  Qatlib.Concepts.TrotterFormula.GeneralOrder.trotter_matrix_order_jets F p hF

/-- The nested integral of Lemma B.2 / Eq. (177): `dτ₁ ⋯ dτ_Γ`, each inner
variable running from `0` to the next outer variable, of the monomial
`τ₁^{p₁} ⋯ τ_Γ^{p_Γ}`.  The list `ps` holds `p₁, …, p_Γ` in that order. -/
noncomputable def nestedMonomial : List ℕ → ℝ → ℝ
  | [], _ => 1
  | p :: ps, t => ∫ s in (0 : ℝ)..t, s ^ p * nestedMonomial ps s

/-- The constant `c` of Eq. (178), computed by the induction of the proof:
`c(p :: ps) = c(ps) / (p + Σps + |ps| + 1)`. -/
noncomputable def monomialConstant : List ℕ → ℝ
  | [] => 1
  | p :: ps => monomialConstant ps / ((p : ℝ) + ((ps.sum : ℝ) + (ps.length : ℝ)) + 1)

/-- **Lemma B.2, Eq. (178)** (arXiv:1912.08854v3, p. 48): the nested monomial
integral evaluates to `c · t^{p₁+⋯+p_Γ+Γ}` with the explicit constant
`monomialConstant ps`. -/
theorem lemmaB2_nestedMonomial_eq (ps : List ℕ) (t : ℝ) :
    nestedMonomial ps t = monomialConstant ps * t ^ (ps.sum + ps.length) := by
  induction ps generalizing t with
  | nil => simp [nestedMonomial, monomialConstant]
  | cons p ps ih =>
    simp only [nestedMonomial]
    have hfun : (fun s : ℝ => s ^ p * nestedMonomial ps s)
        = fun s : ℝ => monomialConstant ps * s ^ (p + (ps.sum + ps.length)) := by
      funext s
      rw [ih s]
      have : s ^ p * (monomialConstant ps * s ^ (ps.sum + ps.length))
          = monomialConstant ps * (s ^ p * s ^ (ps.sum + ps.length)) := by ring
      rw [this, ← pow_add]
    rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
    simp only [monomialConstant, List.sum_cons, List.length_cons]
    push_cast
    have hden : ((p : ℝ) + ((ps.sum : ℝ) + (ps.length : ℝ)) + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- **Lemma B.2, Eq. (178), order form**: the integral is `O(t^{Σp+Γ})`,
with a nonnegative constant. -/
theorem lemmaB2_monomial_order (ps : List ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t : ℝ,
      nestedMonomial ps t = c * t ^ (ps.sum + ps.length) ∧
      ‖nestedMonomial ps t‖ ≤ c * |t| ^ (ps.sum + ps.length) := by
  refine ⟨monomialConstant ps, ?_, fun t => ⟨lemmaB2_nestedMonomial_eq ps t, ?_⟩⟩
  · induction ps with
    | nil => simp [monomialConstant]
    | cons p ps ih =>
      simp only [monomialConstant]
      exact div_nonneg ih (by positivity)
  · rw [lemmaB2_nestedMonomial_eq]
    have hc : 0 ≤ monomialConstant ps := by
      induction ps with
      | nil => simp [monomialConstant]
      | cons p ps ih =>
        simp only [monomialConstant]
        exact div_nonneg ih (by positivity)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc, Real.norm_eq_abs,
      abs_pow]

/-- **Proposition B.3, rule 1 (Addition)** (arXiv:1912.08854v3, p. 49):
`F = O(τ^p)` and `G = O(τ^q)` imply `F + G = O(τ^{min p q})`. -/
theorem propB3_addition {E : Type*} [NormedAddCommGroup E]
    (F G : ℝ → E) (p q : ℕ)
    (hF : OrderCondition F p) (hG : OrderCondition G q) :
    OrderCondition (fun τ => F τ + G τ) (min p q) := by
  obtain ⟨cF, tF, hcF, htF, hF⟩ := hF
  obtain ⟨cG, tG, hcG, htG, hG⟩ := hG
  refine ⟨cF + cG, min tF (min tG 1), by positivity, lt_min htF (lt_min htG one_pos), ?_⟩
  intro t ht
  have htF' : |t| ≤ tF := (le_min_iff.mp ht).1
  have htG' : |t| ≤ tG := (le_min_iff.mp (le_min_iff.mp ht).2).1
  have ht1 : |t| ≤ 1 := (le_min_iff.mp (le_min_iff.mp ht).2).2
  have ha : |t| ^ p ≤ |t| ^ min p q :=
    pow_le_pow_of_le_one (abs_nonneg t) ht1 (min_le_left p q)
  have hb : |t| ^ q ≤ |t| ^ min p q :=
    pow_le_pow_of_le_one (abs_nonneg t) ht1 (min_le_right p q)
  calc ‖F t + G t‖ ≤ ‖F t‖ + ‖G t‖ := norm_add_le _ _
    _ ≤ cF * |t| ^ p + cG * |t| ^ q := add_le_add (hF t htF') (hG t htG')
    _ ≤ cF * |t| ^ min p q + cG * |t| ^ min p q :=
        add_le_add (mul_le_mul_of_nonneg_left ha hcF.le) (mul_le_mul_of_nonneg_left hb hcG.le)
    _ = (cF + cG) * |t| ^ min p q := by ring

/-- **Proposition B.3, rule 2 (Multiplication)** (arXiv:1912.08854v3, p. 49):
`F = O(τ^p)` and `G = O(τ^q)` imply `F·G = O(τ^{p+q})`. -/
theorem propB3_multiplication {E : Type*} [NormedRing E]
    (F G : ℝ → E) (p q : ℕ)
    (hF : OrderCondition F p) (hG : OrderCondition G q) :
    OrderCondition (fun τ => F τ * G τ) (p + q) := by
  obtain ⟨cF, tF, hcF, htF, hF⟩ := hF
  obtain ⟨cG, tG, hcG, htG, hG⟩ := hG
  refine ⟨cF * cG, min tF tG, mul_pos hcF hcG, lt_min htF htG, ?_⟩
  intro t ht
  have htF' : |t| ≤ tF := (le_min_iff.mp ht).1
  have htG' : |t| ≤ tG := (le_min_iff.mp ht).2
  calc ‖F t * G t‖ ≤ ‖F t‖ * ‖G t‖ := norm_mul_le _ _
    _ ≤ (cF * |t| ^ p) * (cG * |t| ^ q) :=
        mul_le_mul (hF t htF') (hG t htG') (norm_nonneg _) (by positivity)
    _ = (cF * cG) * |t| ^ (p + q) := by
        rw [pow_add]; ring

end

end Qatlib.Papers.TrotterError19.MainResults.Appendices
