/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.CostModel.CostAsymptotics

set_option backward.isDefEq.respectTransparency false

/-!
# Exponential rate vocabulary in the level index

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

Proposition 2 (p. 13) describes the exponents `α`, `β`, `γ` of the level model as
`α = r − o(1)`, `β = r − o(1)`, `γ = 1`, where `r` is the strong order of the scheme.
The two definitions below are the formal counterparts of "decays at rate `p` in the level
index" (`ExpRate`) and "grows at rate `p`" (`GrowthRate`).

The main lemma `ExpRate_of_forall_mul_div` converts the paper's `m`-parametrised family
of bounds (4.10), `E|P(X̂_n) − P(X_T)| ≤ O(h^r) + O(h^α) + O(h^{m(r−α)})` for every `m`,
into the `r − o(1)` formulation: rate `r·m/(m+1)` for every `m` gives rate `r − δ` for
every `δ > 0`.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- `2 ^ t` for a real exponent. -/
def twoPow (t : ℝ) : ℝ := (2 : ℝ) ^ t

/-- The real power `twoPow t` is positive. -/
theorem twoPow_pos (t : ℝ) : 0 < twoPow t := Real.rpow_pos_of_pos (by norm_num) t

/-- `ExpRate p f`: `f` decays at least like `2^{-p l}` as the level index grows. -/
def ExpRate (p : ℝ) (f : ℕ → ℝ) : Prop :=
  f =O[atTop] fun l : ℕ => twoPow (-p * (l : ℝ))

/-- `GrowthRate p f`: `f` grows at most like `2^{p l}` as the level index grows. -/
def GrowthRate (p : ℝ) (f : ℕ → ℝ) : Prop :=
  f =O[atTop] fun l : ℕ => twoPow (p * (l : ℝ))

/-- A numerically smaller exponent gives a weaker `ExpRate` statement. -/
theorem ExpRate_mono {p p' : ℝ} {f : ℕ → ℝ} (h : ExpRate p f) (hpp : p' ≤ p) :
    ExpRate p' f := by
  unfold ExpRate at h ⊢
  refine h.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (0 : ℕ)] with l hl
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (twoPow_pos _).le, abs_of_nonneg (twoPow_pos _).le]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

/-- A numerically larger exponent gives a weaker `GrowthRate` statement. -/
theorem GrowthRate_mono {p p' : ℝ} {f : ℕ → ℝ} (h : GrowthRate p f) (hpp : p ≤ p') :
    GrowthRate p' f := by
  unfold GrowthRate at h ⊢
  refine h.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (0 : ℕ)] with l hl
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (twoPow_pos _).le, abs_of_nonneg (twoPow_pos _).le]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

/-- `γ = 1`: the per-level cost of a scheme with `2^l` time steps at level `l` grows
at rate one (Proposition 2, the paragraph after the statement). -/
theorem growthRate_twoPow : GrowthRate 1 (fun l : ℕ => twoPow (l : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with l
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (twoPow_pos _).le, abs_of_nonneg (twoPow_pos _).le, one_mul]

/-- The `o(1)` conversion of Proposition 2: if the bias bound (4.10) is available with
rate `p·m/(m+1)` for every `m ≥ 1`, then it is available with rate `p − δ` for every
`δ > 0`. -/
theorem ExpRate_of_forall_mul_div {p : ℝ} (hp : 0 < p) {f : ℕ → ℝ}
    (h : ∀ m : ℕ, 1 ≤ m → ExpRate (p * (m : ℝ) / ((m : ℝ) + 1)) f) :
    ∀ δ : ℝ, 0 < δ → ExpRate (p - δ) f := by
  intro δ hδ
  obtain ⟨m, hm⟩ := exists_nat_gt (p / δ)
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_trans (div_pos hp hδ) hm
  have hm1 : 1 ≤ m := by exact_mod_cast hmpos
  refine ExpRate_mono (h m hm1) ?_
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsmall : p / ((m : ℝ) + 1) ≤ δ := by
    rw [div_le_iff₀ hden]
    rw [div_lt_iff₀ hδ] at hm
    nlinarith
  have heq : p * (m : ℝ) / ((m : ℝ) + 1) = p - p / ((m : ℝ) + 1) := by
    field_simp
    ring
  rw [heq]
  linarith

/-- Pointwise bias and variance bounds (Proposition 2, second paragraph: the level model
of Theorem 2 under the global-Lipschitz improvement) give the exponential rates
`α = r`, `β = 2r`, `γ = 1`. -/
theorem rates_of_pointwise_bounds {r B V : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hV : 0 ≤ V)
    {bias var : ℕ → ℝ}
    (hbias : ∀ l, |bias l| ≤ B * twoPow (-r * (l : ℝ)))
    (hvar0 : ∀ l, 0 ≤ var l)
    (hvar : ∀ l, var l ≤ V * twoPow (-(2 * r) * (l : ℝ))) :
    ExpRate r bias ∧ ExpRate (2 * r) var ∧ GrowthRate 1 (fun l : ℕ => twoPow (l : ℝ)) := by
  refine ⟨?_, ?_, growthRate_twoPow⟩
  · refine IsBigO.of_bound B ?_
    filter_upwards with l
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (twoPow_pos _).le]
    exact hbias l
  · refine IsBigO.of_bound V ?_
    filter_upwards with l
    have hv : 0 ≤ var l := hvar0 l
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv,
      abs_of_nonneg (twoPow_pos _).le]
    exact hvar l

end Qatlib.Papers.MultilevelMC20.MainResults
