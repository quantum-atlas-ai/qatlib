/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Source model: the asymptotic gate-cost calculus of FermionicQFT14

Paper: S. P. Jordan, K. S. M. Lee, J. Preskill,
*Quantum Algorithms for Fermionic Quantum Field Theories*, arXiv:1404.7115v1 (2014),
§2.3 "Complexity", Eqs. (13)–(20), p. 7.

The paper's total gate count is built from three pieces:

* two adiabatic state-preparation steps, each with gate count `(L³/(a⁶ m³ ε))^{1+o(1)}`
  (Eqs. (16) and (18), following from the adiabatic durations Eq. (14)/(17));
* the wavepacket excitation step `G_excite = ε^{-4-o(1)}` (ε → 0) and
  `p^{3+o(1)}` (p → ∞) (Eq. (19));
* in the high-precision limit, a further `1/ε` postselection factor for the two
  successful wavepacket excitations (§2.3, sentence following Eq. (19)).

Substituting `a ∼ ε` (high-precision limit) or `a ∼ 1/p`, `L ∼ p` (high-momentum
limit) into the preparation base gives the two branches of Eq. (20):
`O(ε^{-8-o(1)})` and `O(p^{9+o(1)})`.

This file fixes the cost calculus used to state that derivation precisely:

* `HasUpperBoundAtZero f e` — `f = O(x ^ (-(e + o(1))))` as `x → 0⁺`;
* `HasUpperBoundAtTop f e` — `f = O(x ^ (e + o(1)))` as `x → ∞`;
* `VanishesAtZero`/`VanishesAtTop` — the `o(1)` exponent function;
* the concrete cost model `prepBase`, `highPrecision*GateCount`,
  `highMomentum*GateCount`.

Every lemma in this file is proved; the claim-level theorems live in
`TotalGateCount.lean` (c001) and `ScatteringAlgorithm.lean` (c002).
-/

namespace Qatlib.Papers.FermionicQFT14.MainResults

set_option autoImplicit false

noncomputable section

/-! ## 1. Asymptotic upper bounds with a slack exponent -/

/-- `f = O(x ^ (-(e + o(1))))` as `x → 0⁺`: for every `δ > 0` there is a constant
`C ≥ 0` and a threshold `x₁ > 0` with `|f x| ≤ C * x ^ (-(e + δ))` for all
`0 < x ≤ x₁`. This is the formal reading of the paper's `x^{-e-o(1)}`
(§2.3, Eqs. (16), (18), (19)) as an upper bound with a vanishing exponent slack. -/
def HasUpperBoundAtZero (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∃ x₁ : ℝ, 0 < x₁ ∧
    ∀ x : ℝ, 0 < x → x ≤ x₁ → |f x| ≤ C * x ^ (-(e + δ))

/-- `f = O(x ^ (e + o(1)))` as `x → ∞`: for every `δ > 0` there is a constant
`C ≥ 0` and a threshold `x₁` with `|f x| ≤ C * x ^ (e + δ)` for all `x ≥ x₁`.
This is the formal reading of the paper's `p^{e+o(1)}`
(§2.3, Eq. (19) and Eq. (20) high-momentum branch). -/
def HasUpperBoundAtTop (f : ℝ → ℝ) (e : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∃ x₁ : ℝ, 1 ≤ x₁ ∧
    ∀ x : ℝ, x₁ ≤ x → |f x| ≤ C * x ^ (e + δ)

/-- `η = o(1)` as `x → 0⁺`: the exponent slack of the paper's
`(·)^{1+o(1)}` and `x^{-4-o(1)}` factors near the high-precision limit. -/
def VanishesAtZero (η : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ x₀ : ℝ, 0 < x₀ ∧
    ∀ x : ℝ, 0 < x → x ≤ x₀ → |η x| ≤ δ

/-- `η = o(1)` as `x → ∞`: the exponent slack in the high-momentum limit. -/
def VanishesAtTop (η : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ x₀ : ℝ, 1 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → |η x| ≤ δ

/-! ## 2. Monomial bounds -/

/-- A nonnegative constant multiple of `x ^ (-e)` is `O(x ^ (-e-o(1)))` at zero. -/
theorem hasUpperBoundAtZero_monomial (c e : ℝ) (hc : 0 ≤ c) :
    HasUpperBoundAtZero (fun x : ℝ => c * x ^ (-e)) e := by
  intro δ hδ
  refine ⟨c, hc, 1, one_pos, ?_⟩
  intro x hx0 hx1
  have hx0' : (0 : ℝ) ≤ x := le_of_lt hx0
  have hpow : x ^ (-e) ≤ x ^ (-(e + δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have hval : c * x ^ (-e) ≤ c * x ^ (-(e + δ)) :=
    mul_le_mul_of_nonneg_left hpow hc
  rw [abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hx0' _))]
  exact hval

/-- A nonnegative constant multiple of `x ^ e` is `O(x ^ (e+o(1)))` at infinity. -/
theorem hasUpperBoundAtTop_monomial (c e : ℝ) (hc : 0 ≤ c) :
    HasUpperBoundAtTop (fun x : ℝ => c * x ^ e) e := by
  intro δ hδ
  refine ⟨c, hc, 1, by norm_num, ?_⟩
  intro x hx1
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hpow : x ^ e ≤ x ^ (e + δ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  rw [abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hx0 _))]
  exact mul_le_mul_of_nonneg_left hpow hc

/-! ## 3. Closure of the cost calculus -/

/-- Monotonicity of the zero-limit bound in its exponent: a bound with exponent
`e₁` implies the bound with any larger exponent `e₂ ≥ e₁`, since near zero the
function `x ↦ x ^ (-(e+δ))` is decreasing in `e`. -/
theorem hasUpperBoundAtZero_mono {f : ℝ → ℝ} {e₁ e₂ : ℝ}
    (h : HasUpperBoundAtZero f e₁) (he : e₁ ≤ e₂) :
    HasUpperBoundAtZero f e₂ := by
  intro δ hδ
  obtain ⟨C, hC, x₁, hx₁, hb⟩ := h δ hδ
  refine ⟨C, hC, min x₁ 1, lt_min hx₁ one_pos, fun x hx0 hx1 => ?_⟩
  have hx1' : x ≤ x₁ := le_trans hx1 (min_le_left _ _)
  have hxle1 : x ≤ 1 := le_trans hx1 (min_le_right _ _)
  refine (hb x hx0 hx1').trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact Real.rpow_le_rpow_of_exponent_ge hx0 hxle1 (by linarith)

/-- Monotonicity of the infinity-limit bound in its exponent. -/
theorem hasUpperBoundAtTop_mono {f : ℝ → ℝ} {e₁ e₂ : ℝ}
    (h : HasUpperBoundAtTop f e₁) (he : e₁ ≤ e₂) :
    HasUpperBoundAtTop f e₂ := by
  intro δ hδ
  obtain ⟨C, hC, x₁, hx₁, hb⟩ := h δ hδ
  refine ⟨C, hC, max x₁ 1, le_max_right _ _, fun x hx1 => ?_⟩
  have hx1' : x₁ ≤ x := le_trans (le_max_left _ _) hx1
  have hxge1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx1
  refine (hb x hx1').trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact Real.rpow_le_rpow_of_exponent_le hxge1 (by linarith)

/-- Products add exponents: the gate counts of independent algorithmic steps
multiply, so does the slack. -/
theorem hasUpperBoundAtZero_mul {f g : ℝ → ℝ} {e₁ e₂ : ℝ}
    (hf : HasUpperBoundAtZero f e₁) (hg : HasUpperBoundAtZero g e₂) :
    HasUpperBoundAtZero (fun x => f x * g x) (e₁ + e₂) := by
  intro δ hδ
  obtain ⟨Cf, hCf, xf, hxf, hbf⟩ := hf (δ / 2) (by linarith)
  obtain ⟨Cg, hCg, xg, hxg, hbg⟩ := hg (δ / 2) (by linarith)
  refine ⟨Cf * Cg, mul_nonneg hCf hCg, min xf xg, lt_min hxf hxg, fun x hx0 hx1 => ?_⟩
  have hx0' : (0 : ℝ) ≤ x := le_of_lt hx0
  have hxf' : x ≤ xf := le_trans hx1 (min_le_left _ _)
  have hxg' : x ≤ xg := le_trans hx1 (min_le_right _ _)
  have hprod : |f x * g x|
      ≤ (Cf * x ^ (-(e₁ + δ / 2))) * (Cg * x ^ (-(e₂ + δ / 2))) := by
    rw [abs_mul]
    exact mul_le_mul (hbf x hx0 hxf') (hbg x hx0 hxg') (abs_nonneg _)
      (mul_nonneg hCf (Real.rpow_nonneg hx0' _))
  have heq : (Cf * x ^ (-(e₁ + δ / 2))) * (Cg * x ^ (-(e₂ + δ / 2)))
      = (Cf * Cg) * x ^ (-(e₁ + e₂ + δ)) := by
    rw [show -(e₁ + e₂ + δ) = (-(e₁ + δ / 2)) + (-(e₂ + δ / 2)) by ring]
    rw [Real.rpow_add hx0]
    ring
  exact hprod.trans_eq heq

/-- Products add exponents at infinity. -/
theorem hasUpperBoundAtTop_mul {f g : ℝ → ℝ} {e₁ e₂ : ℝ}
    (hf : HasUpperBoundAtTop f e₁) (hg : HasUpperBoundAtTop g e₂) :
    HasUpperBoundAtTop (fun x => f x * g x) (e₁ + e₂) := by
  intro δ hδ
  obtain ⟨Cf, hCf, xf, hxf, hbf⟩ := hf (δ / 2) (by linarith)
  obtain ⟨Cg, hCg, xg, hxg, hbg⟩ := hg (δ / 2) (by linarith)
  refine ⟨Cf * Cg, mul_nonneg hCf hCg, max xf xg,
    le_trans hxf (le_max_left _ _), fun x hx1 => ?_⟩
  have h1max : (1 : ℝ) ≤ max xf xg := le_trans hxf (le_max_left _ _)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos (le_trans h1max hx1)
  have hxf' : xf ≤ x := le_trans (le_max_left _ _) hx1
  have hxg' : xg ≤ x := le_trans (le_max_right _ _) hx1
  have hprod : |f x * g x|
      ≤ (Cf * x ^ (e₁ + δ / 2)) * (Cg * x ^ (e₂ + δ / 2)) := by
    rw [abs_mul]
    exact mul_le_mul (hbf x hxf') (hbg x hxg') (abs_nonneg _)
      (mul_nonneg hCf (Real.rpow_nonneg (le_of_lt hx0) _))
  have heq : (Cf * x ^ (e₁ + δ / 2)) * (Cg * x ^ (e₂ + δ / 2))
      = (Cf * Cg) * x ^ (e₁ + e₂ + δ) := by
    rw [show e₁ + e₂ + δ = (e₁ + δ / 2) + (e₂ + δ / 2) by ring]
    conv_rhs => rw [Real.rpow_add hx0]
    ring
  exact hprod.trans_eq heq

/-- Sums take the larger exponent: adding two gate counts costs the dominant
(asymptotically larger) one. -/
theorem hasUpperBoundAtZero_add {f g : ℝ → ℝ} {e₁ e₂ : ℝ}
    (hf : HasUpperBoundAtZero f e₁) (hg : HasUpperBoundAtZero g e₂) :
    HasUpperBoundAtZero (fun x => f x + g x) (max e₁ e₂) := by
  intro δ hδ
  obtain ⟨Cf, hCf, xf, hxf, hbf⟩ :=
    hasUpperBoundAtZero_mono hf (le_max_left e₁ e₂) δ hδ
  obtain ⟨Cg, hCg, xg, hxg, hbg⟩ :=
    hasUpperBoundAtZero_mono hg (le_max_right e₁ e₂) δ hδ
  refine ⟨Cf + Cg, add_nonneg hCf hCg, min xf xg, lt_min hxf hxg, fun x hx0 hx1 => ?_⟩
  have hxf' : x ≤ xf := le_trans hx1 (min_le_left _ _)
  have hxg' : x ≤ xg := le_trans hx1 (min_le_right _ _)
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ Cf * x ^ (-(max e₁ e₂ + δ)) + Cg * x ^ (-(max e₁ e₂ + δ)) :=
        add_le_add (hbf x hx0 hxf') (hbg x hx0 hxg')
    _ = (Cf + Cg) * x ^ (-(max e₁ e₂ + δ)) := by ring

/-- Sums take the larger exponent at infinity. -/
theorem hasUpperBoundAtTop_add {f g : ℝ → ℝ} {e₁ e₂ : ℝ}
    (hf : HasUpperBoundAtTop f e₁) (hg : HasUpperBoundAtTop g e₂) :
    HasUpperBoundAtTop (fun x => f x + g x) (max e₁ e₂) := by
  intro δ hδ
  obtain ⟨Cf, hCf, xf, hxf, hbf⟩ :=
    hasUpperBoundAtTop_mono hf (le_max_left e₁ e₂) δ hδ
  obtain ⟨Cg, hCg, xg, hxg, hbg⟩ :=
    hasUpperBoundAtTop_mono hg (le_max_right e₁ e₂) δ hδ
  refine ⟨Cf + Cg, add_nonneg hCf hCg, max xf xg,
    le_trans hxf (le_max_left _ _), fun x hx1 => ?_⟩
  have hxf' : xf ≤ x := le_trans (le_max_left _ _) hx1
  have hxg' : xg ≤ x := le_trans (le_max_right _ _) hx1
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ Cf * x ^ (max e₁ e₂ + δ) + Cg * x ^ (max e₁ e₂ + δ) :=
        add_le_add (hbf x hxf') (hbg x hxg')
    _ = (Cf + Cg) * x ^ (max e₁ e₂ + δ) := by ring

/-- Multiplying by a constant preserves the zero-limit bound. -/
theorem hasUpperBoundAtZero_const_mul (c : ℝ) {f : ℝ → ℝ} {e : ℝ}
    (hf : HasUpperBoundAtZero f e) :
    HasUpperBoundAtZero (fun x => c * f x) e := by
  intro δ hδ
  obtain ⟨C, hC, x₁, hx₁, hb⟩ := hf δ hδ
  refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, x₁, hx₁, fun x hx0 hx1 => ?_⟩
  rw [abs_mul]
  calc |c| * |f x| ≤ |c| * (C * x ^ (-(e + δ))) :=
        mul_le_mul_of_nonneg_left (hb x hx0 hx1) (abs_nonneg c)
    _ = (|c| * C) * x ^ (-(e + δ)) := by ring

/-- Multiplying by a constant preserves the infinity-limit bound. -/
theorem hasUpperBoundAtTop_const_mul (c : ℝ) {f : ℝ → ℝ} {e : ℝ}
    (hf : HasUpperBoundAtTop f e) :
    HasUpperBoundAtTop (fun x => c * f x) e := by
  intro δ hδ
  obtain ⟨C, hC, x₁, hx₁, hb⟩ := hf δ hδ
  refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, x₁, hx₁, fun x hx1 => ?_⟩
  rw [abs_mul]
  calc |c| * |f x| ≤ |c| * (C * x ^ (e + δ)) :=
        mul_le_mul_of_nonneg_left (hb x hx1) (abs_nonneg c)
    _ = (|c| * C) * x ^ (e + δ) := by ring

/-- `x ↦ x⁻¹` is `O(x^{-1})` at zero (the postselection factor `1/ε` of §2.3). -/
theorem hasUpperBoundAtZero_inv : HasUpperBoundAtZero (fun x : ℝ => x⁻¹) 1 := by
  intro δ hδ
  refine ⟨1, by norm_num, 1, one_pos, fun x hx0 hx1 => ?_⟩
  have hpow : x ^ (-(1 : ℝ)) ≤ x ^ (-(1 + δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have h1 : x ^ (-(1 : ℝ)) = x⁻¹ := Real.rpow_neg_one x
  rw [abs_of_nonneg (le_of_lt (inv_pos.mpr hx0)), ← h1]
  simpa using hpow

/-! ## 4. Variable-exponent (o(1)) slack -/

/-- Scalar core of the `(1 + o(1))` exponent: for `c ≥ 0`, `|η| ≤ 1` and
`η ≤ δ`, the power `c ^ (1 + η)` is dominated by `max c 1 ^ (1 + δ)`. -/
theorem rpow_one_add_le_max {c η δ : ℝ} (hc : 0 ≤ c) (hη1 : |η| ≤ 1)
    (hηδ : η ≤ δ) : c ^ (1 + η) ≤ max c 1 ^ (1 + δ) := by
  rcases le_or_gt 1 c with hc1 | hc1
  · calc c ^ (1 + η) ≤ c ^ (1 + δ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
      _ = max c 1 ^ (1 + δ) := by rw [max_eq_left hc1]
  · have hcle : c ≤ 1 := le_of_lt hc1
    have hmax : max c 1 = 1 := max_eq_right hcle
    have h1η : 0 ≤ 1 + η := by
      have := (abs_le.mp hη1).1
      linarith
    calc c ^ (1 + η) ≤ 1 := Real.rpow_le_one hc hcle h1η
      _ = max c 1 ^ (1 + δ) := by rw [hmax]; simp

/-- If `B x = c * x ^ (-e)` with `c ≥ 0` and the exponent perturbation `η` is
`o(1)` at zero, then `x ↦ (B x) ^ (1 + η x)` is `O(x ^ (-e-o(1)))` at zero.
This is the formal content of the paper's `(·)^{1+o(1)}` in Eqs. (16)/(18):
the `o(1)` in the exponent only raises the effective exponent by an arbitrary
`δ`. -/
theorem hasUpperBoundAtZero_rpow_one_add_slack {c e : ℝ} (hc : 0 ≤ c)
    {η : ℝ → ℝ} (hη : VanishesAtZero η) :
    HasUpperBoundAtZero (fun x => (c * x ^ (-e)) ^ (1 + η x)) e := by
  intro δ hδ
  let δ' : ℝ := min 1 (δ / (2 * (|e| + 1)))
  have hδ'pos : 0 < δ' := lt_min one_pos (by positivity)
  have hδ'le1 : δ' ≤ 1 := min_le_left _ _
  have hδ'le : δ' ≤ δ / (2 * (|e| + 1)) := min_le_right _ _
  have hden : (0 : ℝ) < 2 * (|e| + 1) := by positivity
  have hδ'δ : δ' ≤ δ :=
    le_trans hδ'le (div_le_self (le_of_lt hδ) (by nlinarith [abs_nonneg e]))
  have hfac : |e| * δ' ≤ δ := by
    calc |e| * δ' ≤ |e| * (δ / (2 * (|e| + 1))) :=
          mul_le_mul_of_nonneg_left hδ'le (abs_nonneg e)
      _ = (|e| / (|e| + 1)) * (δ / 2) := by
          field_simp
      _ ≤ 1 * (δ / 2) := by
          apply mul_le_mul_of_nonneg_right
          · rw [div_le_one (by positivity)]
            linarith
          · positivity
      _ ≤ δ := by linarith
  obtain ⟨x₀, hx₀, hηb⟩ := hη δ' hδ'pos
  refine ⟨max c 1 ^ (1 + δ'), by positivity, min x₀ 1, lt_min hx₀ one_pos,
    fun x hx0 hx1 => ?_⟩
  have hx0' : (0 : ℝ) ≤ x := le_of_lt hx0
  have hxx₀ : x ≤ x₀ := le_trans hx1 (min_le_left _ _)
  have hx1' : x ≤ 1 := le_trans hx1 (min_le_right _ _)
  have hηx : |η x| ≤ δ' := hηb x hx0 hxx₀
  have hηx1 : |η x| ≤ 1 := le_trans hηx hδ'le1
  have heη : e * η x ≤ δ := by
    have h1 : e * η x ≤ |e * η x| := le_abs_self _
    have h2 : |e * η x| = |e| * |η x| := abs_mul e (η x)
    have h3 : |e| * |η x| ≤ |e| * δ' :=
      mul_le_mul_of_nonneg_left hηx (abs_nonneg e)
    linarith
  have hmain : (c * x ^ (-e)) ^ (1 + η x)
      = c ^ (1 + η x) * x ^ (-e) * x ^ (-(e * η x)) := by
    rw [Real.mul_rpow hc (Real.rpow_nonneg hx0' _)]
    rw [← Real.rpow_mul hx0' (-e) (1 + η x)]
    rw [show (-e) * (1 + η x) = -e + -(e * η x) by ring, Real.rpow_add hx0]
    ring
  have hcη : c ^ (1 + η x) ≤ max c 1 ^ (1 + δ') :=
    rpow_one_add_le_max hc hηx1 ((abs_le.mp hηx).2)
  have hxpow : x ^ (-(e * η x)) ≤ x ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1' (by linarith)
  have hnonneg : 0 ≤ (c * x ^ (-e)) ^ (1 + η x) :=
    Real.rpow_nonneg (mul_nonneg hc (Real.rpow_nonneg hx0' _)) _
  rw [abs_of_nonneg hnonneg]
  calc (c * x ^ (-e)) ^ (1 + η x)
      = c ^ (1 + η x) * x ^ (-e) * x ^ (-(e * η x)) := hmain
    _ ≤ (max c 1 ^ (1 + δ') * x ^ (-e)) * x ^ (-δ) := by
        apply mul_le_mul
        · exact mul_le_mul hcη le_rfl (Real.rpow_nonneg hx0' _)
            (Real.rpow_nonneg (le_trans hc (le_max_left c 1)) _)
        · exact hxpow
        · exact Real.rpow_nonneg hx0' _
        · exact mul_nonneg (Real.rpow_nonneg (le_trans hc (le_max_left c 1)) _)
            (Real.rpow_nonneg hx0' _)
    _ = max c 1 ^ (1 + δ') * (x ^ (-e) * x ^ (-δ)) := by ring
    _ = max c 1 ^ (1 + δ') * x ^ (-(e + δ)) := by
        rw [show -(e + δ) = -e + -δ by ring, Real.rpow_add hx0]

/-- If `B x = c * x ^ e` with `c ≥ 0` and `η = o(1)` at infinity, then
`x ↦ (B x) ^ (1 + η x)` is `O(x ^ (e+o(1)))` at infinity. This is the
counterpart of `hasUpperBoundAtZero_rpow_one_add_slack` for the high-momentum
branch of Eq. (20). -/
theorem hasUpperBoundAtTop_rpow_one_add_slack {c e : ℝ} (hc : 0 ≤ c)
    {η : ℝ → ℝ} (hη : VanishesAtTop η) :
    HasUpperBoundAtTop (fun x => (c * x ^ e) ^ (1 + η x)) e := by
  intro δ hδ
  let δ' : ℝ := min 1 (δ / (2 * (|e| + 1)))
  have hδ'pos : 0 < δ' := lt_min one_pos (by positivity)
  have hδ'le1 : δ' ≤ 1 := min_le_left _ _
  have hδ'le : δ' ≤ δ / (2 * (|e| + 1)) := min_le_right _ _
  have hδ'δ : δ' ≤ δ :=
    le_trans hδ'le (div_le_self (le_of_lt hδ) (by nlinarith [abs_nonneg e]))
  have hfac : |e| * δ' ≤ δ := by
    calc |e| * δ' ≤ |e| * (δ / (2 * (|e| + 1))) :=
          mul_le_mul_of_nonneg_left hδ'le (abs_nonneg e)
      _ = (|e| / (|e| + 1)) * (δ / 2) := by
          field_simp
      _ ≤ 1 * (δ / 2) := by
          apply mul_le_mul_of_nonneg_right
          · rw [div_le_one (by positivity)]
            linarith
          · positivity
      _ ≤ δ := by linarith
  obtain ⟨x₀, hx₀, hηb⟩ := hη δ' hδ'pos
  refine ⟨max c 1 ^ (1 + δ'), by positivity, max x₀ 1, le_max_right _ _,
    fun x hx1 => ?_⟩
  have hx₀' : x₀ ≤ x := le_trans (le_max_left _ _) hx1
  have hx1' : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx1
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1'
  have hηx : |η x| ≤ δ' := hηb x hx₀'
  have hηx1 : |η x| ≤ 1 := le_trans hηx hδ'le1
  have heη : e * η x ≤ δ := by
    have h1 : e * η x ≤ |e * η x| := le_abs_self _
    have h2 : |e * η x| = |e| * |η x| := abs_mul e (η x)
    have h3 : |e| * |η x| ≤ |e| * δ' :=
      mul_le_mul_of_nonneg_left hηx (abs_nonneg e)
    linarith
  have hmain : (c * x ^ e) ^ (1 + η x)
      = c ^ (1 + η x) * x ^ e * x ^ (e * η x) := by
    rw [Real.mul_rpow hc (Real.rpow_nonneg (le_of_lt hx0) _)]
    rw [← Real.rpow_mul (le_of_lt hx0) e (1 + η x)]
    rw [show e * (1 + η x) = e + e * η x by ring, Real.rpow_add hx0]
    ring
  have hcη : c ^ (1 + η x) ≤ max c 1 ^ (1 + δ') :=
    rpow_one_add_le_max hc hηx1 ((abs_le.mp hηx).2)
  have hxpow : x ^ (e * η x) ≤ x ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hx1' heη
  have hnonneg : 0 ≤ (c * x ^ e) ^ (1 + η x) :=
    Real.rpow_nonneg (mul_nonneg hc (Real.rpow_nonneg (le_of_lt hx0) _)) _
  rw [abs_of_nonneg hnonneg]
  calc (c * x ^ e) ^ (1 + η x)
      = c ^ (1 + η x) * x ^ e * x ^ (e * η x) := hmain
    _ ≤ (max c 1 ^ (1 + δ') * x ^ e) * x ^ δ := by
        apply mul_le_mul
        · exact mul_le_mul hcη le_rfl (Real.rpow_nonneg (le_of_lt hx0) _)
            (Real.rpow_nonneg (le_trans hc (le_max_left c 1)) _)
        · exact hxpow
        · exact Real.rpow_nonneg (le_of_lt hx0) _
        · exact mul_nonneg (Real.rpow_nonneg (le_trans hc (le_max_left c 1)) _)
            (Real.rpow_nonneg (le_of_lt hx0) _)
    _ = max c 1 ^ (1 + δ') * (x ^ e * x ^ δ) := by ring
    _ = max c 1 ^ (1 + δ') * x ^ (e + δ) := by
        rw [← Real.rpow_add hx0]

/-! ## 5. The concrete gate-count model of §2.3 -/

/-- Lattice length `L`, spacing `a`, mass `m`, precision `ε`: the parenthesized
base `L ^ 3 / (a ^ 6 * m ^ 3 * ε)` of the preparation gate count, Eq. (16)/(18)
of arXiv:1404.7115v1, obtained from the adiabatic duration Eq. (14)/(17) and the
Suzuki–Trotter expansion of §3.3. -/
noncomputable def prepBase (L a m ε : ℝ) : ℝ := L ^ 3 / (a ^ 6 * m ^ 3 * ε)

/-- Eq. (16)/(18) after the high-precision substitution `a ∼ ε`
(§2.3, Eq. (13) forces `a ∼ ε`): the base becomes `(L ^ 3 / m ^ 3) * ε ^ (-7)`. -/
noncomputable def highPrecisionPrepBase (L m ε : ℝ) : ℝ :=
  (L ^ 3 / m ^ 3) * ε ^ (-(7 : ℝ))

/-- Substitution lemma: at `a = ε` the preparation base Eq. (16)/(18) equals
`(L ^ 3 / m ^ 3) * ε ^ (-7)`, i.e. the two preparation steps contribute
`O(ε ^ (-7-o(1)))`. -/
theorem prepBase_highPrecision {L m ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    prepBase L ε m ε = highPrecisionPrepBase L m ε := by
  unfold prepBase highPrecisionPrepBase
  have hm3 : m ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hm)
  have hε7 : ε ^ 7 ≠ 0 := pow_ne_zero 7 (ne_of_gt hε)
  have hrpow : ε ^ (-(7 : ℝ)) = (ε ^ 7)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hε)]
    norm_num
  rw [hrpow]
  field_simp

/-- Substitution lemma for the high-momentum limit: with `a = 1/p` and `L = p`
(§2.3 after Eq. (19)), the preparation base becomes `(1/m³) * p^9 * ε⁻¹`,
i.e. the preparation steps contribute `O(p ^ (9+o(1)))`. -/
theorem prepBase_highMomentum {m ε p : ℝ} (hm : 0 < m) (hε : 0 < ε) (hp : 0 < p) :
    prepBase p (1 / p) m ε = (1 / m ^ 3) * p ^ 9 * ε⁻¹ := by
  unfold prepBase
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hm0 : m ≠ 0 := ne_of_gt hm
  have he0 : ε ≠ 0 := ne_of_gt hε
  field_simp

/-- High-precision preparation gate count, Eq. (16)/(18) with `a ∼ ε` and the
`1 + o(1)` exponent of the Suzuki–Trotter step. The constant `c` absorbs
`L ^ 3 / m ^ 3`. -/
noncomputable def highPrecisionPrepGateCount (c : ℝ) (η : ℝ → ℝ) (ε : ℝ) : ℝ :=
  (c * ε ^ (-(7 : ℝ))) ^ (1 + η ε)

/-- High-precision excitation gate count, Eq. (19): `ε ^ (-4-o(1))`. -/
noncomputable def highPrecisionExciteGateCount (c : ℝ) (η : ℝ → ℝ) (ε : ℝ) : ℝ :=
  (c * ε ^ (-(4 : ℝ))) ^ (1 + η ε)

/-- High-precision total, Eq. (20) upper branch: the two adiabatic preparation
steps (Eq. (16)/(18)) plus the excitation step (Eq. (19)), multiplied by the
`1/ε` postselection factor for the two successful wavepacket excitations
(§2.3, the sentence following Eq. (19)). -/
noncomputable def highPrecisionTotalGateCount (cprep cexc : ℝ) (η : ℝ → ℝ)
    (ε : ℝ) : ℝ :=
  (2 * highPrecisionPrepGateCount cprep η ε + highPrecisionExciteGateCount cexc η ε) * ε⁻¹

/-- High-momentum preparation gate count: Eq. (16)/(18) with `a ∼ 1/p`, `L ∼ p`
gives `p ^ (9+o(1))`. The constant `c` absorbs `1 / m ^ 3` and the fixed `ε`. -/
noncomputable def highMomentumPrepGateCount (c : ℝ) (η : ℝ → ℝ) (p : ℝ) : ℝ :=
  (c * p ^ (9 : ℝ)) ^ (1 + η p)

/-- High-momentum excitation gate count, Eq. (19): `p ^ (3+o(1))`. -/
noncomputable def highMomentumExciteGateCount (c : ℝ) (η : ℝ → ℝ) (p : ℝ) : ℝ :=
  (c * p ^ (3 : ℝ)) ^ (1 + η p)

/-- High-momentum total, Eq. (20) lower branch: two preparation steps plus the
lower-order excitation step. -/
noncomputable def highMomentumTotalGateCount (cprep cexc : ℝ) (η : ℝ → ℝ)
    (p : ℝ) : ℝ :=
  2 * highMomentumPrepGateCount cprep η p + highMomentumExciteGateCount cexc η p

/-! ## 6. Nonnegativity of the cost model -/

/-- The high-precision total gate count is nonnegative for `ε > 0`. -/
theorem highPrecisionTotalGateCount_nonneg {cprep cexc : ℝ} (hcprep : 0 ≤ cprep)
    (hcexc : 0 ≤ cexc) {η : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) :
    0 ≤ highPrecisionTotalGateCount cprep cexc η ε := by
  unfold highPrecisionTotalGateCount highPrecisionPrepGateCount highPrecisionExciteGateCount
  have hp : 0 ≤ (cprep * ε ^ (-(7 : ℝ))) ^ (1 + η ε) :=
    Real.rpow_nonneg (mul_nonneg hcprep (Real.rpow_nonneg (le_of_lt hε) _)) _
  have he : 0 ≤ (cexc * ε ^ (-(4 : ℝ))) ^ (1 + η ε) :=
    Real.rpow_nonneg (mul_nonneg hcexc (Real.rpow_nonneg (le_of_lt hε) _)) _
  exact mul_nonneg (by linarith) (le_of_lt (inv_pos.mpr hε))

/-- The high-momentum total gate count is nonnegative for `p > 0`. -/
theorem highMomentumTotalGateCount_nonneg {cprep cexc : ℝ} (hcprep : 0 ≤ cprep)
    (hcexc : 0 ≤ cexc) {η : ℝ → ℝ} {p : ℝ} (hp : 0 < p) :
    0 ≤ highMomentumTotalGateCount cprep cexc η p := by
  unfold highMomentumTotalGateCount highMomentumPrepGateCount highMomentumExciteGateCount
  have hp' : 0 ≤ (cprep * p ^ (9 : ℝ)) ^ (1 + η p) :=
    Real.rpow_nonneg (mul_nonneg hcprep (Real.rpow_nonneg (le_of_lt hp) _)) _
  have he' : 0 ≤ (cexc * p ^ (3 : ℝ)) ^ (1 + η p) :=
    Real.rpow_nonneg (mul_nonneg hcexc (Real.rpow_nonneg (le_of_lt hp) _)) _
  linarith

end

end Qatlib.Papers.FermionicQFT14.MainResults
