/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# FastForwardLi26 / CarlemanEmbed / SourceModel

Scalar parameter model shared by the paper-layer formalisation of
“Fast-forwarding quantum algorithms for weakly nonlinear dissipative
differential equations and beyond” (Li–An), fixed arXiv:2608.25822v1.

The paper reduces all of its Carleman estimates (§3.2, Appendix A) to a small
set of scalar quantities:

* `a = ‖F₂‖`, `b = -μ(F₁) > 0`, `c = ‖F₀‖`, `x = ‖u(0)‖`;
* the weak-nonlinearity ratio `R = (a x + c/x) / b` (Section 2);
* the rescaling factor `γ`, the *smaller* root of
  `a/γ + cγ = ((1+R)/2) b` (Eq. (8)),
  equivalently the smaller root of `c γ² - ((1+R)/2) b γ + a = 0`
  (product of the two roots is `a/c`, hence the smaller root obeys `c γ² ≤ a`);
* the abbreviation `r = a/γ + cγ - b` (Appendix A, below Eq. (14)).

This file records the parameter predicate and the pure real-arithmetic
identities used by Lemmas 3.1–3.3.  Nothing here presupposes the matrix
(tensor-block) construction; that lives in `DissipLift`/`NormBarrier`/
`TruncError`.

Source anchor: fixed version 2608.25822v1, lines 151–169 (Subsection 3.2) and
lines 989–1185 (Appendix A).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastForwardLi26.CarlemanEmbed.SourceModel

/-- Scalar parameters of the Carleman construction of §3.1.

`a = ‖F₂‖` (`‖F₂‖ = sup_t ‖F₂(t)‖`), `b = -μ(F₁)` with `μ(F₁) = sup_t max_{|x|=1}
Re⟨x|F₁(t)|x⟩` the logarithmic norm, `c = ‖F₀‖`, `x = ‖u(0)‖`, `R` the
weak-nonlinearity ratio and `γ` the rescaling factor (Eq. (8)). -/
structure CarlemanParams where
  /-- `a = ‖F₂‖ ≥ 0`. -/
  a : ℝ
  /-- `b = -μ(F₁) > 0`. -/
  b : ℝ
  /-- `c = ‖F₀‖ ≥ 0`. -/
  c : ℝ
  /-- `x = ‖u(0)‖ > 0`. -/
  x : ℝ
  /-- Weak-nonlinearity ratio `R`. -/
  R : ℝ
  /-- Rescaling factor `γ`. -/
  γ : ℝ

namespace CarlemanParams

/-- The logarithmic norm `μ(F₁) = -b`. -/
def muF1 (p : CarlemanParams) : ℝ := -p.b

/-- `r = a/γ + cγ - b` (Appendix A, below Eq. (14)). -/
def r (p : CarlemanParams) : ℝ := p.a / p.γ + p.c * p.γ - p.b

/-- The Gershgorin maximum `max_j (c_j + r_j)` of Eq. (14)–(15):
for the interior rows `c_j + r_j = 2jr + cγ - a/γ`, and the two boundary
rows are dominated by `2r - a/γ` and `4r + cγ - a/γ`. -/
def gershgorinMax (p : CarlemanParams) : ℝ :=
  max (2 * p.r - p.a / p.γ) (4 * p.r + p.c * p.γ - p.a / p.γ)

/-- The source hypotheses of §2–§3.2 together with the paper's choice of `γ`
as the *smaller* root of Eq. (8).  The condition `c γ² ≤ a` is exactly
“smaller root”: the two roots of `c γ² - ((1+R)/2) b γ + a = 0` multiply to
`a/c`, so the smaller root satisfies `γ² ≤ a/c`.

`0 < R` is not an extra assumption: it follows from `R = (a x + c/x)/b` with
`a, c ≥ 0`, `b, x > 0` and the non-degeneracy forced by Eq. (8). -/
structure Valid (p : CarlemanParams) : Prop where
  /-- `‖F₂‖ ≥ 0`. -/
  a_nonneg : 0 ≤ p.a
  /-- `-μ(F₁) > 0` is the dissipation condition. -/
  b_pos : 0 < p.b
  /-- `‖F₀‖ ≥ 0`. -/
  c_nonneg : 0 ≤ p.c
  /-- `‖u(0)‖ > 0`. -/
  x_pos : 0 < p.x
  /-- The rescaling factor is positive. -/
  gamma_pos : 0 < p.γ
  /-- `γ` is the smaller root of Eq. (8). -/
  gamma_smaller : p.c * p.γ ^ 2 ≤ p.a
  /-- Definition of `R` (Section 2). -/
  R_def : p.R = (p.a * p.x + p.c / p.x) / p.b
  /-- Rescaling equation Eq. (8). -/
  rescale : p.a / p.γ + p.c * p.γ = ((1 + p.R) / 2) * p.b
  /-- Weak nonlinearity `R < 1`. -/
  R_lt_one : p.R < 1

variable {p : CarlemanParams}

/-- Eq. (8) multiplied by `γ`: `a + cγ² = ((1+R)/2) b γ`. -/
theorem rescale_mul_gamma (hp : p.Valid) :
    p.a + p.c * p.γ ^ 2 = ((1 + p.R) / 2) * p.b * p.γ := by
  have h := hp.rescale
  have hγ := hp.gamma_pos
  have h2 : ((1 + p.R) / 2) * p.b * p.γ =
      (p.a / p.γ + p.c * p.γ) * p.γ := by rw [h]
  rw [h2]
  field_simp

/-- `R b = a x + c/x` (the defining relation of `R`). -/
theorem R_mul_b (hp : p.Valid) : p.R * p.b = p.a * p.x + p.c / p.x := by
  rw [hp.R_def]
  have hb : p.b ≠ 0 := ne_of_gt hp.b_pos
  field_simp

/-- `R b x = a x² + c`. -/
theorem R_mul_b_mul_x (hp : p.Valid) : p.R * p.b * p.x = p.a * p.x ^ 2 + p.c := by
  have h := R_mul_b hp
  have hx : p.x ≠ 0 := ne_of_gt hp.x_pos
  have : (p.R * p.b) * p.x = (p.a * p.x + p.c / p.x) * p.x := by rw [h]
  rw [this]
  field_simp

/-- `0 < R`.  Derived from `R = (ax + c/x)/b`: the numerator is non-negative,
and `R = 0` would force `a = c = 0`, contradicting Eq. (8) and `b > 0`. -/
theorem R_pos (hp : p.Valid) : 0 < p.R := by
  have hb := hp.b_pos
  have hx := hp.x_pos
  have ha := hp.a_nonneg
  have hc := hp.c_nonneg
  have hRnonneg : 0 ≤ p.R := by
    rw [hp.R_def]
    apply div_nonneg _ (le_of_lt hb)
    have h1 : 0 ≤ p.a * p.x := mul_nonneg ha (le_of_lt hx)
    have h2 : 0 ≤ p.c / p.x := div_nonneg hc (le_of_lt hx)
    linarith
  rcases lt_or_eq_of_le hRnonneg with h | h
  · exact h
  · exfalso
    have hR0 : p.R = 0 := h.symm
    have hx2 : p.a * p.x ^ 2 + p.c = 0 := by
      have h' := p.R_mul_b_mul_x hp
      rw [hR0] at h'
      linarith [h']
    have hx2pos : (0:ℝ) < p.x ^ 2 := by positivity
    have hax2 : p.a * p.x ^ 2 = 0 := by
      have := mul_nonneg ha (le_of_lt hx2pos)
      linarith [this, hx2]
    have ha0 : p.a = 0 := (mul_eq_zero.mp hax2).resolve_right (ne_of_gt hx2pos)
    have hc0 : p.c = 0 := by linarith [hx2, ha0]
    have hr := hp.rescale
    rw [ha0, hc0, hR0] at hr
    simp at hr
    nlinarith [hb]

/-- `1 - R > 0`. -/
theorem one_sub_R_pos (hp : p.Valid) : 0 < 1 - p.R := by
  linarith [hp.R_lt_one]

/-- The smaller-root consequence `cγ ≤ a/γ`. -/
theorem c_gamma_le (hp : p.Valid) : p.c * p.γ ≤ p.a / p.γ := by
  have hγ := hp.gamma_pos
  rw [le_div_iff₀ hγ]
  nlinarith [hp.gamma_smaller]

/-- `r = ((R-1)/2) b` — Eq. (8) restated. -/
theorem r_eq (hp : p.Valid) : p.r = ((p.R - 1) / 2) * p.b := by
  have h := hp.rescale
  have := p.rescale_mul_gamma hp
  unfold CarlemanParams.r
  rw [h]
  ring

/-- `a/γ ≥ 0`. -/
theorem a_div_gamma_nonneg (hp : p.Valid) : 0 ≤ p.a / p.γ :=
  div_nonneg hp.a_nonneg (le_of_lt hp.gamma_pos)

/-- `(R-1) b < 0`. -/
theorem R_sub_one_mul_b_neg (hp : p.Valid) : (p.R - 1) * p.b < 0 := by
  have := hp.R_lt_one
  exact mul_neg_of_neg_of_pos (by linarith) hp.b_pos

/-- The two Gershgorin terms entering Eq. (15) are both at most `(1-R) μ(F₁)`. -/
theorem gershgorin_terms_le (hp : p.Valid) :
    2 * p.r - p.a / p.γ ≤ (1 - p.R) * p.muF1 ∧
    4 * p.r + p.c * p.γ - p.a / p.γ ≤ (1 - p.R) * p.muF1 := by
  have hr := p.r_eq hp
  have ha := p.a_div_gamma_nonneg hp
  have hcle := p.c_gamma_le hp
  have hneg := p.R_sub_one_mul_b_neg hp
  have hone := p.one_sub_R_pos hp
  have hb := hp.b_pos
  unfold CarlemanParams.muF1
  constructor
  · -- `2r - a/γ = (R-1)b - a/γ ≤ (R-1)b = (1-R)μ(F₁)`
    nlinarith [hr, ha]
  · -- `4r + cγ - a/γ = 2(R-1)b + (cγ - a/γ) ≤ (R-1)b`
    nlinarith [hr, hcle, hneg]

/-- **Appendix A, Eq. (13)–(15), final line.**  The largest eigenvalue of the
Gram matrix `H(G)` is at most `max_j (c_j + r_j) = gershgorinMax`, and hence at
most `(1-R) μ(F₁)`.  Written out below Eq. (15) as
`λ₁(H(G)) ≤ -(1-R)b = (1-R) μ(F₁)`. -/
theorem gershgorinMax_le_muF1 (hp : p.Valid) :
    p.gershgorinMax ≤ (1 - p.R) * p.muF1 := by
  have h := p.gershgorin_terms_le hp
  unfold CarlemanParams.gershgorinMax
  exact max_le h.1 h.2

/-- **Lemma 3.2, first inequality (closed form).**  With `t = γx`, the
difference
`(t - 1)(a - cγ²/t)`
equals `((R-1)/2) b γ`, which is negative.  Since `cγ² ≤ a` makes the second
factor non-negative whenever `t ≥ 1`, this forces `t < 1`. -/
theorem gamma_mul_x_lt_one (hp : p.Valid) : p.γ * p.x < 1 := by
  set t := p.γ * p.x with ht_def
  have hγ := hp.gamma_pos
  have hx := hp.x_pos
  have hb := hp.b_pos
  have ha := hp.a_nonneg
  have hc := hp.c_nonneg
  have ht : 0 < t := mul_pos hγ hx
  have htne : t ≠ 0 := ne_of_gt ht
  -- `R b γ = a t + c γ² / t`
  have h1 : p.R * p.b * p.γ = p.a * t + p.c * p.γ ^ 2 / t := by
    have h := p.R_mul_b_mul_x hp
    -- `R b x = a x² + c`, multiplied by `γ/x`: `R b γ = (a x² + c) γ/x = a t + c γ²/t`
    have h' : p.R * p.b * p.γ = (p.a * p.x ^ 2 + p.c) * p.γ / p.x := by
      rw [eq_div_iff (ne_of_gt hx)]
      nlinarith [h]
    rw [h']
    rw [ht_def]
    field_simp
  -- `((1+R)/2) b γ = a + c γ²`
  have h2 : ((1 + p.R) / 2) * p.b * p.γ = p.a + p.c * p.γ ^ 2 :=
    (p.rescale_mul_gamma hp).symm
  -- The key identity.
  have h1t : p.R * p.b * p.γ * t = p.a * t ^ 2 + p.c * p.γ ^ 2 := by
    have h := h1
    field_simp at h
    nlinarith [h]
  have h2t : ((1 + p.R) / 2) * p.b * p.γ * t = (p.a + p.c * p.γ ^ 2) * t := by
    rw [h2]
  have hid : (t - 1) * (p.a - p.c * p.γ ^ 2 / t) = ((p.R - 1) / 2) * p.b * p.γ := by
    field_simp
    nlinarith [h1t, h2t]
  have hneg : ((p.R - 1) / 2) * p.b * p.γ < 0 := by
    have := hp.R_lt_one
    have := mul_pos (mul_pos (by linarith : (0:ℝ) < (1 - p.R) / 2) hb) hγ
    nlinarith [this]
  by_contra hge
  push Not at hge
  have ht1 : 0 ≤ t - 1 := by linarith
  have hsecond : 0 ≤ p.a - p.c * p.γ ^ 2 / t := by
    have hle : p.c * p.γ ^ 2 / t ≤ p.c * p.γ ^ 2 / 1 := by
      apply div_le_div_of_nonneg_left (by positivity) one_pos hge
    have hsmall := hp.gamma_smaller
    nlinarith [hle, hsmall]
  have hprod : 0 ≤ (t - 1) * (p.a - p.c * p.γ ^ 2 / t) := mul_nonneg ht1 hsecond
  linarith [hid ▸ hprod]

/-- The rescaled root `q = γx` satisfies the quadratic form of Eq. (8) used in
the paper's scalar analysis: with `α = a x / b` and `β = c / (b x)`,
`2βq² - (1+R)q + 2α = 0`, and `0 < q < 1`. -/
theorem rescaling_root_quadratic (hp : p.Valid) :
    2 * (p.c / (p.b * p.x)) * (p.γ * p.x) ^ 2
        - (1 + p.R) * (p.γ * p.x) + 2 * (p.a * p.x / p.b) = 0 ∧
      0 < p.γ * p.x ∧ p.γ * p.x < 1 := by
  have h := p.rescale_mul_gamma hp
  have hb := hp.b_pos
  have hx := hp.x_pos
  have hγ := hp.gamma_pos
  constructor
  · field_simp
    nlinarith [h]
  · exact ⟨mul_pos hγ hx, p.gamma_mul_x_lt_one hp⟩

/-- `((1+R)/2) t = R + c(t²-1)/(b x)` for `t = γx`, with `t < 1` and `c ≥ 0`
giving `((1+R)/2) t ≤ R`.  (Appendix A, Proof of Lemma 3.2, second half.) -/
theorem half_one_add_R_mul_le (hp : p.Valid) :
    ((1 + p.R) / 2) * (p.γ * p.x) ≤ p.R := by
  set t := p.γ * p.x with ht_def
  have ht1 := p.gamma_mul_x_lt_one hp
  have hγ := hp.gamma_pos
  have hx := hp.x_pos
  have hb := hp.b_pos
  have hc := hp.c_nonneg
  have ht : 0 < t := mul_pos hγ hx
  -- `((1+R)/2) t = R + c(t²-1)/(b x)`
  have hC : ((1 + p.R) / 2) * t = p.R + p.c * (t ^ 2 - 1) / (p.b * p.x) := by
    have h := p.R_mul_b_mul_x hp
    have h2 := p.rescale_mul_gamma hp
    have key : p.R = (p.a * p.x ^ 2 + p.c) / (p.b * p.x) := by
      have hbx : p.b * p.x ≠ 0 := ne_of_gt (mul_pos hb hx)
      rw [eq_div_iff hbx]
      linarith [h]
    rw [ht_def, key]
    field_simp
    nlinarith [h2, h]
  have hterm_nonpos : p.c * (t ^ 2 - 1) / (p.b * p.x) ≤ 0 := by
    have hnum : p.c * (t ^ 2 - 1) ≤ 0 := by
      have hneg : t ^ 2 - 1 < 0 := by nlinarith [ht1, ht]
      exact mul_nonpos_of_nonneg_of_nonpos hc (le_of_lt hneg)
    exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt (mul_pos hb hx))
  linarith [hC, hterm_nonpos]

/-- **Lemma 3.2, second inequality (Theorem-level form, nondegenerate case).**
`‖u_γ(0)‖ = γx < 2R/(1+R)`.

The printed strict inequality requires `c = ‖F₀‖ > 0`.  When `F₀ ≡ 0` the
identity `((1+R)/2) t = R` is exact and the bound degenerates to equality;
the general non-strict version is `half_one_add_R_mul_le`. -/
theorem gamma_mul_x_lt (hp : p.Valid) (hcpos : 0 < p.c) :
    p.γ * p.x < 2 * p.R / (1 + p.R) := by
  set t := p.γ * p.x with ht_def
  have ht1 := p.gamma_mul_x_lt_one hp
  have hγ := hp.gamma_pos
  have hx := hp.x_pos
  have hb := hp.b_pos
  have hRpos := p.R_pos hp
  have ht : 0 < t := mul_pos hγ hx
  have hC : ((1 + p.R) / 2) * t = p.R + p.c * (t ^ 2 - 1) / (p.b * p.x) := by
    have h := p.R_mul_b_mul_x hp
    have h2 := p.rescale_mul_gamma hp
    have key : p.R = (p.a * p.x ^ 2 + p.c) / (p.b * p.x) := by
      have hbx : p.b * p.x ≠ 0 := ne_of_gt (mul_pos hb hx)
      rw [eq_div_iff hbx]
      linarith [h]
    rw [ht_def, key]
    field_simp
    nlinarith [h2, h]
  have hterm_neg : p.c * (t ^ 2 - 1) / (p.b * p.x) < 0 := by
    have hneg : t ^ 2 - 1 < 0 := by nlinarith [ht1, ht]
    have hnum : p.c * (t ^ 2 - 1) < 0 := mul_neg_of_pos_of_neg hcpos hneg
    exact div_neg_of_neg_of_pos hnum (mul_pos hb hx)
  have hlt : ((1 + p.R) / 2) * t < p.R := by linarith [hC, hterm_neg]
  -- Clear the denominator `(1+R)/2`.
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < 1 + p.R)]
  nlinarith [hlt]

/-- **Lemma 3.3, final arithmetic step.**  Given the Duhamel/contraction
bound
`‖η(t)‖ ≤ 2N‖F₂‖ / (-(1-R)γ μ(F₁)) · (2R/(1+R))^(N+1)`
and the Eq. (8) consequence
`-γ μ(F₁) ≥ 2‖F₂‖/(1+R)`,
the paper's stated bound
`2NR/(1-R) · (2R/(1+R))^N` follows. -/
theorem truncError_rate
    (hp : p.Valid) (N : ℕ) (hN : 1 ≤ N)
    (hgamma_mu : 2 * p.a / (1 + p.R) ≤ -p.γ * p.muF1) :
    2 * (N : ℝ) * p.a / ((1 - p.R) * (-p.γ * p.muF1)) *
        (2 * p.R / (1 + p.R)) ^ (N + 1) ≤
      2 * (N : ℝ) * p.R / (1 - p.R) * (2 * p.R / (1 + p.R)) ^ N := by
  have ha := hp.a_nonneg
  have hb := hp.b_pos
  have hone := p.one_sub_R_pos hp
  have hRpos := p.R_pos hp
  have hbase_nonneg : 0 ≤ 2 * p.R / (1 + p.R) :=
    div_nonneg (by linarith) (by linarith)
  have hmu_pos : 0 < -p.γ * p.muF1 := by
    unfold CarlemanParams.muF1
    have : -p.γ * -p.b = p.γ * p.b := by ring
    rw [this]
    exact mul_pos hp.gamma_pos hb
  have hDpos : 0 < (1 - p.R) * (-p.γ * p.muF1) := mul_pos hone hmu_pos
  -- Eq. (8) consequence: `2a ≤ (1+R) (-γ μ(F₁))`.
  have h2a : 2 * p.a ≤ (1 + p.R) * (-p.γ * p.muF1) := by
    have h := (div_le_iff₀ (by linarith : (0:ℝ) < 1 + p.R)).mp hgamma_mu
    nlinarith [h]
  have hcore : 2 * (N : ℝ) * p.a ≤ (N : ℝ) * (1 + p.R) * (-p.γ * p.muF1) := by
    have hN : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [h2a, hN]
  -- The scalar factor bound `2Na/D ≤ N(1+R)/(1-R)`.
  have hcore2 : 2 * (N : ℝ) * p.a / ((1 - p.R) * (-p.γ * p.muF1)) ≤
      (N : ℝ) * (1 + p.R) / (1 - p.R) := by
    rw [div_le_div_iff₀ hDpos hone]
    nlinarith [hcore, hone]
  have hpow : (2 * p.R / (1 + p.R)) ^ (N + 1) =
      (2 * p.R / (1 + p.R)) ^ N * (2 * p.R / (1 + p.R)) := by
    rw [pow_succ]
  have hbaseN : 0 ≤ (2 * p.R / (1 + p.R)) ^ N := pow_nonneg hbase_nonneg N
  calc
    2 * (N : ℝ) * p.a / ((1 - p.R) * (-p.γ * p.muF1)) *
        (2 * p.R / (1 + p.R)) ^ (N + 1)
        ≤ ((N : ℝ) * (1 + p.R) / (1 - p.R)) *
            (2 * p.R / (1 + p.R)) ^ (N + 1) :=
          mul_le_mul_of_nonneg_right hcore2 (pow_nonneg hbase_nonneg (N + 1))
    _ = ((N : ℝ) * (1 + p.R) / (1 - p.R)) *
            (2 * p.R / (1 + p.R)) ^ N * (2 * p.R / (1 + p.R)) := by
          rw [hpow]; ring
    _ = 2 * (N : ℝ) * p.R / (1 - p.R) * (2 * p.R / (1 + p.R)) ^ N := by
          field_simp

end CarlemanParams

end Qatlib.Papers.FastForwardLi26.CarlemanEmbed.SourceModel
