/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MCMontanaro15.MonteCarlo.TvEstimation.TvEstimationModel

set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: estimating the total variation distance

Source: A. Montanaro, *Quantum speedup of Monte Carlo methods*,
arXiv:1504.06987v3, Section 4 (pp. 21–22).  Fixed PDF SHA256
`361ac540aeba94c89ad19bbd1c122c3a46e43b073522e155653dfb055e76c616`.

The source's §4 argument has five steps, each formalised here:

1. `expect_tvIntegrand_eq_tvDist` — the displayed identity
   `E = Σ_x r(x)·|p(x)−q(x)|/(p(x)+q(x)) = ‖p − q‖`, so Algorithm 5's output
   has exact expectation equal to the total variation distance;
2. `prop16_abs` — Proposition 16 quoted from [13]: if both read-outs are within
   `η(p+q)` of the true masses with `η ≤ 1/5`, the measured ratio is within
   `5η` of the exact one;
3. `ae_relative_of_threshold` — Theorem 2's error bound, together with the
   source's threshold `t ≥ 4π/(η√(p+q))`, yields `|p̃(x) − p(x)| ≤ η(p+q)`;
4. `tv_grid_threshold` — the source's choice `t = ⌈10√2π n^{1/2} ε^{−3/2}⌉`
   satisfies that threshold for every `x` with `p(x)+q(x) ≥ 2ε/n`;
5. `tv_integrand_expect_error` — the error decomposition gives `|Ẽ − E| ≤ 4ε`,
   and `tv_totalSamples_le_headline` + `tv_section4_end_to_end` turn that into
   the paper's `O((√n/ε^{5/2}) log(1/ε) log(1/δ))` cost at error `ε` and
   failure `δ`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo.TvEstimation

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.MCMontanaro15.MonteCarlo.StageBMONTECARLO
open scoped BigOperators

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## Step 1: the exact expectation of Algorithm 5 is the total variation -/

omit [DecidableEq X] in
/-- The pointwise contraction: `r(x) · d(x) = |p(x) − q(x)| / 2`. -/
theorem avgLaw_prob_mul_tvIntegrand (p q : FinDist X) (x : X) :
    (avgLaw p q).prob x * tvIntegrand p q x = |p.prob x - q.prob x| / 2 := by
  by_cases h : p.prob x + q.prob x = 0
  · have hp : p.prob x = 0 := by
      have h1 := p.nonneg x
      have h2 := q.nonneg x
      linarith
    have hq : q.prob x = 0 := by
      have h1 := p.nonneg x
      have h2 := q.nonneg x
      linarith
    rw [avgLaw_prob, h, tvIntegrand_of_sum_eq_zero p q x h, hp, hq]
    norm_num
  · have hpos : 0 < p.prob x + q.prob x := by
      have h1 := p.nonneg x
      have h2 := q.nonneg x
      exact lt_of_le_of_ne (by linarith) (Ne.symm h)
    rw [avgLaw_prob, tvIntegrand_of_sum_ne_zero p q x h]
    field_simp

/-- **The source's displayed identity.**  The expected output of Algorithm 5
with perfect estimates is the total variation distance:
`E = Σ_x ((p(x)+q(x))/2)·|p(x)−q(x)|/(p(x)+q(x)) = (1/2)Σ_x |p(x)−q(x)|`. -/
theorem expect_tvIntegrand_eq_tvDist (p q : FinDist X) :
    tvExactMean p q = tvDist p q := by
  unfold tvExactMean tvDist
  rw [FinDist.expect]
  calc ∑ x, (avgLaw p q).prob x * tvIntegrand p q x
      = ∑ x, |p.prob x - q.prob x| / 2 :=
        Finset.sum_congr rfl (fun x _ => avgLaw_prob_mul_tvIntegrand p q x)
    _ = (1 / 2 : ℝ) * ∑ x, |p.prob x - q.prob x| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring

/-! ## Step 2: Proposition 16 of [13] -/

/-- **Proposition 16** (`f(p,q) = (p−q)/(p+q)`).  If `|p̃ − p| ≤ η(p+q)` and
`|q̃ − q| ≤ η(p+q)` with `η ≤ 1/5`, then the ratio moves by at most `5η`.

The derivation is the exact algebraic identity
`f(p̃,q̃) − f(p,q) = 2(αq − βp)/((p+q)(p̃+q̃))` with `α = p̃−p`, `β = q̃−q`,
which gives `2η/(1−2η) ≤ 5η` because `η ≤ 1/5 < 3/10`. -/
theorem prop16_signed {p q pe qe eta : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (heta : 0 ≤ eta) (heta5 : eta ≤ 1 / 5)
    (hpe : |pe - p| ≤ eta * (p + q)) (hqe : |qe - q| ≤ eta * (p + q))
    (hsum : 0 < p + q) :
    |(pe - qe) / (pe + qe) - (p - q) / (p + q)| ≤ 5 * eta := by
  have hpgt : 0 < pe + qe := by
    have h1 := (abs_le.mp hpe).1
    have h2 := (abs_le.mp hqe).1
    nlinarith [hsum, heta, heta5]
  have hid : (pe - qe) / (pe + qe) - (p - q) / (p + q)
      = 2 * ((pe - p) * q - (qe - q) * p) / ((p + q) * (pe + qe)) := by
    field_simp
    ring
  have hnum : |2 * ((pe - p) * q - (qe - q) * p)| ≤ 2 * eta * (p + q) ^ 2 := by
    have habs : |(pe - p) * q - (qe - q) * p|
        ≤ |(pe - p) * q| + |(qe - q) * p| := by
      exact abs_sub ((pe - p) * q) ((qe - q) * p)
    have hqa : |pe - p| * q ≤ eta * (p + q) * q :=
      mul_le_mul_of_nonneg_right hpe hq
    have hpa : |qe - q| * p ≤ eta * (p + q) * p :=
      mul_le_mul_of_nonneg_right hqe hp
    have hkey : |(pe - p) * q - (qe - q) * p| ≤ eta * (p + q) ^ 2 := by
      have e1 : |(pe - p) * q| = |pe - p| * q := by
        rw [abs_mul, abs_of_nonneg hq]
      have e2 : |(qe - q) * p| = |qe - q| * p := by
        rw [abs_mul, abs_of_nonneg hp]
      rw [e1, e2] at habs
      nlinarith [habs, hqa, hpa]
    calc |2 * ((pe - p) * q - (qe - q) * p)|
        = 2 * |(pe - p) * q - (qe - q) * p| := by
          rw [abs_mul]
          norm_num
      _ ≤ 2 * (eta * (p + q) ^ 2) := mul_le_mul_of_nonneg_left hkey (by norm_num)
      _ = 2 * eta * (p + q) ^ 2 := by ring
  have hden : 0 < (p + q) * (pe + qe) := mul_pos hsum hpgt
  rw [hid, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hbden : (1 - 2 * eta) * (p + q) ≤ pe + qe := by
    have h1 := (abs_le.mp hpe).1
    have h2 := (abs_le.mp hqe).1
    nlinarith [hsum]
  have hlow : (1 - 2 * eta) * (p + q) > 0 := by
    have hpos : (0:ℝ) < 1 - 2 * eta := by linarith
    exact mul_pos hpos hsum
  have hs2 : 0 < (p + q) ^ 2 := by positivity
  have hshape : (p + q) * ((1 - 2 * eta) * (p + q)) = (1 - 2 * eta) * (p + q) ^ 2 := by
    ring
  have hstep1 : 2 * eta * (p + q) ^ 2
      ≤ 5 * eta * ((p + q) * ((1 - 2 * eta) * (p + q))) := by
    rw [hshape]
    have hconst : 2 ≤ 5 * (1 - 2 * eta) := by linarith
    have hnn : 0 ≤ eta * (p + q) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hconst hnn
    nlinarith [this]
  have hstep2 : 5 * eta * ((p + q) * ((1 - 2 * eta) * (p + q)))
      ≤ 5 * eta * ((p + q) * (pe + qe)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbden (le_of_lt hsum))
      (by positivity)
  linarith

/-- **Proposition 16 for the measured ratio.**  Algorithm 5 outputs the absolute
value of the ratio, and `||x| − |y|| ≤ |x − y|` transfers the `5η` bound. -/
theorem prop16_abs {p q pe qe eta : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (heta : 0 ≤ eta) (heta5 : eta ≤ 1 / 5)
    (hpe : |pe - p| ≤ eta * (p + q)) (hqe : |qe - q| ≤ eta * (p + q))
    (hsum : 0 < p + q) :
    abs ((|pe - qe| / (pe + qe)) - (|p - q| / (p + q))) ≤ 5 * eta := by
  have hpgt : 0 < pe + qe := by
    have h1 := (abs_le.mp hpe).1
    have h2 := (abs_le.mp hqe).1
    nlinarith [hsum, heta, heta5]
  have h1 : |pe - qe| / (pe + qe) = |(pe - qe) / (pe + qe)| := by
    rw [abs_div, abs_of_pos hpgt]
  have h2 : |p - q| / (p + q) = |(p - q) / (p + q)| := by
    rw [abs_div, abs_of_pos hsum]
  rw [h1, h2]
  calc abs (|(pe - qe) / (pe + qe)| - |(p - q) / (p + q)|)
      ≤ |(pe - qe) / (pe + qe) - (p - q) / (p + q)| :=
        abs_abs_sub_abs_le_abs_sub _ _
    _ ≤ 5 * eta := prop16_signed hp hq heta heta5 hpe hqe hsum

/-! ## Step 3: Theorem 2's error bound reaches the relative form -/

/-- **The source's substitution.**  Theorem 2 bounds the read-out error of a
mass `p` by `2π√(p(1−p))/t + π²/t²`.  If the depth satisfies
`4π ≤ t·η·√(p+q)`, the source concludes `|p̃ − p| ≤ η(p+q)`: the first term is
at most `η(p+q)/2` and the second at most `η(p+q)/16`. -/
theorem ae_relative_of_threshold {p q t eta : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q)
    (ht : 0 < t) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hthr : 4 * Real.pi ≤ t * eta * Real.sqrt (p + q)) :
    2 * Real.pi * Real.sqrt (p * (1 - p)) / t + Real.pi ^ 2 / t ^ 2 ≤ eta * (p + q) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hprod : 0 < t * eta * Real.sqrt (p + q) := lt_of_lt_of_le (by linarith) hthr
  have hsqrtpos : 0 < Real.sqrt (p + q) := by
    rcases lt_or_eq_of_le (Real.sqrt_nonneg (p + q)) with h | h
    · exact h
    · rw [← h, mul_zero] at hprod
      exact absurd hprod (lt_irrefl 0)
  have hspos : 0 < p + q := Real.sqrt_pos.mp hsqrtpos
  have hsqrt : Real.sqrt (p + q) ^ 2 = p + q := Real.sq_sqrt (le_of_lt hspos)
  have hfirst : 2 * Real.pi * Real.sqrt (p * (1 - p)) / t ≤ eta * (p + q) / 2 := by
    have hstepA : 2 * Real.pi / t ≤ eta * Real.sqrt (p + q) / 2 := by
      rw [div_le_iff₀ ht]
      nlinarith [hthr]
    have hstepB : Real.sqrt (p * (1 - p)) ≤ Real.sqrt p := by
      apply Real.sqrt_le_sqrt
      have h1p : 0 ≤ 1 - p := by linarith
      nlinarith [mul_nonneg hp0 h1p]
    have hstepC : Real.sqrt p ≤ Real.sqrt (p + q) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hsp : 0 ≤ Real.sqrt (p + q) := Real.sqrt_nonneg _
    have hnonneg : 0 ≤ 2 * Real.pi / t := by positivity
    calc 2 * Real.pi * Real.sqrt (p * (1 - p)) / t
        = (2 * Real.pi / t) * Real.sqrt (p * (1 - p)) := by ring
      _ ≤ (eta * Real.sqrt (p + q) / 2) * Real.sqrt p :=
          mul_le_mul_of_nonneg_right hstepA (Real.sqrt_nonneg _) |>.trans
            (mul_le_mul_of_nonneg_left hstepB (by positivity))
      _ ≤ (eta * Real.sqrt (p + q) / 2) * Real.sqrt (p + q) := by
          apply mul_le_mul_of_nonneg_left hstepC
          positivity
      _ = eta * (p + q) / 2 := by
          have h : Real.sqrt (p + q) * Real.sqrt (p + q) = p + q := by
            rw [← sq, hsqrt]
          nlinarith [h]
  have hsecond : Real.pi ^ 2 / t ^ 2 ≤ eta * (p + q) / 2 := by
    have hsq : 16 * Real.pi ^ 2 ≤ (t * eta * Real.sqrt (p + q)) ^ 2 := by
      nlinarith [hthr, hpi]
    have hprod2 : (t * eta * Real.sqrt (p + q)) ^ 2 = t ^ 2 * eta ^ 2 * (p + q) := by
      rw [mul_pow, mul_pow, hsqrt]
    have htpos : 0 < t ^ 2 := by positivity
    have hmain : Real.pi ^ 2 / t ^ 2 ≤ eta ^ 2 * (p + q) / 16 := by
      rw [div_le_iff₀ htpos, hprod2] at *
      nlinarith [hsq]
    have heta2 : eta ^ 2 ≤ eta := by nlinarith [heta0, heta1]
    have hsp : 0 ≤ p + q := le_of_lt hspos
    have h16 : eta ^ 2 * (p + q) / 16 ≤ eta * (p + q) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right heta2 hsp]
    linarith
  linarith

/-! ## Step 4: the source's grid depth meets the threshold -/

/-- **The source's choice of `t`.**  With `t = 10√2π n^{1/2} ε^{−3/2}` and
`η = ε/5`, every `x` with `p(x) + q(x) ≥ 2ε/n` satisfies `4π ≤ t·η·√(p+q)`.
Squaring reduces the claim to `2ε ≤ n(p+q)`, which is the displayed hypothesis. -/
theorem tv_grid_threshold (n : ℕ) {eps p q : ℝ}
    (heps : 0 < eps) (hn : 1 ≤ n) (hs : 2 * eps / n ≤ p + q) :
    4 * Real.pi ≤ tvGridIterations n eps * (eps / 5) * Real.sqrt (p + q) := by
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqrt_eps_pos : 0 < Real.sqrt eps := Real.sqrt_pos.mpr heps
  -- the hypothesis `2ε ≤ n(p+q)`
  have hcore : 2 * eps ≤ (n : ℝ) * (p + q) := by
    rw [div_le_iff₀ hnpos] at hs
    linarith
  -- the threshold with the square roots pulled together
  have hgoal : Real.sqrt 2 * Real.sqrt eps ≤ Real.sqrt (n : ℝ) * Real.sqrt (p + q) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ (n : ℝ))]
    apply Real.sqrt_le_sqrt
    nlinarith [hcore]
  -- rewrite the grid depth as the source's `2√2π√n√s / √ε`
  have hrew : tvGridIterations n eps * (eps / 5) * Real.sqrt (p + q)
      = (2 * Real.sqrt 2 * Real.pi) * (Real.sqrt (n : ℝ) * Real.sqrt (p + q))
          / Real.sqrt eps := by
    unfold tvGridIterations
    field_simp
    ring
  rw [hrew]
  have hcoef : 0 ≤ 2 * Real.sqrt 2 * Real.pi := by positivity
  have hbig : (2 * Real.sqrt 2 * Real.pi) * (Real.sqrt 2 * Real.sqrt eps)
      ≤ (2 * Real.sqrt 2 * Real.pi) * (Real.sqrt (n : ℝ) * Real.sqrt (p + q)) :=
    mul_le_mul_of_nonneg_left hgoal hcoef
  have hdiv := div_le_div_of_nonneg_right hbig (le_of_lt hsqrt_eps_pos)
  have hleft : (2 * Real.sqrt 2 * Real.pi) * (Real.sqrt 2 * Real.sqrt eps) / Real.sqrt eps
      = 4 * Real.pi := by
    field_simp
    nlinarith [hsqrt2]
  rw [hleft] at hdiv
  exact hdiv


/-! ## Step 5: the error decomposition `|Ẽ − E| ≤ 4ε` -/

/-- The expectation of a `[0,1]`-valued function is a `[0,1]` value. -/
theorem expect_mem_unit {L : ℕ} (mu : FinDist (Fin L)) (a : Fin L → ℝ)
    (h0 : ∀ s, 0 ≤ a s) (h1 : ∀ s, a s ≤ 1) :
    0 ≤ mu.expect a ∧ mu.expect a ≤ 1 := by
  constructor
  · unfold FinDist.expect
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (mu.nonneg s) (h0 s))
  · unfold FinDist.expect
    calc ∑ s, mu.prob s * a s ≤ ∑ s, mu.prob s * 1 :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h1 s) (mu.nonneg s))
      _ = ∑ s, mu.prob s := by simp
      _ = 1 := mu.sum_one

/-- **One outcome of Algorithm 5.**  If the read-out is within `ε` of the exact
integrand on the event `G`, takes values in `[0,1]`, and `G` fails with mass at
most `2δ`, then the mean output at that outcome is within `ε + 2δ` of the exact
value.  This is the source's `E[|d̃(x) − d(x)|] ≤ 2δ + (1 − 2δ)ε ≤ 2δ + ε`. -/
theorem expect_abs_sub_le_of_bounded {L : ℕ} (mu : FinDist (Fin L))
    (a : Fin L → ℝ) (d eps delta : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ha0 : ∀ s, 0 ≤ a s) (ha1 : ∀ s, a s ≤ 1)
    (G : Fin L → Prop) (heps : 0 ≤ eps)
    (hG : ∀ s, G s → |a s - d| ≤ eps)
    (hbad : badMass mu G ≤ 2 * delta) :
    |mu.expect a - d| ≤ eps + 2 * delta := by
  classical
  have hsub : mu.expect a - d = ∑ s, mu.prob s * (a s - d) := by
    rw [← expect_sub_const]
    rfl
  have hpt : ∀ s, |a s - d| ≤ eps + (if G s then 0 else 1) := by
    intro s
    by_cases hs : G s
    · rw [if_pos hs]
      linarith [hG s hs]
    · rw [if_neg hs]
      have hab : |a s - d| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [ha0 s, ha1 s]
      linarith
  have habs : |∑ s, mu.prob s * (a s - d)| ≤ ∑ s, mu.prob s * |a s - d| := by
    calc |∑ s, mu.prob s * (a s - d)| ≤ ∑ s, |mu.prob s * (a s - d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s, mu.prob s * |a s - d| := by
          apply Finset.sum_congr rfl
          intro s _
          rw [abs_mul, abs_of_nonneg (mu.nonneg s)]
  have hsum1 : ∑ s, mu.prob s * eps = eps := by
    have h : ∑ s, mu.prob s * eps = eps * ∑ s, mu.prob s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [h, mu.sum_one, mul_one]
  have hbad_eq : ∑ s, mu.prob s * (if G s then 0 else 1) = badMass mu G := rfl
  have hsplit : ∑ s, mu.prob s * (eps + (if G s then 0 else 1))
      = eps + badMass mu G := by
    have h1 : ∑ s, mu.prob s * (eps + (if G s then 0 else 1))
        = ∑ s, (mu.prob s * eps + mu.prob s * (if G s then 0 else 1)) := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [h1, Finset.sum_add_distrib, hsum1, hbad_eq]
  have hstep : ∑ s, mu.prob s * |a s - d|
      ≤ ∑ s, mu.prob s * (eps + (if G s then 0 else 1)) :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hpt s) (mu.nonneg s))
  rw [hsub]
  linarith [habs, hstep, hsplit, hbad]

omit [DecidableEq X] in
/-- **The per-outcome accuracy of Algorithm 5 at the source's grid depth.**
For any `x` whose total mass is at least `2ε/n`, the read-out is within `ε` of
the exact integrand on the event where both amplitude-estimation calls succeed. -/
theorem integrand_close_of_grid {n L : ℕ} (p q : FinDist X) (A : TvEstimator X L)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) (hnpos : 1 ≤ n)
    (x : X) (hx : 2 * eps / n ≤ p.prob x + q.prob x) (s : Fin L)
    (hs : aeGood p q (tvGridIterations n eps) A x s) :
    |A.integrand x s - tvIntegrand p q x| ≤ eps := by
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hsum : 0 < p.prob x + q.prob x := by
    have hp : 0 < 2 * eps / n := div_pos (by positivity) hnR
    linarith
  have hp_le : p.prob x ≤ 1 := by
    have h := Finset.single_le_sum (f := p.prob) (fun i _ => p.nonneg i) (Finset.mem_univ x)
    rwa [p.sum_one] at h
  have hq_le : q.prob x ≤ 1 := by
    have h := Finset.single_le_sum (f := q.prob) (fun i _ => q.nonneg i) (Finset.mem_univ x)
    rwa [q.sum_one] at h
  obtain ⟨hpeae, hqeae⟩ := hs
  have htpos : 0 < tvGridIterations n eps := by
    unfold tvGridIterations
    positivity
  have hthr := tv_grid_threshold n heps hnpos hx
  have hthr' : 4 * Real.pi ≤ tvGridIterations n eps * (eps / 5) * Real.sqrt (q.prob x + p.prob x) := by
    rw [add_comm (q.prob x)]
    exact hthr
  have hpe : |A.pe x s - p.prob x| ≤ (eps / 5) * (p.prob x + q.prob x) :=
    le_trans hpeae (ae_relative_of_threshold (p := p.prob x) (q := q.prob x)
      (t := tvGridIterations n eps) (eta := eps / 5)
      (p.nonneg x) hp_le (q.nonneg x) htpos (by positivity) (by linarith) hthr)
  have hqe0 : |A.qe x s - q.prob x| ≤ (eps / 5) * (q.prob x + p.prob x) :=
    le_trans hqeae (ae_relative_of_threshold (p := q.prob x) (q := p.prob x)
      (t := tvGridIterations n eps) (eta := eps / 5)
      (q.nonneg x) hq_le (p.nonneg x) htpos (by positivity) (by linarith) hthr')
  have hqe : |A.qe x s - q.prob x| ≤ (eps / 5) * (p.prob x + q.prob x) := by
    rw [add_comm (q.prob x)] at hqe0
    exact hqe0
  have hpegt : 0 < A.pe x s + A.qe x s := by
    have h1 := (abs_le.mp hpe).1
    have h2 := (abs_le.mp hqe).1
    have heta5 : eps / 5 ≤ 1 / 5 := by linarith
    nlinarith [hsum, heps, heta5]
  have hi : A.integrand x s = |A.pe x s - A.qe x s| / (A.pe x s + A.qe x s) := by
    simp [TvEstimator.integrand, ne_of_gt hpegt]
  have hd : tvIntegrand p q x = |p.prob x - q.prob x| / (p.prob x + q.prob x) :=
    tvIntegrand_of_sum_ne_zero p q x (ne_of_gt hsum)
  rw [hi, hd]
  have hprop := prop16_abs (p.nonneg x) (q.nonneg x) (by positivity) (by linarith) hpe hqe hsum
  nlinarith [hprop]

omit [DecidableEq X] in
/-- **The source's `|Ẽ − E| ≤ 4ε`.**  Under the amplitude-estimation failure
budget `2ε` per outcome and the grid depth `t = 10√2π n^{1/2} ε^{−3/2}`, the mean
output of Algorithm 5 is within `4ε` of the total variation distance.

The proof follows §4 literally: `x` with `p(x)+q(x) ≥ 2ε/n` contributes at most
`ε + 2ε` per unit mass, and the remaining outcomes contribute their total mass,
which is at most `n·(ε/n) = ε`. -/
theorem tv_integrand_expect_error {n L : ℕ} (p q : FinDist X)
    (hn : Fintype.card X = n) (hnpos : 1 ≤ n)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (A : TvEstimator X L)
    (hfail : ∀ x, badMass A.seedLaw
      (fun s => aeGood p q (tvGridIterations n eps) A x s) ≤ 2 * eps) :
    |A.outputMean p q - tvExactMean p q| ≤ 4 * eps := by
  classical
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  -- the per-outcome bound
  have hbound : ∀ x, |A.conditionalMean x - tvIntegrand p q x|
      ≤ if 2 * eps / n ≤ p.prob x + q.prob x then 3 * eps else 1 := by
    intro x
    by_cases hx : 2 * eps / n ≤ p.prob x + q.prob x
    · rw [if_pos hx]
      have hinner := expect_abs_sub_le_of_bounded A.seedLaw
        (fun s => A.integrand x s) (tvIntegrand p q x) eps eps
        (tvIntegrand_nonneg p q x) (tvIntegrand_le_one p q x)
        (fun s => A.integrand_nonneg x s) (fun s => A.integrand_le_one x s)
        (fun s => aeGood p q (tvGridIterations n eps) A x s) (le_of_lt heps)
        (fun s hs => integrand_close_of_grid p q A heps heps1 hnpos x hx s hs)
        (hfail x)
      show |A.conditionalMean x - tvIntegrand p q x| ≤ 3 * eps
      show |A.seedLaw.expect (fun s => A.integrand x s) - tvIntegrand p q x| ≤ 3 * eps
      nlinarith [hinner]
    · rw [if_neg hx]
      have hcm := expect_mem_unit A.seedLaw (fun s => A.integrand x s)
        (fun s => A.integrand_nonneg x s) (fun s => A.integrand_le_one x s)
      have hd0 := tvIntegrand_nonneg p q x
      have hd1 := tvIntegrand_le_one p q x
      show |A.conditionalMean x - tvIntegrand p q x| ≤ 1
      show |A.seedLaw.expect (fun s => A.integrand x s) - tvIntegrand p q x| ≤ 1
      rw [abs_le]
      constructor <;> linarith [hcm.1, hcm.2]
  -- the large/small split
  have hlarge : ∑ x ∈ Finset.univ.filter (fun x => 2 * eps / n ≤ p.prob x + q.prob x),
      (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|
      ≤ 3 * eps * ∑ x ∈ Finset.univ.filter (fun x => 2 * eps / n ≤ p.prob x + q.prob x),
          (avgLaw p q).prob x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have hxs : 2 * eps / n ≤ p.prob x + q.prob x := (Finset.mem_filter.mp hx).2
    have hb := hbound x
    rw [if_pos hxs] at hb
    calc (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|
        ≤ (avgLaw p q).prob x * (3 * eps) :=
          mul_le_mul_of_nonneg_left hb ((avgLaw p q).nonneg x)
      _ = 3 * eps * (avgLaw p q).prob x := by ring
  have hlarge_sum : ∑ x ∈ Finset.univ.filter (fun x => 2 * eps / n ≤ p.prob x + q.prob x),
      (avgLaw p q).prob x ≤ 1 := by
    calc ∑ x ∈ Finset.univ.filter (fun x => 2 * eps / n ≤ p.prob x + q.prob x),
          (avgLaw p q).prob x
        ≤ ∑ x, (avgLaw p q).prob x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun x _ _ => (avgLaw p q).nonneg x)
      _ = 1 := (avgLaw p q).sum_one
  have hsmall : ∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
      (avgLaw p q).prob x ≤ eps := by
    have hstep : ∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
        (avgLaw p q).prob x
        ≤ ∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
            eps / n := by
      apply Finset.sum_le_sum
      intro x hx
      have hx' : p.prob x + q.prob x < 2 * eps / n := not_le.mp (Finset.mem_filter.mp hx).2
      have hhalf : (2 * eps / n) / 2 = eps / n := by field_simp
      rw [avgLaw_prob]
      linarith
    have hcard : (Finset.univ.filter
        (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x))).card ≤ n := by
      have h := Finset.card_le_univ (Finset.univ.filter
        (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)))
      simpa [hn] using h
    calc ∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
          (avgLaw p q).prob x
        ≤ ∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
            eps / n := hstep
      _ = ((Finset.univ.filter
            (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x))).card : ℝ) * (eps / n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * (eps / n) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
      _ = eps := by
          field_simp
  have hsmallbound : ∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
      (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x| ≤ eps := by
    calc ∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
          (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|
        ≤ ∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
            (avgLaw p q).prob x := by
          apply Finset.sum_le_sum
          intro x hx
          have hb := hbound x
          rw [if_neg (Finset.mem_filter.mp hx).2] at hb
          calc (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|
              ≤ (avgLaw p q).prob x * 1 :=
                mul_le_mul_of_nonneg_left hb ((avgLaw p q).nonneg x)
            _ = (avgLaw p q).prob x := by ring
      _ ≤ eps := hsmall
  have hchain : |A.outputMean p q - tvExactMean p q|
      ≤ ∑ x, (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x| := by
    have hout : A.outputMean p q
        = (avgLaw p q).expect (fun x => A.conditionalMean x) := rfl
    have hex : tvExactMean p q = (avgLaw p q).expect (tvIntegrand p q) := rfl
    rw [hout, hex]
    calc |(avgLaw p q).expect (fun x => A.conditionalMean x)
          - (avgLaw p q).expect (tvIntegrand p q)|
        = |∑ x, (avgLaw p q).prob x
            * (A.conditionalMean x - tvIntegrand p q x)| := by
          congr 1
          unfold FinDist.expect
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ ≤ ∑ x, |(avgLaw p q).prob x
            * (A.conditionalMean x - tvIntegrand p q x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul, abs_of_nonneg ((avgLaw p q).nonneg x)]
  have htotal : ∑ x, (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|
      ≤ 3 * eps + eps := by
    have hsum : ∑ x, (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|
        = (∑ x ∈ Finset.univ.filter (fun x => 2 * eps / n ≤ p.prob x + q.prob x),
              (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|)
          + (∑ x ∈ Finset.univ.filter (fun x => ¬ (2 * eps / n ≤ p.prob x + q.prob x)),
              (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|) := by
      rw [Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset X)
        (fun x => 2 * eps / n ≤ p.prob x + q.prob x)
        (fun x => (avgLaw p q).prob x * |A.conditionalMean x - tvIntegrand p q x|)]
    rw [hsum]
    have h3 : 0 ≤ 3 * eps := by positivity
    nlinarith [hlarge, hlarge_sum, hsmallbound, h3]
  linarith


/-! ## Step 6: the resource composition of §4 -/

/-- The exact factorisation of the pipeline's cost: running the Algorithm 5
subroutine at internal precision `ε/8` costs `8√8·√n/(ε²√ε)·log(8/ε)`, and
Theorem 3's `(1/ε)log(1/δ)` repetitions multiply that by the remaining factor. -/
theorem tvTotalSamples_eq (n : ℕ) {eps delta : ℝ} (heps : 0 < eps) :
    tvTotalSamples n eps delta
      = 8 * Real.sqrt 8 * (Real.sqrt n / (eps ^ 2 * Real.sqrt eps))
          * Real.log (8 / eps) * Real.log (1 / delta) := by
  unfold tvTotalSamples tvSubroutineSamples tvRepetitions
  have harg : (1 : ℝ) / (eps / 8) = 8 / eps := by
    field_simp
  rw [harg]
  have hsqrtdiv : Real.sqrt (eps / 8) = Real.sqrt eps / Real.sqrt 8 :=
    Real.sqrt_div (le_of_lt heps) 8
  rw [hsqrtdiv]
  field_simp

/-- **The source's headline cost.**  With `ε ≤ 1/8` and `δ ≤ 1`, the pipeline's
`O(√n ε^{−3/2} log(1/ε))·O((1/ε)log(1/δ))` cost is at most `46` times the
paper's `O((√n/ε^{5/2}) log(1/ε) log(1/δ))`. -/
theorem tv_totalSamples_le_headline (n : ℕ) {eps delta : ℝ}
    (heps : 0 < eps) (heps8 : eps ≤ 1 / 8) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    tvTotalSamples n eps delta ≤ 46 * tvHeadlineSamples n eps delta := by
  -- `log(8/ε) ≤ 2 log(1/ε)`
  have hlog8 : Real.log 8 ≤ Real.log (1 / eps) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ heps]
    nlinarith
  have hL0 : 0 ≤ Real.log (1 / eps) :=
    le_trans (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 8)) hlog8
  have hlogsplit : Real.log (8 / eps) = Real.log 8 + Real.log (1 / eps) := by
    rw [show (8:ℝ) / eps = 8 * (1 / eps) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hlogle : Real.log (8 / eps) ≤ 2 * Real.log (1 / eps) := by
    rw [hlogsplit]
    linarith
  have hlog8pos : 0 ≤ Real.log (8 / eps) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ heps]
    nlinarith
  -- `8√8 ≤ 23`
  have hsqrt2le : Real.sqrt 2 ≤ 23 / 16 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsq8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
  have h88 : 8 * Real.sqrt 8 ≤ 23 := by
    rw [hsq8]
    nlinarith [hsqrt2le]
  have hfac : 8 * Real.sqrt 8 * Real.log (8 / eps) ≤ 46 * Real.log (1 / eps) := by
    have hs8 : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
    have hcoef : 8 * Real.sqrt 8 ≤ 23 := h88
    nlinarith [hlog8pos, hlogle, hL0, hcoef]
  have hcommon : 0 ≤ Real.sqrt n / (eps ^ 2 * Real.sqrt eps) * Real.log (1 / delta) := by
    have hl : 0 ≤ Real.log (1 / delta) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hdelta]
      linarith
    positivity
  calc tvTotalSamples n eps delta
      = 8 * Real.sqrt 8 * (Real.sqrt n / (eps ^ 2 * Real.sqrt eps))
          * Real.log (8 / eps) * Real.log (1 / delta) :=
        tvTotalSamples_eq n heps
    _ = (8 * Real.sqrt 8 * Real.log (8 / eps))
          * (Real.sqrt n / (eps ^ 2 * Real.sqrt eps) * Real.log (1 / delta)) := by ring
    _ ≤ (46 * Real.log (1 / eps))
          * (Real.sqrt n / (eps ^ 2 * Real.sqrt eps) * Real.log (1 / delta)) :=
        mul_le_mul_of_nonneg_right hfac hcommon
    _ = 46 * tvHeadlineSamples n eps delta := by
        unfold tvHeadlineSamples
        ring

/-- **§4 end to end.**  The two-stage pipeline — Algorithm 5 at internal
precision `ε/8`, then Theorem 3's median stage — estimates the total variation
distance to additive error `ε` whenever Theorem 3's stage contributes at most
`ε/2`, and its sample cost is within the constant `46` of the paper's headline
`O((√n/ε^{5/2}) log(1/ε) log(1/δ))`.

The Theorem-3 stage is a hypothesis here: its own analysis (`t = O(1/ε)` uses
of the subroutine with median over `O(log(1/δ))` repetitions) is the content of
the paper's Theorem 3, which is the subject of the sibling `MonteCarlo` block
endpoints, not of §4. -/
theorem tv_section4_end_to_end {n L : ℕ} (p q : FinDist X)
    (hn : Fintype.card X = n) (hnpos : 1 ≤ n)
    {eps delta : ℝ} (heps : 0 < eps) (heps8 : eps ≤ 1 / 8)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (A : TvEstimator X L)
    (hfail : ∀ x, badMass A.seedLaw
      (fun s => aeGood p q (tvGridIterations n (eps / 8)) A x s) ≤ 2 * (eps / 8))
    (muTilde : ℝ)
    (hthm3 : |muTilde - A.outputMean p q| ≤ eps / 2) :
    |muTilde - tvDist p q| ≤ eps ∧
      tvTotalSamples n eps delta ≤ 46 * tvHeadlineSamples n eps delta := by
  have heps8pos : 0 < eps / 8 := by positivity
  have heps8le : eps / 8 ≤ 1 := by linarith
  have hsub := tv_integrand_expect_error p q hn hnpos (eps / 8) heps8pos heps8le A hfail
  have hexact : tvExactMean p q = tvDist p q := expect_tvIntegrand_eq_tvDist p q
  rw [hexact] at hsub
  constructor
  · calc |muTilde - tvDist p q|
        ≤ |muTilde - A.outputMean p q| + |A.outputMean p q - tvDist p q| :=
          abs_sub_le _ _ _
      _ ≤ eps / 2 + 4 * (eps / 8) := by linarith [hthm3, hsub]
      _ = eps := by ring
  · exact tv_totalSamples_le_headline n heps heps8 hdelta hdelta1

end Qatlib.Papers.MCMontanaro15.MonteCarlo.TvEstimation
