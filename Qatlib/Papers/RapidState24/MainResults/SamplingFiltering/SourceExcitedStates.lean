/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

set_option backward.isDefEq.respectTransparency false

/-!
# Excited-state contribution to multi-sample phase-estimation failure

This file formalizes Section V.C (pp. 21–23, Eqs. (86)–(87)) and Appendix D (pp. 40–41,
Eqs. (D1)–(D11)) of [Berry et al., 2024][BerryEtAl2024Rapid]:

* `excitedFailure`: the `n`-sample failure probability
  `[p δ / 2 + (1 - p) δ₁]^n + 1 - {1 - [p δ / 2 + (1 - p) δ₂]}^n` (Eq. (87)).
* `excitedFailure_deriv` and `excitedFailure_deriv2`: first and second `p`-derivatives
  (Eqs. (D1) and (D3)).
* `d11_ratio_pow` and `no_interior_max`: the ratio inequality Eq. (D11) and algebraic exclusion
  of an interior strict maximum.
* `single_excited_state_dominates`: worst-case reduction showing that any convex combination of
  two excited-state tail pairs `(δ₁ᵃ, δ₂ᵃ)` and `(δ₁ᵇ, δ₂ᵇ)` has failure probability at most
  `max(P_a, P_b)`, so a single excited state attains the worst case.

## Main statements

* `excitedFailure_deriv` / `excitedFailure_deriv2`: derivatives of `excitedFailure` in `p`.
* `d11_ratio_pow`: ratio bound `(1 - lowProb)^{n - 1} / highProb^{n - 1} > 1` (Eq. (D11)).
* `no_interior_max`: algebraic exclusion of an interior maximum.
* `single_excited_state_dominates`: convex combinations of excited states never exceed the
  worst endpoint error.

## References

* [Berry et al., 2024][BerryEtAl2024Rapid]
-/

namespace Qatlib.Papers.RapidState24.MainResults.SamplingFiltering

set_option autoImplicit false

/-! ## §1. Multi-sample failure expression with excited states (Eq. (87)) -/

/-- Per-sample probability `p δ / 2 + (1 - p) δ₁` of obtaining an estimate that is too high
(Eqs. (86)–(87), Section V.C, p. 22). -/
noncomputable def highProb (p δ δ1 : ℝ) : ℝ :=
  p * δ / 2 + (1 - p) * δ1

/-- Per-sample probability `p δ / 2 + (1 - p) δ₂` of obtaining an estimate that is too low
(Eq. (87), Section V.C, p. 22). -/
noncomputable def lowProb (p δ δ2 : ℝ) : ℝ :=
  p * δ / 2 + (1 - p) * δ2

/-- **Eq. (87)** ([Berry et al., 2024][BerryEtAl2024Rapid], Section V.C, p. 22): probability of an
error outside the confidence interval after `n` samples. -/
noncomputable def excitedFailure (p δ δ1 δ2 : ℝ) (n : ℕ) : ℝ :=
  highProb p δ δ1 ^ n + 1 - (1 - lowProb p δ δ2) ^ n

/-- Term-by-term expansion of `excitedFailure` (Eq. (87)). -/
theorem excitedFailure_eq (p δ δ1 δ2 : ℝ) (n : ℕ) :
    excitedFailure p δ δ1 δ2 n
      = (p * δ / 2 + (1 - p) * δ1) ^ n
          + 1 - (1 - (p * δ / 2 + (1 - p) * δ2)) ^ n := by
  unfold excitedFailure highProb lowProb
  rfl

/-- Improvement of `highProb` relative to the ground-state-only bound `1 - p(1 - δ/2)` by
`(1 - p)(1 - δ₁)` (Section V.C, p. 22). -/
theorem highProb_eq_ground_sub (p δ δ1 : ℝ) :
    highProb p δ δ1 = 1 - p * (1 - δ / 2) - (1 - p) * (1 - δ1) := by
  unfold highProb
  ring

/-- Positivity of `highProb` for `0 < p ≤ 1`, `0 < δ`, and `0 < δ₁`. -/
theorem highProb_pos (p δ δ1 : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    (hδ1 : 0 < δ1) : 0 < highProb p δ δ1 := by
  unfold highProb
  have h1 : 0 < p * δ / 2 := by positivity
  have h2 : 0 ≤ (1 - p) * δ1 := mul_nonneg (by linarith) hδ1.le
  linarith

/-- Upper bound `lowProb p δ δ2 < 1` for `0 ≤ p ≤ 1`, `δ < 1`, and `δ₂ < 1`. -/
theorem lowProb_lt_one (p δ δ2 : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : δ < 1)
    (hδ2 : δ2 < 1) : lowProb p δ δ2 < 1 := by
  by_cases hpzero : p = 0
  · subst hpzero
    unfold lowProb
    simpa using hδ2
  · have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpzero)
    have h1 : p * δ / 2 < p / 2 := by
      have : p * δ < p * 1 := mul_lt_mul_of_pos_left hδ hppos
      linarith
    have h2 : (1 - p) * δ2 ≤ (1 - p) * 1 :=
      mul_le_mul_of_nonneg_left hδ2.le (by linarith)
    unfold lowProb
    nlinarith [h1, h2, hp1]

/-! ## §2. Derivatives and single-excited-state dominance (Appendix D) -/

/-- First derivative of `excitedFailure` with respect to `p` (Eq. (D1), Appendix D, p. 40). -/
theorem excitedFailure_deriv (p δ δ1 δ2 : ℝ) (n : ℕ) :
    deriv (fun x => excitedFailure x δ δ1 δ2 n) p
      = (n : ℝ) * (δ / 2 - δ1) * highProb p δ δ1 ^ (n - 1)
        + (n : ℝ) * (δ / 2 - δ2) * (1 - lowProb p δ δ2) ^ (n - 1) := by
  have hH : HasDerivAt (fun x => highProb x δ δ1) (δ / 2 - δ1) p := by
    have hfun : (fun x => highProb x δ δ1) = fun x => (δ / 2 - δ1) * x + δ1 := by
      funext x
      unfold highProb
      ring
    rw [hfun]
    simpa using ((hasDerivAt_id p).const_mul (δ / 2 - δ1)).add_const δ1
  have hL : HasDerivAt (fun x => lowProb x δ δ2) (δ / 2 - δ2) p := by
    have hfun : (fun x => lowProb x δ δ2) = fun x => (δ / 2 - δ2) * x + δ2 := by
      funext x
      unfold lowProb
      ring
    rw [hfun]
    simpa using ((hasDerivAt_id p).const_mul (δ / 2 - δ2)).add_const δ2
  have h1mL : HasDerivAt (fun x => 1 - lowProb x δ δ2) (-(δ / 2 - δ2)) p :=
    hL.const_sub 1
  have hHpow := hH.pow n
  have hLpow := h1mL.pow n
  have hP : HasDerivAt (fun x => excitedFailure x δ δ1 δ2 n)
      ((n : ℝ) * highProb p δ δ1 ^ (n - 1) * (δ / 2 - δ1)
        - (n : ℝ) * (1 - lowProb p δ δ2) ^ (n - 1) * (-(δ / 2 - δ2))) p := by
    unfold excitedFailure
    exact (hHpow.add_const 1).sub hLpow
  rw [hP.deriv]
  ring

/-- Second derivative of `excitedFailure` with respect to `p` (Eq. (D3), Appendix D, p. 40). -/
theorem excitedFailure_deriv2 (p δ δ1 δ2 : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    deriv (fun x => deriv (fun y => excitedFailure y δ δ1 δ2 n) x) p
      = (n : ℝ) * ((n : ℝ) - 1) * (δ / 2 - δ1) ^ 2 * highProb p δ δ1 ^ (n - 2)
        - (n : ℝ) * ((n : ℝ) - 1) * (δ / 2 - δ2) ^ 2
            * (1 - lowProb p δ δ2) ^ (n - 2) := by
  have hfun : (fun x => deriv (fun y => excitedFailure y δ δ1 δ2 n) x)
      = fun x => (n : ℝ) * (δ / 2 - δ1) * highProb x δ δ1 ^ (n - 1)
          + (n : ℝ) * (δ / 2 - δ2) * (1 - lowProb x δ δ2) ^ (n - 1) := by
    funext x
    exact excitedFailure_deriv x δ δ1 δ2 n
  rw [hfun]
  have hH : HasDerivAt (fun x => highProb x δ δ1) (δ / 2 - δ1) p := by
    have hfun' : (fun x => highProb x δ δ1) = fun x => (δ / 2 - δ1) * x + δ1 := by
      funext x
      unfold highProb
      ring
    rw [hfun']
    simpa using ((hasDerivAt_id p).const_mul (δ / 2 - δ1)).add_const δ1
  have hL : HasDerivAt (fun x => lowProb x δ δ2) (δ / 2 - δ2) p := by
    have hfun' : (fun x => lowProb x δ δ2) = fun x => (δ / 2 - δ2) * x + δ2 := by
      funext x
      unfold lowProb
      ring
    rw [hfun']
    simpa using ((hasDerivAt_id p).const_mul (δ / 2 - δ2)).add_const δ2
  have h1mL : HasDerivAt (fun x => 1 - lowProb x δ δ2) (-(δ / 2 - δ2)) p :=
    hL.const_sub 1
  have hHpow := hH.pow (n - 1)
  have hLpow := h1mL.pow (n - 1)
  have hA : HasDerivAt
      (fun x => (n : ℝ) * (δ / 2 - δ1) * highProb x δ δ1 ^ (n - 1))
      ((n : ℝ) * (δ / 2 - δ1) *
        (((n - 1 : ℕ) : ℝ) * highProb p δ δ1 ^ (n - 1 - 1) * (δ / 2 - δ1))) p :=
    hHpow.const_mul ((n : ℝ) * (δ / 2 - δ1))
  have hB : HasDerivAt
      (fun x => (n : ℝ) * (δ / 2 - δ2) * (1 - lowProb x δ δ2) ^ (n - 1))
      ((n : ℝ) * (δ / 2 - δ2) *
        (((n - 1 : ℕ) : ℝ) * (1 - lowProb p δ δ2) ^ (n - 1 - 1) * (-(δ / 2 - δ2)))) p :=
    hLpow.const_mul ((n : ℝ) * (δ / 2 - δ2))
  have hP : HasDerivAt
      (fun x => (n : ℝ) * (δ / 2 - δ1) * highProb x δ δ1 ^ (n - 1)
          + (n : ℝ) * (δ / 2 - δ2) * (1 - lowProb x δ δ2) ^ (n - 1))
      ((n : ℝ) * (δ / 2 - δ1) *
          (((n - 1 : ℕ) : ℝ) * highProb p δ δ1 ^ (n - 1 - 1) * (δ / 2 - δ1))
        + (n : ℝ) * (δ / 2 - δ2) *
          (((n - 1 : ℕ) : ℝ) * (1 - lowProb p δ δ2) ^ (n - 1 - 1) * (-(δ / 2 - δ2)))) p :=
    hA.add hB
  rw [hP.deriv]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1 : 1 ≤ n := by omega
    push_cast [h1]
    ring
  have hexp : n - 1 - 1 = n - 2 := by omega
  rw [hcast, hexp]
  ring

/-- **Eq. (D11)** ([Berry et al., 2024][BerryEtAl2024Rapid], Appendix D, p. 41): if
`δ₂ < 1 - δ₁`, `0 < δ < 1`, `0 < δ₁`, and `0 < p ≤ 1`, then
`(1 - lowProb p δ δ2)^{n - 1} / highProb p δ δ1^{n - 1} > 1` for all `n ≥ 2`. -/
theorem d11_ratio_pow (p δ δ1 δ2 : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hp : 0 < p) (hp1 : p ≤ 1) (hδpos : 0 < δ) (hδ : δ < 1)
    (hδ2 : δ2 < 1 - δ1) (hδ1 : 0 < δ1) :
    1 < (1 - lowProb p δ δ2) ^ (n - 1) / highProb p δ δ1 ^ (n - 1) := by
  have hHpos : 0 < highProb p δ δ1 := highProb_pos p δ δ1 hp hp1 hδpos hδ1
  have hcmp : highProb p δ δ1 < 1 - lowProb p δ δ2 := by
    unfold highProb lowProb
    have hsum : δ1 + δ2 < 1 := by linarith
    have h1p : 0 ≤ 1 - p := by linarith
    have hmul : (1 - p) * (δ1 + δ2) ≤ (1 - p) * 1 :=
      mul_le_mul_of_nonneg_left hsum.le h1p
    have hpδ : p * δ < p * 1 := mul_lt_mul_of_pos_left hδ hp
    nlinarith [hmul, hpδ]
  have hrat : 1 < (1 - lowProb p δ δ2) / highProb p δ δ1 := by
    rw [lt_div_iff₀ hHpos]
    linarith
  have hpow : 1 < ((1 - lowProb p δ δ2) / highProb p δ δ1) ^ (n - 1) :=
    one_lt_pow₀ hrat (by omega)
  rwa [div_pow] at hpow

/-- Algebraic exclusion of an interior strict maximum under Eqs. (D2) and (D4)
(Appendix D, pp. 40–41). -/
theorem no_interior_max (A B R : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (_hA : 0 < A) (hB : 0 < B) (hR : 0 < R) (hBA : B ≤ A)
    (hfirst : A / B = R ^ (n - 1))
    (hsecond : (A / B) ^ 2 < R ^ (n - 2)) : False := by
  have hexp : (n - 1) * 2 = n + (n - 2) := by omega
  have hRpow : 0 < R ^ (n - 2) := pow_pos hR _
  have hRn : R ^ n < 1 := by
    have h := hsecond
    rw [hfirst, ← pow_mul, hexp, pow_add] at h
    have h' : R ^ n * R ^ (n - 2) < 1 * R ^ (n - 2) := by simpa using h
    exact lt_of_mul_lt_mul_right h' hRpow.le
  have hRlt1 : R < 1 := by
    by_contra hcon
    push Not at hcon
    have hone : 1 ≤ R ^ n := one_le_pow₀ hcon
    linarith
  have hRpow1 : R ^ (n - 1) < 1 := pow_lt_one₀ hR.le hRlt1 (by omega)
  have hAB : A < B := by
    have hdiv : A / B < 1 := by
      rw [hfirst]
      exact hRpow1
    rwa [div_lt_one hB] at hdiv
  linarith

/-- **Appendix D** ([Berry et al., 2024][BerryEtAl2024Rapid], pp. 40–41, Eqs. (D6)–(D11)): for
any convex combination of two excited states with tail probabilities `(δ₁ᵃ, δ₂ᵃ)` and
`(δ₁ᵇ, δ₂ᵇ)`, the `n`-sample failure probability never exceeds the larger of the two endpoint
failure probabilities. -/
theorem single_excited_state_dominates
    (p δ δ1a δ1b δ2a δ2b s : ℝ) (n : ℕ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ) (hδlt : δ < 1)
    (hn : 1 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hδ1a : 0 < δ1a) (hδ1b : 0 < δ1b)
    (hdisj_a : δ2a < 1 - δ1a) (hdisj_b : δ2b < 1 - δ1b) :
    excitedFailure p δ (s * δ1a + (1 - s) * δ1b) (s * δ2a + (1 - s) * δ2b) n
      ≤ max (excitedFailure p δ δ1a δ2a n) (excitedFailure p δ δ1b δ2b n) := by
  by_cases hn2 : 2 ≤ n
  · let H : ℝ → ℝ := fun t => highProb p δ (t * δ1a + (1 - t) * δ1b)
    let Q : ℝ → ℝ := fun t => 1 - lowProb p δ (t * δ2a + (1 - t) * δ2b)
    let f : ℝ → ℝ := fun t => H t ^ n + 1 - Q t ^ n
    let a₁ : ℝ := (1 - p) * (δ1a - δ1b)
    let a₂ : ℝ := (1 - p) * (δ2b - δ2a)
    have hH_aff : ∀ t : ℝ, H t = a₁ * t + highProb p δ δ1b := by
      intro t
      dsimp [H, a₁, highProb]
      ring
    have hQ_aff : ∀ t : ℝ, Q t = a₂ * t + (1 - lowProb p δ δ2b) := by
      intro t
      dsimp [Q, a₂, lowProb]
      ring
    have hf0 : f 0 = excitedFailure p δ δ1b δ2b n := by
      simp [f, H, Q, excitedFailure]
    have hf1 : f 1 = excitedFailure p δ δ1a δ2a n := by
      simp [f, H, Q, excitedFailure]
    change f s ≤ max (excitedFailure p δ δ1a δ2a n) (excitedFailure p δ δ1b δ2b n)
    rw [← hf1, ← hf0]
    by_cases hconst : a₁ = 0 ∧ a₂ = 0
    · have hfeq : f s = f 0 := by
        dsimp [f]
        rw [hH_aff s, hH_aff 0, hQ_aff s, hQ_aff 0, hconst.1, hconst.2]
        ring
      rw [hfeq]
      exact le_max_right _ _
    · let f' : ℝ → ℝ := fun t =>
        (n : ℝ) * a₁ * H t ^ (n - 1) - (n : ℝ) * a₂ * Q t ^ (n - 1)
      let f'' : ℝ → ℝ := fun t =>
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
          (a₁ ^ 2 * H t ^ (n - 2) - a₂ ^ 2 * Q t ^ (n - 2))
      have hf_deriv : ∀ t : ℝ, HasDerivAt f (f' t) t := by
        intro t
        have hHd : HasDerivAt H a₁ t := by
          rw [funext hH_aff]
          simpa using ((hasDerivAt_id t).const_mul a₁).add_const (highProb p δ δ1b)
        have hQd : HasDerivAt Q a₂ t := by
          rw [funext hQ_aff]
          simpa using ((hasDerivAt_id t).const_mul a₂).add_const (1 - lowProb p δ δ2b)
        convert ((hHd.pow n).add_const 1).sub (hQd.pow n) using 1
        dsimp [f']
        ring
      have hf'_deriv : ∀ t : ℝ, HasDerivAt f' (f'' t) t := by
        intro t
        have hHd : HasDerivAt H a₁ t := by
          rw [funext hH_aff]
          simpa using ((hasDerivAt_id t).const_mul a₁).add_const (highProb p δ δ1b)
        have hQd : HasDerivAt Q a₂ t := by
          rw [funext hQ_aff]
          simpa using ((hasDerivAt_id t).const_mul a₂).add_const (1 - lowProb p δ δ2b)
        have h1 := (hHd.pow (n - 1)).const_mul ((n : ℝ) * a₁)
        have h2 := (hQd.pow (n - 1)).const_mul ((n : ℝ) * a₂)
        have hexp : n - 1 - 1 = n - 2 := by omega
        convert h1.sub h2 using 1
        dsimp [f'']
        rw [hexp]
        ring
      have hf_cont : ContinuousOn f (Set.Icc 0 1) :=
        fun t _ => (hf_deriv t).continuousAt.continuousWithinAt
      obtain ⟨t₀, ht₀_mem, ht₀_max⟩ :=
        isCompact_Icc.exists_isMaxOn ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ hf_cont
      have hfs_le : f s ≤ f t₀ := ht₀_max ⟨hs0, hs1⟩
      rcases eq_or_lt_of_le ht₀_mem.1 with rfl | ht₀_pos
      · exact hfs_le.trans (le_max_right _ _)
      rcases eq_or_lt_of_le ht₀_mem.2 with rfl | ht₀_lt1
      · exact hfs_le.trans (le_max_left _ _)
      -- Interior maximizer `t₀ ∈ (0, 1)` leads to a contradiction: `f'(t₀) = 0` forces `f''(t₀) > 0`.
      exfalso
      have hloc : IsLocalMax f t₀ :=
        ht₀_max.isLocalMax (Filter.mem_of_superset (Ioo_mem_nhds ht₀_pos ht₀_lt1) Set.Ioo_subset_Icc_self)
      have hf'0 : f' t₀ = 0 := hloc.hasDerivAt_eq_zero (hf_deriv t₀)
      have hδ1_t₀ : 0 < t₀ * δ1a + (1 - t₀) * δ1b := by nlinarith
      have hdisj_t₀ : t₀ * δ2a + (1 - t₀) * δ2b < 1 - (t₀ * δ1a + (1 - t₀) * δ1b) := by nlinarith
      have hH_pos : 0 < H t₀ :=
        highProb_pos p δ (t₀ * δ1a + (1 - t₀) * δ1b) hp hp1 hδ hδ1_t₀
      have hH_lt_Q : H t₀ < Q t₀ := by
        dsimp [H, Q]
        unfold highProb lowProb
        have h1p : 0 ≤ 1 - p := by linarith
        have hsum : (t₀ * δ1a + (1 - t₀) * δ1b) + (t₀ * δ2a + (1 - t₀) * δ2b) < 1 := by linarith
        have hmul : (1 - p) * ((t₀ * δ1a + (1 - t₀) * δ1b) + (t₀ * δ2a + (1 - t₀) * δ2b)) ≤
            (1 - p) * 1 := mul_le_mul_of_nonneg_left hsum.le h1p
        have hpδ : p * δ < p * 1 := mul_lt_mul_of_pos_left hδlt hp
        nlinarith [hmul, hpδ]
      have hQ_pos : 0 < Q t₀ := lt_trans hH_pos hH_lt_Q
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
        have : 0 < n - 1 := by omega
        exact_mod_cast this
      have hstat : a₁ * H t₀ ^ (n - 1) = a₂ * Q t₀ ^ (n - 1) := by
        dsimp [f'] at hf'0
        nlinarith
      have ha₂_ne : a₂ ≠ 0 := by
        intro ha₂0
        rw [ha₂0, zero_mul] at hstat
        have hHpow_ne : H t₀ ^ (n - 1) ≠ 0 := pow_ne_zero _ hH_pos.ne'
        have ha₁0 : a₁ = 0 := (mul_eq_zero.mp hstat).resolve_right hHpow_ne
        exact hconst ⟨ha₁0, ha₂0⟩
      have hf''_pos : 0 < f'' t₀ := by
        have hexp1 : 2 * (n - 1) = n + (n - 2) := by omega
        have hcore : (a₁ ^ 2 * H t₀ ^ (n - 2) - a₂ ^ 2 * Q t₀ ^ (n - 2)) * H t₀ ^ n =
            a₂ ^ 2 * Q t₀ ^ (n - 2) * (Q t₀ ^ n - H t₀ ^ n) := by
          have hsq : a₁ ^ 2 * (H t₀ ^ (n - 1)) ^ 2 = a₂ ^ 2 * (Q t₀ ^ (n - 1)) ^ 2 := by
            have h := congrArg (fun z => z ^ 2) hstat
            simpa [mul_pow] using h
          have hlhs : a₁ ^ 2 * H t₀ ^ (n - 2) * H t₀ ^ n = a₁ ^ 2 * (H t₀ ^ (n - 1)) ^ 2 := by
            rw [mul_assoc, ← pow_add, ← pow_mul, Nat.mul_comm (n - 1) 2, hexp1, Nat.add_comm]
          have hrhs : a₂ ^ 2 * (Q t₀ ^ (n - 1)) ^ 2 = a₂ ^ 2 * Q t₀ ^ (n - 2) * Q t₀ ^ n := by
            rw [mul_assoc, ← pow_add, ← pow_mul, Nat.mul_comm (n - 1) 2, hexp1, Nat.add_comm]
          calc (a₁ ^ 2 * H t₀ ^ (n - 2) - a₂ ^ 2 * Q t₀ ^ (n - 2)) * H t₀ ^ n
              = a₁ ^ 2 * H t₀ ^ (n - 2) * H t₀ ^ n - a₂ ^ 2 * Q t₀ ^ (n - 2) * H t₀ ^ n :=
                sub_mul _ _ _
            _ = a₂ ^ 2 * Q t₀ ^ (n - 2) * Q t₀ ^ n - a₂ ^ 2 * Q t₀ ^ (n - 2) * H t₀ ^ n := by
                rw [hlhs, hsq, hrhs]
            _ = a₂ ^ 2 * Q t₀ ^ (n - 2) * (Q t₀ ^ n - H t₀ ^ n) := by ring
        have hQ_gt_H_pow : H t₀ ^ n < Q t₀ ^ n :=
          pow_lt_pow_left₀ hH_lt_Q hH_pos.le (by omega)
        have hrhs_pos : 0 < a₂ ^ 2 * Q t₀ ^ (n - 2) * (Q t₀ ^ n - H t₀ ^ n) :=
          mul_pos (mul_pos (sq_pos_of_ne_zero ha₂_ne) (pow_pos hQ_pos _))
            (sub_pos.mpr hQ_gt_H_pow)
        have hbracket_pos : 0 < a₁ ^ 2 * H t₀ ^ (n - 2) - a₂ ^ 2 * Q t₀ ^ (n - 2) := by
          rw [← hcore] at hrhs_pos
          exact pos_of_mul_pos_left hrhs_pos (pow_nonneg hH_pos.le n)
        dsimp [f'']
        exact mul_pos (mul_pos hn_pos hn1_pos) hbracket_pos
      -- Since `f'(t₀) = 0` and `f''(t₀) > 0`, `f'` is strictly positive on `(t₀, t₀ + ε]`,
      -- giving `f t₀ < f (t₀ + ε) ≤ f t₀`.
      have hslope := (hf'_deriv t₀).tendsto_slope_zero_right
      have hev := hslope.eventually (Ioi_mem_nhds hf''_pos)
      rw [eventually_nhdsWithin_iff] at hev
      obtain ⟨r, hr_pos, hr_ball⟩ := Metric.eventually_nhds_iff.mp hev
      let ε : ℝ := min (r / 2) (1 - t₀)
      have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
      have hε_lt_r : ε < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have ht₀_add_le1 : t₀ + ε ≤ 1 := by
        have : ε ≤ 1 - t₀ := min_le_right _ _
        linarith
      have hf'_pos_on : ∀ x ∈ Set.Ioo t₀ (t₀ + ε), 0 < deriv f x := by
        intro x hx
        rw [(hf_deriv x).deriv]
        have hh_pos : 0 < x - t₀ := sub_pos.mpr hx.1
        have hh_lt_r : dist (x - t₀) 0 < r := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hh_pos]
          linarith [hx.2]
        have hsl := hr_ball hh_lt_r hh_pos
        dsimp [slope] at hsl
        rw [add_sub_cancel, hf'0, sub_zero] at hsl
        exact pos_of_mul_pos_right hsl (inv_nonneg.mpr hh_pos.le)
      have hstrict : StrictMonoOn f (Set.Icc t₀ (t₀ + ε)) :=
        strictMonoOn_of_deriv_pos (convex_Icc t₀ (t₀ + ε))
          (fun x _ => (hf_deriv x).continuousAt.continuousWithinAt)
          (fun x hx => hf'_pos_on x (by simpa [interior_Icc] using hx))
      have hlt : f t₀ < f (t₀ + ε) :=
        hstrict (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
          (by linarith)
      have hle : f (t₀ + ε) ≤ f t₀ := ht₀_max ⟨by linarith, ht₀_add_le1⟩
      linarith
  · have hn1 : n = 1 := by omega
    subst hn1
    have haff : excitedFailure p δ (s * δ1a + (1 - s) * δ1b) (s * δ2a + (1 - s) * δ2b) 1 =
        s * excitedFailure p δ δ1a δ2a 1 + (1 - s) * excitedFailure p δ δ1b δ2b 1 := by
      unfold excitedFailure highProb lowProb
      ring
    rw [haff]
    have h1 := mul_le_mul_of_nonneg_left
      (le_max_left (excitedFailure p δ δ1a δ2a 1) (excitedFailure p δ δ1b δ2b 1)) hs0
    have h2 := mul_le_mul_of_nonneg_left
      (le_max_right (excitedFailure p δ δ1a δ2a 1) (excitedFailure p δ δ1b δ2b 1))
      (show 0 ≤ 1 - s by linarith)
    linarith

end Qatlib.Papers.RapidState24.MainResults.SamplingFiltering
