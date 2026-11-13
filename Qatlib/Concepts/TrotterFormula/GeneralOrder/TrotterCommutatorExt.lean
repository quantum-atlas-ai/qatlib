/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExtDefs

/-!
# Ordered derivatives and segment accuracy specifications

This module proves smoothness and an ordered derivative-level decomposition for conjugation by
exponential words. It identifies the Taylor integral remainder and the grouping of integral
levels, providing analytic components for the product-formula framework [ChildsEtAl2021Trotter].

It also proves the raw-budget segment guarantee and computes the two-generator degree-two error
as half the commutator, including optimality of that coefficient when the commutator is nonzero.
The structures `Clause49Spec`, `Clause50Spec`, and `Clause51Spec` collect these results into
explicit propositions.

## Main statements

* `pfConjWord_hasDerivAt_levelSum`: ordered level decomposition of the derivative.
* `pfConjWord_taylor_integral_remainder`: Taylor integral remainder for conjugation words.
* `clause50_epsilon_error`: segmented accuracy under the raw-budget condition.
* `clause51_constant_optimal`: optimality of the half-commutator coefficient.
* `stageB_trotter_commutator_clause49`: proof of the analytic remainder specification.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExt

open Matrix
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Set
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff

noncomputable section

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A matrix commutes with the exponential of any real scalar multiple of itself. -/
theorem exp_smul_comm (X : Matrix I I ℂ) (t : ℝ) :
    NormedSpace.exp (t • X) * X = X * NormedSpace.exp (t • X) := by
  have h : Commute X (t • X) := (Commute.refl X).smul_right t
  exact h.exp_right.eq.symm

/-- Exponential conjugation preserves addition of the conjugated matrices. -/
theorem pfConjExp_add (X C D : Matrix I I ℂ) (t : ℝ) :
    pfConjExp X (C + D) t = pfConjExp X C t + pfConjExp X D t := by
  simp only [pfConjExp]
  noncomm_ring

/-- Exponential conjugation commutes with real scalar multiplication of the conjugated matrix. -/
theorem pfConjExp_smul (X C : Matrix I I ℂ) (a : ℝ) (t : ℝ) :
    pfConjExp X (a • C) t = a • pfConjExp X C t := by
  simp only [pfConjExp]
  noncomm_ring

/-- Conjugating the zero matrix by a product word gives zero. -/
theorem pfConjWord_zero (xs : List (Matrix I I ℂ)) (t : ℝ) :
    pfConjWord xs 0 t = 0 := by
  induction xs with
  | nil => simp [pfConjWord]
  | cons X xs ih =>
    rw [pfConjWord]
    simp only [ih, pfConjExp, zero_mul, mul_zero]

/-- Conjugation by a product word preserves matrix addition. -/
theorem pfConjWord_add (xs : List (Matrix I I ℂ)) (C D : Matrix I I ℂ) (t : ℝ) :
    pfConjWord xs (C + D) t = pfConjWord xs C t + pfConjWord xs D t := by
  induction xs with
  | nil => simp [pfConjWord]
  | cons X xs ih =>
    rw [pfConjWord, pfConjWord, ih]
    exact pfConjExp_add X _ _ t

/-- Conjugation by a product word commutes with finite sums of matrices. -/
theorem pfConjWord_sum (xs : List (Matrix I I ℂ)) (s : Finset ℕ)
    (f : ℕ → Matrix I I ℂ) (t : ℝ) :
    pfConjWord xs (∑ i ∈ s, f i) t = ∑ i ∈ s, pfConjWord xs (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, pfConjWord_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    rw [pfConjWord_add, ih]

/-- A finite sum of matrices conjugated by the same exponential equals the conjugation of their
sum. -/
theorem pfConjExp_sum (X : Matrix I I ℂ) (s : Finset ℕ)
    (f : ℕ → Matrix I I ℂ) (t : ℝ) :
    (∑ k ∈ s, pfConjExp X (f k) t) = pfConjExp X (∑ k ∈ s, f k) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simp only [pfConjExp, zero_mul, mul_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    rw [pfConjExp_add, ih]

/-- Conjugation by a product of matrix exponentials is infinitely differentiable as a function
of real time. -/
theorem pfConjWord_contDiff (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) :
    ContDiff ℝ ∞ (pfConjWord xs B) := by
  induction xs with
  | nil => simpa only [pfConjWord] using! (contDiff_const : ContDiff ℝ ∞ (fun _ => B))
  | cons X xs ih =>
    have hn := (trotter_exp_contDiff X).comp contDiff_id.neg
    simpa only [pfConjWord, pfConjExp, Function.comp_def] using!
      ((trotter_exp_contDiff X).mul ih).mul hn

/-- The zeroth derivative-level term for `X :: xs` is the conjugation by `X` of its commutator
with the tail-conjugated seed. -/
theorem orderedLevelTerm_cons_zero (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (τ : ℝ) :
    orderedLevelTerm (X :: xs) B 0 τ =
      pfConjExp X (pfComm X (pfConjWord xs B τ)) τ := by
  simp [orderedLevelTerm, pfConjWord]

/-- A successor derivative-level term for `X :: xs` is the corresponding tail term conjugated by
`X`. -/
theorem orderedLevelTerm_cons_succ (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (k : ℕ) (τ : ℝ) :
    orderedLevelTerm (X :: xs) B (Nat.succ k) τ = pfConjExp X (orderedLevelTerm xs B k τ) τ := by
  have htake : (X :: xs).take (Nat.succ k) = X :: xs.take k := by
    rw [List.take_succ_cons]
  have hget : (X :: xs).getD (Nat.succ k) 0 = xs.getD k 0 := by
    rw [List.getD_cons_succ]
  have hdrop : (X :: xs).drop (Nat.succ (Nat.succ k)) = xs.drop (Nat.succ k) := by
    rw [List.drop_succ_cons]
  simp only [orderedLevelTerm, htake, hget, hdrop]
  rw [pfConjWord]

/-- Splits a sum over `range (n+1)` into its zeroth term and the sum of its successor-indexed
terms. -/
theorem sum_range_cons_split {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∑ k ∈ Finset.range (Nat.succ n), f k) =
      f 0 + ∑ k ∈ Finset.range n, f (Nat.succ k) := by
  induction n with
  | zero =>
    simp [Finset.sum_range_succ]
  | succ n ih =>
    have h := Finset.sum_range_succ (f := f) (n := Nat.succ n)
    rw [h, ih]
    simp [Finset.sum_range_succ, add_assoc]

/-- The derivative of the conjugation word at `t` is the sum of its ordered derivative-level
terms. -/
theorem pfConjWord_hasDerivAt_levelSum (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ)
    (t : ℝ) :
    HasDerivAt (pfConjWord xs B) (orderedLevelSum xs B t) t := by
  induction xs with
  | nil =>
    have h0 : pfConjWord [] B = fun _ => B := by simp [pfConjWord]
    rw [h0]
    simpa [orderedLevelSum] using! (hasDerivAt_const t (B : Matrix I I ℂ))
  | cons X xs ih =>
    have hinner : HasDerivAt (pfConjWord xs B) (orderedLevelSum xs B t) t := ih
    have hE : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
        (NormedSpace.exp (t • X) * X) t := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
    have hEn : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • X))
        (-(X * NormedSpace.exp ((-t) • X))) t := by
      have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (-t)).scomp t
        (hasDerivAt_id t).neg
      simpa only [neg_smul, Function.comp_def, one_smul] using! h
    have hmul' : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X) * pfConjWord xs B u)
        (NormedSpace.exp (t • X) * X * pfConjWord xs B t +
          NormedSpace.exp (t • X) * orderedLevelSum xs B t) t := by
      have h := hE.mul hinner
      have hfun : (fun u : ℝ => NormedSpace.exp (u • X)) * pfConjWord xs B =
          (fun u : ℝ => NormedSpace.exp (u • X) * pfConjWord xs B u) := by
        funext u; rfl
      rw [hfun] at h
      exact h
    have hprod' : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X) * pfConjWord xs B u *
          NormedSpace.exp ((-u) • X))
        ((NormedSpace.exp (t • X) * X * pfConjWord xs B t +
            NormedSpace.exp (t • X) * orderedLevelSum xs B t) * NormedSpace.exp ((-t) • X) +
          (NormedSpace.exp (t • X) * pfConjWord xs B t) *
            (-(X * NormedSpace.exp ((-t) • X)))) t := by
      have h := hmul'.mul hEn
      have hfun : (fun u : ℝ => NormedSpace.exp (u • X) * pfConjWord xs B u) *
          (fun u : ℝ => NormedSpace.exp ((-u) • X)) =
          (fun u : ℝ => NormedSpace.exp (u • X) * pfConjWord xs B u *
            NormedSpace.exp ((-u) • X)) := by
        funext u; rfl
      rw [hfun] at h
      exact h

    have hlevels : orderedLevelSum (X :: xs) B t =
        pfConjExp X (pfComm X (pfConjWord xs B t) + orderedLevelSum xs B t) t := by
      have hrw : orderedLevelSum (X :: xs) B t =
          orderedLevelTerm (X :: xs) B 0 t +
            ∑ k ∈ Finset.range xs.length, orderedLevelTerm (X :: xs) B (Nat.succ k) t := by
        rw [orderedLevelSum]
        simp only [List.length_cons]
        exact sum_range_cons_split xs.length (fun k => orderedLevelTerm (X :: xs) B k t)
      rw [hrw, orderedLevelTerm_cons_zero]
      have hcongr : (∑ k ∈ Finset.range xs.length, orderedLevelTerm (X :: xs) B (Nat.succ k) t) =
          ∑ k ∈ Finset.range xs.length, pfConjExp X (orderedLevelTerm xs B k t) t := by
        exact Finset.sum_congr rfl (fun k _ => orderedLevelTerm_cons_succ X xs B k t)
      rw [hcongr]
      have hlin : (∑ k ∈ Finset.range xs.length, pfConjExp X (orderedLevelTerm xs B k t) t) =
          pfConjExp X (∑ k ∈ Finset.range xs.length, orderedLevelTerm xs B k t) t := by
        exact pfConjExp_sum X (Finset.range xs.length)
          (fun k => orderedLevelTerm xs B k t) t
      rw [hlin]
      rw [orderedLevelSum]
      exact (pfConjExp_add X _ _ t).symm
    rw [hlevels]
    refine hprod'.congr_deriv ?_
    simp only [pfConjExp, pfComm]
    noncomm_ring

/-- For positive order `p`, the conjugation-word truncation error is the Taylor-weighted
integral of its `p`th iterated derivative. -/
theorem pfConjWord_taylor_integral_remainder (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (hp : 0 < p) (t : ℝ) :
    pfConjWord xs B t - pfConjTrunc xs B p t =
      ∫ τ in 0..t, (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        iteratedDeriv p (pfConjWord xs B) τ) := by
  have hpoly := pfConjWord_taylor_before xs B p t
  rw [← hpoly]
  have hp1 : p - 1 + 1 = p := by omega
  have hbefore : pfTaylorBefore (pfConjWord xs B) p t =
      taylorWithinEval (pfConjWord xs B) (p - 1) univ 0 t := by
    rw [← hp1]
    exact pfTaylorBefore_succ _ _ _
  rw [hbefore]
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [taylorWithinEval_self, sub_self, intervalIntegral.integral_same]
  · have hu : UniqueDiffOn ℝ (uIcc 0 t) := uniqueDiffOn_Icc (by grind)
    have hcd := pfConjWord_contDiff xs B
    have hca (k : ℕ) (x : ℝ) : ContDiffAt ℝ ((k : ℕ) : ℕ∞) (pfConjWord xs B) x :=
      (hcd.contDiffAt).of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
    have hrem := taylor_integral_remainder (f := pfConjWord xs B) (x := t) (x₀ := 0)
      (n := p - 1) ((hcd.of_le (by
        rw [hp1]
        exact_mod_cast (le_top : ((p : ℕ) : ℕ∞) ≤ ⊤))).contDiffOn (s := uIcc 0 t))
    have hpoly2 : taylorWithinEval (pfConjWord xs B) (p - 1) (uIcc 0 t) 0 t =
        taylorWithinEval (pfConjWord xs B) (p - 1) univ 0 t := by
      rw [taylor_within_apply, taylor_within_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (hca j 0) (left_mem_uIcc),
        iteratedDerivWithin_univ]
    have hcongr : EqOn (fun τ => (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        iteratedDerivWithin p (pfConjWord xs B) (uIcc 0 t) τ))
        (fun τ => (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        iteratedDeriv p (pfConjWord xs B) τ)) (uIcc 0 t) := by
      intro τ hτ
      show (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        iteratedDerivWithin p (pfConjWord xs B) (uIcc 0 t) τ) = _
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (hca p τ) hτ]
    rw [← hpoly2, hrem, hp1]
    exact intervalIntegral.integral_congr hcongr

/-- The grouped integral remainder is the sum of its grouped integral levels from one to the
generator-list length. -/
theorem groupedIntegralRemainder_eq_level_sum {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    groupedIntegralRemainder xs B p t =
      ∑ k ∈ Finset.Icc 1 xs.length, groupedIntegralLevel xs B p k t := by
  rfl

/-- Every member of `groupedCompositions p k` has length `k`. -/
theorem groupedCompositions_length {p k : ℕ} {q : List ℕ}
    (hq : q ∈ groupedCompositions p k) : q.length = k := by
  classical
  rw [groupedCompositions, Finset.mem_filter, Finset.mem_image] at hq
  obtain ⟨a, -, ha⟩ := hq.1
  rw [← ha]
  simp [List.length_ofFn]

/-- Expands a grouped integral level as a sum of weighted inner conjugation integrals followed
by outer prefix conjugation. -/
theorem groupedIntegralLevel_outer_inner {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p k : ℕ) (t : ℝ) :
    groupedIntegralLevel xs B p k t =
      ∑ q ∈ groupedCompositions p k,
        pfConjWord (xs.take (xs.length - k))
          (∫ τ in 0..t, (groupedScalar p q t τ) •
            pfConjWord [srcGen xs k] (pfNestedCommList (B :: groupedRepetition xs q)) τ) t := by
  classical
  unfold groupedIntegralLevel
  apply Finset.sum_congr rfl
  intro q hq
  have hlen : q.length = k := groupedCompositions_length hq
  have hterm : groupedIntegralTerm xs B p q t =
      pfConjWord (xs.take (xs.length - k))
        (∫ τ in 0..t, (groupedScalar p q t τ) •
          pfConjWord [srcGen xs k] (pfNestedCommList (B :: groupedRepetition xs q)) τ) t := by
    simp only [groupedIntegralTerm]
    rw [hlen]
  rw [hterm]

/-- The degree-one coefficient of the two-generator product is `X + Y`. -/
theorem clause51_first_order_agrees (X Y : Matrix I I ℂ) :
    suzukiSeries [X, Y] 1 = X + Y := by
  simp [suzukiSeries_cons_one, suzukiSeries_nil_succ, add_comm]

/-- The degree-two coefficient of the two-generator product differs from that of `exp (t •
(X+Y))` by one half of `pfComm X Y`. -/
theorem clause51_second_order_deviates (X Y : Matrix I I ℂ) :
    suzukiSeries [X, Y] 2 - (((2 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2 =
      (1 / 2 : ℝ) • pfComm X Y :=
  clause22_leading_coeff_pair X Y

/-- The norm of the two-generator degree-two coefficient error is one half of the commutator
norm. -/
theorem clause51_second_order_norm (X Y : Matrix I I ℂ) :
    ‖suzukiSeries [X, Y] 2 - (((2 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2‖
      = (1 / 2 : ℝ) * ‖pfComm X Y‖ := by
  rw [clause51_second_order_deviates, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]

/-- When the commutator is nonzero, any positive constant bounding the degree-two coefficient
error by that commutator norm is at least one half. -/
theorem clause51_constant_optimal (X Y : Matrix I I ℂ) (hne : pfComm X Y ≠ 0)
    (c : ℝ) (hc : 0 < c)
    (h : ‖suzukiSeries [X, Y] 2 - (((2 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2‖
        ≤ c * ‖pfComm X Y‖) :
    (1 / 2 : ℝ) ≤ c := by
  rw [clause51_second_order_norm] at h
  have hpos : 0 < ‖pfComm X Y‖ := norm_pos_iff.mpr hne
  by_contra hcon
  push_neg at hcon
  have hlt : c * ‖pfComm X Y‖ < (1 / 2 : ℝ) * ‖pfComm X Y‖ :=
    mul_lt_mul_of_pos_right hcon hpos
  linarith

/-- The commutator norm of two generators is bounded by their order-two raw commutator budget. -/
theorem clause51_raw_budget_slack (X Y : Matrix I I ℂ) :
    ‖pfComm X Y‖ ≤ pfCommAlphaSelf [X, Y] 2 := by
  have h := clause22_leading_budget_pair X Y
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)] at h
  linarith

/-- For a real base at least one and a positive natural exponent, the power is at least the
base. -/
theorem pow_ge_base_of_one_le {a : ℝ} (ha : 1 ≤ a) (n : ℕ) (hn : 1 ≤ n) : a ≤ a ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [pow_succ]
    by_cases hn0 : n = 0
    · subst hn0
      simp
    · have h1 : (1 : ℝ) ≤ a ^ n := one_le_pow₀ ha
      nlinarith

/-- For positive order, the selected raw segment count raised to that order dominates
`rawTrotterBudgetFactor`. -/
theorem rawTrotterSegments_pow_ge (xs : List (Matrix I I ℂ)) (p : ℕ) (hp : 1 ≤ p)
    (t ε : ℝ) :
    ((rawTrotterSegments xs p t ε : ℝ) ^ p) ≥ rawTrotterBudgetFactor xs p t ε := by
  set A := rawTrotterBudgetFactor xs p t ε with hAdef
  have hrdef : rawTrotterSegments xs p t ε = max 1 (Nat.ceil A) := by
    unfold rawTrotterSegments
    rw [hAdef]
  have hr1 : (1 : ℝ) ≤ (rawTrotterSegments xs p t ε : ℝ) := by
    rw [hrdef]
    exact_mod_cast le_max_left 1 (Nat.ceil A)
  have hrA : A ≤ (rawTrotterSegments xs p t ε : ℝ) := by
    rw [hrdef]
    refine Nat.le_ceil A |>.trans ?_
    exact_mod_cast le_max_right 1 (Nat.ceil A)
  by_cases hA1 : A ≤ 1
  · have h1pow : (1 : ℝ) ≤ (rawTrotterSegments xs p t ε : ℝ) ^ p :=
      one_le_pow₀ hr1
    exact hA1.trans h1pow
  · have hA1' : (1 : ℝ) ≤ A := le_of_lt (lt_of_not_ge (b := A) (a := 1) hA1)
    have hrpow : (rawTrotterSegments xs p t ε : ℝ) ≤
        (rawTrotterSegments xs p t ε : ℝ) ^ p :=
      pow_ge_base_of_one_le hr1 p hp
    exact hrA.trans hrpow

/-- A matched skew-Hermitian word has segmented error at most a positive tolerance whenever the
positive segment count satisfies the stated raw-budget inequality. -/
theorem clause50_epsilon_error (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p r : ℕ) (hp : 1 ≤ p) (hr : 0 < r)
    (hanti : ∀ X ∈ xs, Xᴴ = -X) (hH : Hᴴ = -H)
    (hmatch : ∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n)
    (t ε : ℝ) (hε : 0 < ε)
    (hseg : (r : ℝ) ^ p ≥ rawTrotterBudgetFactor xs p t ε) :
    ‖(List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten.prod
        - NormedSpace.exp (t • H)‖ ≤ ε := by
  have hsc := trotterCommutatorScalingCorrected I xs H p r hp hr hanti hH hmatch t
  have hbound := hsc.2.2
  have hrp : 0 < (r : ℝ) ^ p := by positivity
  have hnum : (p.factorial : ℝ) * pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) =
      rawTrotterBudgetFactor xs p t ε * ε * (p + 1).factorial := by
    have hε0 : ε ≠ 0 := ne_of_gt hε
    have hf0 : ((p + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (p + 1)
    unfold rawTrotterBudgetFactor
    field_simp
  rw [hnum] at hbound
  have hquot : (rawTrotterBudgetFactor xs p t ε * ε * (p + 1).factorial) /
      (((p + 1).factorial : ℝ) * (r : ℝ) ^ p) =
      rawTrotterBudgetFactor xs p t ε * ε / (r : ℝ) ^ p := by
    have hf0 : ((p + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (p + 1)
    field_simp
  rw [hquot] at hbound
  refine hbound.trans ?_
  rw [div_le_iff₀ hrp]
  have hmul : rawTrotterBudgetFactor xs p t ε * ε ≤
      (r : ℝ) ^ p * ε := mul_le_mul_of_nonneg_right hseg hε.le
  nlinarith

/-- The segmented visit count equals the segment count times the label multiplicity in the base
generator list. -/
theorem segment_visits_eq (xs : List (Matrix I I ℂ)) {m : ℕ}
    (lab : Fin xs.length → Fin m) (r : ℕ) (j : Fin m) :
    segmentLabelVisits xs lab r j =
      r * ((List.finRange xs.length).filter (fun i => lab i = j)).length := by
  rfl

/-- Under the stated matching and skew-Hermitian hypotheses, the repeated exponential factor
list has length `r * xs.length`. -/
theorem clause50_visit_ledger (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p r : ℕ)
    (hp : 1 ≤ p) (hr : 0 < r) (hanti : ∀ X ∈ xs, Xᴴ = -X) (hH : Hᴴ = -H)
    (hmatch : ∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n)
    (t : ℝ) :
    (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten.length
      = r * xs.length := by
  have hsc := trotterCommutatorScalingCorrected I xs H p r hp hr hanti hH hmatch t
  exact hsc.2.1

/-- The specification collecting smoothness, derivative-level decomposition, Taylor integral
remainders, and the level grouping of the conjugation remainder. -/
structure Clause49Spec : Prop where

  smooth : ∀ {I : Type} [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ), ContDiff ℝ ∞ (pfConjWord xs B)

  levelDecomposition : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (t : ℝ),
    HasDerivAt (pfConjWord xs B) (orderedLevelSum xs B t) t

  integralRemainder : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (hp : 0 < p) (t : ℝ),
    pfConjWord xs B t - pfConjTrunc xs B p t =
      ∫ τ in 0..t, (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        iteratedDeriv p (pfConjWord xs B) τ)

  levelGrouping : ∀ {I : Type} [Fintype I] (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (t : ℝ),
    groupedIntegralRemainder xs B p t =
      ∑ k ∈ Finset.Icc 1 xs.length, groupedIntegralLevel xs B p k t

  outerInner : ∀ {I : Type} [Fintype I] (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p k : ℕ) (t : ℝ),
    groupedIntegralLevel xs B p k t =
      ∑ q ∈ groupedCompositions p k,
        pfConjWord (xs.take (xs.length - k))
          (∫ τ in 0..t, (groupedScalar p q t τ) •
            pfConjWord [srcGen xs k] (pfNestedCommList (B :: groupedRepetition xs q)) τ) t

/-- Establishes the smoothness, derivative, and integral-remainder statements collected in
`Clause49Spec`. -/
theorem stageB_trotter_commutator_clause49 : Clause49Spec where
  smooth := pfConjWord_contDiff
  levelDecomposition := pfConjWord_hasDerivAt_levelSum
  integralRemainder := pfConjWord_taylor_integral_remainder
  levelGrouping := groupedIntegralRemainder_eq_level_sum
  outerInner := groupedIntegralLevel_outer_inner

/-- The specification collecting raw segment selection, tolerance guarantees for matched
skew-Hermitian words, word length, and label visits. -/
structure Clause50Spec : Prop where

  segmentSelectorDominates : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (p : ℕ) (hp : 1 ≤ p) (t ε : ℝ),
    ((rawTrotterSegments xs p t ε : ℝ) ^ p) ≥ rawTrotterBudgetFactor xs p t ε

  epsilonError : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p r : ℕ) (hp : 1 ≤ p) (hr : 0 < r)
    (hanti : ∀ X ∈ xs, Xᴴ = -X) (hH : Hᴴ = -H)
    (hmatch : ∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n)
    (t ε : ℝ) (hε : 0 < ε)
    (hseg : (r : ℝ) ^ p ≥ rawTrotterBudgetFactor xs p t ε),
    ‖(List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten.prod
        - NormedSpace.exp (t • H)‖ ≤ ε

  visitLedger : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p r : ℕ) (hp : 1 ≤ p) (hr : 0 < r)
    (hanti : ∀ X ∈ xs, Xᴴ = -X) (hH : Hᴴ = -H)
    (hmatch : ∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n)
    (t : ℝ),
    (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten.length
      = r * xs.length

  labelVisits : ∀ {I : Type} [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    {m : ℕ} (lab : Fin xs.length → Fin m) (r : ℕ) (j : Fin m),
    segmentLabelVisits xs lab r j =
      r * ((List.finRange xs.length).filter (fun i => lab i = j)).length

/-- Establishes the segment-selection, error, and visit-count statements collected in
`Clause50Spec`. -/
theorem stageB_trotter_commutator_clause50 : Clause50Spec where
  segmentSelectorDominates := rawTrotterSegments_pow_ge
  epsilonError := clause50_epsilon_error
  visitLedger := clause50_visit_ledger
  labelVisits := segment_visits_eq

/-- The specification collecting the two-generator first- and second-order coefficients, the
sharp half-commutator error constant, and the raw-budget comparison. -/
structure Clause51Spec : Prop where

  firstOrderAgrees : ∀ {I : Type} [Fintype I] [DecidableEq I] (X Y : Matrix I I ℂ),
    suzukiSeries [X, Y] 1 = X + Y

  secondOrderDeviates : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ),
    suzukiSeries [X, Y] 2 - (((2 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2 =
      (1 / 2 : ℝ) • pfComm X Y

  secondOrderNorm : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ),
    ‖suzukiSeries [X, Y] 2 - (((2 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2‖
      = (1 / 2 : ℝ) * ‖pfComm X Y‖

  constantOptimal : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (hne : pfComm X Y ≠ 0) (c : ℝ) (hc : 0 < c),
    ‖suzukiSeries [X, Y] 2 - (((2 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2‖
        ≤ c * ‖pfComm X Y‖ → (1 / 2 : ℝ) ≤ c

  rawBudgetSlack : ∀ {I : Type} [Fintype I] [DecidableEq I] (X Y : Matrix I I ℂ),
    ‖pfComm X Y‖ ≤ pfCommAlphaSelf [X, Y] 2

/-- Establishes the coefficient identities, optimal constant, and budget comparison collected in
`Clause51Spec`. -/
theorem stageB_trotter_commutator_clause51 : Clause51Spec where
  firstOrderAgrees := clause51_first_order_agrees
  secondOrderDeviates := clause51_second_order_deviates
  secondOrderNorm := clause51_second_order_norm
  constantOptimal := clause51_constant_optimal
  rawBudgetSlack := clause51_raw_budget_slack

end

end Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExt
