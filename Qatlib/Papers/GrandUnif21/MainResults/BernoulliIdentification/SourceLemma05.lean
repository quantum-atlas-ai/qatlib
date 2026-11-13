/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Identifying one of two Bernoulli distributions

This file formalizes Lemma 5 of [Martyn et al., 2021][MartynEtAl2021] (Section III, around
Eq. (73)): given two Bernoulli laws on `Bool` with means `0 ≤ a < b ≤ 1`, an unknown law
chosen from the two can be identified with confidence at least `1 - δ` under both hypotheses
using `O((a + b) / (b - a)² · log(1 / δ))` i.i.d. samples.

Unlike Hoeffding's `O(1 / (b - a)² · log(1 / δ))` bound, the `(a + b)` numerator factor
captures the sharper small-mean Chernoff scaling as `a + b → 0`. We prove the result with the
explicit constant `C = 32` using a midpoint threshold test at `(a + b) / 2` and quadratic
exponential moment bounds under `twoPoint`.

## Main statements

* `twoPoint`: the Bernoulli `FinDist Bool` with parameter `p ∈ [0, 1]`.
* `source_lemma5_bernoulli_identification`: sample complexity bound
  `C · ((b + a) / (b - a)²) · log(1 / δ)` for symmetric hypothesis testing between two
  Bernoulli laws (Lemma 5).

## References

* [Martyn et al., 2021][MartynEtAl2021]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.BernoulliIdentification

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-- The Bernoulli law on `Bool` with mass `p` of `true` and `1 - p` of `false`. -/
def twoPoint (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinDist Bool where
  prob b := Bool.rec (1 - p) p b
  nonneg b := by
    cases b
    · exact sub_nonneg.mpr hp1
    · exact hp0
  sum_one := by
    rw [Fintype.sum_bool]
    ring

/-- The mass of `true` under `twoPoint p` is `p`. -/
theorem twoPoint_prob_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (twoPoint p hp0 hp1).prob true = p := rfl

/-- The expected value of the `{0, 1}` indicator under `twoPoint p` is `p`. -/
theorem twoPoint_expect_indicator (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FinDist.expect (twoPoint p hp0 hp1) (fun b => if b then (1 : ℝ) else 0) = p := by
  simp [FinDist.expect, twoPoint]

/-- The empirical mean of `n` Bernoulli samples. -/
def sampleMean {n : ℕ} (ω : Fin n → Bool) : ℝ :=
  (∑ i, if ω i then (1 : ℝ) else 0) / (n : ℝ)

/-- Quadratic upper bound `exp t ≤ 1 + t + 2 t²` for `t ≤ 1/2`. -/
private lemma exp_le_one_add_add_two_sq {t : ℝ} (ht1 : t ≤ 1 / 2) :
    Real.exp t ≤ 1 + t + 2 * t ^ 2 := by
  have h1 : 1 - t ≤ Real.exp (-t) := by
    have h := Real.add_one_le_exp (-t)
    linarith
  have hmul : (1 - t) * Real.exp t ≤ 1 := by
    calc (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
      _ = Real.exp (-t + t) := (Real.exp_add (-t) t).symm
      _ = 1 := by simp
  have hpoly : 1 ≤ (1 - t) * (1 + t + 2 * t ^ 2) := by
    have hsq : 0 ≤ t ^ 2 * (1 - 2 * t) := mul_nonneg (sq_nonneg t) (by linarith)
    nlinarith
  have hpos : 0 < 1 - t := by linarith
  exact le_of_mul_le_mul_left (hmul.trans hpoly) hpos

/-- Quadratic upper bound `exp (-t) ≤ 1 - t + t²` for `t ≥ 0`. -/
private lemma exp_neg_le_one_sub_add_sq {t : ℝ} (ht0 : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 := by
  have h1 : 1 + t ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith
  have hmul : (1 + t) * Real.exp (-t) ≤ 1 := by
    calc (1 + t) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-t)).le
      _ = Real.exp (t + -t) := (Real.exp_add t (-t)).symm
      _ = 1 := by simp
  have hpoly : 1 ≤ (1 + t) * (1 - t + t ^ 2) := by
    have hcube : 0 ≤ t ^ 3 := pow_nonneg ht0 3
    nlinarith
  have hpos : 0 < 1 + t := by linarith
  exact le_of_mul_le_mul_left (hmul.trans hpoly) hpos

/-- Partition of `eventMass` across a Boolean test `g ω = false` and `g ω = true`. -/
private lemma eventMass_bool_partition {X : Type*} [Fintype X] (p : FinDist X) (g : X → Bool) :
    eventMass p (fun ω => g ω = false) + eventMass p (fun ω => g ω = true) = 1 := by
  classical
  unfold eventMass
  rw [← Finset.sum_union]
  · have huniv : (Finset.univ.filter (fun ω => g ω = false)) ∪
        (Finset.univ.filter (fun ω => g ω = true)) = Finset.univ := by
      ext ω
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases g ω <;> simp
    rw [huniv]
    exact p.sum_one
  · rw [Finset.disjoint_left]
    intro ω h1 h2
    have hf := (Finset.mem_filter.mp h1).2
    have ht := (Finset.mem_filter.mp h2).2
    rw [hf] at ht
    exact Bool.false_ne_true ht

/-- Upper-tail Chernoff bound at the midpoint `(a + b) / 2` under the `a`-law. -/
private lemma bernoulli_upper_tail_bound (a b : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (n : ℕ) :
    let pa := independent (fun _ : Fin n => twoPoint a ha0 (le_trans hab.le hb1))
    let S : (Fin n → Bool) → ℝ := fun ω => ∑ i, if ω i then (1 : ℝ) else 0
    eventMass pa (fun ω => (n : ℝ) * ((a + b) / 2) ≤ S ω) ≤
      Real.exp (-((n : ℝ) * (b - a) ^ 2 / (32 * (a + b)))) := by
  intro pa S
  have hab_pos : 0 < a + b := by linarith
  let t : ℝ := (b - a) / (8 * (a + b))
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by positivity)
  have ht_half : t ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hcher := chernoff_upper pa S ((n : ℝ) * ((a + b) / 2)) t ht0
  have hmgf_coord :
      (twoPoint a ha0 (le_trans hab.le hb1)).expect
        (fun x => Real.exp (t * (if x then (1 : ℝ) else 0))) ≤
        Real.exp (a * t + 2 * (a + b) * t ^ 2) := by
    have hexp_eval :
        (twoPoint a ha0 (le_trans hab.le hb1)).expect
          (fun x => Real.exp (t * (if x then (1 : ℝ) else 0))) =
          1 + a * (Real.exp t - 1) := by
      simp [FinDist.expect, twoPoint]
      ring
    rw [hexp_eval]
    have hquad := exp_le_one_add_add_two_sq ht_half
    have hstep1 : 1 + a * (Real.exp t - 1) ≤ 1 + (a * t + 2 * (a + b) * t ^ 2) := by
      have h1 : a * (Real.exp t - 1) ≤ a * (t + 2 * t ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) ha0
      have h2 : a * t ^ 2 ≤ (a + b) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
      linarith
    exact hstep1.trans (by linarith [Real.add_one_le_exp (a * t + 2 * (a + b) * t ^ 2)])
  have hmgf_prod :
      pa.expect (fun ω => Real.exp (t * S ω)) ≤
        Real.exp ((n : ℝ) * (a * t + 2 * (a + b) * t ^ 2)) := by
    have hrew : (fun ω : Fin n → Bool => Real.exp (t * S ω)) =
        fun ω => ∏ i : Fin n, Real.exp (t * (if ω i then (1 : ℝ) else 0)) := by
      ext ω
      simp only [S, Finset.mul_sum, Real.exp_sum]
    dsimp only [pa]
    rw [hrew,
      independent_expect_product (f := fun (_ : Fin n) (x : Bool) =>
        Real.exp (t * (if x then (1 : ℝ) else 0)))]
    calc (∏ _i : Fin n, (twoPoint a ha0 (le_trans hab.le hb1)).expect
            (fun x => Real.exp (t * (if x then (1 : ℝ) else 0))))
        = ((twoPoint a ha0 (le_trans hab.le hb1)).expect
            (fun x => Real.exp (t * (if x then (1 : ℝ) else 0)))) ^ n := by
          rw [Finset.prod_const, Finset.card_fin]
      _ ≤ (Real.exp (a * t + 2 * (a + b) * t ^ 2)) ^ n := by
          refine pow_le_pow_left₀ ?_ hmgf_coord n
          exact Finset.sum_nonneg fun x _ =>
            mul_nonneg ((twoPoint a ha0 (le_trans hab.le hb1)).nonneg x) (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) * (a * t + 2 * (a + b) * t ^ 2)) :=
          (Real.exp_nat_mul _ n).symm
  calc eventMass pa (fun ω => (n : ℝ) * ((a + b) / 2) ≤ S ω)
      ≤ Real.exp (-(t * ((n : ℝ) * ((a + b) / 2)))) *
          pa.expect (fun ω => Real.exp (t * S ω)) := hcher
    _ ≤ Real.exp (-(t * ((n : ℝ) * ((a + b) / 2)))) *
          Real.exp ((n : ℝ) * (a * t + 2 * (a + b) * t ^ 2)) :=
        mul_le_mul_of_nonneg_left hmgf_prod (Real.exp_pos _).le
    _ = Real.exp (-(t * ((n : ℝ) * ((a + b) / 2))) +
          (n : ℝ) * (a * t + 2 * (a + b) * t ^ 2)) :=
        (Real.exp_add _ _).symm
    _ = Real.exp (-((n : ℝ) * (b - a) ^ 2 / (32 * (a + b)))) := by
        congr 1
        simp only [t]
        field_simp
        ring

/-- Lower-tail Chernoff bound below the midpoint `(a + b) / 2` under the `b`-law. -/
private lemma bernoulli_lower_tail_bound (a b : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (n : ℕ) :
    let pb := independent (fun _ : Fin n => twoPoint b (le_trans ha0 hab.le) hb1)
    let S : (Fin n → Bool) → ℝ := fun ω => ∑ i, if ω i then (1 : ℝ) else 0
    eventMass pb (fun ω => -((n : ℝ) * ((a + b) / 2)) ≤ -S ω) ≤
      Real.exp (-((n : ℝ) * (b - a) ^ 2 / (32 * (a + b)))) := by
  intro pb S
  have hab_pos : 0 < a + b := by linarith
  have hb0 : 0 ≤ b := le_trans ha0 hab.le
  let t : ℝ := (b - a) / (8 * (a + b))
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by positivity)
  have hcher := chernoff_upper pb (fun ω => -S ω) (-((n : ℝ) * ((a + b) / 2))) t ht0
  have hmgf_coord :
      (twoPoint b hb0 hb1).expect
        (fun x => Real.exp (t * -(if x then (1 : ℝ) else 0))) ≤
        Real.exp (-b * t + 2 * (a + b) * t ^ 2) := by
    have hexp_eval :
        (twoPoint b hb0 hb1).expect
          (fun x => Real.exp (t * -(if x then (1 : ℝ) else 0))) =
          1 + b * (Real.exp (-t) - 1) := by
      simp [FinDist.expect, twoPoint]
      ring
    rw [hexp_eval]
    have hquad := exp_neg_le_one_sub_add_sq ht0
    have hstep1 : 1 + b * (Real.exp (-t) - 1) ≤ 1 + (-b * t + 2 * (a + b) * t ^ 2) := by
      have h1 : b * (Real.exp (-t) - 1) ≤ b * (-t + t ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hb0
      have h2 : b * t ^ 2 ≤ 2 * (a + b) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
      linarith
    exact hstep1.trans (by linarith [Real.add_one_le_exp (-b * t + 2 * (a + b) * t ^ 2)])
  have hmgf_prod :
      pb.expect (fun ω => Real.exp (t * -S ω)) ≤
        Real.exp ((n : ℝ) * (-b * t + 2 * (a + b) * t ^ 2)) := by
    have hrew : (fun ω : Fin n → Bool => Real.exp (t * -S ω)) =
        fun ω => ∏ i : Fin n, Real.exp (t * -(if ω i then (1 : ℝ) else 0)) := by
      ext ω
      have hsum : t * -S ω = ∑ i : Fin n, t * -(if ω i then (1 : ℝ) else 0) := by
        simp only [S, ← Finset.sum_neg_distrib, Finset.mul_sum]
      rw [hsum, Real.exp_sum]
    dsimp only [pb]
    rw [hrew,
      independent_expect_product (f := fun (_ : Fin n) (x : Bool) =>
        Real.exp (t * -(if x then (1 : ℝ) else 0)))]
    calc (∏ _i : Fin n, (twoPoint b hb0 hb1).expect
            (fun x => Real.exp (t * -(if x then (1 : ℝ) else 0))))
        = ((twoPoint b hb0 hb1).expect
            (fun x => Real.exp (t * -(if x then (1 : ℝ) else 0)))) ^ n := by
          rw [Finset.prod_const, Finset.card_fin]
      _ ≤ (Real.exp (-b * t + 2 * (a + b) * t ^ 2)) ^ n := by
          refine pow_le_pow_left₀ ?_ hmgf_coord n
          exact Finset.sum_nonneg fun x _ =>
            mul_nonneg ((twoPoint b hb0 hb1).nonneg x) (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) * (-b * t + 2 * (a + b) * t ^ 2)) :=
          (Real.exp_nat_mul _ n).symm
  calc eventMass pb (fun ω => -((n : ℝ) * ((a + b) / 2)) ≤ -S ω)
      ≤ Real.exp (-(t * -((n : ℝ) * ((a + b) / 2)))) *
          pb.expect (fun ω => Real.exp (t * -S ω)) := hcher
    _ ≤ Real.exp (-(t * -((n : ℝ) * ((a + b) / 2)))) *
          Real.exp ((n : ℝ) * (-b * t + 2 * (a + b) * t ^ 2)) :=
        mul_le_mul_of_nonneg_left hmgf_prod (Real.exp_pos _).le
    _ = Real.exp (-(t * -((n : ℝ) * ((a + b) / 2))) +
          (n : ℝ) * (-b * t + 2 * (a + b) * t ^ 2)) :=
        (Real.exp_add _ _).symm
    _ = Real.exp (-((n : ℝ) * (b - a) ^ 2 / (32 * (a + b)))) := by
        congr 1
        simp only [t]
        field_simp
        ring

/-- **Lemma 5** ([Martyn et al., 2021][MartynEtAl2021], Section III, Eq. (73)): there is an
absolute constant `C > 0` such that for all `0 ≤ a < b ≤ 1` and `δ ∈ (0, 1)`,
`C ((b + a) / (b - a)²) log(1 / δ)` samples suffice to decide, with confidence at least
`1 - δ` under both hypotheses, whether an unknown Bernoulli law has mean `a` or mean `b`. -/
theorem source_lemma5_bernoulli_identification :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b δ : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
        (_hδ0 : 0 < δ) (_hδ1 : δ < 1) (n : ℕ),
        C * ((b + a) / (b - a) ^ 2) * Real.log (1 / δ) ≤ (n : ℝ) →
        ∃ test : (Fin n → Bool) → Bool,
          eventMass
              (independent (fun _ : Fin n =>
                twoPoint a ha0 (le_trans (le_of_lt hab) hb1)))
              (fun ω => test ω = false) ≥ 1 - δ ∧
          eventMass
              (independent (fun _ : Fin n =>
                twoPoint b (le_trans ha0 (le_of_lt hab)) hb1))
              (fun ω => test ω = true) ≥ 1 - δ := by
  refine ⟨32, by norm_num, ?_⟩
  intro a b δ ha0 hab hb1 hδ0 _hδ1 n hn
  let S : (Fin n → Bool) → ℝ := fun ω => ∑ i, if ω i then (1 : ℝ) else 0
  let test : (Fin n → Bool) → Bool := fun ω => decide ((n : ℝ) * ((a + b) / 2) ≤ S ω)
  have hab_pos : 0 < a + b := by linarith
  have hdiff_pos : 0 < b - a := by linarith
  have hexp_le_δ : Real.exp (-((n : ℝ) * (b - a) ^ 2 / (32 * (a + b)))) ≤ δ := by
    have hlog : Real.log (1 / δ) ≤ (n : ℝ) * (b - a) ^ 2 / (32 * (a + b)) := by
      have hpos : 0 < (b - a) ^ 2 / (32 * (a + b)) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hn hpos.le
      have hsimp : (b - a) ^ 2 / (32 * (a + b)) *
          (32 * ((b + a) / (b - a) ^ 2) * Real.log (1 / δ)) = Real.log (1 / δ) := by
        have hba : b + a = a + b := add_comm b a
        rw [hba]
        field_simp
      rwa [hsimp, mul_comm ((b - a) ^ 2 / (32 * (a + b))) (n : ℝ), ← mul_div_assoc] at hmul
    have hlog_inv : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    have hneg : -((n : ℝ) * (b - a) ^ 2 / (32 * (a + b))) ≤ Real.log δ := by
      linarith
    calc Real.exp (-((n : ℝ) * (b - a) ^ 2 / (32 * (a + b))))
        ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hneg
      _ = δ := Real.exp_log hδ0
  refine ⟨test, ?_, ?_⟩
  · let pa := independent (fun _ : Fin n => twoPoint a ha0 (le_trans (le_of_lt hab) hb1))
    have hpart := eventMass_bool_partition pa test
    have htrue_le : eventMass pa (fun ω => test ω = true) ≤ δ := by
      calc eventMass pa (fun ω => test ω = true)
          ≤ eventMass pa (fun ω => (n : ℝ) * ((a + b) / 2) ≤ S ω) := by
            refine eventMass_mono pa _ _ fun ω h => ?_
            exact of_decide_eq_true h
        _ ≤ Real.exp (-((n : ℝ) * (b - a) ^ 2 / (32 * (a + b)))) :=
            bernoulli_upper_tail_bound a b ha0 hab hb1 n
        _ ≤ δ := hexp_le_δ
    linarith
  · let pb := independent (fun _ : Fin n => twoPoint b (le_trans ha0 (le_of_lt hab)) hb1)
    have hpart := eventMass_bool_partition pb test
    have hfalse_le : eventMass pb (fun ω => test ω = false) ≤ δ := by
      calc eventMass pb (fun ω => test ω = false)
          ≤ eventMass pb (fun ω => -((n : ℝ) * ((a + b) / 2)) ≤ -S ω) := by
            refine eventMass_mono pb _ _ fun ω h => ?_
            have hlt : ¬ (n : ℝ) * ((a + b) / 2) ≤ S ω := of_decide_eq_false h
            linarith
        _ ≤ Real.exp (-((n : ℝ) * (b - a) ^ 2 / (32 * (a + b)))) :=
            bernoulli_lower_tail_bound a b ha0 hab hb1 n
        _ ≤ δ := hexp_le_δ
    linarith

end Qatlib.Papers.GrandUnif21.MainResults.BernoulliIdentification
