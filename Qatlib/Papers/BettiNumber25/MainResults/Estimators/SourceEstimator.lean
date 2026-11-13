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
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Papers.BettiNumber25.MainResults.TraceEstimation.SourceBernoulliTrace
import Qatlib.Papers.BettiNumber25.MainResults.SpectralTrace.SourceSpectralTrace

set_option backward.isDefEq.respectTransparency false

/-!
# `(ε, η)`-Estimator Guarantees for Betti Number Algorithms

This module formalizes the `(ε, η)`-estimator guarantees for the four quantum
and classical Monte Carlo Betti-number estimation algorithms of Akhalwaya et al.
The output `β̂_k` lies within additive error `ε` of the normalized Betti number
`β_k / |S_k|` with probability at least `1 - η`, established via weighted
Hoeffding concentration (`independent_weighted_hoeffding`) and finite union
bounds over independent product laws.

## Main statements

* `theorem_4_4_estimator`: Algorithm 3's Chebyshev estimate is an
  `(ε, η)`-estimator (Theorem 4.4).
* `lemma_5_2_power_estimator`: the classical power-trace sample average of
  Algorithm 4 is an `(ε, η)`-estimator (Lemma 5.2).
* `lemma_5_6_reflected_estimator`: the classical Chebyshev combination of `d`
  independent power estimates in Algorithm 5 is an `(ε, η)`-estimator
  (Lemma 5.6).
* `theorem_6_2_power_quantum_estimator`: the quantum power estimate of
  Algorithm 6 is an `(ε, η)`-estimator (Theorem 6.2).

## References

* [Akhalwaya et al., 2025][AkhalwayaEtAl2025], Theorem 4.4, Lemma 5.2,
  Lemma 5.6, and Theorem 6.2.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.BettiNumber25.MainResults.TraceEstimation
open Qatlib.Papers.BettiNumber25.MainResults.SpectralTrace
open scoped BigOperators

namespace Qatlib.Papers.BettiNumber25.MainResults.Estimators
open Qatlib.Papers.BettiNumber25.MainResults

/-- Complement formula for the mass of an event. -/
theorem eventMass_not {X : Type*} [Fintype X] (p : FinDist X) (E : X → Prop)
    [DecidablePred E] :
    eventMass p (fun x => ¬ E x) = 1 - eventMass p E := by
  have hsplit : eventMass p E + eventMass p (fun x => ¬ E x) = 1 := by
    rw [eventMass, eventMass,
      Finset.sum_filter_add_sum_filter_not (Finset.univ) E (fun x => p.prob x), p.sum_one]
  linarith

/-- The mass of the always-true event is `1`. -/
theorem eventMass_true {X : Type*} [Fintype X] (p : FinDist X) :
    eventMass p (fun _ => True) = 1 := by
  have h : Finset.univ.filter (fun _ : X => True) = Finset.univ := by
    ext x; simp
  rw [eventMass, h, p.sum_one]

/-- The polynomial `a₀ + a₁X + ⋯ + a_dX^d` attached to the coefficients of
Algorithm 3 (Eq. (10)). -/
def polyOfCoeffs (a : ℕ → ℝ) (d : ℕ) : Polynomial ℝ :=
  ∑ j : Fin (d + 1), Polynomial.C (a j.val) * Polynomial.X ^ j.val

/-- Evaluation of `polyOfCoeffs`. -/
theorem polyOfCoeffs_eval (a : ℕ → ℝ) (d : ℕ) (x : ℝ) :
    (polyOfCoeffs a d).eval x = ∑ j : Fin (d + 1), a j.val * x ^ j.val := by
  unfold polyOfCoeffs
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- `a₀ + ∑_{j<d} a_{j+1} x^{j+1} = p(x)` for `p = polyOfCoeffs a d`. -/
theorem sum_shift_eq (a : ℕ → ℝ) (d : ℕ) (x : ℝ) :
    ∑ j : Fin d, a (j.val + 1) * x ^ (j.val + 1)
      = (polyOfCoeffs a d).eval x - a 0 := by
  rw [polyOfCoeffs_eval, Fin.sum_univ_succ (fun j : Fin (d + 1) => a j.val * x ^ j.val)]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
  rw [add_sub_cancel_left]

/-- Uniform weight `a_{j+1}/q` attached to the `(i,j)`-th sample of Algorithm 3. -/
def powWeight {d : ℕ} (a : ℕ → ℝ) (q : ℕ) : Fin q × Fin d → ℝ :=
  fun p => a (p.2.val + 1) / (q : ℝ)

/-- Product law of the `q × d` Bernoulli samples of Algorithm 3, with per-column
mean `ν j`. -/
def powLaw (q d : ℕ) (ν : Fin d → ℝ) (hν0 : ∀ j, 0 ≤ ν j) (hν1 : ∀ j, ν j ≤ 1) :
    FinDist (Fin q × Fin d → Bool) :=
  independent (I := Fin q × Fin d)
    (fun p => bernoulliLaw (ν p.2) (hν0 p.2) (hν1 p.2))

/-- Algorithm 3's estimate `β̂_k = a₀ + ∑_{i,j} (a_{j+1}/q) x_{ij}`. -/
def betaHatPow (a : ℕ → ℝ) (q d : ℕ) (ω : Fin q × Fin d → Bool) : ℝ :=
  a 0 + weightedSum (powWeight (d := d) a q) (fun _ b => boolIndicator b) ω

/-- `∑_{i,j} (a_{j+1}/q) ν_j = ∑_j a_{j+1} ν_j`. -/
theorem sum_powWeight_expect {d : ℕ} (a : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (ν : Fin d → ℝ) :
    ∑ p : Fin q × Fin d, powWeight (d := d) a q p * ν p.2
      = ∑ j : Fin d, a (j.val + 1) * ν j := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [powWeight]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hqne : (q : ℝ) ≠ 0 := by positivity
  field_simp

/-- The Hoeffding denominator of Algorithm 3's weighted sum. -/
theorem sum_weight_sq {d : ℕ} (a : ℕ → ℝ) (q : ℕ) (hq : 0 < q) :
    ∑ p : Fin q × Fin d, (powWeight (d := d) a q p) ^ 2 * ((1 : ℝ) - 0) ^ 2
      = (q : ℝ)⁻¹ * ∑ j : Fin d, (a (j.val + 1)) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [powWeight, sub_zero, one_pow, mul_one, div_pow]
  have hqne : (q : ℝ) ≠ 0 := by positivity
  calc ∑ j : Fin d, ∑ _i : Fin q, (a (j.val + 1)) ^ 2 / (q : ℝ) ^ 2
      = ∑ j : Fin d, (q : ℝ) * ((a (j.val + 1)) ^ 2 / (q : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ j : Fin d, (q : ℝ)⁻¹ * (a (j.val + 1)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        field_simp
    _ = (q : ℝ)⁻¹ * ∑ j : Fin d, (a (j.val + 1)) ^ 2 := by
        rw [Finset.mul_sum]

/-- Hoeffding bound for Algorithm 3's weighted Bernoulli sum. -/
theorem hoeffding_pow {d : ℕ} (a : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (ν : Fin d → ℝ) (hν0 : ∀ j, 0 ≤ ν j) (hν1 : ∀ j, ν j ≤ 1)
    (u : ℝ) (hu : 0 < u) (hS : 0 < ∑ j : Fin d, (a (j.val + 1)) ^ 2) :
    eventMass (powLaw q d ν hν0 hν1)
        (fun ω => u ≤ |weightedSum (powWeight (d := d) a q)
          (fun _ b => boolIndicator b) ω - ∑ j : Fin d, a (j.val + 1) * ν j|)
      ≤ 2 * Real.exp (-2 * u ^ 2 / ((q : ℝ)⁻¹ * ∑ j : Fin d, (a (j.val + 1)) ^ 2)) := by
  have hS' : 0 < ∑ p : Fin q × Fin d,
      (powWeight (d := d) a q p) ^ 2 * ((1 : ℝ) - 0) ^ 2 := by
    rw [sum_weight_sq a q hq]
    positivity
  have h := independent_weighted_hoeffding (I := Fin q × Fin d) (X := fun _ => Bool)
    (fun p => bernoulliLaw (ν p.2) (hν0 p.2) (hν1 p.2))
    (powWeight (d := d) a q) (fun _ b => boolIndicator b)
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) u
    (fun _ => by norm_num) (fun _ b => by
      cases b <;> simp [boolIndicator, Set.mem_Icc]) hu hS'
  have hexp : (independent (I := Fin q × Fin d)
      (fun p => bernoulliLaw (ν p.2) (hν0 p.2) (hν1 p.2))).expect
      (weightedSum (powWeight (d := d) a q) (fun _ b => boolIndicator b))
        = ∑ j : Fin d, a (j.val + 1) * ν j := by
    rw [ProbabilityInterfaces.independent_weighted_expectation]
    have h1 : ∀ p : Fin q × Fin d,
        (bernoulliLaw (ν p.2) (hν0 p.2) (hν1 p.2)).expect
          (fun b => boolIndicator b) = ν p.2 :=
      fun p => bernoulli_expect_indicator _ _ _
    simp only [h1]
    exact sum_powWeight_expect a q hq ν
  rw [hexp, sum_weight_sq a q hq] at h
  simpa only [powLaw] using h

/-- **Theorem 4.4**: let `p(x) = a₀ + ⋯ + a_d x^d` be an `(ε/2, δ)`-filter for
the normalized Laplacian (`p(0) = 1`, `|p| < ε / 2` on `[δ, 1]`), and let
`ν_j = (1 / N) ∑_i λ_i^{j+1}` be the normalized power traces. Algorithm 3's
estimate `β̂_k = a₀ + ∑_{i,j} (a_{j+1} / q) x_{ij}` is an `(ε, η)`-estimator of
`β_k / N` whenever `q ≥ 2 log(2 / η) (∑_j a_{j+1}²) / ε²`. -/
theorem theorem_4_4_estimator
    (ε η δ : ℝ) (hε : 0 < ε) (hη : 0 < η)
    {N : ℕ} (hN : 0 < N) (β : ℕ)
    (lam : Fin N → ℝ) (hspec : ∀ i, lam i ≠ 0 → lam i ∈ Set.Icc δ 1)
    (a : ℕ → ℝ) (d q : ℕ) (hq : 0 < q) (ha0 : a 0 = 1)
    (hp : ∀ x ∈ Set.Icc δ 1, |(polyOfCoeffs a d).eval x| < ε / 2)
    (hβ : (Finset.univ.filter (fun i => lam i = 0)).card = β)
    (hqbound : 2 * Real.log (2 / η) * (∑ j : Fin d, (a (j.val + 1)) ^ 2)
      ≤ ε ^ 2 * (q : ℝ))
    (ν : Fin d → ℝ) (hν0 : ∀ j, 0 ≤ ν j) (hν1 : ∀ j, ν j ≤ 1)
    (hνdef : ∀ j, ν j = (1 / (N : ℝ)) * ∑ i, (lam i) ^ (j.val + 1)) :
    1 - η ≤ eventMass (powLaw q d ν hν0 hν1)
      (fun ω => |betaHatPow a q d ω - (β : ℝ) / (N : ℝ)| ≤ ε) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  set P := powLaw q d ν hν0 hν1 with hP
  set W : (Fin q × Fin d → Bool) → ℝ :=
    weightedSum (powWeight (d := d) a q) (fun _ b => boolIndicator b) with hW
  set M : ℝ := ∑ j : Fin d, a (j.val + 1) * ν j with hM
  have hp0 : (polyOfCoeffs a d).eval 0 = 1 := by
    rw [polyOfCoeffs_eval]
    have hz : ∀ j : Fin (d + 1), a j.val * (0 : ℝ) ^ j.val = if j.val = 0 then a 0 else 0 := by
      intro j
      rcases Nat.eq_zero_or_pos j.val with h | h
      · rw [h]; simp
      · rw [zero_pow (Nat.ne_of_gt h), mul_zero]; simp [h.ne']
    rw [Finset.sum_congr rfl (fun j _ => hz j)]
    simp [ha0]
  have htrace : |(∑ i, (polyOfCoeffs a d).eval (lam i)) / (N : ℝ) - (β : ℝ) / (N : ℝ)|
      < ε / 2 := by
    have := lemma_4_1_filter_trace (polyOfCoeffs a d) (ε / 2) δ (by linarith) hp0 hp lam hspec
    rwa [hβ] at this
  have hbridge : M = (∑ i, (polyOfCoeffs a d).eval (lam i)) / (N : ℝ) - a 0 := by
    rw [hM]
    have hstep1 : ∑ j : Fin d, a (j.val + 1) * ν j
        = (1 / (N : ℝ)) * ∑ j : Fin d, ∑ i, a (j.val + 1) * (lam i) ^ (j.val + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hνdef j, ← mul_assoc, mul_comm (a _) (1 / (N : ℝ)), mul_assoc]
      rw [Finset.mul_sum]
    rw [hstep1, Finset.sum_comm]
    have hi : ∀ i : Fin N, ∑ j : Fin d, a (j.val + 1) * (lam i) ^ (j.val + 1)
        = (polyOfCoeffs a d).eval (lam i) - a 0 := fun i => sum_shift_eq a d (lam i)
    rw [Finset.sum_congr rfl (fun i _ => hi i)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hSnn : 0 ≤ ∑ j : Fin d, (a (j.val + 1)) ^ 2 :=
    Finset.sum_nonneg (fun (j : Fin d) _ => sq_nonneg (a (j.val + 1)))
  rcases lt_or_eq_of_le hSnn with hS | hS0
  · have hhoef := hoeffding_pow a q hq ν hν0 hν1 (ε / 2) (by linarith) hS
    have hge : Real.log (2 / η)
        ≤ ε ^ 2 * (q : ℝ) / (2 * ∑ j : Fin d, (a (j.val + 1)) ^ 2) := by
      rw [le_div_iff₀ (by nlinarith [hS])]
      nlinarith [hqbound]
    have harg : -2 * (ε / 2) ^ 2 / ((q : ℝ)⁻¹ * ∑ j : Fin d, (a (j.val + 1)) ^ 2)
        = -(ε ^ 2 * (q : ℝ) / (2 * ∑ j : Fin d, (a (j.val + 1)) ^ 2)) := by
      field_simp
    have hexpval : Real.exp (-Real.log (2 / η)) = η / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have hbound : 2 * Real.exp
        (-2 * (ε / 2) ^ 2 / ((q : ℝ)⁻¹ * ∑ j : Fin d, (a (j.val + 1)) ^ 2)) ≤ η := by
      rw [harg]
      have hle : -(ε ^ 2 * (q : ℝ) / (2 * ∑ j : Fin d, (a (j.val + 1)) ^ 2))
          ≤ -Real.log (2 / η) := neg_le_neg hge
      calc 2 * Real.exp (-(ε ^ 2 * (q : ℝ) / (2 * ∑ j : Fin d, (a (j.val + 1)) ^ 2)))
          ≤ 2 * Real.exp (-Real.log (2 / η)) := by
            linarith [Real.exp_le_exp.mpr hle]
        _ = η := by rw [hexpval]; ring
    have hmass : eventMass P (fun ω => ε / 2 ≤ |W ω - M|) ≤ η := by
      rw [hP, hW, hM]
      exact hhoef.trans hbound
    have hstep1 : 1 - η ≤ eventMass P (fun ω => |W ω - M| ≤ ε / 2) := by
      have hcompl : eventMass P (fun ω => ¬ (ε / 2 ≤ |W ω - M|))
          = 1 - eventMass P (fun ω => ε / 2 ≤ |W ω - M|) := eventMass_not P _
      have hmono : eventMass P (fun ω => ¬ (ε / 2 ≤ |W ω - M|))
          ≤ eventMass P (fun ω => |W ω - M| ≤ ε / 2) := by
        apply eventMass_mono
        intro ω hω
        exact le_of_lt (not_le.mp hω)
      linarith
    refine le_trans hstep1 ?_
    apply eventMass_mono
    intro ω hω
    have hβeq : betaHatPow a q d ω - (β : ℝ) / (N : ℝ)
        = (W ω - M)
          + ((∑ i, (polyOfCoeffs a d).eval (lam i)) / (N : ℝ) - (β : ℝ) / (N : ℝ)) := by
      unfold betaHatPow
      rw [← hW, hbridge]
      ring
    rw [hβeq]
    calc |(W ω - M) + ((∑ i, (polyOfCoeffs a d).eval (lam i)) / (N : ℝ) - (β : ℝ) / (N : ℝ))|
        ≤ |W ω - M|
          + |(∑ i, (polyOfCoeffs a d).eval (lam i)) / (N : ℝ) - (β : ℝ) / (N : ℝ)| :=
          abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := by
          have h2 : |(∑ i, (polyOfCoeffs a d).eval (lam i)) / (N : ℝ) - (β : ℝ) / (N : ℝ)|
              ≤ ε / 2 := le_of_lt htrace
          linarith
      _ = ε := by ring
  · have hcoef0 : ∀ j : Fin d, a (j.val + 1) = 0 := by
      intro j
      have hle0 : (a (j.val + 1)) ^ 2 ≤ ∑ k : Fin d, (a (k.val + 1)) ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (a (k.val + 1))) (Finset.mem_univ j)
      have hle : (a (j.val + 1)) ^ 2 ≤ 0 := by
        rw [← hS0] at hle0
        exact hle0
      have hsq : a (j.val + 1) * a (j.val + 1) = 0 := by
        have := le_antisymm hle (sq_nonneg (a (j.val + 1)))
        simpa [pow_two] using this
      exact mul_self_eq_zero.mp hsq
    have hW0 : ∀ ω, W ω = 0 := by
      intro ω
      rw [hW]
      simp only [weightedSum]
      apply Finset.sum_eq_zero
      intro p _
      have hp0' : a (p.2.val + 1) = 0 := hcoef0 p.2
      simp [powWeight, hp0']
    have hM0 : M = 0 := by
      rw [hM]
      apply Finset.sum_eq_zero
      intro j _
      simp [hcoef0 j]
    have hsingle : ∀ i, (polyOfCoeffs a d).eval (lam i) = a 0 := by
      intro i
      rw [polyOfCoeffs_eval, Fin.sum_univ_succ
        (fun j : Fin (d + 1) => a j.val * (lam i) ^ j.val)]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      have hz : ∑ j : Fin d, a (j.val + 1) * (lam i) ^ (j.val + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hcoef0 j, zero_mul]
      rw [hz, add_zero]
    have htr : (∑ i, (polyOfCoeffs a d).eval (lam i)) / (N : ℝ) = a 0 := by
      have hsum : ∑ i, (polyOfCoeffs a d).eval (lam i) = (N : ℝ) * a 0 := by
        rw [Finset.sum_congr rfl (fun i _ => hsingle i), Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hsum]
      field_simp
    have hev : ∀ ω, |betaHatPow a q d ω - (β : ℝ) / (N : ℝ)| ≤ ε := by
      intro ω
      have hb : betaHatPow a q d ω = a 0 + W ω := by
        unfold betaHatPow
        rw [← hW]
      rw [hb, hW0 ω, add_zero]
      have h2 : |a 0 - (β : ℝ) / (N : ℝ)| < ε / 2 := by
        rw [← htr]; exact htrace
      linarith [le_of_lt h2]
    have hone : eventMass P (fun ω => |betaHatPow a q d ω - (β : ℝ) / (N : ℝ)| ≤ ε) = 1 := by
      have hpred : (fun ω => |betaHatPow a q d ω - (β : ℝ) / (N : ℝ)| ≤ ε)
          = (fun _ => True) := by
        funext ω
        exact propext ⟨fun _ => trivial, fun _ => hev ω⟩
      simp only [hpred]
      exact eventMass_true _
    rw [hone]
    linarith

/-- Hoeffding tail bound for the empirical average of `q` i.i.d. bounded samples
taking values in `[0, B]` with `B > 0` (Lemma 3.1). -/
theorem hoeffding_bounded {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinDist Ω) (s : Ω → ℝ) (B u : ℝ) (hB : 0 < B) (hu : 0 < u)
    (hs0 : ∀ x, 0 ≤ s x) (hsB : ∀ x, s x ≤ B)
    {q : ℕ} (hq : 0 < q) :
    eventMass (independent (I := Fin q) (fun _ => P))
        (fun ω => u ≤ |(∑ l, s (ω l)) / (q : ℝ) - P.expect s|)
      ≤ 2 * Real.exp (-2 * u ^ 2 / (B ^ 2 / (q : ℝ))) := by
  classical
  have hBne : B ≠ 0 := ne_of_gt hB
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hSterm : ∀ l : Fin q, ((q : ℝ)⁻¹) ^ 2 * (B - 0) ^ 2 = B ^ 2 / (q : ℝ) ^ 2 := by
    intro l
    field_simp
    ring
  have hSpos : 0 < ∑ l : Fin q, ((q : ℝ)⁻¹) ^ 2 * (B - 0) ^ 2 := by
    rw [Finset.sum_congr rfl (fun l _ => hSterm l), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    positivity
  have h := independent_weighted_hoeffding (I := Fin q) (X := fun _ => Ω)
    (fun _ => P) (fun _ => (q : ℝ)⁻¹) (fun _ x => s x)
    (fun _ => (0 : ℝ)) (fun _ => B) u
    (fun _ => le_of_lt hB) (fun _ x => ⟨hs0 x, hsB x⟩) hu hSpos
  have hexp : (independent (I := Fin q) (fun _ => P)).expect
      (weightedSum (fun _ => (q : ℝ)⁻¹) (fun _ x => s x)) = P.expect s := by
    rw [ProbabilityInterfaces.independent_weighted_expectation]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hexp] at h
  have hstat : ∀ ω : Fin q → Ω,
      weightedSum (fun _ => (q : ℝ)⁻¹) (fun _ x => s x) ω
        = (∑ l, s (ω l)) / (q : ℝ) := by
    intro ω
    rw [weightedSum, ← Finset.mul_sum]
    field_simp
  have hpred : (fun ω : Fin q → Ω =>
        u ≤ |weightedSum (fun _ => (q : ℝ)⁻¹) (fun _ x => s x) ω - P.expect s|)
      = (fun ω => u ≤ |(∑ l, s (ω l)) / (q : ℝ) - P.expect s|) := by
    funext ω
    rw [hstat ω]
  simp only [hpred] at h
  have hSval : (∑ l : Fin q, ((q : ℝ)⁻¹) ^ 2 * (B - 0) ^ 2) = B ^ 2 / (q : ℝ) := by
    rw [Finset.sum_congr rfl (fun l _ => hSterm l), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rwa [hSval] at h

/-- **Lemma 5.2**: if every sample of Algorithm 4 lies in `[0, B]` with mean
`nrm` within `ε / 2` of `β`, then the empirical average of `q` i.i.d. samples
is an `(ε, η)`-estimator whenever `q ≥ 2 log(2 / η) B² / ε²`. -/
theorem lemma_5_2_power_estimator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinDist Ω) (s : Ω → ℝ) (B ε η : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (hB : 0 ≤ B) (hs0 : ∀ x, 0 ≤ s x) (hsB : ∀ x, s x ≤ B)
    (nrm : ℝ) (hmean : P.expect s = nrm)
    (q : ℕ) (hq : 0 < q)
    (hqbound : 2 * Real.log (2 / η) * B ^ 2 ≤ ε ^ 2 * (q : ℝ))
    (β : ℝ) (hclose : |nrm - β| ≤ ε / 2) :
    1 - η ≤ eventMass (independent (I := Fin q) (fun _ => P))
      (fun ω => |(∑ l, s (ω l)) / (q : ℝ) - β| ≤ ε) := by
  classical
  have hqne : (q : ℝ) ≠ 0 := by positivity
  rcases lt_or_eq_of_le hB with hBpos | hB0
  · have h := hoeffding_bounded P s B (ε / 2) hBpos (by linarith) hs0 hsB hq
    rw [hmean] at h
    have hge : Real.log (2 / η) ≤ ε ^ 2 * (q : ℝ) / (2 * B ^ 2) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * B ^ 2)]
      nlinarith [hqbound]
    have harg : -2 * (ε / 2) ^ 2 / (B ^ 2 / (q : ℝ))
        = -(ε ^ 2 * (q : ℝ) / (2 * B ^ 2)) := by
      field_simp
    have hexpval : Real.exp (-Real.log (2 / η)) = η / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have hbound : 2 * Real.exp (-2 * (ε / 2) ^ 2 / (B ^ 2 / (q : ℝ))) ≤ η := by
      rw [harg]
      have hle : -(ε ^ 2 * (q : ℝ) / (2 * B ^ 2)) ≤ -Real.log (2 / η) := neg_le_neg hge
      calc 2 * Real.exp (-(ε ^ 2 * (q : ℝ) / (2 * B ^ 2)))
          ≤ 2 * Real.exp (-Real.log (2 / η)) := by
            linarith [Real.exp_le_exp.mpr hle]
        _ = η := by rw [hexpval]; ring
    have hmass : eventMass (independent (I := Fin q) (fun _ => P))
        (fun ω => ε / 2 ≤ |(∑ l, s (ω l)) / (q : ℝ) - nrm|) ≤ η := h.trans hbound
    have hstep : 1 - η ≤ eventMass (independent (I := Fin q) (fun _ => P))
        (fun ω => |(∑ l, s (ω l)) / (q : ℝ) - nrm| ≤ ε / 2) := by
      have hcompl := eventMass_not (independent (I := Fin q) (fun _ => P))
        (fun ω => ε / 2 ≤ |(∑ l, s (ω l)) / (q : ℝ) - nrm|)
      have hmono : eventMass (independent (I := Fin q) (fun _ => P))
          (fun ω => ¬ (ε / 2 ≤ |(∑ l, s (ω l)) / (q : ℝ) - nrm|))
          ≤ eventMass (independent (I := Fin q) (fun _ => P))
            (fun ω => |(∑ l, s (ω l)) / (q : ℝ) - nrm| ≤ ε / 2) := by
        apply eventMass_mono
        intro ω hω
        exact le_of_lt (not_le.mp hω)
      linarith
    refine le_trans hstep ?_
    apply eventMass_mono
    intro ω hω
    have hsplit : (∑ l, s (ω l)) / (q : ℝ) - β
        = ((∑ l, s (ω l)) / (q : ℝ) - nrm) + (nrm - β) := by ring
    rw [hsplit]
    calc |((∑ l, s (ω l)) / (q : ℝ) - nrm) + (nrm - β)|
        ≤ |(∑ l, s (ω l)) / (q : ℝ) - nrm| + |nrm - β| := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  · have hBz : B = 0 := hB0.symm
    have hszero : ∀ x, s x = 0 := by
      intro x
      exact le_antisymm (by simpa [hBz] using hsB x) (hs0 x)
    have hnrm0 : nrm = 0 := by
      rw [← hmean, FinDist.expect]
      apply Finset.sum_eq_zero
      intro x _
      rw [hszero x, mul_zero]
    have hev : ∀ ω : Fin q → Ω, |(∑ l, s (ω l)) / (q : ℝ) - β| ≤ ε := by
      intro ω
      have hsum : (∑ l, s (ω l)) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        rw [hszero (ω l)]
      rw [hsum, zero_div, zero_sub, abs_neg]
      have hβ : |β| ≤ ε / 2 := by
        have hc := hclose
        rwa [hnrm0, zero_sub, abs_neg] at hc
      linarith [le_of_lt (lt_of_le_of_lt hβ (by linarith : ε / 2 < ε))]
    have hone : eventMass (independent (I := Fin q) (fun _ => P))
        (fun ω => |(∑ l, s (ω l)) / (q : ℝ) - β| ≤ ε) = 1 := by
      have hpred : (fun (ω : Fin q → Ω) => |(∑ l, s (ω l)) / (q : ℝ) - β| ≤ ε)
          = (fun _ => True) := by
        funext ω
        exact propext ⟨fun _ => trivial, fun _ => hev ω⟩
      simp only [hpred]
      exact eventMass_true _
    rw [hone]
    linarith

/-- **Lemma 5.6**: the classical Chebyshev estimate of Algorithm 5 — a weighted
combination of `d` independently estimated power traces — is an
`(ε, η)`-estimator whenever each coordinate estimate fails with probability at
most `η'`, `d * η' ≤ η`, and both the weighted estimation error and filter bias
are at most `ε / 2`. -/
theorem lemma_5_6_reflected_estimator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (d : ℕ) (a : ℕ → ℝ) (ε η : ℝ) (_hε : 0 < ε) (_hη : 0 < η) (_hd : 0 < d)
    (β : ℝ) (P : Fin d → FinDist Ω) (est : Fin d → Ω → ℝ) (mean : Fin d → ℝ)
    (err : Fin d → ℝ) (_herr : ∀ j, 0 < err j) (η' : ℝ) (_hη' : 0 < η')
    (_hmean : ∀ j, (P j).expect (est j) = mean j)
    (hfail : ∀ j, eventMass (P j) (fun x => err j ≤ |est j x - mean j|) ≤ η')
    (hunion : (d : ℝ) * η' ≤ η)
    (hweighted : ∑ j : Fin d, |a (j.val + 1)| * err j ≤ ε / 2)
    (hfilter : |(∑ j : Fin d, a (j.val + 1) * mean j) - β| ≤ ε / 2) :
    1 - η ≤ eventMass (independent (I := Fin d) P)
      (fun ω => |(∑ j : Fin d, a (j.val + 1) * est j (ω j)) - β| ≤ ε) := by
  classical
  let Q := independent (I := Fin d) P
  let B (j : Fin d) (ω : Fin d → Ω) := err j ≤ |est j (ω j) - mean j|
  have hmarginal (j : Fin d) :
      eventMass Q (B j) = eventMass (P j) (fun x => err j ≤ |est j x - mean j|) := by
    simpa only [Q, B, FinDist.expect, eventMass, Finset.sum_filter, mul_ite,
      mul_one, mul_zero] using
      (@independent_expect_coord (Fin d) _ _ (fun _ => Ω)
        (fun _ => inferInstance) (fun _ => ‹DecidableEq Ω›) P j
        (fun x => if err j ≤ |est j x - mean j| then (1 : ℝ) else 0))
  have hunion_mass : eventMass Q (fun ω => ∃ j : Fin d, B j ω)
      ≤ ∑ j : Fin d, eventMass Q (B j) := by
    simp only [eventMass, Finset.sum_filter]
    calc
      _ ≤ ∑ ω : Fin d → Ω, ∑ j : Fin d, if B j ω then Q.prob ω else 0 := by
        apply Finset.sum_le_sum
        intro ω _
        have hnonneg (j : Fin d) : 0 ≤ if B j ω then Q.prob ω else 0 := by
          split_ifs
          · exact Q.nonneg ω
          · exact le_rfl
        by_cases hω : ∃ j : Fin d, B j ω
        · rw [ite_eq_left hω]
          obtain ⟨j, hj⟩ := hω
          calc
            Q.prob ω = (if B j ω then Q.prob ω else 0) := (ite_eq_left hj).symm
            _ ≤ ∑ j : Fin d, if B j ω then Q.prob ω else 0 :=
              Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
        · rw [ite_eq_right hω]
          exact Finset.sum_nonneg fun j _ => hnonneg j
      _ = _ := Finset.sum_comm
  have hmass : eventMass Q (fun ω => ∃ j : Fin d, B j ω) ≤ η := by
    calc
      _ ≤ ∑ j : Fin d, eventMass Q (B j) := hunion_mass
      _ = ∑ j : Fin d, eventMass (P j) (fun x => err j ≤ |est j x - mean j|) :=
        Finset.sum_congr rfl fun j _ => hmarginal j
      _ ≤ ∑ _j : Fin d, η' := Finset.sum_le_sum fun j _ => hfail j
      _ = (d : ℝ) * η' := by simp
      _ ≤ η := hunion
  have hcompl := eventMass_not Q (fun ω => ∃ j : Fin d, B j ω)
  calc
    1 - η ≤ eventMass Q (fun ω => ¬ ∃ j : Fin d, B j ω) := by
      rw [hcompl]
      linarith
    _ ≤ _ := by
      apply eventMass_mono
      intro ω hω
      have hcoord (j : Fin d) : |est j (ω j) - mean j| ≤ err j :=
        (not_le.mp (fun hj => hω ⟨j, hj⟩)).le
      have hsplit : (∑ j : Fin d, a (j.val + 1) * est j (ω j)) - β =
          (∑ j : Fin d, a (j.val + 1) * (est j (ω j) - mean j)) +
            ((∑ j : Fin d, a (j.val + 1) * mean j) - β) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      rw [hsplit]
      calc
        _ ≤ |∑ j : Fin d, a (j.val + 1) * (est j (ω j) - mean j)| +
            |(∑ j : Fin d, a (j.val + 1) * mean j) - β| := abs_add_le _ _
        _ ≤ (∑ j : Fin d, |a (j.val + 1)| * |est j (ω j) - mean j|) + ε / 2 := by
          apply add_le_add _ hfilter
          simpa only [abs_mul] using
            (Finset.abs_sum_le_sum_abs
              (fun j : Fin d => a (j.val + 1) * (est j (ω j) - mean j)) Finset.univ)
        _ ≤ (∑ j : Fin d, |a (j.val + 1)| * err j) + ε / 2 := by
          apply add_le_add _ le_rfl
          exact Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hcoord j) (abs_nonneg _)
        _ ≤ ε / 2 + ε / 2 := add_le_add hweighted le_rfl
        _ = ε := by ring

/-- **Theorem 6.2**: with `m = tr(H^d) / N` the mean of the `d`-th power trace,
if `d ≥ log(2 / ε) / δ` and `q ≥ 2 log(2 / η) / ε²`, then the empirical mean of
`q` Bernoulli samples is an `(ε, η)`-estimator of `β_k / N`. -/
theorem theorem_6_2_power_quantum_estimator
    {N : ℕ} (hN : 0 < N) (ν : Fin N → ℝ) (hν0 : ∀ i, 0 ≤ ν i) (hν1 : ∀ i, ν i ≤ 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hνgap : ∀ i, ν i ≠ 1 → ν i ≤ 1 - δ)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (β : ℕ) (hβ : (Finset.univ.filter (fun i => ν i = 1)).card = β)
    (d : ℕ) (hd : Real.log (2 / ε) / δ ≤ (d : ℝ))
    (q : ℕ) (hq : 0 < q) (hqbound : 2 * Real.log (2 / η) / ε ^ 2 ≤ (q : ℝ))
    (m : ℝ) (hm : m = (∑ i, (ν i) ^ d) / (N : ℝ)) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    1 - η ≤ eventMass
      (independent (I := Fin q) (fun _ => bernoulliLaw m hm0 hm1))
      (fun ω => |(∑ l : Fin q, boolIndicator (ω l)) / (q : ℝ) - (β : ℝ) / (N : ℝ)| ≤ ε) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hd' : Real.log (1 / (ε / 2)) / δ ≤ (d : ℝ) := by
    rw [show 1 / (ε / 2) = 2 / ε by field_simp]
    exact hd
  have h51 := lemma_5_1_power_trace (ε / 2) δ (by linarith) hδ0 hδ1 d hd' ν hν0 hν1 hνgap
  obtain ⟨hlo, hhi⟩ := h51
  rw [hβ] at hlo hhi
  have hclose : |m - (β : ℝ) / (N : ℝ)| ≤ ε / 2 := by
    have h2 : m - (β : ℝ) / (N : ℝ) = ((∑ i, (ν i) ^ d) - (β : ℝ)) / (N : ℝ) := by
      rw [hm]
      field_simp
    rw [h2]
    have hnum_lo : 0 ≤ (∑ i, (ν i) ^ d) - (β : ℝ) := by linarith
    have hnum_hi : (∑ i, (ν i) ^ d) - (β : ℝ) ≤ (ε / 2) * (N : ℝ) := by linarith
    rw [abs_of_nonneg (div_nonneg hnum_lo (le_of_lt hNpos))]
    rw [div_le_iff₀ hNpos]
    linarith
  have hq2 : 2 * Real.log (2 / η) * (1 : ℝ) ^ 2 ≤ ε ^ 2 * (q : ℝ) := by
    have h := hqbound
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)] at h
    nlinarith
  have hmain := lemma_5_2_power_estimator (P := bernoulliLaw m hm0 hm1)
    (s := boolIndicator) (B := 1) (ε := ε) (η := η) hε hη
    (by norm_num) (fun b => by cases b <;> simp [boolIndicator])
    (fun b => by cases b <;> simp [boolIndicator])
    m (bernoulli_expect_indicator m hm0 hm1) q hq hq2 ((β : ℝ) / (N : ℝ)) hclose
  exact hmain

end Qatlib.Papers.BettiNumber25.MainResults.Estimators
