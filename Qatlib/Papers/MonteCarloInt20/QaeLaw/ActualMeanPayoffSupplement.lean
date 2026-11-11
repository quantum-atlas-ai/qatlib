/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.ActualReadout
import Qatlib.Papers.MonteCarloInt20.QaeLaw.ActualMeanPayoff

/-!
# ActualMeanPayoff identities for the finite mathematical model.

This module extends the corresponding public results with finite proved identities.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff Qatlib.Papers.MonteCarloInt20.QaeLaw.Actual
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.AmplitudeCore.PreparedReadout


namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.MeanPayoff

open Qatlib.Papers.MonteCarloInt20.QaeLaw.MeanPayoff

/-- The actual prepared-QAE law has a quadratic payoff error bound around its
physical preparation mean, including the zero and one endpoints. -/
theorem actual_mean_quadratic_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (hEven : 2 ∣ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) :
    let a := MeasureProb (preparedAAState A j) S
    |(∑ k,(aeLaw M A j S hA hM).prob k*(D*aeEstimate M k)^2)-(D*a)^2| ≤
      (|2*(D*a)| * |D| + 2*D^2)/(M:ℝ) := by
  dsimp only
  apply actual_mean_smooth_error M hM hEven A j S hA D (fun x => x^2) (fun x => 2*x) 2
  · intro x
    convert! (hasDerivAt_pow 2 x) using 1 <;> ring
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,Real.dist_eq,← mul_sub,abs_mul]
    norm_num

/-- The endpoint-safe physical-mean bridge also composes with any affine
payoff: its additive offset cancels exactly and only the slope is charged. -/
theorem actual_mean_affine_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (hEven : 2 ∣ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D α β : ℝ) :
    let a := MeasureProb (preparedAAState A j) S
    |(∑ k,(aeLaw M A j S hA hM).prob k*(α*(D*aeEstimate M k)+β))-
      (α*(D*a)+β)| ≤ |α| * |D| / (M:ℝ) := by
  dsimp only
  have h := actual_mean_smooth_error M hM hEven A j S hA D
    (fun x => α*x + β) (fun _ => α) 0
    (by intro x; simpa using ((hasDerivAt_id x).const_mul α).add_const β)
    (by simpa using (LipschitzWith.const (α : ℝ)))
  simpa using h

/-- Any pointwise bounded payoff has the same bound after averaging over the
actual finite QAE law.  This is the probability bridge for bounded consumers
that do not satisfy the smooth derivative hypotheses. -/
theorem actual_bounded_payoff_bound {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ) (B : ℝ)
    (hg : ∀ x, |g x| ≤ B) :
    |∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)| ≤ B := by
  calc
    |∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)| ≤
        ∑ k, |(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k,(aeLaw M A j S hA hM).prob k*|g (D*aeEstimate M k)| := by
      apply Finset.sum_congr rfl
      intro k _
      have hprob := (aeLaw M A j S hA hM).nonneg k
      rw [abs_mul, abs_of_nonneg hprob]
    _ ≤ ∑ k,(aeLaw M A j S hA hM).prob k*B := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hg _) ((aeLaw M A j S hA hM).nonneg k)
    _ = B := by
      rw [← Finset.sum_mul, (aeLaw M A j S hA hM).sum_one, one_mul]

/-- A payoff valued pointwise in `[0,B]` stays in `[0,B]` after the actual
finite QAE probability average. -/
theorem actual_bounded_payoff_interval {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ) (B : ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B) :
    0 ≤ ∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k) ∧
      (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) ≤ B := by
  constructor
  · apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg ((aeLaw M A j S hA hM).nonneg k) (hg0 _)
  · calc
      ∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k) ≤
          ∑ k,(aeLaw M A j S hA hM).prob k*B := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hgB _) ((aeLaw M A j S hA hM).nonneg k)
      _ = B := by
        rw [← Finset.sum_mul, (aeLaw M A j S hA hM).sum_one, one_mul]

/-- Convex combinations of bounded payoff consumers remain bounded after the
same physical finite-law average. -/
theorem actual_bounded_payoff_convex {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (g h : ℝ → ℝ) (Bg Bh : ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ Bg)
    (hh0 : ∀ x, 0 ≤ h x) (hhB : ∀ x, h x ≤ Bh) :
    0 ≤ ∑ k,(aeLaw M A j S hA hM).prob k *
        (w*g (D*aeEstimate M k) + (1-w)*h (D*aeEstimate M k)) ∧
      (∑ k,(aeLaw M A j S hA hM).prob k *
        (w*g (D*aeEstimate M k) + (1-w)*h (D*aeEstimate M k))) ≤
        w*Bg + (1-w)*Bh := by
  apply actual_bounded_payoff_interval M hM A j S hA D
    (fun x => w*g x + (1-w)*h x) (w*Bg + (1-w)*Bh)
  · intro x
    exact add_nonneg (mul_nonneg hw0 (hg0 x))
      (mul_nonneg (sub_nonneg.mpr hw1) (hh0 x))
  · intro x
    have hg := mul_le_mul_of_nonneg_left (hgB x) hw0
    have hh := mul_le_mul_of_nonneg_left (hhB x) (sub_nonneg.mpr hw1)
    nlinarith

/-- The actual finite QAE law preserves affine payoff combinations: its
normalized probability mass extracts the additive constant exactly. -/
theorem actual_payoff_affine_combination {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D α β : ℝ) (g : ℝ → ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k *
      (α*g (D*aeEstimate M k) + β)) =
      α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) + β := by
  calc
    (∑ k,(aeLaw M A j S hA hM).prob k *
        (α*g (D*aeEstimate M k) + β)) =
        ∑ k, (α * ((aeLaw M A j S hA hM).prob k *
          g (D*aeEstimate M k)) + β * (aeLaw M A j S hA hM).prob k) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) +
        β * (∑ k,(aeLaw M A j S hA hM).prob k) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) + β := by
      rw [(aeLaw M A j S hA hM).sum_one, mul_one]

/-- An affine transform of a bounded payoff has the corresponding actual
finite-law expectation bound. -/
theorem actual_affine_bounded_payoff_bound {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D α β : ℝ) (g : ℝ → ℝ) (B : ℝ)
    (hg : ∀ x, |g x| ≤ B) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      (α*g (D*aeEstimate M k) + β)| ≤ |α| * B + |β| := by
  apply actual_bounded_payoff_bound M hM A j S hA D
    (fun x => α*g x + β) (|α| * B + |β|)
  intro x
  calc
    |α*g x + β| ≤ |α*g x| + |β| := abs_add_le _ _
    _ = |α| * |g x| + |β| := by rw [abs_mul]
    _ ≤ |α| * B + |β| := by
      nlinarith [mul_le_mul_of_nonneg_left (hg x) (abs_nonneg α)]

/-- The actual finite QAE law preserves constant payoffs exactly; this is the
normalization consumer used by the payoff-composition theorems. -/
theorem actual_constant_payoff_expectation {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (c : ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k*c) = c := by
  rw [← Finset.sum_mul, (aeLaw M A j S hA hM).sum_one, one_mul]

/-- The actual finite QAE expectation is linear in two arbitrary payoff
consumers, not only in an affine shift by a constant. -/
theorem actual_payoff_linear_combination {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D α β : ℝ) (g h : ℝ → ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k *
      (α*g (D*aeEstimate M k) + β*h (D*aeEstimate M k))) =
      α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) +
      β * (∑ k,(aeLaw M A j S hA hM).prob k*h (D*aeEstimate M k)) := by
  calc
    (∑ k,(aeLaw M A j S hA hM).prob k *
        (α*g (D*aeEstimate M k) + β*h (D*aeEstimate M k))) =
        ∑ k, (α * ((aeLaw M A j S hA hM).prob k *
          g (D*aeEstimate M k)) + β * ((aeLaw M A j S hA hM).prob k *
          h (D*aeEstimate M k))) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) +
        β * (∑ k,(aeLaw M A j S hA hM).prob k*h (D*aeEstimate M k)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The same actual finite-law expectation is linear in three payoff
consumers, which is the common small-basis composition used by estimators. -/
theorem actual_payoff_linear_combination_three {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D α β γ : ℝ) (g h q : ℝ → ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k *
      (α*g (D*aeEstimate M k) + β*h (D*aeEstimate M k) +
        γ*q (D*aeEstimate M k))) =
      α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) +
      β * (∑ k,(aeLaw M A j S hA hM).prob k*h (D*aeEstimate M k)) +
      γ * (∑ k,(aeLaw M A j S hA hM).prob k*q (D*aeEstimate M k)) := by
  calc
    (∑ k,(aeLaw M A j S hA hM).prob k *
        (α*g (D*aeEstimate M k) + β*h (D*aeEstimate M k) +
          γ*q (D*aeEstimate M k))) =
        ∑ k, (α * ((aeLaw M A j S hA hM).prob k *
          g (D*aeEstimate M k)) + β * ((aeLaw M A j S hA hM).prob k *
          h (D*aeEstimate M k)) + γ * ((aeLaw M A j S hA hM).prob k *
          q (D*aeEstimate M k))) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) +
        β * (∑ k,(aeLaw M A j S hA hM).prob k*h (D*aeEstimate M k)) +
        γ * (∑ k,(aeLaw M A j S hA hM).prob k*q (D*aeEstimate M k)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Four-way linearity for the actual finite-law payoff consumer. -/
theorem actual_payoff_linear_combination_four {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D α β γ δ : ℝ) (g h q r : ℝ → ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k *
      (α*g (D*aeEstimate M k) + β*h (D*aeEstimate M k) +
        γ*q (D*aeEstimate M k) + δ*r (D*aeEstimate M k))) =
      α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) +
      β * (∑ k,(aeLaw M A j S hA hM).prob k*h (D*aeEstimate M k)) +
      γ * (∑ k,(aeLaw M A j S hA hM).prob k*q (D*aeEstimate M k)) +
      δ * (∑ k,(aeLaw M A j S hA hM).prob k*r (D*aeEstimate M k)) := by
  calc
    (∑ k,(aeLaw M A j S hA hM).prob k *
        (α*g (D*aeEstimate M k) + β*h (D*aeEstimate M k) +
          γ*q (D*aeEstimate M k) + δ*r (D*aeEstimate M k))) =
        ∑ k, (α * ((aeLaw M A j S hA hM).prob k *
          g (D*aeEstimate M k)) + β * ((aeLaw M A j S hA hM).prob k *
          h (D*aeEstimate M k)) + γ * ((aeLaw M A j S hA hM).prob k *
          q (D*aeEstimate M k)) + δ * ((aeLaw M A j S hA hM).prob k *
          r (D*aeEstimate M k))) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = α * (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k)) +
        β * (∑ k,(aeLaw M A j S hA hM).prob k*h (D*aeEstimate M k)) +
        γ * (∑ k,(aeLaw M A j S hA hM).prob k*q (D*aeEstimate M k)) +
        δ * (∑ k,(aeLaw M A j S hA hM).prob k*r (D*aeEstimate M k)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Finite-basis payoff composition: the actual finite-law expectation
commutes with any finite linear combination of payoff consumers. -/
theorem actual_payoff_fin_basis_combination {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff : Fin N → ℝ)
    (payoff : Fin N → ℝ → ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k *
      (∑ i, coeff i * payoff i (D*aeEstimate M k))) =
      ∑ i, coeff i * (∑ k,(aeLaw M A j S hA hM).prob k *
        payoff i (D*aeEstimate M k)) := by
  calc
    (∑ k,(aeLaw M A j S hA hM).prob k *
        (∑ i, coeff i * payoff i (D*aeEstimate M k))) =
        ∑ k, ∑ i, (aeLaw M A j S hA hM).prob k *
          (coeff i * payoff i (D*aeEstimate M k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ k, (aeLaw M A j S hA hM).prob k *
          (coeff i * payoff i (D*aeEstimate M k)) := by
      rw [Finset.sum_comm]
    _ = ∑ i, coeff i * (∑ k,(aeLaw M A j S hA hM).prob k *
          payoff i (D*aeEstimate M k)) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ k,(aeLaw M A j S hA hM).prob k *
            (coeff i * payoff i (D*aeEstimate M k))) =
            ∑ k, coeff i * ((aeLaw M A j S hA hM).prob k *
              payoff i (D*aeEstimate M k)) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = coeff i * (∑ k,(aeLaw M A j S hA hM).prob k *
              payoff i (D*aeEstimate M k)) := by
          rw [Finset.mul_sum]

/-- A finite payoff basis also composes with an affine constant shift; the
constant is extracted by the actual law's normalization. -/
theorem actual_payoff_fin_basis_affine {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff : Fin N → ℝ)
    (payoff : Fin N → ℝ → ℝ) (c : ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k *
      ((∑ i, coeff i * payoff i (D*aeEstimate M k)) + c)) =
      (∑ i, coeff i * (∑ k,(aeLaw M A j S hA hM).prob k *
        payoff i (D*aeEstimate M k))) + c := by
  calc
    (∑ k,(aeLaw M A j S hA hM).prob k *
        ((∑ i, coeff i * payoff i (D*aeEstimate M k)) + c)) =
        (∑ k,(aeLaw M A j S hA hM).prob k *
          (∑ i, coeff i * payoff i (D*aeEstimate M k))) +
          ∑ k,(aeLaw M A j S hA hM).prob k*c := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (∑ i, coeff i * (∑ k,(aeLaw M A j S hA hM).prob k *
          payoff i (D*aeEstimate M k))) + c := by
      rw [actual_payoff_fin_basis_combination M hM A j S hA D coeff payoff]
      rw [← Finset.sum_mul, (aeLaw M A j S hA hM).sum_one, one_mul]

/-- A pointwise budget for each finite payoff basis yields a weighted absolute
expectation budget for the actual finite QAE law. -/
theorem actual_payoff_fin_basis_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff : Fin N → ℝ)
    (payoff : Fin N → ℝ → ℝ) (bound : Fin N → ℝ)
    (hpay : ∀ i x, |payoff i x| ≤ bound i) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      (∑ i, coeff i * payoff i (D*aeEstimate M k))| ≤
      ∑ i, |coeff i| * bound i := by
  apply actual_bounded_payoff_bound M hM A j S hA D
    (fun x => ∑ i, coeff i * payoff i x) (∑ i, |coeff i| * bound i)
  intro x
  calc
    |∑ i, coeff i * payoff i x| ≤
        ∑ i, |coeff i * payoff i x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |coeff i| * |payoff i x| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]
    _ ≤ ∑ i, |coeff i| * bound i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hpay i x) (abs_nonneg _)

/-- The weighted finite-basis budget composes with an additive offset, charging
only the offset's absolute value in addition to the basis budget. -/
theorem actual_payoff_fin_basis_affine_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff : Fin N → ℝ)
    (payoff : Fin N → ℝ → ℝ) (bound : Fin N → ℝ) (c : ℝ)
    (hpay : ∀ i x, |payoff i x| ≤ bound i) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      ((∑ i, coeff i * payoff i (D*aeEstimate M k)) + c)| ≤
      (∑ i, |coeff i| * bound i) + |c| := by
  apply actual_bounded_payoff_bound M hM A j S hA D
    (fun x => (∑ i, coeff i * payoff i x) + c)
    ((∑ i, |coeff i| * bound i) + |c|)
  intro x
  calc
    |(∑ i, coeff i * payoff i x) + c| ≤
        |∑ i, coeff i * payoff i x| + |c| := abs_add_le _ _
    _ ≤ (∑ i, |coeff i| * bound i) + |c| := by
      have hsum : |∑ i, coeff i * payoff i x| ≤
          ∑ i, |coeff i| * bound i := by
        calc
          |∑ i, coeff i * payoff i x| ≤
              ∑ i, |coeff i * payoff i x| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i, |coeff i| * |payoff i x| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul]
          _ ≤ ∑ i, |coeff i| * bound i := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (hpay i x) (abs_nonneg _)
      nlinarith [hsum]

/-- Pointwise basis payoff differences propagate to a weighted difference bound
for the actual finite-law expectation. -/
theorem actual_payoff_fin_basis_difference_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff : Fin N → ℝ)
    (payoff₁ payoff₂ : Fin N → ℝ → ℝ) (bound : Fin N → ℝ)
    (hdiff : ∀ i x, |payoff₁ i x - payoff₂ i x| ≤ bound i) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      (∑ i, coeff i * (payoff₁ i (D*aeEstimate M k) -
        payoff₂ i (D*aeEstimate M k)))| ≤
      ∑ i, |coeff i| * bound i := by
  apply actual_payoff_fin_basis_bound M hM A j S hA D coeff
    (fun i x => payoff₁ i x - payoff₂ i x) bound
  intro i x
  exact hdiff i x

/-- Difference budgets also compose with two affine offsets, charging the
absolute offset difference in addition to the weighted basis budget. -/
theorem actual_payoff_fin_basis_affine_difference_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff : Fin N → ℝ)
    (payoff₁ payoff₂ : Fin N → ℝ → ℝ) (bound : Fin N → ℝ) (c₁ c₂ : ℝ)
    (hdiff : ∀ i x, |payoff₁ i x - payoff₂ i x| ≤ bound i) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      ((∑ i, coeff i * (payoff₁ i (D*aeEstimate M k) -
        payoff₂ i (D*aeEstimate M k))) + (c₁ - c₂))| ≤
      (∑ i, |coeff i| * bound i) + |c₁ - c₂| := by
  apply actual_bounded_payoff_bound M hM A j S hA D
    (fun x => (∑ i, coeff i * (payoff₁ i x - payoff₂ i x)) + (c₁ - c₂))
    ((∑ i, |coeff i| * bound i) + |c₁ - c₂|)
  intro x
  calc
    |(∑ i, coeff i * (payoff₁ i x - payoff₂ i x)) + (c₁ - c₂)| ≤
        |∑ i, coeff i * (payoff₁ i x - payoff₂ i x)| + |c₁ - c₂| :=
      abs_add_le _ _
    _ ≤ (∑ i, |coeff i| * bound i) + |c₁ - c₂| := by
      have hsum : |∑ i, coeff i * (payoff₁ i x - payoff₂ i x)| ≤
          ∑ i, |coeff i| * bound i := by
        calc
          |∑ i, coeff i * (payoff₁ i x - payoff₂ i x)| ≤
              ∑ i, |coeff i * (payoff₁ i x - payoff₂ i x)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i, |coeff i| * |payoff₁ i x - payoff₂ i x| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul]
          _ ≤ ∑ i, |coeff i| * bound i := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (hdiff i x) (abs_nonneg _)
      nlinarith [hsum]

/-- Coefficient perturbations on a fixed bounded payoff basis obey the same
weighted budget under the actual finite-law average. -/
theorem actual_payoff_fin_coeff_difference_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff₁ coeff₂ : Fin N → ℝ)
    (payoff : Fin N → ℝ → ℝ) (bound : Fin N → ℝ)
    (hpay : ∀ i x, |payoff i x| ≤ bound i) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      (∑ i, (coeff₁ i - coeff₂ i) * payoff i (D*aeEstimate M k))| ≤
      ∑ i, |coeff₁ i - coeff₂ i| * bound i := by
  apply actual_payoff_fin_basis_bound M hM A j S hA D
    (fun i => coeff₁ i - coeff₂ i) payoff bound hpay

/-- Coefficient perturbations with an affine offset difference add exactly the
absolute offset difference to the weighted basis budget. -/
theorem actual_payoff_fin_coeff_affine_difference_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff₁ coeff₂ : Fin N → ℝ)
    (payoff : Fin N → ℝ → ℝ) (bound : Fin N → ℝ) (c₁ c₂ : ℝ)
    (hpay : ∀ i x, |payoff i x| ≤ bound i) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      ((∑ i, (coeff₁ i - coeff₂ i) * payoff i (D*aeEstimate M k)) +
        (c₁ - c₂))| ≤
      (∑ i, |coeff₁ i - coeff₂ i| * bound i) + |c₁ - c₂| := by
  exact actual_payoff_fin_basis_affine_bound M hM A j S hA D
    (fun i => coeff₁ i - coeff₂ i) payoff bound (c₁ - c₂) hpay

/-- Joint coefficient and payoff perturbations compose by the usual two-term
decomposition, with both budgets preserved by the actual finite-law average. -/
theorem actual_payoff_fin_joint_difference_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff₁ coeff₂ : Fin N → ℝ)
    (payoff₁ payoff₂ : Fin N → ℝ → ℝ) (bound₁ boundΔ : Fin N → ℝ)
    (hpay₁ : ∀ i x, |payoff₁ i x| ≤ bound₁ i)
    (hdiff : ∀ i x, |payoff₁ i x - payoff₂ i x| ≤ boundΔ i) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      (∑ i, (coeff₁ i * payoff₁ i (D*aeEstimate M k) -
        coeff₂ i * payoff₂ i (D*aeEstimate M k)))| ≤
      ∑ i, (|coeff₁ i - coeff₂ i| * bound₁ i +
        |coeff₂ i| * boundΔ i) := by
  have h := actual_payoff_fin_basis_bound M hM A j S hA D
    (fun _ => 1)
    (fun i x => coeff₁ i * payoff₁ i x - coeff₂ i * payoff₂ i x)
    (fun i => |coeff₁ i - coeff₂ i| * bound₁ i + |coeff₂ i| * boundΔ i)
    (by
      intro i x
      have hdecomp : coeff₁ i * payoff₁ i x - coeff₂ i * payoff₂ i x =
          (coeff₁ i - coeff₂ i) * payoff₁ i x + coeff₂ i *
            (payoff₁ i x - payoff₂ i x) := by ring
      change |coeff₁ i * payoff₁ i x - coeff₂ i * payoff₂ i x| ≤
        |coeff₁ i - coeff₂ i| * bound₁ i + |coeff₂ i| * boundΔ i
      have h₁ := mul_le_mul_of_nonneg_left (hpay₁ i x)
        (abs_nonneg (coeff₁ i - coeff₂ i))
      have h₂ := mul_le_mul_of_nonneg_left (hdiff i x) (abs_nonneg (coeff₂ i))
      rw [hdecomp]
      calc
        |(coeff₁ i - coeff₂ i) * payoff₁ i x + coeff₂ i *
            (payoff₁ i x - payoff₂ i x)| ≤
            |(coeff₁ i - coeff₂ i) * payoff₁ i x| +
              |coeff₂ i * (payoff₁ i x - payoff₂ i x)| := abs_add_le _ _
        _ = |coeff₁ i - coeff₂ i| * |payoff₁ i x| +
              |coeff₂ i| * |payoff₁ i x - payoff₂ i x| := by
            rw [abs_mul, abs_mul]
        _ ≤ |coeff₁ i - coeff₂ i| * bound₁ i +
              |coeff₂ i| * boundΔ i := by nlinarith)
  simpa using h

/-- Joint coefficient/payoff perturbations with an additional affine offset
difference preserve the complete additive budget. -/
theorem actual_payoff_fin_joint_affine_difference_bound {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (coeff₁ coeff₂ : Fin N → ℝ)
    (payoff₁ payoff₂ : Fin N → ℝ → ℝ) (bound₁ boundΔ : Fin N → ℝ)
    (c₁ c₂ : ℝ)
    (hpay₁ : ∀ i x, |payoff₁ i x| ≤ bound₁ i)
    (hdiff : ∀ i x, |payoff₁ i x - payoff₂ i x| ≤ boundΔ i) :
    |∑ k,(aeLaw M A j S hA hM).prob k *
      ((∑ i, (coeff₁ i * payoff₁ i (D*aeEstimate M k) -
        coeff₂ i * payoff₂ i (D*aeEstimate M k))) + (c₁ - c₂))| ≤
      (∑ i, (|coeff₁ i - coeff₂ i| * bound₁ i +
        |coeff₂ i| * boundΔ i)) + |c₁ - c₂| := by
  have h := actual_payoff_fin_basis_affine_bound M hM A j S hA D
    (fun _ => 1)
    (fun i x => coeff₁ i * payoff₁ i x - coeff₂ i * payoff₂ i x)
    (fun i => |coeff₁ i - coeff₂ i| * bound₁ i + |coeff₂ i| * boundΔ i)
    (c₁ - c₂)
    (by
      intro i x
      have hdecomp : coeff₁ i * payoff₁ i x - coeff₂ i * payoff₂ i x =
          (coeff₁ i - coeff₂ i) * payoff₁ i x + coeff₂ i *
            (payoff₁ i x - payoff₂ i x) := by ring
      change |coeff₁ i * payoff₁ i x - coeff₂ i * payoff₂ i x| ≤
        |coeff₁ i - coeff₂ i| * bound₁ i + |coeff₂ i| * boundΔ i
      rw [hdecomp]
      calc
        |(coeff₁ i - coeff₂ i) * payoff₁ i x + coeff₂ i *
            (payoff₁ i x - payoff₂ i x)| ≤
            |(coeff₁ i - coeff₂ i) * payoff₁ i x| +
              |coeff₂ i * (payoff₁ i x - payoff₂ i x)| := abs_add_le _ _
        _ = |coeff₁ i - coeff₂ i| * |payoff₁ i x| +
              |coeff₂ i| * |payoff₁ i x - payoff₂ i x| := by
            rw [abs_mul, abs_mul]
        _ ≤ |coeff₁ i - coeff₂ i| * bound₁ i +
              |coeff₂ i| * boundΔ i := by
            have h₁ := mul_le_mul_of_nonneg_left (hpay₁ i x)
              (abs_nonneg (coeff₁ i - coeff₂ i))
            have h₂ := mul_le_mul_of_nonneg_left (hdiff i x) (abs_nonneg (coeff₂ i))
            nlinarith)
  simpa using h

/-- A normalized nonnegative finite payoff basis stays in `[0,1]` after the
actual finite-law expectation. -/
theorem actual_payoff_fin_basis_interval {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (weights : Fin N → ℝ)
    (payoff : Fin N → ℝ → ℝ)
    (hw0 : ∀ i, 0 ≤ weights i) (hw1 : ∑ i, weights i = 1)
    (hpay0 : ∀ i x, 0 ≤ payoff i x) (hpay1 : ∀ i x, payoff i x ≤ 1) :
    0 ≤ ∑ k,(aeLaw M A j S hA hM).prob k *
        (∑ i, weights i * payoff i (D*aeEstimate M k)) ∧
      (∑ k,(aeLaw M A j S hA hM).prob k *
        (∑ i, weights i * payoff i (D*aeEstimate M k))) ≤ 1 := by
  apply actual_bounded_payoff_interval M hM A j S hA D
    (fun x => ∑ i, weights i * payoff i x) 1
  · intro x
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hw0 i) (hpay0 i x)
  · intro x
    calc
      ∑ i, weights i * payoff i x ≤ ∑ i, weights i * 1 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hpay1 i x) (hw0 i)
      _ = 1 := by simpa using hw1

/-- Weighted basis payoffs with arbitrary pointwise lower and upper bounds
remain within the corresponding weighted interval under the actual law. -/
theorem actual_payoff_fin_basis_weighted_interval {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (weights : Fin N → ℝ)
    (payoff : Fin N → ℝ → ℝ) (lower upper : Fin N → ℝ)
    (hw0 : ∀ i, 0 ≤ weights i)
    (hlow : ∀ i x, lower i ≤ payoff i x) (hupp : ∀ i x, payoff i x ≤ upper i) :
    (∑ i, weights i * lower i) ≤
        ∑ k,(aeLaw M A j S hA hM).prob k *
          (∑ i, weights i * payoff i (D*aeEstimate M k)) ∧
      (∑ k,(aeLaw M A j S hA hM).prob k *
          (∑ i, weights i * payoff i (D*aeEstimate M k))) ≤
        ∑ i, weights i * upper i := by
  have hconst (v : Fin N → ℝ) (i : Fin N) :
      (∑ k,(aeLaw M A j S hA hM).prob k * v i) = v i := by
    rw [← Finset.sum_mul, (aeLaw M A j S hA hM).sum_one, one_mul]
  have hLower :
      (∑ k,(aeLaw M A j S hA hM).prob k *
        (∑ i, weights i * lower i)) ≤
        ∑ k,(aeLaw M A j S hA hM).prob k *
          (∑ i, weights i * payoff i (D*aeEstimate M k)) := by
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ ((aeLaw M A j S hA hM).nonneg k)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hlow i _) (hw0 i)
  have hUpper :
      (∑ k,(aeLaw M A j S hA hM).prob k *
        (∑ i, weights i * payoff i (D*aeEstimate M k))) ≤
      (∑ k,(aeLaw M A j S hA hM).prob k *
        (∑ i, weights i * upper i)) := by
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ ((aeLaw M A j S hA hM).nonneg k)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hupp i _) (hw0 i)
  have hLowerEq :
      (∑ k,(aeLaw M A j S hA hM).prob k *
        (∑ i, weights i * lower i)) = ∑ i, weights i * lower i := by
    calc
      (∑ k,(aeLaw M A j S hA hM).prob k *
          (∑ i, weights i * lower i)) =
          ∑ k, ∑ i, (aeLaw M A j S hA hM).prob k *
            (weights i * lower i) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ k, (aeLaw M A j S hA hM).prob k *
            (weights i * lower i) := by rw [Finset.sum_comm]
      _ = ∑ i, weights i * (∑ k,(aeLaw M A j S hA hM).prob k * lower i) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          (∑ k,(aeLaw M A j S hA hM).prob k * (weights i * lower i)) =
              ∑ k, weights i * ((aeLaw M A j S hA hM).prob k * lower i) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = weights i * (∑ k,(aeLaw M A j S hA hM).prob k * lower i) := by
            rw [Finset.mul_sum]
      _ = ∑ i, weights i * lower i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hconst lower i]
  have hUpperEq :
      (∑ k,(aeLaw M A j S hA hM).prob k *
        (∑ i, weights i * upper i)) = ∑ i, weights i * upper i := by
    calc
      (∑ k,(aeLaw M A j S hA hM).prob k *
          (∑ i, weights i * upper i)) =
          ∑ k, ∑ i, (aeLaw M A j S hA hM).prob k *
            (weights i * upper i) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ k, (aeLaw M A j S hA hM).prob k *
            (weights i * upper i) := by rw [Finset.sum_comm]
      _ = ∑ i, weights i * (∑ k,(aeLaw M A j S hA hM).prob k * upper i) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          (∑ k,(aeLaw M A j S hA hM).prob k * (weights i * upper i)) =
              ∑ k, weights i * ((aeLaw M A j S hA hM).prob k * upper i) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = weights i * (∑ k,(aeLaw M A j S hA hM).prob k * upper i) := by
            rw [Finset.mul_sum]
      _ = ∑ i, weights i * upper i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hconst upper i]
  constructor
  · rw [← hLowerEq]
    exact hLower
  · rw [← hUpperEq]
    exact hUpper

end Qatlib.Papers.MonteCarloInt20.QaeLaw.MeanPayoff
