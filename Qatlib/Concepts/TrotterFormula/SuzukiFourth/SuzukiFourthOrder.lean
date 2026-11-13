/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Fourth-order Suzuki product formulas

This module defines the fifteen-factor Suzuki word `suzuki4Word` and its repeated application
`suzuki4Run` for two matrix Hamiltonians. The coefficient `suzukiP` gives the symmetric
composition of five Strang steps described in [Suzuki1990].

The coefficient series `suzukiSeries` supplies norm bounds and Taylor remainders for matrix
exponential words. Matching its coefficients through degree four yields local and repeated-step
error estimates for Hermitian inputs, in the setting of product-formula error analysis
[ChildsEtAl2021Trotter].

## Main statements

* `suzuki4Generators_first_five_coefficients`: equality with the exponential coefficients
  through degree four.
* `suzuki_fourth_order_local_error`: a fifth-order local error bound with constant 100.
* `suzuki_fourth_order_actual_word_and_cost`: unitarity, a factor count of `15 * r`, and an
  error bound proportional to `r⁻⁴`.

## References

* [Suzuki, 1990][Suzuki1990]
* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The Suzuki composition coefficient `1 / (4 - 4^(1/3))` used to cancel the cubic error term. -/
noncomputable def suzukiP : ℝ := (4 - (4 : ℝ)^(1/3 : ℝ))⁻¹

/-- The three-factor Strang word consisting of evolution under `A` for time `t / 2`, under `B`
for time `t`, and under `A` for time `t / 2`. -/
noncomputable def suzukiStrangWord {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) : List (Matrix I I ℂ) :=
  [hamiltonianEvolution A (t/2),hamiltonianEvolution B t,hamiltonianEvolution A (t/2)]

/-- The fifteen-factor fourth-order Suzuki word formed from four Strang steps of duration
`suzukiP * t` and a central step of duration `(1 - 4 * suzukiP) * t`. -/
noncomputable def suzuki4Word {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) : List (Matrix I I ℂ) :=
  let w := suzukiStrangWord A B (suzukiP*t)
  w++w++suzukiStrangWord A B ((1-4*suzukiP)*t)++w++w

/-- The matrix product obtained by concatenating `r` copies of `suzuki4Word A B (t / r)`. -/
noncomputable def suzuki4Run {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (r : ℕ) : Matrix I I ℂ :=
  ((List.replicate r (suzuki4Word A B (t/r))).flatten).prod

/-- The Suzuki coefficient lies strictly between zero and one half and satisfies the cubic
cancellation identity `4 * suzukiP^3 + (1 - 4 * suzukiP)^3 = 0`. -/
theorem suzukiP_order_conditions : 0 < suzukiP ∧ suzukiP < 1 / 2 ∧
    4 * suzukiP ^ 3 + (1 - 4 * suzukiP) ^ 3 = 0 := by
  let c := (4 : ℝ) ^ (1 / 3 : ℝ)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc3 : c ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hc2 : c < 2 := by
    by_contra h
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (not_lt.mp h) 3
    rw [hc3] at hp
    norm_num at hp
  have hc1 : 1 < c := by
    by_contra h
    have hp := pow_le_pow_left₀ hc0 (not_lt.mp h) 3
    rw [hc3] at hp
    norm_num at hp
  have hden : 0 < 4 - c := by linarith
  change 0 < (4 - c)⁻¹ ∧ (4 - c)⁻¹ < 1 / 2 ∧ _
  refine ⟨inv_pos.mpr hden, ?_, ?_⟩
  · rw [← one_div, div_lt_iff₀ hden]
    linarith
  · change 4 * ((4 - c)⁻¹) ^ 3 + (1 - 4 * (4 - c)⁻¹) ^ 3 = 0
    field_simp
    nlinarith

/-- The coefficient of degree `n` in the exponential word determined by a list of matrices,
defined recursively by convolution of exponential-series coefficients. -/
noncomputable def suzukiSeries {I : Type} [Fintype I] [DecidableEq I] :
    List (Matrix I I ℂ) → ℕ → Matrix I I ℂ
  | [], 0 => 1
  | [], _ + 1 => 0
  | X :: xs, n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (((kl.1.factorial : ℝ)⁻¹) • X ^ kl.1) * suzukiSeries xs kl.2

/-- The constant coefficient of every matrix exponential word is the identity matrix. -/
@[simp] theorem suzukiSeries_zero {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) : suzukiSeries xs 0 = 1 := by
  induction xs with
  | nil => rfl
  | cons X xs ih => simp [suzukiSeries, ih]

/-- Every positive-degree coefficient of the empty exponential word is zero. -/
@[simp] theorem suzukiSeries_nil_succ {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) :
    suzukiSeries ([] : List (Matrix I I ℂ)) (n + 1) = 0 := rfl

/-- Prepending `X` adds `X` to the degree-one coefficient of the exponential word. -/
@[simp] theorem suzukiSeries_cons_one {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) :
    suzukiSeries (X :: xs) 1 = suzukiSeries xs 1 + X := by
  rw [suzukiSeries, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

/-- The degree-two coefficient after prepending `X` is the sum of the old degree-two
coefficient, `X` times the old degree-one coefficient, and `X² / 2`. -/
@[simp] theorem suzukiSeries_cons_two {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) :
    suzukiSeries (X :: xs) 2 = suzukiSeries xs 2 + X * suzukiSeries xs 1 + (1 / 2 : ℝ) • X ^ 2 := by
  rw [suzukiSeries, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The degree-three coefficient after prepending `X` is the convolution of the remaining word
coefficients with `1`, `X`, `X² / 2`, and `X³ / 6`. -/
@[simp] theorem suzukiSeries_cons_three {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) :
    suzukiSeries (X :: xs) 3 = suzukiSeries xs 3 + X * suzukiSeries xs 2 +
      ((1 / 2 : ℝ) • X ^ 2) * suzukiSeries xs 1 + (1 / 6 : ℝ) • X ^ 3 := by
  rw [suzukiSeries, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The degree-four coefficient after prepending `X` is the convolution of the remaining word
coefficients with the exponential coefficients of `X` through `X⁴ / 24`. -/
@[simp] theorem suzukiSeries_cons_four {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) :
    suzukiSeries (X :: xs) 4 = suzukiSeries xs 4 + X * suzukiSeries xs 3 +
      ((1 / 2 : ℝ) • X ^ 2) * suzukiSeries xs 2 +
      ((1 / 6 : ℝ) • X ^ 3) * suzukiSeries xs 1 + (1 / 24 : ℝ) • X ^ 4 := by
  rw [suzukiSeries, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The list of fifteen scaled copies of `X` and `Y` whose exponential word realizes the
symmetric fourth-order Suzuki composition. -/
noncomputable def suzuki4Generators {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) : List (Matrix I I ℂ) :=
  let w := [(suzukiP / 2) • X, suzukiP • Y, (suzukiP / 2) • X]
  w ++ w ++ [((1 - 4 * suzukiP) / 2) • X, (1 - 4 * suzukiP) • Y,
    ((1 - 4 * suzukiP) / 2) • X] ++ w ++ w

/-- The degree-`n` convolution of the scalar exponential coefficients for `a` and `b` equals `(a
+ b)^n / n!`. -/
private theorem suzuki_scalar_convolution (a b : ℝ) (n : ℕ) :
    (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (a ^ kl.1 / (kl.1.factorial : ℝ)) * (b ^ kl.2 / (kl.2.factorial : ℝ))) =
      (a + b) ^ n / (n.factorial : ℝ) := by
  rw [(Commute.all a b).add_pow' n, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro kl hk
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hk, ← Nat.cast_smul_eq_nsmul ℝ,
      Nat.cast_add_choose]
  rw [smul_eq_mul]
  field_simp [Nat.factorial_ne_zero]

/-- The operator norm of `X^n` is at most `‖X‖^n`, including the zeroth power. -/
private theorem suzuki_norm_pow_le {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (n : ℕ) : ‖X ^ n‖ ≤ ‖X‖ ^ n := by
  induction n with
  | zero =>
    simpa using! l2_norm_unitary_le_one
      (show (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ from by simp)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg X))

/-- The sum of the operator norms of the matrices in an exponential-word generator list. -/
noncomputable def suzukiMass {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) : ℝ := (xs.map norm).sum

/-- The sum of generator norms `suzukiMass xs` is nonnegative. -/
private theorem suzukiMass_nonneg {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) : 0 ≤ suzukiMass xs := by
  unfold suzukiMass
  exact List.sum_nonneg
      (fun x hx => by obtain ⟨Y, _, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg Y)

/-- The norm of the degree-`n` exponential-word coefficient is at most `suzukiMass xs ^ n / n!`. -/
theorem suzukiSeries_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (n : ℕ) :
    ‖suzukiSeries xs n‖ ≤ suzukiMass xs ^ n / (n.factorial : ℝ) := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero =>
      simpa [suzukiSeries, suzukiMass] using! l2_norm_unitary_le_one
        (show (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ from by simp)
    | succ n => simp [suzukiSeries, suzukiMass]
  | cons X xs ih =>
    rw [suzukiSeries]
    calc
      _ ≤ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (‖X‖ ^ kl.1 / (kl.1.factorial : ℝ)) *
            (suzukiMass xs ^ kl.2 / (kl.2.factorial : ℝ)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro kl _
        have hx : ‖((kl.1.factorial : ℝ)⁻¹) • X ^ kl.1‖ ≤
            ‖X‖ ^ kl.1 / (kl.1.factorial : ℝ) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← inv_mul_eq_div]
          exact mul_le_mul_of_nonneg_left (suzuki_norm_pow_le X _) (by positivity)
        exact (norm_mul_le _ _).trans (mul_le_mul hx (ih kl.2)
          (norm_nonneg _) (by positivity))
      _ = _ := by rw [suzuki_scalar_convolution]; simp [suzukiMass]

/-- The norm of the degree-`n` series term at real time `t` is at most `(|t| * suzukiMass xs)^n
/ n!`. -/
private theorem suzukiSeries_term_norm {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) (n : ℕ) :
    ‖t ^ n • suzukiSeries xs n‖ ≤ (|t| * suzukiMass xs) ^ n / (n.factorial : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    _ ≤ |t| ^ n * (suzukiMass xs ^ n / (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (suzukiSeries_norm_le xs n) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The norms of the time-scaled exponential-word coefficients form a summable series for every
real time. -/
private theorem suzukiSeries_norm_summable {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) :
    Summable (fun n => ‖t ^ n • suzukiSeries xs n‖) := by
  have h : Summable (fun n => (|t| * suzukiMass xs) ^ n / (n.factorial : ℝ)) := by
    simpa only [smul_eq_mul, inv_mul_eq_div] using!
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (|t| * suzukiMass xs)).summable
  exact h.of_nonneg_of_le (fun _ => norm_nonneg _) (suzukiSeries_term_norm xs t)

/-- The ordered product of the matrix exponentials `exp (t • X)` for the generators `X` in `xs`. -/
noncomputable def suzukiExponentialWord {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) : Matrix I I ℂ :=
  (xs.map (fun X => NormedSpace.exp (t • X))).prod

/-- The coefficient series of an exponential word sums to `suzukiExponentialWord xs t` at every
real time `t`. -/
theorem suzukiSeries_hasSum {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) :
    HasSum (fun n => t ^ n • suzukiSeries xs n) (suzukiExponentialWord xs t) := by
  induction xs with
  | nil =>
    convert! hasSum_ite_eq (0 : ℕ) (1 : Matrix I I ℂ) using 1
    · funext n
      cases n <;> simp [suzukiSeries]
  | cons X xs ih =>
    let f := fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • X) ^ n
    let g := fun n : ℕ => t ^ n • suzukiSeries xs n
    have hf : Summable (fun n => ‖f n‖) := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (t • X)
    have hg : Summable (fun n => ‖g n‖) := suzukiSeries_norm_summable xs t
    have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum
    have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
    have hexp : (∑' n, f n) = NormedSpace.exp (t • X) :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • X)).tsum_eq
    have hval : (∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, f kl.1 * g kl.2) =
        NormedSpace.exp (t • X) * suzukiExponentialWord xs t := by
      calc
        _ = (∑' n, f n) * (∑' n, g n) := heq.symm
        _ = _ := congrArg₂ (fun A B : Matrix I I ℂ => A * B) hexp ih.tsum_eq
    have hprod := hval ▸ hsum
    convert! hprod using 1
    · funext n
      rw [suzukiSeries, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro kl hk
      simp only [f, g, _root_.smul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hk, pow_add]
      congr 1
      ring

/-- The real exponential `Real.exp a` is the sum of the series with terms `a^n / n!`. -/
private theorem suzuki_real_exp_hasSum (a : ℝ) :
    HasSum (fun n : ℕ => a ^ n / (n.factorial : ℝ)) (Real.exp a) := by
  simpa only [smul_eq_mul, inv_mul_eq_div, ← Real.exp_eq_exp_ℝ] using!
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a

/-- For nonnegative `a`, the exponential-series tail starting at degree `m` is summable and
bounded by `a^m / m! * Real.exp a`. -/
private theorem suzuki_scalar_tail (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    Summable (fun n : ℕ => a ^ (n + m) / ((n + m).factorial : ℝ)) ∧
    (∑' n : ℕ, a ^ (n + m) / ((n + m).factorial : ℝ)) ≤
      a ^ m / (m.factorial : ℝ) * Real.exp a := by
  have hterm (n : ℕ) : a ^ (n + m) / ((n + m).factorial : ℝ) ≤
      (a ^ m / (m.factorial : ℝ)) * (a ^ n / (n.factorial : ℝ)) := by
    have hfac : (n.factorial : ℝ) * (m.factorial : ℝ) ≤ ((n + m).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n m)
    calc
      _ ≤ a ^ (n + m) / ((n.factorial : ℝ) * (m.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = _ := by rw [pow_add]; ring
  have hg := (suzuki_real_exp_hasSum a).mul_left (a ^ m / (m.factorial : ℝ))
  have hs : Summable (fun n : ℕ => a ^ (n + m) / ((n + m).factorial : ℝ)) :=
    hg.summable.of_nonneg_of_le (fun _ => by positivity) hterm
  exact ⟨hs, (hs.tsum_le_tsum hterm hg.summable).trans_eq hg.tsum_eq⟩

/-- Truncating the exponential-word series after degree four incurs an error of at most `exp
(|t| * suzukiMass xs) * (|t| * suzukiMass xs)^5 / 120`. -/
theorem suzukiSeries_taylor_error {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) :
    ‖suzukiExponentialWord xs t - ∑ n ∈ Finset.range 5, t ^ n • suzukiSeries xs n‖ ≤
      Real.exp (|t| * suzukiMass xs) * (|t| * suzukiMass xs) ^ 5 / 120 := by
  let f := fun n : ℕ => t ^ n • suzukiSeries xs n
  let a := |t| * suzukiMass xs
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg _) (suzukiMass_nonneg xs)
  have hs := suzukiSeries_norm_summable xs t
  have hn : Summable (fun n => ‖f (n + 5)‖) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have he : suzukiExponentialWord xs t - ∑ n ∈ Finset.range 5, f n = ∑' n, f (n + 5) := by
    have h : (∑ n ∈ Finset.range 5, f n) + (∑' n, f (n + 5)) =
        suzukiExponentialWord xs t :=
      (hs.of_norm.sum_add_tsum_nat_add 5).trans (suzukiSeries_hasSum xs t).tsum_eq
    calc
      _ = ((∑ n ∈ Finset.range 5, f n) + (∑' n, f (n + 5))) -
          (∑ n ∈ Finset.range 5, f n) := congrArg (fun X => X - ∑ n ∈ Finset.range 5, f n) h.symm
      _ = _ := by abel
  rw [he]
  obtain ⟨hscalar, hb⟩ := suzuki_scalar_tail a ha 5
  calc
    _ ≤ ∑' n, ‖f (n + 5)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, a ^ (n + 5) / ((n + 5).factorial : ℝ) :=
      hn.tsum_le_tsum (fun n => suzukiSeries_term_norm xs t (n + 5)) hscalar
    _ ≤ a ^ 5 / (Nat.factorial 5 : ℝ) * Real.exp a := hb
    _ = _ := by norm_num [Nat.factorial]; ring

/-- The sum of generator norms in the fourth-order Suzuki composition is at most `3 * (‖X‖ +
‖Y‖)`. -/
theorem suzuki4Generators_mass {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) : suzukiMass (suzuki4Generators X Y) ≤ 3 * (‖X‖ + ‖Y‖) := by
  obtain ⟨hp, hhalf, hc⟩ := suzukiP_order_conditions
  have hq : 1 - 4 * suzukiP < 0 := by
    by_contra h
    have h1 := pow_pos hp 3
    have h2 := pow_nonneg (not_lt.mp h) 3
    nlinarith
  have he : suzukiMass (suzuki4Generators X Y) = (8 * suzukiP - 1) * (‖X‖ + ‖Y‖) := by
    simp [suzuki4Generators, suzukiMass, norm_smul, Real.norm_eq_abs,
      abs_of_pos hp, abs_of_neg hq]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (norm_nonneg X) (norm_nonneg Y))

/-- Exponentiating the scaled generator `c • ((-Complex.I) • A)` at time `t` gives Hamiltonian
evolution under `A` for time `c * t`. -/
private theorem suzuki_evolution_generator {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (c t : ℝ) :
    NormedSpace.exp (t • (c • ((-Complex.I) • A))) = hamiltonianEvolution A (c * t) := by
  unfold hamiltonianEvolution
  congr 1
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]
  ring

/-- The exponential word of the Suzuki generators `(-Complex.I) • A` and `(-Complex.I) • B`
equals the product of `suzuki4Word A B t`. -/
theorem suzuki4Generators_actual_word {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) :
    suzukiExponentialWord (suzuki4Generators ((-Complex.I) • A) ((-Complex.I) • B)) t =
      (suzuki4Word A B t).prod := by
  simp only [suzukiExponentialWord, suzuki4Generators, suzuki4Word, suzukiStrangWord,
    List.map_append, List.map_cons, List.map_nil, suzuki_evolution_generator,
    div_mul_eq_mul_div]

/-- The product of the fourth-order Suzuki word is unitary when both input matrices are
Hermitian. -/
private theorem suzuki_word_unitary {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (suzuki4Word A B t).prod ∈ Matrix.unitaryGroup I ℂ := by
  have hstrang (s : ℝ) : ∀ U ∈ suzukiStrangWord A B s, U ∈ Matrix.unitaryGroup I ℂ := by
    intro U hU
    simp only [suzukiStrangWord, List.mem_cons, List.not_mem_nil, or_false] at hU
    rcases hU with rfl | rfl | rfl
    · exact Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary hA _
    · exact Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary hB _
    · exact Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary hA _
  have hword : ∀ U ∈ suzuki4Word A B t, U ∈ Matrix.unitaryGroup I ℂ := by
    intro U hU
    simp only [suzuki4Word, List.mem_append] at hU
    aesop
  exact (Matrix.unitaryGroup I ℂ).list_prod_mem hword

/-- The empty exponential word has identity coefficient in degree zero and zero coefficient in
every other degree. -/
private theorem suzukiSeries_nil {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) :
    suzukiSeries ([] : List (Matrix I I ℂ)) n = if n = 0 then 1 else 0 := by
  cases n <;> simp [suzukiSeries]

/-- The degree-`n` coefficient of a singleton exponential word is `X^n / n!`. -/
theorem suzukiSeries_singleton {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (n : ℕ) :
    suzukiSeries (X :: []) n = ((n.factorial : ℝ)⁻¹) • X ^ n := by
  rw [suzukiSeries]
  rw [Finset.sum_eq_single (n, 0)]
  · simp [suzukiSeries]
  · intro kl hk hne
    have hl : kl.2 ≠ 0 := by
      intro hl
      have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hk
      have he : kl = (n, 0) := by
        apply Prod.ext
        · simpa only [hl, add_zero] using! h
        · exact hl
      exact hne he
    simp only [suzukiSeries_nil, if_neg hl, Matrix.mul_zero]
  · simp

/-- The real exponential of any `a ≤ 2` is bounded above by nine. -/
private theorem suzuki_real_exp_le_nine (a : ℝ) (ha : a ≤ 2) : Real.exp a ≤ 9 := by
  have he : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, pow_two]
  apply (Real.exp_le_exp.mpr ha).trans
  rw [he]
  nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]

/-- The concatenated Suzuki run equals the `r`th power of the single-word product at time `t /
r`. -/
theorem suzuki4Run_eq_power {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (r : ℕ) :
    suzuki4Run A B t r = (suzuki4Word A B (t / r)).prod ^ r := by
  simp [suzuki4Run, List.prod_flatten]

/-- For Hermitian `A` and `B`, the repeated Suzuki run is unitary and its concatenated word
contains exactly `15 * r` factors. -/
theorem suzuki4Run_unitary_and_length {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (r : ℕ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    suzuki4Run A B t r ∈ Matrix.unitaryGroup I ℂ ∧
      ((List.replicate r (suzuki4Word A B (t / r))).flatten).length = 15 * r := by
  constructor
  · rw [suzuki4Run_eq_power]
    exact (Matrix.unitaryGroup I ℂ).pow_mem (suzuki_word_unitary A B _ hA hB) r
  · simp [suzuki4Word, suzukiStrangWord, List.length_flatten, Nat.mul_comm]

set_option maxHeartbeats 40000000 in

/-- The Suzuki generator word and the exponential of `X + Y` have identical coefficients in
every degree below five. -/
theorem suzuki4Generators_first_five_coefficients {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (n : ℕ) (hn : n < 5) :
    suzukiSeries (suzuki4Generators X Y) n = ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n := by
  have hc := suzukiP_order_conditions.2.2
  have hp3 : suzukiP ^ 3 = (1 / 60 : ℝ) - suzukiP / 5 + (4 / 5 : ℝ) * suzukiP ^ 2 := by
    linear_combination (-1 / 60 : ℝ) * hc
  interval_cases n
  all_goals simp only [suzuki4Generators, List.cons_append, List.nil_append,
    suzukiSeries_zero, suzukiSeries_cons_one, suzukiSeries_cons_two,
    suzukiSeries_cons_three, suzukiSeries_cons_four, suzukiSeries_nil_succ,
    Nat.factorial, Nat.cast_one, inv_one, one_smul]
  all_goals try simp only [pow_succ, pow_zero, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc,
    smul_add, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add]
  all_goals match_scalars <;> try ring_nf
  all_goals try simp only [hp3]
  all_goals ring

/-- The difference between the Suzuki exponential word and `exp (t • (X + Y))` is bounded by the
sum of their fifth-order exponential Taylor remainder bounds. -/
theorem suzuki4Generators_taylor_error {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (t : ℝ) :
    ‖suzukiExponentialWord (suzuki4Generators X Y) t - NormedSpace.exp (t • (X + Y))‖ ≤
      (Real.exp (|t| * suzukiMass (suzuki4Generators X Y)) *
        (|t| * suzukiMass (suzuki4Generators X Y)) ^ 5 +
       Real.exp (|t| * ‖X + Y‖) * (|t| * ‖X + Y‖) ^ 5) / 120 := by
  have hp : (∑ n ∈ Finset.range 5, t ^ n • suzukiSeries (suzuki4Generators X Y) n) =
      ∑ n ∈ Finset.range 5, t ^ n • suzukiSeries ((X + Y) :: []) n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [suzuki4Generators_first_five_coefficients X Y n (Finset.mem_range.mp hn),
      suzukiSeries_singleton]
  have hf := suzukiSeries_taylor_error (suzuki4Generators X Y) t
  have hg := suzukiSeries_taylor_error ((X + Y) :: []) t
  simp only [suzukiExponentialWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, suzukiMass, List.sum_cons, List.sum_nil, add_zero] at hg
  rw [← hp] at hg
  have he : suzukiExponentialWord (suzuki4Generators X Y) t - NormedSpace.exp (t • (X + Y)) =
      (suzukiExponentialWord (suzuki4Generators X Y) t -
        ∑ n ∈ Finset.range 5, t ^ n • suzukiSeries (suzuki4Generators X Y) n) -
      (NormedSpace.exp (t • (X + Y)) -
        ∑ n ∈ Finset.range 5, t ^ n • suzukiSeries (suzuki4Generators X Y) n) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hf hg).trans_eq (by ring))

/-- For Hermitian `A` and `B`, the fourth-order Suzuki word approximates evolution under `A + B`
with operator-norm error at most `100 * (‖A‖ + ‖B‖)^5 * |t|^5`. See [ChildsEtAl2021Trotter]
for the product-formula error framework. -/
theorem suzuki_fourth_order_local_error :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ) (t : ℝ),
      A.IsHermitian → B.IsHermitian →
      ‖(suzuki4Word A B t).prod - hamiltonianEvolution (A + B) t‖ ≤
        100 * (‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 := by
  intro I _ _ A B t hA hB
  let X := (-Complex.I) • A
  let Y := (-Complex.I) • B
  let N := ‖A‖ + ‖B‖
  let x := |t| * N
  have hN : 0 ≤ N := add_nonneg (norm_nonneg A) (norm_nonneg B)
  have hx0 : 0 ≤ x := mul_nonneg (abs_nonneg t) hN
  have hnX : ‖X‖ = ‖A‖ := by simp only [X, norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hnY : ‖Y‖ = ‖B‖ := by simp only [Y, norm_smul, norm_neg, Complex.norm_I, one_mul]
  have htarget : NormedSpace.exp (t • (X + Y)) = hamiltonianEvolution (A + B) t := by
    have he : X + Y = (-Complex.I) • (A + B) := by simp only [X, Y, smul_add]
    rw [he]
    simpa only [one_smul, one_mul] using! suzuki_evolution_generator (A + B) 1 t
  have hrate : 100 * (‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 = 100 * x ^ 5 := by
    dsimp only [x, N]
    rw [mul_pow]
    ring
  rw [hrate]
  by_cases hx : x ≤ 1 / 2
  · let a := |t| * suzukiMass (suzuki4Generators X Y)
    let b := |t| * ‖X + Y‖
    have ha0 : 0 ≤ a := mul_nonneg (abs_nonneg _) (suzukiMass_nonneg _)
    have hb0 : 0 ≤ b := mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have ha : a ≤ 3 * x := by
      have h := mul_le_mul_of_nonneg_left (suzuki4Generators_mass X Y) (abs_nonneg t)
      simpa only [hnX, hnY, a, x, N, mul_assoc, mul_left_comm] using! h
    have hb : b ≤ x := by
      exact (mul_le_mul_of_nonneg_left (norm_add_le X Y) (abs_nonneg t)).trans_eq
        (by rw [hnX, hnY])
    have hfa : Real.exp a * a ^ 5 ≤ 9 * (3 * x) ^ 5 :=
      mul_le_mul (suzuki_real_exp_le_nine a (by linarith))
        (pow_le_pow_left₀ ha0 ha 5) (by positivity) (by norm_num)
    have hfb : Real.exp b * b ^ 5 ≤ 9 * x ^ 5 :=
      mul_le_mul (suzuki_real_exp_le_nine b (by linarith))
        (pow_le_pow_left₀ hb0 hb 5) (by positivity) (by norm_num)
    have h := suzuki4Generators_taylor_error X Y t
    rw [suzuki4Generators_actual_word, htarget] at h
    calc
      _ ≤ (Real.exp a * a ^ 5 + Real.exp b * b ^ 5) / 120 := h
      _ ≤ (9 * (3 * x) ^ 5 + 9 * x ^ 5) / 120 := by linarith [add_le_add hfa hfb]
      _ ≤ 100 * x ^ 5 := by rw [mul_pow]; nlinarith [pow_nonneg hx0 5]
  · have hword : ‖(suzuki4Word A B t).prod‖ ≤ 1 :=
      l2_norm_unitary_le_one (suzuki_word_unitary A B t hA hB)
    have hevol : ‖hamiltonianEvolution (A + B) t‖ ≤ 1 :=
      l2_norm_unitary_le_one (Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary (hA.add hB) t)
    have hp : (1 / 2 : ℝ) ^ 5 ≤ x ^ 5 :=
      pow_le_pow_left₀ (by norm_num) (not_le.mp hx).le 5
    exact (norm_sub_le _ _).trans (by nlinarith)

/-- For Hermitian `A` and `B` and positive `r`, the repeated Suzuki word is unitary, contains
`15 * r` factors, and has error at most `100 * (‖A‖ + ‖B‖)^5 * |t|^5 / r^4`. See
[ChildsEtAl2021Trotter] for the product-formula error framework. -/
theorem suzuki_fourth_order_actual_word_and_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
      (t : ℝ) (r : ℕ), A.IsHermitian → B.IsHermitian → 0 < r →
      suzuki4Run A B t r ∈ Matrix.unitaryGroup I ℂ ∧
      ((List.replicate r (suzuki4Word A B (t / r))).flatten).length = 15 * r ∧
      ‖suzuki4Run A B t r - hamiltonianEvolution (A + B) t‖ ≤
        100 * (‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / (r : ℝ) ^ 4 := by
  intro I _ _ A B t r hA hB hr
  obtain ⟨hu, hl⟩ := suzuki4Run_unitary_and_length A B t r hA hB
  refine ⟨hu, hl, ?_⟩
  have hrp : 0 < (r : ℝ) := by exact_mod_cast hr
  have he : (hamiltonianEvolution (A + B) (t / r)) ^ r = hamiltonianEvolution (A + B) t := by
    change (HamiltonianEvolution (A + B) (t / r)) ^ r = HamiltonianEvolution (A + B) t
    rw [pf_evolution_pow]
    congr 1
    field_simp
  rw [suzuki4Run_eq_power, ← he]
  have h := pf_unitary_power_error (suzuki4Word A B (t / r)).prod
    (hamiltonianEvolution (A + B) (t / r)) (suzuki_word_unitary A B _ hA hB)
    (Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary (hA.add hB) _) r
  exact h.trans ((mul_le_mul_of_nonneg_left
    (suzuki_fourth_order_local_error I A B (t / r) hA hB) (Nat.cast_nonneg r)).trans_eq (by
      rw [abs_div, abs_of_pos hrp]
      field_simp))

end Qatlib.Concepts.TrotterFormula.SuzukiFourth
