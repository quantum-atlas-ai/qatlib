/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Measurement
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bernoulli sample moments and Fourier readout

This module computes the mean and variance of the empirical occupation frequency under Bernoulli
product weights. `sample_tail_le_variance` gives a finite Chebyshev bound, while
`qftWord_correct` records a unitary Fourier transform circuit for changing the measurement
basis.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `productWeight_sampleMean_variance`: For a nonempty sample, the weighted squared deviation of
  the sample mean from `p` is `p * (1 - p) / N`.
* `sample_tail_le_variance`: For `0 ≤ p ≤ 1` and positive sample size and tolerance, the weight
  of samples deviating by at least `ε` is at most `p * (1 - p) / (N * ε ^ 2)`.
* `qftWord_correct`: For `M > 0`, the Fourier circuit is unitary, has no queries and one gate,
  and acts by `QFTMatrix M`.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.SampleVariance
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Papers.ManyBodyFermi97.MainResults.Measurement
open scoped Classical BigOperators

/-- The real-valued indicator of a Boolean outcome. -/
def indicator (b : Bool) : ℝ := if b then 1 else 0

/-- The number of true outcomes in a finite sample, expressed as a real sum. -/
def sampleSum {N : ℕ} (b : Fin N → Bool) : ℝ := ∑ i, indicator (b i)

/-- The sample sum divided by the number of observations, using real division. -/
def sampleMean {N : ℕ} (b : Fin N → Bool) : ℝ := sampleSum b / (N:ℝ)

/-- Bernoulli outcome weights are nonnegative when `0 ≤ p ≤ 1`. -/
theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b <;> simp [bitWeight] <;> linarith

/-- Every Bernoulli product weight is nonnegative when `0 ≤ p ≤ 1`. -/
theorem productWeight_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (b : Fin N → Bool) : 0 ≤ productWeight p b := by
  unfold productWeight
  exact Finset.prod_nonneg (fun i _ => bitWeight_nonneg hp0 hp1 (b i))

/-- The product weight of a sample with a prepended bit factors into that bit's weight and the
remaining sample's weight. -/
theorem productWeight_cons {N : ℕ} (p : ℝ) (b : Bool) (v : Fin N → Bool) :
    productWeight p (Fin.cons b v) = bitWeight p b * productWeight p v := by
  simp [productWeight, Fin.prod_univ_succ]

/-- Prepending a bit adds its indicator to the sample sum. -/
theorem sampleSum_cons {N : ℕ} (b : Bool) (v : Fin N → Bool) :
    sampleSum (Fin.cons b v) = indicator b + sampleSum v := by
  simp [sampleSum, Fin.sum_univ_succ]

/-- A sum over Boolean samples of length `N + 1` splits into sums over the first bit and the
remaining `N` bits. -/
theorem sum_fun_succ {M : Type*} [AddCommMonoid M] {N : ℕ}
    (F : (Fin (N+1) → Bool) → M) :
    ∑ b : Fin (N+1) → Bool, F b =
      ∑ b0 : Bool, ∑ v : Fin N → Bool, F (Fin.cons b0 v) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N+1) => Bool))
      (fun q : Bool × (Fin N → Bool) => F (Fin.cons q.1 q.2))
      (fun b => F b)]
  · rw [Fintype.sum_prod_type]
  · intro q
    rfl

/-- The two Bernoulli outcome weights sum to one for every real `p`. -/
theorem sum_bitWeight (p : ℝ) : ∑ b : Bool, bitWeight p b = 1 := by
  rw [Fintype.sum_bool]
  simp [bitWeight]

/-- The weighted sum of the Boolean indicator is `p`. -/
theorem sum_bitWeight_indicator (p : ℝ) :
    ∑ b : Bool, bitWeight p b * indicator b = p := by
  rw [Fintype.sum_bool]
  simp [bitWeight, indicator]

/-- The weighted first moment of the sample sum is `N * p` for every real `p`. -/
theorem productWeight_sampleSum (p : ℝ) :
    ∀ N : ℕ, ∑ b : Fin N → Bool, productWeight p b * sampleSum b = (N:ℝ) * p
  | 0 => by simp [sampleSum]
  | N+1 => by
      have hN : ((N+1:ℕ) : ℝ) = (N:ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hN]
      rw [sum_fun_succ]
      simp only [productWeight_cons, sampleSum_cons]
      have hinner : ∀ b : Bool,
          ∑ v : Fin N → Bool, bitWeight p b * productWeight p v *
            (indicator b + sampleSum v) =
          bitWeight p b * indicator b + bitWeight p b * ((N:ℝ)*p) := by
        intro b
        calc
          ∑ v, bitWeight p b * productWeight p v * (indicator b + sampleSum v)
              = ∑ v, (bitWeight p b * (productWeight p v * indicator b)
                  + bitWeight p b * (productWeight p v * sampleSum v)) := by
                    apply Finset.sum_congr rfl
                    intro v _
                    ring
          _ = bitWeight p b * (∑ v, productWeight p v * indicator b)
                + bitWeight p b * (∑ v, productWeight p v * sampleSum v) := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = bitWeight p b * indicator b + bitWeight p b * ((N:ℝ)*p) := by
                    rw [productWeight_sampleSum p N]
                    have hconst : (∑ v : Fin N → Bool, productWeight p v * indicator b) = indicator b := by
                      rw [← Finset.sum_mul, productWeight_sum_one]
                      ring
                    rw [hconst]
      calc
        ∑ b : Bool, ∑ v : Fin N → Bool, bitWeight p b * productWeight p v *
            (indicator b + sampleSum v)
            = ∑ b : Bool, (bitWeight p b * indicator b + bitWeight p b * ((N:ℝ)*p)) := by
                apply Finset.sum_congr rfl
                intro b _
                exact hinner b
        _ = (∑ b : Bool, bitWeight p b * indicator b)
              + (∑ b : Bool, bitWeight p b) * ((N:ℝ)*p) := by
                rw [Finset.sum_add_distrib]
                congr 1
                rw [Finset.sum_mul]
        _ = p + 1 * ((N:ℝ)*p) := by
                rw [sum_bitWeight_indicator, sum_bitWeight]
        _ = ((N:ℝ) + 1) * p := by
                ring

/-- The weighted second moment of the sample sum is `N * p * (1 - p) + (N * p) ^ 2`. -/
theorem productWeight_sampleSum_sq (p : ℝ) :
    ∀ N : ℕ, ∑ b : Fin N → Bool, productWeight p b * (sampleSum b)^2 =
      (N:ℝ)*p*(1-p) + ((N:ℝ)*p)^2
  | 0 => by simp [sampleSum]
  | N+1 => by
      have hN : ((N+1:ℕ) : ℝ) = (N:ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hN]
      rw [sum_fun_succ]
      simp only [productWeight_cons, sampleSum_cons]
      have hinner : ∀ b : Bool,
          ∑ v : Fin N → Bool, bitWeight p b * productWeight p v *
            (indicator b + sampleSum v)^2 =
          bitWeight p b * ((N:ℝ)*p*(1-p) + ((N:ℝ)*p)^2)
            + (2 * (bitWeight p b * indicator b)) * ((N:ℝ)*p)
            + bitWeight p b * indicator b := by
        intro b
        calc
          ∑ v, bitWeight p b * productWeight p v * (indicator b + sampleSum v)^2
              = ∑ v, (bitWeight p b * (productWeight p v * (sampleSum v)^2)
                  + (2 * (bitWeight p b * indicator b)) *
                      (productWeight p v * sampleSum v)
                  + (bitWeight p b * indicator b) * productWeight p v) := by
                    apply Finset.sum_congr rfl
                    intro v _
                    by_cases hb : b
                    · simp [indicator, hb]
                      ring
                    · simp [indicator, hb]
                      ring
          _ = bitWeight p b * (∑ v, productWeight p v * (sampleSum v)^2)
                + (2 * (bitWeight p b * indicator b)) *
                    (∑ v, productWeight p v * sampleSum v)
                + (bitWeight p b * indicator b) * (∑ v, productWeight p v) := by
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = bitWeight p b * ((N:ℝ)*p*(1-p) + ((N:ℝ)*p)^2)
                + (2 * (bitWeight p b * indicator b)) * ((N:ℝ)*p)
                + bitWeight p b * indicator b := by
                    rw [productWeight_sampleSum_sq p N, productWeight_sampleSum p N,
                      productWeight_sum_one]
                    ring
      calc
        ∑ b : Bool, ∑ v : Fin N → Bool, bitWeight p b * productWeight p v *
            (indicator b + sampleSum v)^2
            = ∑ b : Bool, (bitWeight p b * ((N:ℝ)*p*(1-p) + ((N:ℝ)*p)^2)
                + (2 * (bitWeight p b * indicator b)) * ((N:ℝ)*p)
                + bitWeight p b * indicator b) := by
                  apply Finset.sum_congr rfl
                  intro b _
                  exact hinner b
        _ = (∑ b : Bool, bitWeight p b) * ((N:ℝ)*p*(1-p) + ((N:ℝ)*p)^2)
              + 2 * (∑ b : Bool, bitWeight p b * indicator b) * ((N:ℝ)*p)
              + (∑ b : Bool, bitWeight p b * indicator b) := by
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                  ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
        _ = 1 * ((N:ℝ)*p*(1-p) + ((N:ℝ)*p)^2)
              + 2 * p * ((N:ℝ)*p) + p := by
                rw [sum_bitWeight, sum_bitWeight_indicator]
        _ = ((N:ℝ) + 1)*p*(1-p) + (((N:ℝ) + 1)*p)^2 := by
                ring

/-- For a nonempty sample, the weighted mean of the sample mean is `p`. [AbramsLloyd1997] -/
theorem productWeight_sampleMean {N : ℕ} (p : ℝ) (hN : 0 < N) :
    ∑ b : Fin N → Bool, productWeight p b * sampleMean b = p := by
  have hNne : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  calc
    ∑ b, productWeight p b * sampleMean b
        = (∑ b, productWeight p b * sampleSum b) / (N:ℝ) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro b _
            simp only [sampleMean]
            ring
    _ = ((N:ℝ)*p) / (N:ℝ) := by rw [productWeight_sampleSum]
    _ = p := by field_simp [hNne]

/-- For a nonempty sample, the weighted squared deviation of the sample mean from `p` is `p * (1
- p) / N`. [AbramsLloyd1997] -/
theorem productWeight_sampleMean_variance {N : ℕ} (p : ℝ) (hN : 0 < N) :
    ∑ b : Fin N → Bool, productWeight p b * (sampleMean b - p)^2 =
      p*(1-p)/(N:ℝ) := by
  have hNne : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  have hpoint : ∀ b : Fin N → Bool,
      productWeight p b * (sampleMean b - p)^2
        = productWeight p b * (sampleSum b - (N:ℝ)*p)^2 / (N:ℝ)^2 := by
    intro b
    simp only [sampleMean]
    field_simp [hNne]
  calc
    ∑ b, productWeight p b * (sampleMean b - p)^2
        = ∑ b, productWeight p b * (sampleSum b - (N:ℝ)*p)^2 / (N:ℝ)^2 := by
            apply Finset.sum_congr rfl
            intro b _
            exact hpoint b
    _ = (∑ b, productWeight p b * (sampleSum b - (N:ℝ)*p)^2) / (N:ℝ)^2 := by
            rw [Finset.sum_div]
    _ = (∑ b, (productWeight p b * (sampleSum b)^2
          - (2*(N:ℝ)*p) * (productWeight p b * sampleSum b)
          + ((N:ℝ)*p)^2 * productWeight p b)) / (N:ℝ)^2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro b _
            ring
    _ = ((∑ b, productWeight p b * (sampleSum b)^2)
          - (2*(N:ℝ)*p) * (∑ b, productWeight p b * sampleSum b)
          + ((N:ℝ)*p)^2 * (∑ b, productWeight p b)) / (N:ℝ)^2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (((N:ℝ)*p*(1-p) + ((N:ℝ)*p)^2)
          - (2*(N:ℝ)*p) * ((N:ℝ)*p)
          + ((N:ℝ)*p)^2 * 1) / (N:ℝ)^2 := by
            rw [productWeight_sampleSum_sq, productWeight_sampleSum,
              productWeight_sum_one]
    _ = p*(1-p)/(N:ℝ) := by
            field_simp [hNne]
            ring

/-- For `0 ≤ p ≤ 1` and positive sample size and tolerance, the weight of samples deviating by
at least `ε` is at most `p * (1 - p) / (N * ε ^ 2)`. [AbramsLloyd1997] -/
theorem sample_tail_le_variance {N : ℕ} (p ε : ℝ) (hN : 0 < N)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) :
    (Finset.univ.filter (fun b : Fin N → Bool => ε ≤ |sampleMean b - p|)).sum
        (fun b => productWeight p b) ≤ (p*(1-p)/(N:ℝ)) / ε^2 := by
  have hcheb := chebyshev_finite (fun b : Fin N → Bool => productWeight p b)
    sampleMean (fun b => productWeight_nonneg hp0 hp1 b) p hε
  rwa [productWeight_sampleMean_variance p hN] at hcheb

/-- The expression `p * (1 - p)` is at most `1 / 4` for every real `p`. [AbramsLloyd1997] -/
theorem bernoulli_variance_le_quarter (p : ℝ) : p*(1-p) ≤ (1/4 : ℝ) := by
  nlinarith [sq_nonneg (p - 1/2)]

/-- The single-gate circuit given by the Fourier matrix `QFTMatrix M`. -/
def qftWord (M : ℕ) : Circuit (Fin M) := [.gate (QFTMatrix M)]

/-- For `M > 0`, the Fourier circuit is unitary, has no queries and one gate, and acts by
`QFTMatrix M`. [AbramsLloyd1997] -/
theorem qftWord_correct (M : ℕ) (hM : 0 < M) (ψ : QState (Fin M)) :
    IsUnitaryCircuit (qftWord M) ∧ QueryCount (qftWord M) = 0 ∧
      GateCount (qftWord M) = 1 ∧
      Run 1 (qftWord M) ψ = ApplyGate (QFTMatrix M) ψ := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [qftWord, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact qftMatrix_unitary hM

end Qatlib.Papers.ManyBodyFermi97.MainResults.SampleVariance
