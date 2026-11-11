/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Source.EngineeredChain

/-!
# Spectral amplitudes of engineered chains

`engineeredEigenvalue` and `engineeredWeight` specify an equally spaced spectrum with
alternating binomial weights. Their generating polynomial gives the closed form
`engineeredSpectralAmplitude_closed` and unit transfer amplitude at time `π / lam`. See
[ChristandlEtAl2004].

## Main statements

* `engineeredWeight_sum_pow`: the weight generating polynomial is a scaled power of `1 - z`.
* `engineeredSpectralAmplitude_closed`: the amplitude is `(-i sin (lam * t / 2)) ^ (N - 1)`.
* `engineered_perfect_transfer`: the amplitude has norm one at `π / lam` for nonzero `lam`.

## References

* [Christandl et al., 2004][ChristandlEtAl2004]
-/

set_option warningAsError false

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open scoped BigOperators
open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section

/-- The engineered energy at index `k`, equal to `lam * (N - 1) / 2 - lam * k` over the reals. -/
def engineeredEigenvalue (N : ℕ) (lam : ℝ) (k : Fin N) : ℝ :=
  lam * (((N : ℝ) - 1) / 2) - lam * (k.val : ℝ)

/-- The complex endpoint weight `(-1) ^ k * choose (N - 1) k / 2 ^ (N - 1)` for the engineered
spectrum. -/
def engineeredWeight (N : ℕ) (k : Fin N) : ℂ :=
  (((-1 : ℝ) ^ k.val * (Nat.choose (N - 1) k.val : ℝ) / 2 ^ (N - 1) : ℝ) : ℂ)

/-- The spectral transfer amplitude formed from the engineered energies and endpoint weights. -/
def engineeredSpectralAmplitude (N : ℕ) (lam t : ℝ) : ℂ :=
  spectralAmplitude (engineeredEigenvalue N lam) (engineeredWeight N) t

/-- Euler's formula for a purely imaginary exponential with real argument. -/
theorem exp_I_mul (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [mul_comm Complex.I (θ : ℂ)]
  simpa [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.exp_mul_I (θ : ℂ)

/-- The difference `1 - exp (iθ)` equals `exp (iθ / 2) * (-2i sin (θ / 2))`. -/
theorem one_sub_exp_mul_I (θ : ℝ) :
    1 - Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) *
        (-(2 : ℂ) * Complex.I * (Real.sin (θ / 2) : ℂ)) := by
  rw [exp_I_mul, exp_I_mul]
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  rw [hc, hs]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]
  push_cast
  ring_nf
  rw [show Complex.I ^ 2 = -1 from by rw [pow_two, Complex.I_mul_I]]
  ring

/-- For positive `N`, the generating polynomial of the engineered weights is `(1 - z) ^ (N - 1)
/ 2 ^ (N - 1)`. See [ChristandlEtAl2004]. -/
theorem engineeredWeight_sum_pow (N : ℕ) (hN : 0 < N) (z : ℂ) :
    (∑ k : Fin N, engineeredWeight N k * z ^ k.val) =
      (1 - z) ^ (N - 1) / (2 : ℂ) ^ (N - 1) := by
  have hterm : ∀ k : Fin N, engineeredWeight N k * z ^ k.val =
      ((((-1 : ℝ) ^ k.val * (Nat.choose (N - 1) k.val : ℝ) / 2 ^ (N - 1) : ℝ) : ℂ) *
        z ^ k.val) := fun k => by simp [engineeredWeight]
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ((((-1 : ℝ) ^ i * (Nat.choose (N - 1) i : ℝ) / 2 ^ (N - 1) : ℝ) : ℂ) *
      z ^ i))]
  calc (∑ i ∈ Finset.range N,
        ((((-1 : ℝ) ^ i * (Nat.choose (N - 1) i : ℝ) / 2 ^ (N - 1) : ℝ) : ℂ) * z ^ i))
      = (1 / (2 : ℂ) ^ (N - 1)) *
          ∑ i ∈ Finset.range N, ((Nat.choose (N - 1) i : ℂ) * (-z) ^ i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [neg_pow]
        push_cast
        ring
    _ = (1 / (2 : ℂ) ^ (N - 1)) * (1 + -z) ^ (N - 1) := by
        congr 1
        rw [show (1 : ℂ) + -z = -z + 1 by ring]
        rw [add_pow]
        rw [show (N - 1) + 1 = N by omega]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [one_pow, mul_one]
        ring
    _ = (1 - z) ^ (N - 1) / (2 : ℂ) ^ (N - 1) := by
        rw [show (1 : ℂ) + -z = 1 - z by ring, one_div, inv_mul_eq_div]

/-- For positive `N`, the engineered spectral amplitude equals `(-i sin (lam * t / 2)) ^ (N -
1)`. See [ChristandlEtAl2004]. -/
theorem engineeredSpectralAmplitude_closed (N : ℕ) (hN : 0 < N) (lam t : ℝ) :
    engineeredSpectralAmplitude N lam t =
      (-(Complex.I) * (Real.sin (lam * t / 2) : ℂ)) ^ (N - 1) := by
  set A : ℂ := Complex.exp (-(Complex.I * ((t * (lam * (((N : ℝ) - 1) / 2)) : ℝ) : ℂ)))
  set z : ℂ := Complex.exp (Complex.I * ((lam * t : ℝ) : ℂ))
  have hphase : ∀ k : Fin N, phase (engineeredEigenvalue N lam k) t = A * z ^ k.val := by
    intro k
    unfold phase engineeredEigenvalue
    rw [show (-(Complex.I * (t : ℂ) *
          ((lam * (((N : ℝ) - 1) / 2) - lam * (k.val : ℝ) : ℝ) : ℂ)))
        = -(Complex.I * ((t * (lam * (((N : ℝ) - 1) / 2)) : ℝ) : ℂ))
            + (k.val : ℂ) * (Complex.I * ((lam * t : ℝ) : ℂ)) by
      push_cast
      ring]
    rw [Complex.exp_add, Complex.exp_nat_mul]
  have hsum : (∑ k : Fin N, engineeredWeight N k * phase (engineeredEigenvalue N lam k) t)
      = A * ((1 - z) ^ (N - 1) / (2 : ℂ) ^ (N - 1)) := by
    calc (∑ k : Fin N, engineeredWeight N k * phase (engineeredEigenvalue N lam k) t)
        = ∑ k : Fin N, engineeredWeight N k * (A * z ^ k.val) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hphase k]
      _ = A * ∑ k : Fin N, engineeredWeight N k * z ^ k.val := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
      _ = A * ((1 - z) ^ (N - 1) / (2 : ℂ) ^ (N - 1)) := by
          rw [engineeredWeight_sum_pow N hN z]
  rw [engineeredSpectralAmplitude, spectralAmplitude, hsum]
  have hz : 1 - z = Complex.exp (Complex.I * ((lam * t / 2 : ℝ) : ℂ)) *
      (-(2 : ℂ) * Complex.I * (Real.sin (lam * t / 2) : ℂ)) := one_sub_exp_mul_I (lam * t)
  rw [hz, mul_pow]
  have hAA : A * Complex.exp (Complex.I * ((lam * t / 2 : ℝ) : ℂ)) ^ (N - 1) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    have harg : -(Complex.I * ((t * (lam * (((N : ℝ) - 1) / 2)) : ℝ) : ℂ)) +
        ((N - 1 : ℕ) : ℂ) * (Complex.I * ((lam * t / 2 : ℝ) : ℂ)) = 0 := by
      have hN1 : ((N - 1 : ℕ) : ℂ) = (N : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ N), Nat.cast_one]
      rw [hN1]
      push_cast
      ring
    rw [harg, Complex.exp_zero]
  have hFG : (-(2 : ℂ) * Complex.I * (Real.sin (lam * t / 2) : ℂ)) =
      (2 : ℂ) * (-(Complex.I) * (Real.sin (lam * t / 2) : ℂ)) := by ring
  rw [hFG, mul_pow]
  have hsplit : A * (Complex.exp (Complex.I * ((lam * t / 2 : ℝ) : ℂ)) ^ (N - 1) *
      ((2 : ℂ) ^ (N - 1) * (-(Complex.I) * (Real.sin (lam * t / 2) : ℂ)) ^ (N - 1)) /
        (2 : ℂ) ^ (N - 1)) =
      (A * Complex.exp (Complex.I * ((lam * t / 2 : ℝ) : ℂ)) ^ (N - 1)) *
        (((2 : ℂ) ^ (N - 1) * (-(Complex.I) * (Real.sin (lam * t / 2) : ℂ)) ^ (N - 1)) /
          (2 : ℂ) ^ (N - 1)) := by ring
  rw [hsplit, hAA, one_mul]
  have h2 : ((2 : ℂ) ^ (N - 1)) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
  rw [mul_div_cancel_left₀ _ h2]

/-- For positive `N` and nonzero `lam`, the engineered spectral amplitude has norm one at time
`π / lam`. See [ChristandlEtAl2004]. -/
theorem engineered_perfect_transfer (N : ℕ) (hN : 0 < N) (lam : ℝ) (hlam : lam ≠ 0) :
    ‖engineeredSpectralAmplitude N lam (Real.pi / lam)‖ = 1 := by
  rw [engineeredSpectralAmplitude_closed N hN]
  have hsin : lam * (Real.pi / lam) / 2 = Real.pi / 2 := by
    field_simp
  rw [hsin, Real.sin_pi_div_two]
  simp

/-- For positive `N`, the norms of the engineered endpoint weights sum to one. See
[ChristandlEtAl2004]. -/
theorem engineeredWeight_abs_sum (N : ℕ) (hN : 0 < N) :
    (∑ k : Fin N, ‖engineeredWeight N k‖) = 1 := by
  have hterm : ∀ k : Fin N, ‖engineeredWeight N k‖ =
      (Nat.choose (N - 1) (k : ℕ) : ℝ) / 2 ^ (N - 1) := by
    intro k
    simp only [engineeredWeight, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_div, abs_mul, abs_pow]
    have h1 : |(-1 : ℝ)| = 1 := by norm_num
    rw [h1, one_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.choose (N - 1) (k : ℕ) : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (N - 1)))]
    ring
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => (Nat.choose (N - 1) i : ℝ) / 2 ^ (N - 1))]
  rw [← Finset.sum_div]
  have hsum : (∑ i ∈ Finset.range N, (Nat.choose (N - 1) i : ℝ)) =
      ((2 : ℕ) ^ (N - 1) : ℝ) := by
    have h1 : ((∑ i ∈ Finset.range N, Nat.choose (N - 1) i : ℕ) : ℝ) =
        ∑ i ∈ Finset.range N, (Nat.choose (N - 1) i : ℝ) := by
      push_cast
      rfl
    rw [← h1]
    have hrange : Finset.range N = Finset.range ((N - 1) + 1) := by
      congr 1
      omega
    rw [hrange, Nat.sum_range_choose]
    push_cast
    simp
  rw [hsum, show ((2 : ℕ) ^ (N - 1) : ℝ) = (2 : ℝ) ^ (N - 1) by push_cast; simp]
  exact div_self (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
