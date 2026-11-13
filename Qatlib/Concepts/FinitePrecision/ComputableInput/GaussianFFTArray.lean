/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.GaussianBinaryFFT

/-!
# Vector interfaces for Gaussian binary FFTs

This module supplies vector-input interfaces to the ordinary and positive Gaussian binary FFT
computations. Each certificate combines agreement with the shared run, exact operation counts,
and a binary charge bound under the corresponding intermediate-integer audit.

For background on finite Fourier transforms in quantum computation, see [NielsenChuang2010].

## Main statements

* `gaussianBinaryFFTArray` and `gaussianBinaryPositiveFFTArray`: vector-input wrappers.
* `gaussian_binary_fft_array_certificate`: ordinary transform certificate.
* `gaussian_binary_positive_array_certificate`: positive transform certificate.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput

/-- Applies the Gaussian binary FFT to the entries of a fixed-length input vector. -/
def gaussianBinaryFFTArray (D k : ℕ) (t : GaussianTwiddleTable k)
    (input : Vector GaussianDyadicScalar (2 ^ k)) : GaussianBinaryFFTRun k :=
  gaussianBinaryFFT D k t (fun j => input[j.val])

/-- Applies the positive Gaussian binary FFT to the entries of a fixed-length input vector. -/
def gaussianBinaryPositiveFFTArray (D k : ℕ) (t : GaussianTwiddleTable k)
    (input : Vector GaussianDyadicScalar (2 ^ k)) : GaussianBinaryFFTRun k :=
  gaussianBinaryPositiveFFT D k t (fun j => input[j.val])

/-- Under the stated integer audit, the vector-input transform agrees with the shared run and
its values, has the exact product and addition counts, and has charge at most `2048 * k * 2
^ k * (W + 1) ^ 2`. -/
theorem gaussian_binary_fft_array_certificate (D k W : ℕ) (t : GaussianTwiddleTable k)
    (input : Vector GaussianDyadicScalar (2 ^ k))
    (h : GaussianFFTIntegerBounded (D : ℤ) k t (fun j => input[j.val]) (2 ^ W - 1)) :
    let r := gaussianBinaryFFTArray D k t input
    r.run = gaussianSharedFFT (D : ℤ) k t (fun j => input[j.val]) ∧
    r.run.values = (gaussianSharedFFT (D : ℤ) k t (fun j => input[j.val])).values ∧
    2 * r.run.products = k * 2 ^ k ∧ r.run.additions = k * 2 ^ k ∧
    r.charge ≤ 2048 * k * 2 ^ k * (W + 1) ^ 2 := by
  have hv := gaussian_binary_fft_value D k t (fun j => input[j.val])
  have hc := gaussian_shared_fft_counts (D : ℤ) k t (fun j => input[j.val])
  dsimp only [gaussianBinaryFFTArray]
  refine ⟨hv, congrArg GaussianDyadicFFTRun.values hv, ?_, ?_,
    gaussian_binary_fft_charge D k W t (fun j => input[j.val]) h⟩
  · rw [hv]; exact hc.1
  · rw [hv]; exact hc.2

/-- Under the conjugated-input integer audit, the positive vector-input transform agrees with
the positive shared run and its values, has the exact operation counts, and has charge at
most `4096 * (k + 1) * 2 ^ k * (W + 1) ^ 2`. -/
theorem gaussian_binary_positive_array_certificate (D k W : ℕ) (t : GaussianTwiddleTable k)
    (input : Vector GaussianDyadicScalar (2 ^ k))
    (h : GaussianFFTIntegerBounded (D : ℤ) k t
      (fun j => gaussianScalarConj input[j.val]) (2 ^ W - 1)) :
    let r := gaussianBinaryPositiveFFTArray D k t input
    r.run = gaussianSharedPositiveFFT (D : ℤ) k t (fun j => input[j.val]) ∧
    r.run.values = (gaussianSharedPositiveFFT (D : ℤ) k t (fun j => input[j.val])).values ∧
    2 * r.run.products = k * 2 ^ k ∧ r.run.additions = k * 2 ^ k ∧
    r.charge ≤ 4096 * (k + 1) * 2 ^ k * (W + 1) ^ 2 := by
  have hv := gaussian_binary_positive_value D k t (fun j => input[j.val])
  have hc := gaussian_shared_fft_counts (D : ℤ) k t (fun j => gaussianScalarConj input[j.val])
  dsimp only [gaussianBinaryPositiveFFTArray]
  refine ⟨hv, congrArg GaussianDyadicFFTRun.values hv, ?_, ?_,
    gaussian_binary_positive_charge D k W t (fun j => input[j.val]) h⟩
  · rw [hv]; exact hc.1
  · rw [hv]; exact hc.2

end Qatlib.Concepts.FinitePrecision.ComputableInput
