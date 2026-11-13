/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.LinearSystemCostModelDefs

/-!
# Signed dyadic quantization

`signedQuantizeReal` rounds the magnitude of a real number with the existing natural-floor
quantizer and restores its sign. `signedQuantizeComplex` applies this construction to both
components, supplying finite-precision inputs for the HHL computations of
[HarrowHassidimLloyd2009].

## Main statements

* `quantizeReal_nonneg_error`: downward rounding has error below `(1 / 2)^k` on nonnegative
  inputs.
* `signedQuantizeReal_error`: the same absolute error bound holds for every real input.
* `signedQuantizeComplex_error`: both complex components satisfy the dyadic error bound.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter (quantizeReal)

/-- The rational dyadic quantization of the magnitude of `t`, with the sign of `t` restored. -/
noncomputable def signedQuantizeReal (k : ℕ) (t : ℝ) : ℚ :=
  if 0 ≤ t then quantizeReal k t else -(quantizeReal k (-t))

/-- The complex value obtained by applying `signedQuantizeReal` to its real and imaginary parts. -/
noncomputable def signedQuantizeComplex (k : ℕ) (z : ℂ) : ℂ :=
  ((signedQuantizeReal k z.re : ℚ) : ℂ) + ((signedQuantizeReal k z.im : ℚ) : ℂ) * Complex.I

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.S1_Q03
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

/-- For nonnegative input, the natural-floor quantizer rounds downward with error strictly less
than `(1 / 2)^k`. -/
theorem quantizeReal_nonneg_error (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ t - ((quantizeReal k t : ℚ) : ℝ) ∧
      t - ((quantizeReal k t : ℚ) : ℝ) < (1 / 2 : ℝ) ^ k := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hmul : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
    rw [← mul_pow, one_div_mul_cancel (by norm_num : (2:ℝ) ≠ 0), one_pow]
  have hq : ((quantizeReal k t : ℚ) : ℝ)
      = (Nat.floor ((2:ℝ) ^ k * t) : ℝ) / (2:ℝ) ^ k := by
    unfold quantizeReal
    push_cast
    rfl
  have hle : (Nat.floor ((2:ℝ) ^ k * t) : ℝ) ≤ (2:ℝ) ^ k * t :=
    Nat.floor_le (mul_nonneg hpow.le ht)
  have hlt : (2:ℝ) ^ k * t < (Nat.floor ((2:ℝ) ^ k * t) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfin : (2:ℝ) ^ k * t - (Nat.floor ((2:ℝ) ^ k * t) : ℝ) < 1 := by linarith
  rw [hq]
  have hdiv : t - (Nat.floor ((2:ℝ) ^ k * t) : ℝ) / (2:ℝ) ^ k
      = ((2:ℝ) ^ k * t - (Nat.floor ((2:ℝ) ^ k * t) : ℝ)) / (2:ℝ) ^ k := by
    field_simp
  rw [hdiv]
  constructor
  · exact div_nonneg (by linarith) hpow.le
  · exact (div_lt_iff₀ hpow).2 (by linarith)

/-- Signed real quantization has absolute error strictly less than `(1 / 2)^k` for every real
input. -/
theorem signedQuantizeReal_error (k : ℕ) (t : ℝ) :
    |t - ((signedQuantizeReal k t : ℚ) : ℝ)| < (1 / 2 : ℝ) ^ k := by
  unfold signedQuantizeReal
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    have h := quantizeReal_nonneg_error k t ht
    rw [abs_of_nonneg h.1]
    exact h.2
  · rw [if_neg ht]
    have h := quantizeReal_nonneg_error k (-t) (by linarith)
    have heq : t - ((-(quantizeReal k (-t)) : ℚ) : ℝ)
        = -((-t) - ((quantizeReal k (-t) : ℚ) : ℝ)) := by
      push_cast
      ring
    rw [heq, abs_neg, abs_of_nonneg h.1]
    exact h.2

/-- Signed complex quantization has error strictly less than `(1 / 2)^k` in each real and
imaginary component. -/
theorem signedQuantizeComplex_error (k : ℕ) (z : ℂ) :
    |z.re - (signedQuantizeComplex k z).re| < (1 / 2 : ℝ) ^ k ∧
      |z.im - (signedQuantizeComplex k z).im| < (1 / 2 : ℝ) ^ k := by
  unfold signedQuantizeComplex
  constructor
  · have h := signedQuantizeReal_error k z.re
    simpa [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] using! h
  · have h := signedQuantizeReal_error k z.im
    simpa [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] using! h

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.S1_Q03
