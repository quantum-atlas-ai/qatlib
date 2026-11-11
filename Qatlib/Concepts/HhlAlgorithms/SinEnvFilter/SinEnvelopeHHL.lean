/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.Analysis.PSeries
import Qatlib.Concepts.HhlErrorBridge.FilterStability

/-!
# Sine-envelope preparation and phase-estimation bounds

`sinEnvelopeState`, `sinEnvelopePrep`, and `sinEnvelopeFlagRotation` implement sine-envelope
preparation and the three-state filter used in the HHL construction [HarrowHassidimLloyd2009].
The module proves preparation unitarity, state normalization, and the corrected relative
filter-stability estimate.

For `sinEnvelopeKernel`, it derives finite Fourier and geometric-sum identities, a
factorization, an inverse fourth-power tail bound in circular phase distance, and an explicit
bound on the scaled second moment.

## Main statements

* `sin_envelope_state_normalized_and_prep`: normalized sine-envelope preparation by a unitary
  reflection.
* `sin_envelope_kernel_geometric_identity`: the kernel as a difference of shifted geometric
  sums.
* `sin_envelope_kernel_far_label_tail`: the explicit fourth-power probability tail.
* `sin_envelope_kernel_second_moment`: the scaled error second moment is at most `4 * π^2 + 40 *
  π^4 / 3`.

## References

* [Harrow et al., 2009, Appendix A][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

open Matrix
open scoped Real
open Qatlib.Concepts.HhlErrorBridge.FilterStability

/-- The sine-envelope vector with amplitudes `sqrt (2 / M) * sin (π * (τ + 1 / 2) / M)`. -/
noncomputable def sinEnvelopeState (M : ℕ) : QState (Fin M) :=
  fun τ =>
    (Real.sqrt (2 / (M : ℝ)) : ℂ) *
      (Real.sin (Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ)) : ℂ)

/-- The phase-estimation amplitude obtained by applying inverse QFT to the phase-modulated
sine-envelope vector. -/
noncomputable def sinEnvelopeKernel (M : ℕ) (φ : ℝ) (z : Fin M) : ℂ :=
  ApplyGate (QFTMatrix M)ᴴ
      (fun τ => Complex.exp (2 * Real.pi * Complex.I * ((τ.val : ℝ) * φ)) *
        sinEnvelopeState M τ) z

/-- The scaled phase discrepancy `2 * π * (M * φ - z)`. -/
noncomputable def sinEnvelopeDelta (M : ℕ) (φ : ℝ) (z : Fin M) : ℝ :=
  2 * Real.pi * ((M : ℝ) * φ - (z.val : ℝ))

/-- The geometric-sum quotient `(1 - exp (I * w)) / (1 - exp (I * w / M))`. -/
noncomputable def sinEnvelopeGeoSum (M : ℕ) (w : ℝ) : ℂ :=
  (1 - Complex.exp (Complex.I * w)) / (1 - Complex.exp (Complex.I * w / (M : ℝ)))

/-- The scaled sum of the zero basis state and the sine-envelope state used as the preparation
reflection direction. -/
noncomputable def sinEnvelopePrepUnit (M : ℕ) (hM : 2 ≤ M) : QState (Fin M) :=
  ((Real.sqrt (2 * (1 + (sinEnvelopeState M ⟨0, by omega⟩).re)) : ℂ))⁻¹ •
    (Ket (⟨0, by omega⟩ : Fin M) + sinEnvelopeState M)

/-- The reflection about `sinEnvelopePrepUnit` used to prepare the sine-envelope state. -/
noncomputable def sinEnvelopePrep (M : ℕ) (hM : 2 ≤ M) :
    Matrix (Fin M) (Fin M) ℂ :=
  ReflectionAbout (outerProduct (sinEnvelopePrepUnit M hM))

/-- The scaled sum of filter label zero and `sinEnvelopeHVector d θ` used as the flag-rotation
reflection direction. -/
noncomputable def sinEnvelopeFlagRotationDir (d θ : ℝ) : QState (Fin 3) :=
  ((Real.sqrt (2 * (1 + (sinEnvelopeHVector d θ 0).re)) : ℂ))⁻¹ •
    ((fun s => if s = 0 then (1 : ℂ) else 0) + sinEnvelopeHVector d θ)

/-- The three-state reflection defined by the outer product of `sinEnvelopeFlagRotationDir d θ`. -/
noncomputable def sinEnvelopeFlagRotation (d θ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ReflectionAbout (outerProduct (sinEnvelopeFlagRotationDir d θ))

/-- The reflection defined by the scaled sum of a basis state and a real vector equals
`nonnegativePrepare` for that vector. -/
private theorem sin_envelope_real_preparation_eq {J : Type} [Fintype J] [DecidableEq J]
    (r : J → ℝ) (j₀ : J) :
    ReflectionAbout (outerProduct
      (((Real.sqrt (2 * (1+r j₀)) : ℂ))⁻¹ • (Ket j₀ + fun j => (r j : ℂ)))) =
      Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare r j₀ := by
  have ha : Qatlib.Concepts.BlockEncoding.EncodingCore.preparationAxis r j₀ =
      (((Real.sqrt (2 * (1+r j₀)) : ℂ))⁻¹ • (Ket j₀ + fun j => (r j : ℂ))) := by
    ext j
    by_cases hj : j = j₀ <;>
      simp [Qatlib.Concepts.BlockEncoding.EncodingCore.preparationAxis, Qatlib.Concepts.BlockEncoding.EncodingCore.preparationDenominator, Ket,
        div_eq_mul_inv, mul_comm, hj]
  unfold Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare
  rw [ha]
  congr 1
  ext i j
  simp [outerProduct, Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector, Matrix.mul_apply]
  ring

/-- For positive `d`, the flag rotation is unitary and sends filter label zero to
`sinEnvelopeHVector d θ`; see [Harrow et al., Appendix A.1][HarrowHassidimLloyd2009]. -/
theorem sin_envelope_flag_rotation_unitary_and_column (d θ : ℝ) (hd : 0 < d) :
    sinEnvelopeFlagRotation d θ ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
      sinEnvelopeFlagRotation d θ *ᵥ Ket (0 : Fin 3) = sinEnvelopeHVector d θ := by
  let r : Fin 3 → ℝ := fun s => (sinEnvelopeHVector d θ s).re
  have hr : ∀ s, 0 ≤ r s := by
    intro s
    have hf := sin_envelope_filter_nonnegative d θ hd
    dsimp [r, sinEnvelopeHVector]
    split_ifs <;> simp only [Complex.ofReal_re]
    · exact Real.sqrt_nonneg _
    · exact hf.1
    · exact hf.2
  have hc : (fun s => (r s : ℂ)) = sinEnvelopeHVector d θ := by
    ext s
    simp [r, sinEnvelopeHVector]
    split_ifs <;> rfl
  have hn : ∑ s, (r s)^2 = 1 := by
    have hn := sin_envelope_h_normalized d θ hd
    rw [← hc] at hn
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using! hn
  have he : sinEnvelopeFlagRotation d θ = Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare r 0 := by
    unfold sinEnvelopeFlagRotation sinEnvelopeFlagRotationDir
    change ReflectionAbout (outerProduct
      (((Real.sqrt (2 * (1+r 0)) : ℂ))⁻¹ •
        ((fun s : Fin 3 => if s = 0 then (1 : ℂ) else 0) + sinEnvelopeHVector d θ))) = _
    rw [← hc]
    exact sin_envelope_real_preparation_eq r 0
  rw [he]
  exact ⟨Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_unitary r 0 hr hn,
    (Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_mulVec_ket r 0 hr).trans hc⟩

/-- For `M ≥ 2`, the cosines of the equally spaced half-step angles sum to zero. -/
private theorem sin_envelope_cosine_sum (M : ℕ) (hM : 2 ≤ M) :
    ∑ τ : Fin M, Real.cos (2 * (Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ))) = 0 := by
  have hM0 : 0 < M := by omega
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hdiv : ¬ (M : ℤ) ∣ 1 := by
    intro hd
    have hd' : M ∣ 1 := by exact_mod_cast hd
    have := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hd'
    omega
  have hroot : ∑ τ : Fin M, primRoot M ^ τ.val = 0 := by
    simpa only [one_mul, zpow_natCast] using! (sum_primRoot_zpow hM0 hdiv)
  have ht (τ : Fin M) :
      Complex.exp ((2 * (Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ)) : ℝ) * Complex.I) =
        Complex.exp (Real.pi * Complex.I / (M : ℝ)) * primRoot M ^ τ.val := by
    unfold primRoot
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have he : ∑ τ : Fin M,
      Complex.exp ((2 * (Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ)) : ℝ) * Complex.I) = 0 := by
    simp_rw [ht]
    rw [← Finset.mul_sum, hroot, mul_zero]
  have hre := congrArg Complex.re he
  simpa only [Complex.re_sum, Complex.exp_ofReal_mul_I_re, Complex.zero_re] using! hre

/-- For `M ≥ 2`, the squared sines at the envelope's half-step angles sum to `M / 2`. -/
theorem sin_envelope_sine_sum_sq (M : ℕ) (hM : 2 ≤ M) :
    ∑ τ : Fin M, (Real.sin (Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ)))^2 =
      (M : ℝ)/2 := by
  have ht (τ : Fin M) :
      (Real.sin (Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ)))^2 =
        (1 - Real.cos (2 * (Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ)))) / 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ))]
  simp_rw [ht]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, sin_envelope_cosine_sum M hM]
  simp

/-- For `M ≥ 2`, the squared moduli of the sine-envelope amplitudes sum to one. -/
theorem sin_envelope_state_normalized (M : ℕ) (hM : 2 ≤ M) :
    ∑ τ, ‖sinEnvelopeState M τ‖^2 = 1 := by
  have hMr : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hrad : 0 ≤ 2 / (M : ℝ) := by positivity
  simp only [sinEnvelopeState, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt hrad]
  rw [← Finset.mul_sum, sin_envelope_sine_sum_sq M hM]
  field_simp

/-- Every sine-envelope amplitude has nonnegative real part for `M ≥ 2`. -/
private theorem sin_envelope_state_real_nonnegative (M : ℕ) (hM : 2 ≤ M) (τ : Fin M) :
    0 ≤ (sinEnvelopeState M τ).re := by
  have hMr : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hv : (τ.val : ℝ) + 1/2 ≤ (M : ℝ) := by
    have hv' : (τ.val : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast τ.isLt
    linarith
  have ha : 0 ≤ Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ) := by positivity
  have hb : Real.pi * ((τ.val : ℝ)+1/2) / (M : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ hMr).mpr
    exact mul_le_mul_of_nonneg_left hv Real.pi_pos.le
  simpa only [sinEnvelopeState, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using!
      mul_nonneg (Real.sqrt_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi ha hb)

/-- For `M ≥ 2`, the sine-envelope state is normalized and its preparation matrix is unitary and
sends the zero basis state to it. See [Harrow et al., Appendix
A.1][HarrowHassidimLloyd2009]. -/
theorem sin_envelope_state_normalized_and_prep (M : ℕ) (hM : 2 ≤ M) :
    (∑ τ, ‖sinEnvelopeState M τ‖^2 = 1) ∧
      sinEnvelopePrep M hM ∈ Matrix.unitaryGroup (Fin M) ℂ ∧
      sinEnvelopePrep M hM *ᵥ Ket (⟨0, by omega⟩ : Fin M) = sinEnvelopeState M := by
  let r : Fin M → ℝ := fun τ => (sinEnvelopeState M τ).re
  have hr : ∀ τ, 0 ≤ r τ := sin_envelope_state_real_nonnegative M hM
  have hc : (fun τ => (r τ : ℂ)) = sinEnvelopeState M := by
    ext τ
    simp [r, sinEnvelopeState, -Complex.ofReal_sin]
  have hn := sin_envelope_state_normalized M hM
  have hnr : ∑ τ, (r τ)^2 = 1 := by
    rw [← hc] at hn
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using! hn
  have he : sinEnvelopePrep M hM = Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare r ⟨0, by omega⟩ := by
    unfold sinEnvelopePrep sinEnvelopePrepUnit
    change ReflectionAbout (outerProduct
      (((Real.sqrt (2 * (1+r ⟨0, by omega⟩)) : ℂ))⁻¹ •
        (Ket (⟨0, by omega⟩ : Fin M) + sinEnvelopeState M))) = _
    rw [← hc]
    exact sin_envelope_real_preparation_eq r ⟨0, by omega⟩
  rw [he]
  exact ⟨hn, Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_unitary r ⟨0, by omega⟩ hr hnr,
    (Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_mulVec_ket r ⟨0, by omega⟩ hr).trans hc⟩

/-- For `M ≥ 2`, the squared moduli of the phase-estimation kernel sum to one; see [Harrow et
al., Appendix A.3][HarrowHassidimLloyd2009]. -/
theorem sin_envelope_kernel_normalized (M : ℕ) (φ : ℝ) (hM : 2 ≤ M) :
    ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 = 1 := by
  have hn : Normalized (fun τ : Fin M =>
      Complex.exp (2 * Real.pi * Complex.I * ((τ.val : ℝ) * φ)) * sinEnvelopeState M τ) := by
    simpa [Normalized, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im] using!
      sin_envelope_state_normalized M hM
  exact normalized_applyGate
      (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary (qftMatrix_unitary (by omega))) hn

/-- Adding an integer to the input phase leaves the sine-envelope kernel unchanged. -/
theorem sin_envelope_kernel_int_add (M : ℕ) (φ : ℝ) (z : Fin M) (c : ℤ) :
    sinEnvelopeKernel M (φ+(c : ℝ)) z = sinEnvelopeKernel M φ z := by
  unfold sinEnvelopeKernel
  congr 1
  ext τ
  have h := exp_two_pi_I_mul_int φ τ.val c
  push_cast at h ⊢
  rw [h]

/-- The sine-envelope kernel equals its explicit finite Fourier sum of phase factors weighted by
half-step sine amplitudes. -/
theorem sin_envelope_kernel_sum_formula (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M) :
    sinEnvelopeKernel M φ z = ((Real.sqrt 2 : ℂ)/(M : ℂ)) *
      ∑ τ : Fin M,
        Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*(φ-(z.val : ℝ)/(M : ℝ)))) *
          (Real.sin (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ)) : ℂ) := by
  have hM0 : 0 < M := by omega
  have hcoef : (Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (2/(M : ℝ)) : ℂ) =
      (Real.sqrt 2 : ℂ)/(M : ℂ) := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2), Complex.ofReal_div]
    calc
      _ = (Real.sqrt 2 : ℂ) *
          ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (M : ℝ) : ℂ)⁻¹) := by ring
      _ = _ := by rw [inv_sqrt_mul_inv_sqrt hM0]; rfl
  have hconj (τ : Fin M) :
      (starRingEnd ℂ) (QFTMatrix M τ z) = (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        primRoot M ^ (-((τ.val : ℤ)*(z.val : ℤ))) := by
    rw [qftMatrix_apply, map_mul, map_inv₀, Complex.conj_ofReal, primRoot_conj_zpow]
  have ht (τ : Fin M) :
      (starRingEnd ℂ) (QFTMatrix M τ z) *
        (Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*φ)) * sinEnvelopeState M τ) =
      ((Real.sqrt 2 : ℂ)/(M : ℂ)) *
        (Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*(φ-(z.val : ℝ)/(M : ℝ)))) *
          (Real.sin (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ)) : ℂ)) := by
    rw [hconj, primRoot_zpow_eq_exp, sinEnvelopeState]
    rw [show (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        Complex.exp (2*Real.pi*Complex.I*((((-((τ.val : ℤ)*(z.val : ℤ)) : ℤ) : ℝ)/(M : ℝ)))) *
        (Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*φ)) *
          ((Real.sqrt (2/(M : ℝ)) : ℂ) *
            (Real.sin (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ)) : ℂ))) =
        ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (2/(M : ℝ)) : ℂ)) *
          (Complex.exp (2*Real.pi*Complex.I*((((-((τ.val : ℤ)*(z.val : ℤ)) : ℤ) : ℝ)/(M : ℝ)))) *
            Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*φ)) *
            (Real.sin (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ)) : ℂ)) by ring]
    rw [hcoef, ← Complex.exp_add]
    congr 2
    congr 1
    push_cast
    ring
  simp only [sinEnvelopeKernel, ApplyGate, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  simp only [starRingEnd_apply] at ht
  rw [Finset.sum_congr rfl (fun τ _ => ht τ), ← Finset.mul_sum]

/-- When `exp (I * w / M) ≠ 1`, the finite exponential sum equals `sinEnvelopeGeoSum M w`. -/
private theorem sin_envelope_geometric_sum (M : ℕ) (hM : 2 ≤ M) (w : ℝ)
    (hne : Complex.exp (Complex.I * w / (M : ℝ)) ≠ 1) :
    (∑ τ : Fin M, Complex.exp (Complex.I * w * (τ.val : ℝ) / (M : ℝ))) =
      sinEnvelopeGeoSum M w := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have ht (τ : Fin M) : Complex.exp (Complex.I * w * (τ.val : ℝ) / (M : ℝ)) =
      (Complex.exp (Complex.I * w / (M : ℝ))) ^ τ.val := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hp : (Complex.exp (Complex.I * w / (M : ℝ))) ^ M = Complex.exp (Complex.I * w) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simp_rw [ht]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hne, hp]
  unfold sinEnvelopeGeoSum
  rw [show (1 : ℂ) - Complex.exp (Complex.I * w) =
      -(Complex.exp (Complex.I * w)-1) by ring,
    show (1 : ℂ) - Complex.exp (Complex.I * w/(M : ℝ)) =
      -(Complex.exp (Complex.I * w/(M : ℝ))-1) by ring, neg_div_neg_eq]

/-- The real sine, cast to the complex numbers, equals the difference of its two complex
exponentials divided by `2 * I`. -/
private theorem sin_envelope_sine_exp (t : ℝ) :
    (Real.sin t : ℂ) = (Complex.exp (Complex.I * t) - Complex.exp (-(Complex.I * t))) /
      (2 * Complex.I) := by
  rw [Complex.ofReal_sin, Complex.sin]
  field_simp
  rw [pow_two, Complex.I_mul_I]
  ring

/-- Away from the two exceptional geometric ratios, the kernel equals the stated difference of
geometric sums shifted by `π`; see [Harrow et al., Appendix A.3][HarrowHassidimLloyd2009]. -/
theorem sin_envelope_kernel_geometric_identity (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hp : Complex.exp (Complex.I * (sinEnvelopeDelta M φ z + Real.pi) / (M : ℝ)) ≠ 1)
    (hm : Complex.exp (Complex.I * (sinEnvelopeDelta M φ z - Real.pi) / (M : ℝ)) ≠ 1) :
    sinEnvelopeKernel M φ z =
      ((Real.sqrt 2 : ℂ) / (2 * Complex.I * (M : ℝ))) *
        (Complex.exp (Complex.I * Real.pi / (2 * (M : ℝ))) *
            sinEnvelopeGeoSum M (sinEnvelopeDelta M φ z + Real.pi) -
          Complex.exp (-(Complex.I * Real.pi / (2 * (M : ℝ)))) *
            sinEnvelopeGeoSum M (sinEnvelopeDelta M φ z - Real.pi)) := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have ht (τ : Fin M) :
      Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*(φ-(z.val : ℝ)/(M : ℝ)))) *
          (Real.sin (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ)) : ℂ) =
      (Complex.exp (Complex.I * Real.pi / (2 * (M : ℝ))) *
          Complex.exp (Complex.I * (sinEnvelopeDelta M φ z + Real.pi) * (τ.val : ℝ) / (M : ℝ)) -
        Complex.exp (-(Complex.I * Real.pi / (2 * (M : ℝ)))) *
          Complex.exp (Complex.I * (sinEnvelopeDelta M φ z - Real.pi) * (τ.val : ℝ) / (M : ℝ))) /
        (2 * Complex.I) := by
    have hplus :
        Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*(φ-(z.val : ℝ)/(M : ℝ)))) *
          Complex.exp (Complex.I * (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ))) =
        Complex.exp (Complex.I * Real.pi / (2 * (M : ℝ))) *
          Complex.exp (Complex.I * (sinEnvelopeDelta M φ z + Real.pi) * (τ.val : ℝ) / (M : ℝ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      unfold sinEnvelopeDelta
      push_cast
      field_simp
      ring
    have hminus :
        Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*(φ-(z.val : ℝ)/(M : ℝ)))) *
          Complex.exp (-(Complex.I * (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ)))) =
        Complex.exp (-(Complex.I * Real.pi / (2 * (M : ℝ)))) *
          Complex.exp (Complex.I * (sinEnvelopeDelta M φ z - Real.pi) * (τ.val : ℝ) / (M : ℝ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      unfold sinEnvelopeDelta
      push_cast
      field_simp
      ring
    rw [sin_envelope_sine_exp]
    push_cast at hplus hminus ⊢
    calc
      _ = (Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*(φ-(z.val : ℝ)/(M : ℝ)))) *
          Complex.exp (Complex.I * (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ))) -
        Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*(φ-(z.val : ℝ)/(M : ℝ)))) *
          Complex.exp (-(Complex.I * (Real.pi*((τ.val : ℝ)+1/2)/(M : ℝ))))) /
          (2 * Complex.I) := by push_cast; ring
      _ = _ := by push_cast; rw [hplus, hminus]
  have hgp := sin_envelope_geometric_sum M hM (sinEnvelopeDelta M φ z + Real.pi)
    (by simpa only [Complex.ofReal_add] using! hp)
  have hgm := sin_envelope_geometric_sum M hM (sinEnvelopeDelta M φ z - Real.pi)
    (by simpa only [Complex.ofReal_sub] using! hm)
  push_cast at hgp hgm
  rw [sin_envelope_kernel_sum_formula M φ z hM,
    Finset.sum_congr rfl (fun τ _ => ht τ), ← Finset.sum_div,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  rw [hgp, hgm]
  ring

/-- On the stated phase ranges, the two selected filter amplitudes satisfy the relative
squared-error bound with coefficient `2 * π^2 * (1 / (2 * d))^2`. This is the corrected
stability estimate for [Harrow et al., Lemma 3][HarrowHassidimLloyd2009]. -/
theorem sin_envelope_filter_stability (d θ θ' : ℝ) (hd : 0 < d)
    (_hθ : 0 ≤ θ) (_hθ' : θ ≤ 1/4) (_hl : -1/2 ≤ θ') (_hu : θ' ≤ 1/2) :
    (sinEnvelopeFilterF d θ-sinEnvelopeFilterF d θ')^2 +
      (sinEnvelopeFilterG d θ-sinEnvelopeFilterG d θ')^2 ≤
      2*Real.pi^2*(1/(2*d))^2*(θ-θ')^2*
        (sinEnvelopeFilterF d θ^2+sinEnvelopeFilterG d θ^2) :=
  sin_envelope_filter_stability_global d θ θ' hd

/-- For `0 ≤ t ≤ 1 / 2`, the lower bound `2 * t ≤ sin (π * t)` holds. -/
private theorem sin_envelope_sine_lower (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 1/2) :
    2*t ≤ Real.sin (Real.pi*t) := by
  have h := Real.mul_le_sin (show 0 ≤ Real.pi*t by positivity)
    (show Real.pi*t ≤ Real.pi/2 by nlinarith [Real.pi_pos])
  have he : 2/Real.pi*(Real.pi*t) = 2*t := by field_simp
  rwa [he] at h

/-- For `1 / M ≤ r ≤ 1 / 2`, the product of the two shifted sine magnitudes is at least `r^2`. -/
theorem sin_envelope_far_sine_product (M : ℕ) (hM : 2 ≤ M) (r : ℝ)
    (hr : 1/(M : ℝ) ≤ r) (hr' : r ≤ 1/2) :
    r^2 ≤ |Real.sin (Real.pi*(r-1/(2*(M : ℝ))))| *
      |Real.sin (Real.pi*(r+1/(2*(M : ℝ))))| := by
  let h : ℝ := 1/(2*(M : ℝ))
  have hMr : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hmpos : (0:ℝ) < M := by linarith
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hh : h ≤ 1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hrr : 2*h ≤ r := by
    have he : 2*h = 1/(M : ℝ) := by dsimp [h]; ring
    rw [he]
    exact hr
  have h₁ := sin_envelope_sine_lower (r-h) (by linarith) (by linarith)
  have hs₁ : 0 ≤ Real.sin (Real.pi*(r-h)) := by linarith
  change r^2 ≤ |Real.sin (Real.pi*(r-h))| * |Real.sin (Real.pi*(r+h))|
  by_cases hc : r+h ≤ 1/2
  · have h₂ := sin_envelope_sine_lower (r+h) (by linarith) hc
    have hs₂ : 0 ≤ Real.sin (Real.pi*(r+h)) := by linarith
    rw [abs_of_nonneg hs₁, abs_of_nonneg hs₂]
    have hp := mul_le_mul h₁ h₂ (show 0 ≤ 2*(r+h) by linarith) hs₁
    nlinarith

  · have h₂ := sin_envelope_sine_lower (1-r-h) (by linarith) (by linarith)
    have hs₂ : 0 ≤ Real.sin (Real.pi*(1-r-h)) := by linarith
    have he : Real.sin (Real.pi*(r+h)) = Real.sin (Real.pi*(1-r-h)) := by
      rw [show Real.pi*(1-r-h) = Real.pi-Real.pi*(r+h) by ring, Real.sin_pi_sub]
    rw [he, abs_of_nonneg hs₁, abs_of_nonneg hs₂]
    have hp := mul_le_mul h₁ h₂ (show 0 ≤ 2*(1-r-h) by linarith) hs₁
    have hpoly : r^2 ≤ 4*(r-h)*(1-r-h) := by
      have hp₁ := mul_nonneg (show 0 ≤ r-2*h by linarith) (show 0 ≤ 1/2-r by linarith)
      by_cases ht : h ≤ 3/20
      · have hp₂ := mul_nonneg hh0 (show 0 ≤ 1-4*h by linarith)
        have hp₃ := mul_nonneg (show 0 ≤ r-2*h by linarith) (show 0 ≤ 3/2-10*h by linarith)
        nlinarith
      · have hp₂ := mul_nonneg (show 0 ≤ 1/4-h by linarith) (show 0 ≤ 3/4-h by linarith)
        have hp₃ := mul_nonneg (show 0 ≤ 1/2-r by linarith) (show 0 ≤ 10*h-3/2 by linarith)
        nlinarith
    nlinarith

/-- Under `a * b = 1` and the stated nonzero denominators, the difference of the two rational
expressions factors into the displayed common-denominator expression. -/
private theorem sin_envelope_fraction_cancellation (a b p q : ℂ) (hab : a*b = 1)
    (ha : 1-p*a^2 ≠ 0) (hb : 1-p*b^2 ≠ 0) :
    a*((1+q)/(1-p*a^2))-b*((1+q)/(1-p*b^2)) =
      (1+q)*(a-b)*(1+p)/((1-p*a^2)*(1-p*b^2)) := by
  have ha' : 1-a^2*p ≠ 0 := by simpa only [mul_comm] using! ha
  have hb' : 1-b^2*p ≠ 0 := by simpa only [mul_comm] using! hb
  field_simp [ha, hb, ha', hb']
  linear_combination (1+q)*p*(a-b)*hab

/-- Away from the exceptional geometric ratios, the sine-envelope kernel has the displayed
factorization into exponential numerator factors and two shifted denominator factors. -/
theorem sin_envelope_kernel_factorization (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hp : Complex.exp (Complex.I * (sinEnvelopeDelta M φ z + Real.pi) / (M : ℝ)) ≠ 1)
    (hm : Complex.exp (Complex.I * (sinEnvelopeDelta M φ z - Real.pi) / (M : ℝ)) ≠ 1) :
    sinEnvelopeKernel M φ z =
      ((Real.sqrt 2 : ℂ)/(2*Complex.I*(M : ℝ))) *
        ((1+Complex.exp (Complex.I*sinEnvelopeDelta M φ z)) *
          (Complex.exp (Complex.I*Real.pi/(2*(M : ℝ))) -
            Complex.exp (-(Complex.I*Real.pi/(2*(M : ℝ))))) *
          (1+Complex.exp (Complex.I*sinEnvelopeDelta M φ z/(M : ℝ)))) /
        ((1-Complex.exp (Complex.I*(sinEnvelopeDelta M φ z+Real.pi)/(M : ℝ))) *
          (1-Complex.exp (Complex.I*(sinEnvelopeDelta M φ z-Real.pi)/(M : ℝ)))) := by
  let δ := sinEnvelopeDelta M φ z
  let a : ℂ := Complex.exp (Complex.I*Real.pi/(2*(M : ℝ)))
  let b : ℂ := Complex.exp (-(Complex.I*Real.pi/(2*(M : ℝ))))
  let p : ℂ := Complex.exp (Complex.I*δ/(M : ℝ))
  let q : ℂ := Complex.exp (Complex.I*δ)
  have hab : a*b = 1 := by dsimp [a,b]; rw [← Complex.exp_add]; simp
  have hep : Complex.exp (Complex.I*(δ+Real.pi)/(M : ℝ)) = p*a^2 := by
    dsimp [p,a]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hem : Complex.exp (Complex.I*(δ-Real.pi)/(M : ℝ)) = p*b^2 := by
    dsimp [p,b]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hqp : Complex.exp (Complex.I*(δ+Real.pi)) = -q := by
    dsimp [q]
    rw [mul_add, Complex.exp_add, mul_comm Complex.I (Real.pi : ℂ), Complex.exp_pi_mul_I]
    ring
  have hqm : Complex.exp (Complex.I*(δ-Real.pi)) = -q := by
    dsimp [q]
    rw [mul_sub, Complex.exp_sub, mul_comm Complex.I (Real.pi : ℂ), Complex.exp_pi_mul_I]
    rw [div_neg, div_one]
  have ha : 1-p*a^2 ≠ 0 := by rw [← hep]; exact sub_ne_zero.mpr (Ne.symm hp)
  have hb : 1-p*b^2 ≠ 0 := by rw [← hem]; exact sub_ne_zero.mpr (Ne.symm hm)
  rw [sin_envelope_kernel_geometric_identity M φ z hM hp hm]
  change ((Real.sqrt 2 : ℂ)/(2*Complex.I*(M : ℝ))) *
      (a*sinEnvelopeGeoSum M (δ+Real.pi)-b*sinEnvelopeGeoSum M (δ-Real.pi)) = _
  have hgeop : sinEnvelopeGeoSum M (δ+Real.pi) = (1+q)/(1-p*a^2) := by
    unfold sinEnvelopeGeoSum
    push_cast
    have hepp := hep
    push_cast at hepp
    rw [hqp, hepp]
    ring
  have hgeom : sinEnvelopeGeoSum M (δ-Real.pi) = (1+q)/(1-p*b^2) := by
    unfold sinEnvelopeGeoSum
    push_cast
    have hemm := hem
    push_cast at hemm
    rw [hqm, hemm]
    ring
  rw [hgeop, hgeom, sin_envelope_fraction_cancellation a b p q hab ha hb]
  change ((Real.sqrt 2 : ℂ)/(2*Complex.I*(M : ℝ))) *
      ((1+q)*(a-b)*(1+p)/((1-p*a^2)*(1-p*b^2))) =
      ((Real.sqrt 2 : ℂ)/(2*Complex.I*(M : ℝ))) * ((1+q)*(a-b)*(1+p)) /
        ((1-Complex.exp (Complex.I*(δ+Real.pi)/(M : ℝ))) *
          (1-Complex.exp (Complex.I*(δ-Real.pi)/(M : ℝ))))
  rw [hep, hem]
  ring

/-- The norm of `1 - exp (I * t)` is `2 * |sin (t / 2)|`. -/
private theorem exp_den_norm (t : ℝ) :
    ‖1-Complex.exp (Complex.I*(t:ℂ))‖ = 2*|Real.sin (t/2)| := by
  rw [norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  norm_num

/-- The norm of `exp (I * t) - exp (-I * t)` is `2 * |sin t|`. -/
private theorem exp_diff_norm (t : ℝ) :
    ‖Complex.exp (Complex.I*(t:ℂ))-Complex.exp (-(Complex.I*(t:ℂ)))‖ =
      2*|Real.sin t| := by
  have he : Complex.exp (Complex.I*(t:ℂ))-Complex.exp (-(Complex.I*(t:ℂ))) =
      2*Complex.I*(Real.sin t:ℂ) := by
    have h : (Real.sin t : ℂ) = (Complex.exp (Complex.I*t)-Complex.exp (-(Complex.I*t)))/(2*Complex.I) := by
      rw [Complex.ofReal_sin, Complex.sin]
      field_simp
      rw [pow_two, Complex.I_mul_I]
      ring
    rw [eq_div_iff (by simp)] at h
    linear_combination -h
  rw [he, norm_mul, norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs]
  norm_num [Complex.norm_I]

/-- For `1 / M ≤ |r| ≤ 1 / 2`, the product of the two shifted sine magnitudes is at least `r^2`. -/
private theorem signed_far_sine_product (M : ℕ) (hM : 2 ≤ M) (r : ℝ)
    (hr : 1/(M : ℝ) ≤ |r|) (hr' : |r| ≤ 1/2) :
    r^2 ≤ |Real.sin (Real.pi*(r-1/(2*(M : ℝ))))| *
      |Real.sin (Real.pi*(r+1/(2*(M : ℝ))))| := by
  have h := sin_envelope_far_sine_product M hM |r| hr hr'
  by_cases hs : 0 ≤ r
  · simpa only [abs_of_nonneg hs] using! h
  · rw [abs_of_neg (lt_of_not_ge hs)] at h
    rw [show -r-1/(2*(M:ℝ)) = -(r+1/(2*(M:ℝ))) by ring,
      show -r+1/(2*(M:ℝ)) = -(r-1/(2*(M:ℝ))) by ring,
      mul_neg, mul_neg, Real.sin_neg, Real.sin_neg, abs_neg, abs_neg, neg_sq] at h
    simpa only [mul_comm] using! h

/-- When the unreduced phase discrepancy has magnitude between `1 / M` and `1 / 2`, the kernel
probability satisfies the fourth-power tail bound with constant `9 * π^2 / 16`. -/
private theorem reduced_tail (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hr : 1/(M:ℝ) ≤ |φ-(z.val:ℝ)/(M:ℝ)|)
    (hu : |φ-(z.val:ℝ)/(M:ℝ)| ≤ 1/2) :
    ‖sinEnvelopeKernel M φ z‖^2 ≤
      (9*Real.pi^2/16)/((M:ℝ)^4*(φ-(z.val:ℝ)/(M:ℝ))^4) := by
  let r : ℝ := φ-(z.val:ℝ)/(M:ℝ)
  have hm0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hmC : (M:ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hr0 : 0 < |r| := lt_of_lt_of_le (by positivity) hr
  have hrne : r ≠ 0 := abs_pos.mp hr0
  have hs := signed_far_sine_product M hM r hr hu
  have hdpos : 0 < |Real.sin (Real.pi*(r-1/(2*(M:ℝ))))| *
      |Real.sin (Real.pi*(r+1/(2*(M:ℝ))))| := (sq_pos_of_ne_zero hrne).trans_le hs
  have heplus : (sinEnvelopeDelta M φ z+Real.pi)/(M:ℝ)/2 =
      Real.pi*(r+1/(2*(M:ℝ))) := by dsimp [r,sinEnvelopeDelta]; field_simp
  have heminus : (sinEnvelopeDelta M φ z-Real.pi)/(M:ℝ)/2 =
      Real.pi*(r-1/(2*(M:ℝ))) := by dsimp [r,sinEnvelopeDelta]; field_simp
  have he (t : ℝ) : (Complex.I*(t:ℂ)/(M:ℝ):ℂ) = Complex.I*((t/(M:ℝ):ℝ):ℂ) := by push_cast; ring
  simp only [Complex.ofReal_natCast] at he
  have hp : Complex.exp (Complex.I*(sinEnvelopeDelta M φ z+Real.pi)/(M:ℝ)) ≠ 1 := by
    intro h
    have hn := exp_den_norm ((sinEnvelopeDelta M φ z+Real.pi)/(M:ℝ))
    rw [← he] at hn
    push_cast at h hn
    rw [h, sub_self, norm_zero, heplus] at hn
    have hz : |Real.sin (Real.pi*(r+1/(2*(M:ℝ))))| = 0 := by linarith only [hn]
    rw [hz, mul_zero] at hdpos
    exact (lt_irrefl 0 hdpos).elim
  have hm : Complex.exp (Complex.I*(sinEnvelopeDelta M φ z-Real.pi)/(M:ℝ)) ≠ 1 := by
    intro h
    have hn := exp_den_norm ((sinEnvelopeDelta M φ z-Real.pi)/(M:ℝ))
    rw [← he] at hn
    push_cast at h hn
    rw [h, sub_self, norm_zero, heminus] at hn
    have hz : |Real.sin (Real.pi*(r-1/(2*(M:ℝ))))| = 0 := by linarith only [hn]
    rw [hz, zero_mul] at hdpos
    exact (lt_irrefl 0 hdpos).elim
  have hg := sin_envelope_kernel_factorization M φ z hM hp hm
  have hden : ((1-Complex.exp (Complex.I*(sinEnvelopeDelta M φ z+Real.pi)/(M:ℝ))) *
      (1-Complex.exp (Complex.I*(sinEnvelopeDelta M φ z-Real.pi)/(M:ℝ))) : ℂ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hp.symm) (sub_ne_zero.mpr hm.symm)
  rw [eq_div_iff hden] at hg
  have hn := congrArg norm hg
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_div,
    norm_mul, norm_mul] at hn
  have hd₁ := exp_den_norm ((sinEnvelopeDelta M φ z+Real.pi)/(M:ℝ))
  have hd₂ := exp_den_norm ((sinEnvelopeDelta M φ z-Real.pi)/(M:ℝ))
  rw [← he, heplus] at hd₁
  rw [← he, heminus] at hd₂
  have haa : (Complex.I*Real.pi/(2*(M:ℝ)):ℂ) = Complex.I*((Real.pi/(2*(M:ℝ)):ℝ):ℂ) := by
    push_cast; ring
  push_cast at hd₁ hd₂ hn
  simp only [Complex.ofReal_natCast] at haa
  rw [hd₁, hd₂, haa, exp_diff_norm] at hn
  norm_num only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Complex.norm_I, Complex.norm_natCast] at hn
  rw [show ‖(2:ℂ)‖ = (2:ℝ) by norm_num] at hn
  simp only [mul_one] at hn
  have hn₁ : ‖1+Complex.exp (Complex.I*sinEnvelopeDelta M φ z)‖ ≤ 2 := by
    have h := norm_add_le (1:ℂ) (Complex.exp (Complex.I*sinEnvelopeDelta M φ z))
    simpa only [norm_one, Complex.norm_exp_I_mul_ofReal, one_add_one_eq_two] using! h
  have hn₂ : ‖1+Complex.exp (Complex.I*sinEnvelopeDelta M φ z/(M:ℝ))‖ ≤ 2 := by
    simp only [Complex.ofReal_natCast]
    calc
      _ ≤ ‖(1:ℂ)‖+‖Complex.exp (Complex.I*sinEnvelopeDelta M φ z/(M:ℂ))‖ := norm_add_le _ _
      _ = 2 := by rw [he, Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num
  have hsin : 2*|Real.sin (Real.pi/(2*(M:ℝ)))| ≤ Real.pi/(M:ℝ) := by
    have h := Real.abs_sin_le_abs (x := Real.pi/(2*(M:ℝ)))
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi/(2*(M:ℝ)))] at h
    rw [show Real.pi/(M:ℝ) = 2*(Real.pi/(2*(M:ℝ))) by ring]
    linarith only [h]
  have hc : Real.sqrt 2/(2*(M:ℝ)) ≤ 3/(4*(M:ℝ)) := by
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hle : Real.sqrt 2 ≤ 3/2 := by nlinarith [Real.sqrt_nonneg 2]
    apply (div_le_div_iff₀ (by positivity) (by positivity : (0:ℝ) < 4*(M:ℝ))).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hle hm0.le]
  have hprod : (Real.sqrt 2/(2*(M:ℝ))) * ‖1+Complex.exp (Complex.I*sinEnvelopeDelta M φ z)‖ *
      (2*|Real.sin (Real.pi/(2*(M:ℝ)))|) * ‖1+Complex.exp (Complex.I*sinEnvelopeDelta M φ z/(M:ℝ))‖ ≤
      (3/(4*(M:ℝ)))*2*(Real.pi/(M:ℝ))*2 := by
    gcongr
  simp only [Complex.ofReal_natCast] at hprod
  have hnorm : ‖sinEnvelopeKernel M φ z‖*(4*r^2) ≤ 3*Real.pi/(M:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hs (norm_nonneg (sinEnvelopeKernel M φ z))
    have heq : ‖sinEnvelopeKernel M φ z‖*(4*(|Real.sin (Real.pi*(r-1/(2*(M:ℝ))))| *
        |Real.sin (Real.pi*(r+1/(2*(M:ℝ))))|)) ≤ (3/(4*(M:ℝ)))*2*(Real.pi/(M:ℝ))*2 := by
      calc
        _ = (Real.sqrt 2/(2*(M:ℝ))) * ‖1+Complex.exp (Complex.I*sinEnvelopeDelta M φ z)‖ *
          (2*|Real.sin (Real.pi/(2*(M:ℝ)))|) * ‖1+Complex.exp (Complex.I*sinEnvelopeDelta M φ z/(M:ℝ))‖ := by
          simp only [Complex.ofReal_natCast]
          nlinarith only [hn]
        _ ≤ _ := hprod
    have heq' : (3/(4*(M:ℝ)))*2*(Real.pi/(M:ℝ))*2 = 3*Real.pi/(M:ℝ)^2 := by ring
    rw [heq'] at heq
    nlinarith only [hh, heq]
  have hk : ‖sinEnvelopeKernel M φ z‖ ≤ 3*Real.pi/(4*(M:ℝ)^2*r^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := (le_div_iff₀ (by positivity : (0:ℝ) < (M:ℝ)^2)).mp hnorm
    nlinarith only [h]
  have hsq := pow_le_pow_left₀ (norm_nonneg (sinEnvelopeKernel M φ z)) hk 2
  calc
    _ ≤ (3*Real.pi/(4*(M:ℝ)^2*r^2))^2 := hsq
    _ = (9*Real.pi^2/16)/((M:ℝ)^4*r^4) := by field_simp; norm_num

/-- At circular phase distance at least `1 / M`, the kernel probability is at most `(9 * π^2 /
16) / (M^4 * phaseDistance^4)`. -/
private theorem sin_envelope_kernel_far_label_precise (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hr : 1/(M:ℝ) ≤ phaseDistance φ ((z.val:ℝ)/(M:ℝ))) :
    ‖sinEnvelopeKernel M φ z‖^2 ≤
      (9*Real.pi^2/16)/((M:ℝ)^4*phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4) := by
  let n : ℤ := ⌊φ-(z.val:ℝ)/(M:ℝ)+1/2⌋
  have hd : phaseDistance φ ((z.val:ℝ)/(M:ℝ)) = |(φ-(n:ℝ))-(z.val:ℝ)/(M:ℝ)| := by
    unfold phaseDistance
    dsimp [n]
    congr 1
    ring
  have hu : |(φ-(n:ℝ))-(z.val:ℝ)/(M:ℝ)| ≤ 1/2 := by
    apply abs_le.mpr
    have hn₀ := Int.floor_le (φ-(z.val:ℝ)/(M:ℝ)+1/2)
    have hn₁ := Int.lt_floor_add_one (φ-(z.val:ℝ)/(M:ℝ)+1/2)
    dsimp [n]
    constructor <;> linarith only [hn₀,hn₁]
  have ht := reduced_tail M (φ-(n:ℝ)) z hM (hd ▸ hr) hu
  have hp := sin_envelope_kernel_int_add M (φ-(n:ℝ)) z n
  rw [sub_add_cancel] at hp
  rw [← hp] at ht
  have hpow : ((φ-(n:ℝ))-(z.val:ℝ)/(M:ℝ))^4 = phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4 := by
    rw [hd, (by decide : Even 4).pow_abs]
  rw [hpow] at ht
  exact ht

/-- At circular phase distance at least `1 / M`, the kernel probability is at most `10 / (M^4 *
phaseDistance^4)`; see [Harrow et al., Appendix A.3][HarrowHassidimLloyd2009]. -/
theorem sin_envelope_kernel_far_label_tail (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hr : 1/(M:ℝ) ≤ phaseDistance φ ((z.val:ℝ)/(M:ℝ))) :
    ‖sinEnvelopeKernel M φ z‖^2 ≤
      10/((M:ℝ)^4*phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4) := by
  apply (sin_envelope_kernel_far_label_precise M φ z hM hr).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hpi : Real.pi^2 ≤ 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
  linarith only [hpi]

/-- The sum of reciprocal squares over any finite set of positive natural numbers is at most
two. -/
private theorem nat_inv_sq_sum_le_two (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    ∑ n ∈ s, 1/(n:ℝ)^2 ≤ 2 := by
  have hh := sum_Ioo_inv_sq_le (α := ℝ) 0 (s.sup id+1)
  norm_num only [Nat.cast_zero, zero_add, div_one] at hh
  apply le_trans _ hh
  simp only [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Ioo.mpr ⟨by have := hs n hn; omega,
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
  · intro n _ _; positivity

/-- The sum of `1 / (x - n)^2` over a finite set of integers with `n ≤ x - 1` is at most two. -/
private theorem integer_left_inverse_sum (s : Finset ℤ) (x : ℝ)
    (hs : ∀ n ∈ s, (n:ℝ) ≤ x-1) :
    ∑ n ∈ s, 1/(x-(n:ℝ))^2 ≤ 2 := by
  let k (n : ℤ) : ℕ := (⌊x⌋-n).toNat
  have hpos (n : ℤ) (hn : n ∈ s) : 1 ≤ ⌊x⌋-n := by
    have hh : n+1 ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith only [hs n hn])
    omega
  have hval (n : ℤ) (hn : n ∈ s) : (k n : ℤ) = ⌊x⌋-n := by
    exact Int.toNat_of_nonneg (by have := hpos n hn; omega)
  have hinj : Set.InjOn k (↑s : Set ℤ) := by
    intro a ha b hb he
    have h := congrArg (fun n : ℕ => (n:ℤ)) he

    rw [hval a ha, hval b hb] at h
    omega
  calc
    _ ≤ ∑ n ∈ s, 1/(k n:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hp : (0:ℝ) < k n := by
        have hi : (0:ℤ) < k n := by rw [hval n hn]; exact lt_of_lt_of_le (by norm_num) (hpos n hn)
        exact_mod_cast hi
      have hv : (k n:ℝ) = (⌊x⌋:ℝ)-(n:ℝ) := by exact_mod_cast hval n hn
      have hx : (k n:ℝ) ≤ x-(n:ℝ) := by rw [hv]; linarith only [Int.floor_le x]
      gcongr
    _ = ∑ n ∈ s.image k, 1/(n:ℝ)^2 := (Finset.sum_image (f := fun n : ℕ => 1/(n:ℝ)^2) hinj).symm
    _ ≤ 2 := nat_inv_sq_sum_le_two _ (by
      intro n hn
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
      have hh := hpos m hm
      have hv := hval m hm
      omega)

/-- The sum of `1 / (x - n)^2` over a finite set of integers with `x + 1 ≤ n` is at most two. -/
private theorem integer_right_inverse_sum (s : Finset ℤ) (x : ℝ)
    (hs : ∀ n ∈ s, x+1 ≤ (n:ℝ)) :
    ∑ n ∈ s, 1/(x-(n:ℝ))^2 ≤ 2 := by
  have hn : ∀ n ∈ s.image Neg.neg, (n:ℝ) ≤ -x-1 := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    push_cast
    linarith only [hs m hm]
  have h := integer_left_inverse_sum (s.image Neg.neg) (-x) hn
  rw [Finset.sum_image (fun a _ b _ hh => neg_injective hh)] at h
  have he (n : ℤ) : 1/(-x-((-n:ℤ):ℝ))^2 = 1/(x-(n:ℝ))^2 := by push_cast; ring
  simpa only [he] using! h

/-- The sum of `1 / (x - n)^2` over a finite set of integers at distance at least one from `x`
is at most four. -/
private theorem integer_far_inverse_sum (s : Finset ℤ) (x : ℝ) :
    ∑ n ∈ s.filter (fun n : ℤ => 1 ≤ |x-(n:ℝ)|), 1/(x-(n:ℝ))^2 ≤ 4 := by
  let a := s.filter (fun n : ℤ => (n:ℝ) ≤ x-1)
  let b := s.filter (fun n : ℤ => x+1 ≤ (n:ℝ))
  have hab : Disjoint a b := by
    apply Finset.disjoint_left.mpr
    intro n ha hb
    have hl := (Finset.mem_filter.mp ha).2
    have hr := (Finset.mem_filter.mp hb).2
    linarith only [hl,hr]
  have he : s.filter (fun n : ℤ => 1 ≤ |x-(n:ℝ)|) = a ∪ b := by
    ext n
    simp only [a,b,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨hn,hd⟩
      by_cases hp : 0 ≤ x-(n:ℝ)
      · rw [abs_of_nonneg hp] at hd
        exact Or.inl ⟨hn,by linarith only [hd]⟩
      · rw [abs_of_neg (lt_of_not_ge hp)] at hd
        exact Or.inr ⟨hn,by linarith only [hd]⟩
    · rintro (⟨hn,hl⟩|⟨hn,hr⟩)
      · exact ⟨hn,le_trans (by linarith only [hl]) (le_abs_self _)⟩
      · exact ⟨hn,le_trans (by linarith only [hr]) (neg_le_abs _)⟩
  rw [he,Finset.sum_union hab]
  have ha := integer_left_inverse_sum a x (fun n hn => (Finset.mem_filter.mp hn).2)
  have hb := integer_right_inverse_sum b x (fun n hn => (Finset.mem_filter.mp hn).2)
  linarith only [ha,hb]
/-- The integer lift `z + M * ⌊φ - z / M + 1 / 2⌋` of phase label `z`, chosen from its residue
class modulo `M`. -/
private noncomputable def circularIntegerLabel (M : ℕ) (φ : ℝ) (z : Fin M) : ℤ :=
  (z.val:ℤ)+(M:ℤ)*⌊φ-(z.val:ℝ)/(M:ℝ)+1/2⌋

/-- Distinct finite phase labels have distinct lifted integer representatives. -/
private theorem circularIntegerLabel_injective (M : ℕ) (φ : ℝ) :
    Function.Injective (circularIntegerLabel M φ) := by
  have hmod (z : Fin M) : circularIntegerLabel M φ z % (M:ℤ) = (z.val:ℤ) := by
    unfold circularIntegerLabel
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast z.isLt)]
  intro a b he
  have hh := congrArg (fun n : ℤ => n % (M:ℤ)) he

  rw [hmod,hmod] at hh
  apply Fin.ext
  exact_mod_cast hh

/-- The absolute distance from `M * φ` to the lifted integer label equals `M` times the circular
phase distance. -/
private theorem circularIntegerLabel_distance (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M) :
    (M:ℝ)*phaseDistance φ ((z.val:ℝ)/(M:ℝ)) =
      |(M:ℝ)*φ-(circularIntegerLabel M φ z:ℝ)| := by
  have hm0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  unfold phaseDistance
  calc
    _ = |(M:ℝ)*(φ-(z.val:ℝ)/(M:ℝ)-(⌊φ-(z.val:ℝ)/(M:ℝ)+1/2⌋:ℝ))| := by rw [abs_mul,abs_of_pos hm0]
    _ = _ := by
      congr 1
      unfold circularIntegerLabel
      push_cast
      field_simp
      ring

/-- The sum of reciprocal squared scaled circular distances over labels at distance at least `1
/ M` is at most four. -/
private theorem circular_inverse_square_sum (M : ℕ) (φ : ℝ) (hM : 2 ≤ M) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M => 1/(M:ℝ) ≤ phaseDistance φ ((z.val:ℝ)/(M:ℝ))),
      1/((M:ℝ)*phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2 ≤ 4 := by
  classical
  let s := Finset.univ.filter (fun z : Fin M => 1/(M:ℝ) ≤ phaseDistance φ ((z.val:ℝ)/(M:ℝ)))
  let n := circularIntegerLabel M φ
  let t := s.image n
  have hm0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hn : ∀ k ∈ t, 1 ≤ |(M:ℝ)*φ-(k:ℝ)| := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    rw [← circularIntegerLabel_distance M φ z hM]
    have hd := (Finset.mem_filter.mp hz).2
    have hh := (div_le_iff₀ hm0).mp hd
    linarith only [hh]
  have hh := integer_far_inverse_sum t ((M:ℝ)*φ)
  rw [Finset.filter_eq_self.mpr hn] at hh
  dsimp [t] at hh
  rw [Finset.sum_image (circularIntegerLabel_injective M φ).injOn] at hh
  have he (z : Fin M) : 1/((M:ℝ)*φ-(n z:ℝ))^2 =
      1/((M:ℝ)*phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2 := by
    rw [circularIntegerLabel_distance M φ z hM,sq_abs]
  change (∑ z ∈ s, 1/((M:ℝ)*φ-(n z:ℝ))^2) ≤ 4 at hh
  simp_rw [he] at hh
  exact hh

/-- The kernel's second moment in the scaled circular phase error is at most `4 * π^2 + 40 * π^4
/ 3`; see [Harrow et al., Appendix A.3][HarrowHassidimLloyd2009]. -/
theorem sin_envelope_kernel_second_moment (M : ℕ) (φ : ℝ) (hM : 2 ≤ M) :
    ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (2*Real.pi*(M:ℝ)*phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2 ≤
        4*Real.pi^2+40*Real.pi^4/3 := by
  classical
  have hm0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let d (z : Fin M) := phaseDistance φ ((z.val:ℝ)/(M:ℝ))
  let p (z : Fin M) := ‖sinEnvelopeKernel M φ z‖^2
  let far := Finset.univ.filter (fun z : Fin M => 1/(M:ℝ) ≤ d z)
  have hpoint (z : Fin M) : p z*(2*Real.pi*(M:ℝ)*d z)^2 ≤
      4*Real.pi^2*p z+(if 1/(M:ℝ) ≤ d z then
        (9*Real.pi^4/4)*(1/((M:ℝ)*d z)^2) else 0) := by
    have hp : 0 ≤ p z := sq_nonneg _
    have hd : 0 ≤ d z := abs_nonneg _
    by_cases hr : 1/(M:ℝ) ≤ d z
    · rw [if_pos hr]
      have hdpos : 0 < d z := lt_of_lt_of_le (by positivity) hr
      have ht := sin_envelope_kernel_far_label_precise M φ z hM hr
      have hh := mul_le_mul_of_nonneg_right ht (sq_nonneg (2*Real.pi*(M:ℝ)*d z))
      have he : ((9*Real.pi^2/16)/((M:ℝ)^4*d z^4)) *
          (2*Real.pi*(M:ℝ)*d z)^2 = (9*Real.pi^4/4)*(1/((M:ℝ)*d z)^2) := by
        field_simp
        ring
      change p z*(2*Real.pi*(M:ℝ)*d z)^2 ≤ _ at hh
      rw [he] at hh
      exact hh.trans (le_add_of_nonneg_left (by positivity))
    · rw [if_neg hr,add_zero]
      have hmd : (M:ℝ)*d z ≤ 1 := by
        have hh := (lt_div_iff₀ hm0).mp (lt_of_not_ge hr)
        linarith only [hh]
      have hmnon : 0 ≤ (M:ℝ)*d z := mul_nonneg hm0.le hd
      have hs : ((M:ℝ)*d z)^2 ≤ 1 := by nlinarith only [hmd,hmnon]
      have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*Real.pi^2*p z by positivity)
      nlinarith only [hh]
  have hp : ∑ z : Fin M, p z = 1 := sin_envelope_kernel_normalized M φ hM
  have hf : ∑ z ∈ far, 1/((M:ℝ)*d z)^2 ≤ 4 := circular_inverse_square_sum M φ hM
  calc
    _ ≤ ∑ z : Fin M, (4*Real.pi^2*p z+(if 1/(M:ℝ) ≤ d z then
        (9*Real.pi^4/4)*(1/((M:ℝ)*d z)^2) else 0)) := Finset.sum_le_sum (fun z _ => hpoint z)
    _ = 4*Real.pi^2+(9*Real.pi^4/4)*(∑ z ∈ far, 1/((M:ℝ)*d z)^2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,hp,mul_one]
      congr 1
      rw [Finset.mul_sum]
      dsimp [far]
      rw [Finset.sum_filter]
    _ ≤ 4*Real.pi^2+(9*Real.pi^4/4)*4 := by gcongr
    _ ≤ _ := by nlinarith only [pow_nonneg Real.pi_pos.le 4]

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
