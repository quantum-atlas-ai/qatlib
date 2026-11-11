/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Norm

set_option backward.isDefEq.respectTransparency false

/-!
# Coherent use of a unitary target

Fixed arXiv:2610.08714v1, Lemma 4.5 (printed p.30, Section 4.3).  The paper lets
`U` be the circuit unitary, `J0` the isometric embedding of the zero-ancilla
subspace, `M = J0† U J0` the selected block and `Vtar` a unitary target.  If
`‖M - Vtar‖ ≤ δ ≤ 1`, then `‖U J0 - J0 Vtar‖ ≤ √(2δ)`, every unit input keeps
success probability at least `(1 - δ)²`, and at `δ = 0` the ancillary registers
return exactly.

The statement below is the norm-level content of the lemma for an arbitrary
complex Hilbert space; unitarity enters only through preservation of norms.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PolyTransform26.ResidualCert

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Lemma 4.5: a unitary target whose selected block is `δ`-close is used
coherently, with the selected-block error inflating by at most `√(2δ)` and the
success amplitude by at most `1 - δ`. -/
theorem coherent_unitary_target
    (U : E →L[ℂ] E) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (J : F →L[ℂ] E) (hJ : ∀ x, ‖J x‖ = ‖x‖)
    (V : F →L[ℂ] F) (hV : ∀ x, ‖V x‖ = ‖x‖)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : ∀ x,
      ‖(ContinuousLinearMap.adjoint J).comp (U.comp J) x - V x‖ ≤ δ * ‖x‖) :
    (∀ x, ‖U (J x) - J (V x)‖ ≤ Real.sqrt (2 * δ) * ‖x‖) ∧
      (∀ x, (1 - δ) * ‖x‖ ≤
        ‖(ContinuousLinearMap.adjoint J).comp (U.comp J) x‖) ∧
      (∀ x, (1 - δ) ^ 2 * ‖x‖ ^ 2 ≤
        ‖(ContinuousLinearMap.adjoint J).comp (U.comp J) x‖ ^ 2) ∧
      (δ = 0 → ∀ x, U (J x) = J (V x)) := by
  let M : F →L[ℂ] F := (ContinuousLinearMap.adjoint J).comp (U.comp J)
  have hMnorm : ∀ x, ‖M x - V x‖ ≤ δ * ‖x‖ := hM
  have hcross : ∀ x, inner ℂ (U (J x)) (J (V x)) = inner ℂ (M x) (V x) := by
    intro x
    exact (ContinuousLinearMap.adjoint_inner_left J (V x) (U (J x))).symm
  have hself : ∀ x, (inner ℂ (V x) (V x)).re = ‖x‖ ^ 2 := by
    intro x
    have hsq : ((‖V x‖ : ℂ) ^ 2).re = ‖V x‖ ^ 2 := by
      rw [show ((‖V x‖ : ℂ) ^ 2) = ((‖V x‖ ^ 2 : ℝ) : ℂ) from
        (Complex.ofReal_pow ‖V x‖ 2).symm]
      exact Complex.ofReal_re _
    rw [inner_self_eq_norm_sq_to_K]
    rw [hV x]
    rw [hV x] at hsq
    exact hsq
  have hre_ge : ∀ x, ‖x‖ ^ 2 - δ * ‖x‖ ^ 2 ≤ (inner ℂ (M x) (V x)).re := by
    intro x
    have hsplit : inner ℂ (M x) (V x) = inner ℂ (M x - V x) (V x) + inner ℂ (V x) (V x) := by
      rw [inner_sub_left]
      abel
    have hbound : (inner ℂ (M x - V x) (V x)).re ≥ -(δ * ‖x‖ ^ 2) := by
      have habs : |(inner ℂ (M x - V x) (V x)).re| ≤ δ * ‖x‖ ^ 2 := by
        calc
          |(inner ℂ (M x - V x) (V x)).re| ≤
              ‖inner ℂ (M x - V x) (V x)‖ := Complex.abs_re_le_norm _
          _ ≤ ‖M x - V x‖ * ‖V x‖ := norm_inner_le_norm _ _
          _ ≤ (δ * ‖x‖) * ‖x‖ :=
            mul_le_mul (hMnorm x) (le_of_eq (hV x))
              (norm_nonneg _) (by positivity)
          _ = δ * ‖x‖ ^ 2 := by ring
      have hnonneg : 0 ≤ δ * ‖x‖ ^ 2 := by positivity
      nlinarith [neg_abs_le (inner ℂ (M x - V x) (V x)).re, habs, hnonneg]
    rw [hsplit, Complex.add_re, hself x]
    nlinarith [hbound]
  have hsq : ∀ x, ‖U (J x) - J (V x)‖ ^ 2 ≤ 2 * δ * ‖x‖ ^ 2 := by
    intro x
    have h1 : ‖U (J x) - J (V x)‖ ^ 2 =
        2 * ‖x‖ ^ 2 - 2 * (inner ℂ (M x) (V x)).re := by
      rw [norm_sub_sq (𝕜 := ℂ), hcross, hU, hJ, hJ, hV]
      rw [show (inner ℂ (M x) (V x)).re =
        RCLike.re (inner ℂ (M x) (V x)) from rfl]
      ring
    nlinarith [hre_ge x]
  have hmain : ∀ x, ‖U (J x) - J (V x)‖ ≤ Real.sqrt (2 * δ) * ‖x‖ := by
    intro x
    have hsqrt : Real.sqrt (2 * δ) * ‖x‖ = Real.sqrt ((2 * δ) * ‖x‖ ^ 2) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * δ)]
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
      rw [Real.sqrt_sq (norm_nonneg x)]
    rw [hsqrt, ← Real.sqrt_sq (norm_nonneg (U (J x) - J (V x)))]
    exact Real.sqrt_le_sqrt (hsq x)
  have hsucc : ∀ x, (1 - δ) * ‖x‖ ≤ ‖M x‖ := by
    intro x
    have htri : ‖V x‖ ≤ ‖M x‖ + ‖M x - V x‖ := by
      calc
        ‖V x‖ = ‖M x - (M x - V x)‖ := by
          congr 1
          abel
        _ ≤ ‖M x‖ + ‖M x - V x‖ := norm_sub_le _ _
    have hmargin : (1 - δ) * ‖x‖ = ‖x‖ - δ * ‖x‖ := by ring
    rw [hmargin]
    linarith [hV x, hMnorm x, htri]
  refine ⟨hmain, hsucc, ?_, ?_⟩
  · intro x
    have h1δ : 0 ≤ 1 - δ := by linarith
    have hsquare : ((1 - δ) * ‖x‖) ^ 2 ≤ ‖M x‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg h1δ (norm_nonneg x)) (hsucc x) 2
    calc
      (1 - δ) ^ 2 * ‖x‖ ^ 2 = ((1 - δ) * ‖x‖) ^ 2 := by ring
      _ ≤ ‖M x‖ ^ 2 := hsquare
  · intro hzero x
    have hle : ‖U (J x) - J (V x)‖ ≤ 0 := by
      simpa [hzero] using hmain x
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

end Qatlib.Papers.PolyTransform26.ResidualCert
