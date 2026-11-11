/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.HamLCUSim12.TaylorBounds.ProductExponentialTaylorRemainderHami

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 9 (Eq. (40)) — Taylor remainder of a product of exponentials

Fixed source: arXiv:1202.5822v1, Lemma 9, p.9, Eq. (40):
for `a_j ∈ ℝ`, `‖H_j‖ ≤ h`,

`‖R_ℓ(∏_{j=1}^M e^{-i a_j H_j t})‖ ≤ (Σ_j |a_j| h t)^{ℓ+1}/(ℓ+1)! · exp(Σ_q |a_q| h t)`.

The frozen development proves the stronger generator-norm form with
`x = Σ_j |a_j|·‖H_j‖·|t|` (`productExponentialTaylorRemainder`, imported here); the
printed uniform-`h` form follows by monotonicity of `y ↦ y^{ℓ+1}/(ℓ+1)!·e^y` on
`y ≥ 0`, which is proved here in full (`lemma9_uniform_h`).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.HamLCUSim12.TaylorBounds.Lemma9Remainder

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.HamLCUSim12.TaylorBounds

/-- Fixed arXiv:1202.5822v1, Lemma 9 Eq. (40), generator-norm form (frozen
`productExponentialTaylorRemainder`): the Taylor remainder of the ordered product
`∏_j e^{-i a_j H_j t}` at order `ℓ` is at most
`x^{ℓ+1}/(ℓ+1)! · e^x` with `x = Σ_j |a_j| ‖H_j‖ |t|`. -/
theorem lemma9_taylor_remainder {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (a : Fin M → ℝ) (H : Fin M → Matrix I I ℂ) (t : ℝ) (ℓ : ℕ) :
    ‖expProductMul (fun j => HamiltonianEvolution (H j) (a j * t)) -
        expProductTaylor (expProductGenerator a H) t ℓ‖ ≤
      ((∑ j, |a j| * ‖H j‖ * |t|) ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ)) *
        Real.exp (∑ j, |a j| * ‖H j‖ * |t|) :=
  productExponentialTaylorRemainder M a H t ℓ

/-- Fixed arXiv:1202.5822v1, Lemma 9 Eq. (40) in the printed uniform-`h` form:
if `‖H_j‖ ≤ h` with `h ≥ 0`, the remainder is at most
`S^{ℓ+1}/(ℓ+1)! · e^S` with `S = Σ_j |a_j| h |t|`.  Monotonicity of
`y ↦ y^{ℓ+1}/(ℓ+1)! · e^y` on `y ≥ 0` upgrades the frozen generator-norm bound. -/
theorem lemma9_uniform_h {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (a : Fin M → ℝ) (H : Fin M → Matrix I I ℂ) (t h : ℝ) (ℓ : ℕ) (hh : 0 ≤ h)
    (hH : ∀ j, ‖H j‖ ≤ h) :
    ‖expProductMul (fun j => HamiltonianEvolution (H j) (a j * t)) -
        expProductTaylor (expProductGenerator a H) t ℓ‖ ≤
      ((∑ j, |a j| * h * |t|) ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ)) *
        Real.exp (∑ j, |a j| * h * |t|) := by
  set x : ℝ := ∑ j, |a j| * ‖H j‖ * |t| with hxdef
  set S : ℝ := ∑ j, |a j| * h * |t| with hSdef
  have hxS : x ≤ S := by
    apply Finset.sum_le_sum
    intro j _
    have ha : (0 : ℝ) ≤ |a j| := abs_nonneg _
    have ht : (0 : ℝ) ≤ |t| := abs_nonneg _
    have h1 : |a j| * ‖H j‖ ≤ |a j| * h :=
      mul_le_mul_of_nonneg_left (hH j) ha
    exact mul_le_mul_of_nonneg_right h1 ht
  have hx0 : 0 ≤ x := by
    apply Finset.sum_nonneg
    intro j _
    positivity
  have hpow : x ^ (ℓ + 1) ≤ S ^ (ℓ + 1) := pow_le_pow_left₀ hx0 hxS _
  have hexp : Real.exp x ≤ Real.exp S := Real.exp_le_exp.mpr hxS
  have hfac : (0 : ℝ) ≤ ((ℓ + 1).factorial : ℝ) := by positivity
  have hdiv : x ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ)
      ≤ S ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ) :=
    div_le_div_of_nonneg_right hpow hfac
  have hSnonneg : (0 : ℝ) ≤ S ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ) := by positivity
  calc ‖expProductMul (fun j => HamiltonianEvolution (H j) (a j * t)) -
        expProductTaylor (expProductGenerator a H) t ℓ‖
      ≤ x ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ) * Real.exp x := by
        simpa only [hxdef] using lemma9_taylor_remainder M a H t ℓ
    _ ≤ S ^ (ℓ + 1) / ((ℓ + 1).factorial : ℝ) * Real.exp S :=
        mul_le_mul hdiv hexp (le_of_lt (Real.exp_pos x)) hSnonneg

end Qatlib.Papers.HamLCUSim12.TaylorBounds.Lemma9Remainder
