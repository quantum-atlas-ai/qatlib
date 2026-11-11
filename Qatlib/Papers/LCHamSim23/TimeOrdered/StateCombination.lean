/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 14: linear combination of two block-encoded states

The paper's Lemma 14 (`arXiv:2303.01029v2`, supplementary Eq. (S64)–(S68)) combines
two imperfectly prepared states with one extra ancilla qubit:

if `U_j |0⟩_a|0⟩ = η_j⁻¹ |0⟩_a x̃_j + |⊥⟩` with `‖x_j - x̃_j‖ ≤ ε_j`, then the
single-qubit LCU rotation `R` with amplitudes `√(η_j θ_j)` gives

`(R† ⊗ I ⊗ I) (|0⟩⟨0| ⊗ U₀ + |1⟩⟨1| ⊗ U₁) (R ⊗ I ⊗ I) |0⟩_c|0⟩_a|0⟩
   = 1/(η₀θ₀ + η₁θ₁) |0⟩_c|0⟩_a (θ₀x̃₀ + θ₁x̃₁) + |⊥⟩`,

so the success flag carries the exact combination amplitude. Choosing
`ε_j = ‖θ₀x₀ + θ₁x₁‖ ε / (4θ_j)` makes the flag amplitude an `ε`-approximation
of the normalized `|θ₀x₀ + θ₁x₁⟩`.

The amplification that converts the flag probability into the paper's
`O((η₀θ₀ + η₁θ₁)/‖θ₀x₀ + θ₁x₁‖)` query count is not formalized here; the success
probability lower bound it would amplify is.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LCHamSim23.TimeOrdered

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Foundations.PureStateMath

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The standard-frame ket component of an LCU circuit is the compressed block
applied to the system vector. -/
theorem prepareLift_zero_component {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (j₀ : J) (U : Matrix (J × I) (J × I) ℂ) (ψ : I → ℂ) (p : I) :
    (U *ᵥ (prepareLift (Ket j₀) *ᵥ ψ)) (j₀, p) =
      (compress (prepareLift (Ket j₀) : Matrix (J × I) I ℂ) U
        (prepareLift (Ket j₀)) *ᵥ ψ) p := by
  set L : Matrix (J × I) I ℂ := prepareLift (Ket j₀) with hL
  have hentry : (Lᴴ *ᵥ (U *ᵥ (L *ᵥ ψ))) p = (U *ᵥ (L *ᵥ ψ)) (j₀, p) := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (j₀, p)]
    · simp [hL, prepareLift, Ket]
    · intro b _ hb
      have hsplit : b.2 ≠ p ∨ b.1 ≠ j₀ := by
        by_contra hcon
        push Not at hcon
        exact hb (Prod.ext hcon.2 hcon.1)
      rcases hsplit with h2 | h1
      · simp [hL, prepareLift, h2]
      · simp [hL, prepareLift, Ket, h1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [compress, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hentry.symm

variable {F X : Type} [Fintype F] [DecidableEq F] [Fintype X] [DecidableEq X]

/-- Lemma 14, success-flag amplitude (Eq. (S66)). The two-state LCU output carries
exactly `1/(η₀θ₀ + η₁θ₁) • (θ₀x̃₀ + θ₁x̃₁)` on the success flag. -/
theorem two_state_combination_flag_amplitude
    (f₀ : F) (i₀ : X) (θ η : Fin 2 → ℝ)
    (hθ : ∀ j, 0 < θ j) (hη : ∀ j, 0 < η j)
    (U : Fin 2 → Matrix (F × X) (F × X) ℂ)
    (x : Fin 2 → X → ℂ)
    (hx : ∀ (j : Fin 2) (i : X), (U j *ᵥ Ket (f₀, i₀)) (f₀, i) = ((η j : ℂ))⁻¹ * x j i)
    (i : X) :
    (coefficientLCUUnitary (fun j => ((η j * θ j : ℝ) : ℂ)) U 0 *ᵥ
        (prepareLift (Ket (0 : Fin 2)) *ᵥ Ket (f₀, i₀))) (0, (f₀, i)) =
      ((η 0 * θ 0 + η 1 * θ 1 : ℝ) : ℂ)⁻¹ * (θ 0 * x 0 i + θ 1 * x 1 i) := by
  have hmul : ∀ j : Fin 2, (0 : ℝ) ≤ η j * θ j := fun j => (mul_pos (hη j) (hθ j)).le
  have hmass : coefficientMass (fun j : Fin 2 => ((η j * θ j : ℝ) : ℂ)) =
      η 0 * θ 0 + η 1 * θ 1 := by
    simp only [coefficientMass, Fin.sum_univ_two, Complex.norm_real, Real.norm_of_nonneg,
      hmul]
  have hN : (0 : ℝ) < η 0 * θ 0 + η 1 * θ 1 :=
    add_pos (mul_pos (hη 0) (hθ 0)) (mul_pos (hη 1) (hθ 1))
  have hpos : 0 < coefficientMass (fun j : Fin 2 => ((η j * θ j : ℝ) : ℂ)) := by
    rw [hmass]; exact hN
  have key : ∀ j : Fin 2,
      ((η j * θ j : ℝ) : ℂ) / ((η 0 * θ 0 + η 1 * θ 1 : ℝ) : ℂ) * ((η j : ℂ))⁻¹ =
        (θ j : ℂ) / ((η 0 * θ 0 + η 1 * θ 1 : ℝ) : ℂ) := by
    intro j
    have hηj : ((η j : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (hη j)
    have hNj : ((η 0 * θ 0 + η 1 * θ 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hN
    rw [show ((η j * θ j : ℝ) : ℂ) = ((η j : ℝ) : ℂ) * ((θ j : ℝ) : ℂ) by push_cast; ring]
    field_simp
  rw [prepareLift_zero_component,
    coefficientLCUUnitary_compress (fun j : Fin 2 => ((η j * θ j : ℝ) : ℂ)) U 0 hpos, hmass]
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply, Fin.sum_univ_two, Matrix.smul_mulVec, Pi.smul_apply,
    smul_eq_mul, hx, ← mul_assoc, key]
  field_simp

/-- The unnormalized combination `θ₀ • x₀ + θ₁ • x₁` of two state vectors. -/
def twoStateCombination (θ : Fin 2 → ℝ) (x : Fin 2 → X → ℂ) : X → ℂ :=
  fun i => (θ 0 : ℂ) * x 0 i + (θ 1 : ℂ) * x 1 i

omit [DecidableEq X] in
/-- The combination is a positive linear combination: its deviation is bounded
by `θ₀ε₀ + θ₁ε₁`. -/
theorem twoStateCombination_error (θ : Fin 2 → ℝ) (hθ : ∀ j, 0 ≤ θ j)
    (x y : Fin 2 → X → ℂ) (ε : Fin 2 → ℝ)
    (hxy : ∀ j, ‖x j - y j‖ ≤ ε j) :
    ‖twoStateCombination θ x - twoStateCombination θ y‖ ≤ θ 0 * ε 0 + θ 1 * ε 1 := by
  have hdecomp : twoStateCombination θ x - twoStateCombination θ y =
      (θ 0 : ℂ) • (x 0 - y 0) + (θ 1 : ℂ) • (x 1 - y 1) := by
    funext i
    simp only [twoStateCombination, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  have h0 : ‖(θ 0 : ℂ) • (x 0 - y 0)‖ ≤ θ 0 * ε 0 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hθ 0)]
    exact mul_le_mul_of_nonneg_left (hxy 0) (hθ 0)
  have h1 : ‖(θ 1 : ℂ) • (x 1 - y 1)‖ ≤ θ 1 * ε 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hθ 1)]
    exact mul_le_mul_of_nonneg_left (hxy 1) (hθ 1)
  linarith

omit [DecidableEq X] in
/-- Normalized vectors move by at most `2‖a-b‖/‖b‖`; this is the sharp
normalization stability used for the Lemma 14 state error. -/
theorem norm_smul_inv_norm_sub_le {a b : X → ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖(‖a‖)⁻¹ • a - (‖b‖)⁻¹ • b‖ ≤ 2 * ‖a - b‖ / ‖b‖ := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hua : ‖(‖a‖)⁻¹ • a‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hapos, inv_mul_cancel₀ hapos.ne']
  have hdecomp : ‖b‖ • ((‖a‖)⁻¹ • a - (‖b‖)⁻¹ • b) =
      (a - b) - (‖a‖ - ‖b‖) • ((‖a‖)⁻¹ • a) := by
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, Complex.real_smul]
    have hane : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hapos.ne'
    have hbne : ((‖b‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hbpos.ne'
    push_cast
    field_simp
    ring
  have hstep : ‖b‖ * ‖(‖a‖)⁻¹ • a - (‖b‖)⁻¹ • b‖ =
      ‖(a - b) - (‖a‖ - ‖b‖) • ((‖a‖)⁻¹ • a)‖ := by
    rw [← hdecomp, norm_smul, Real.norm_of_nonneg hbpos.le]
  have hbnd : ‖(a - b) - (‖a‖ - ‖b‖) • ((‖a‖)⁻¹ • a)‖ ≤ ‖a - b‖ + (‖a - b‖) := by
    refine (norm_sub_le _ _).trans ?_
    have hcoef : ‖(‖a‖ - ‖b‖) • ((‖a‖)⁻¹ • a)‖ ≤ ‖a - b‖ := by
      rw [norm_smul, hua, mul_one, Real.norm_eq_abs]
      exact abs_norm_sub_norm_le a b
    linarith
  rw [le_div_iff₀ hbpos]
  rw [mul_comm ‖(‖a‖)⁻¹ • a - (‖b‖)⁻¹ • b‖ ‖b‖, hstep]
  linarith [hbnd]

omit [DecidableEq X] in
/-- Lemma 14, error bound (Eq. (S67)). With `ε_j = ‖θ₀x₀ + θ₁x₁‖ ε / (4θ_j)`, the
normalized flag amplitude is an `ε`-approximation of `|θ₀x₀ + θ₁x₁⟩`. -/
theorem two_state_combination_state_error (θ : Fin 2 → ℝ) (hθ : ∀ j, 0 < θ j)
    (ε : ℝ) (hε1 : ε ≤ 1) (x y : Fin 2 → X → ℂ)
    (hy : twoStateCombination θ y ≠ 0)
    (hxy : ∀ j, ‖x j - y j‖ ≤ ‖twoStateCombination θ y‖ * ε / (4 * θ j)) :
    ‖(‖twoStateCombination θ x‖)⁻¹ • twoStateCombination θ x -
      (‖twoStateCombination θ y‖)⁻¹ • twoStateCombination θ y‖ ≤ ε := by
  have hbpos : 0 < ‖twoStateCombination θ y‖ := norm_pos_iff.mpr hy
  have hδ : ‖twoStateCombination θ x - twoStateCombination θ y‖ ≤
      ‖twoStateCombination θ y‖ * ε / 2 := by
    have hmix := twoStateCombination_error θ (fun j => (hθ j).le) x y
      (fun j => ‖twoStateCombination θ y‖ * ε / (4 * θ j)) hxy
    have hsum : θ 0 * (‖twoStateCombination θ y‖ * ε / (4 * θ 0)) +
        θ 1 * (‖twoStateCombination θ y‖ * ε / (4 * θ 1)) =
          ‖twoStateCombination θ y‖ * ε / 2 := by
      have h0 : θ 0 ≠ 0 := ne_of_gt (hθ 0)
      have h1 : θ 1 ≠ 0 := ne_of_gt (hθ 1)
      field_simp
      ring
    linarith [hmix, hsum.le, hsum.ge]
  rcases eq_or_ne (twoStateCombination θ x) 0 with hx0 | hx0
  · exfalso
    have hsmall : ‖twoStateCombination θ y‖ ≤ ‖twoStateCombination θ y‖ * ε / 2 := by
      simpa [hx0] using hδ
    nlinarith [hbpos, hε1, hsmall]
  · have hbound := norm_smul_inv_norm_sub_le hx0 hy
    have hdouble : 2 * ‖twoStateCombination θ x - twoStateCombination θ y‖ /
        ‖twoStateCombination θ y‖ ≤ ε := by
      rw [div_le_iff₀ hbpos]
      nlinarith [hδ, hbpos]
    linarith

omit [DecidableEq X] in
/-- Lemma 14, success probability. The success-flag probability of the two-state
LCU output is at least `((1-ε/2) ‖θ₀x₀+θ₁x₁‖ / (η₀θ₀+η₁θ₁))²`. -/
theorem two_state_combination_success_probability
    (θ η : Fin 2 → ℝ) (hθ : ∀ j, 0 < θ j) (hη : ∀ j, 0 < η j)
    (ε : ℝ) (hε1 : ε ≤ 1) (x y : Fin 2 → X → ℂ)
    (hxy : ∀ j, ‖x j - y j‖ ≤ ‖twoStateCombination θ y‖ * ε / (4 * θ j)) :
    ((1 - ε/2) * (‖twoStateCombination θ y‖ / (η 0 * θ 0 + η 1 * θ 1))) ^ 2 ≤
      (‖twoStateCombination θ x‖ / (η 0 * θ 0 + η 1 * θ 1)) ^ 2 := by
  have hN : (0 : ℝ) < η 0 * θ 0 + η 1 * θ 1 :=
    add_pos (mul_pos (hη 0) (hθ 0)) (mul_pos (hη 1) (hθ 1))
  have hle : ‖twoStateCombination θ x - twoStateCombination θ y‖ ≤
      ‖twoStateCombination θ y‖ * ε / 2 := by
    have hmix := twoStateCombination_error θ (fun j => (hθ j).le) x y
      (fun j => ‖twoStateCombination θ y‖ * ε / (4 * θ j)) hxy
    have hsum : θ 0 * (‖twoStateCombination θ y‖ * ε / (4 * θ 0)) +
        θ 1 * (‖twoStateCombination θ y‖ * ε / (4 * θ 1)) =
          ‖twoStateCombination θ y‖ * ε / 2 := by
      have h0 : θ 0 ≠ 0 := ne_of_gt (hθ 0)
      have h1 : θ 1 ≠ 0 := ne_of_gt (hθ 1)
      field_simp
      ring
    linarith [hmix, hsum.le, hsum.ge]
  have hdiff : ‖twoStateCombination θ y‖ - ‖twoStateCombination θ x‖ ≤
      ‖twoStateCombination θ x - twoStateCombination θ y‖ := by
    simpa only [norm_sub_rev] using
      norm_sub_norm_le (twoStateCombination θ y) (twoStateCombination θ x)
  have hlow : (1 - ε/2) * ‖twoStateCombination θ y‖ ≤ ‖twoStateCombination θ x‖ := by
    nlinarith [hdiff, hle, norm_nonneg (twoStateCombination θ y)]
  have hkey : (1 - ε/2) * (‖twoStateCombination θ y‖ /
      (η 0 * θ 0 + η 1 * θ 1)) ≤ ‖twoStateCombination θ x‖ /
        (η 0 * θ 0 + η 1 * θ 1) := by
    have h := mul_le_mul_of_nonneg_right hlow (le_of_lt (one_div_pos.mpr hN))
    simpa only [div_eq_mul_inv, mul_assoc, one_mul] using h
  have hnonneg : 0 ≤ (1 - ε/2) * (‖twoStateCombination θ y‖ /
      (η 0 * θ 0 + η 1 * θ 1)) := by
    refine mul_nonneg (by linarith) ?_
    positivity
  exact pow_le_pow_left₀ hnonneg hkey 2

end Qatlib.Papers.LCHamSim23.TimeOrdered
