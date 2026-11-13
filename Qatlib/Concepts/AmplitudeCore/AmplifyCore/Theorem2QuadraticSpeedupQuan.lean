/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem2QuadraticSpeedupStat

/-!
# Grover rotation and quadratic amplification

`quantum_amplitude_amplification_theorem2` proves the success lower bound after the prescribed
number of Grover iterations. The module derives the rotation law, its orthonormal eigenvectors,
the exact success probability, and the zero and unit probability endpoint formulas. See
[BrassardEtAl2002] for background.

## Main statements

* `quantum_amplitude_amplification_theorem2_rotation`: For an interior success angle, `j` Grover
  steps multiply the good and bad components by the sine and cosine ratios at angle `(2 * j + 1)
  * θ`. See [BrassardEtAl2002].
* `quantum_amplitude_amplification_theorem2`: For positive initial success probability `a = sin
  θ^2`, taking `floor (π / (4 * θ))` Grover steps gives success probability at least `max (1 -
  a) a`, as in [Brassard et al., Theorem 2][BrassardEtAl2002].

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

open Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib.Concepts.AmplitudeCore.AmplifyCore

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Grover step preserves complex linear combinations. -/
lemma quantum_amplitude_amplification_theorem2_step_combination
    (A : E ≃ₗᵢ[ℂ] E) (e₀ : E) (P : E →L[ℂ] E)
    (z t : ℂ) (v w : E) :
    step A e₀ P (z • v + t • w) = z • step A e₀ P v + t • step A e₀ P w := by
  simp only [step, zeroSign, map_add, map_sub, map_smul,
    inner_add_right, inner_sub_right, inner_smul_right]
  module

/-- The vector `(u + σ * I • w) / sqrt 2` used to diagonalize a two dimensional Grover rotation. -/
noncomputable def quantum_amplitude_amplification_theorem2_eigenvector
    (u w : E) (σ : ℂ) : E :=
  (↑(1 / Real.sqrt 2) : ℂ) • (u + (σ * Complex.I) • w)

/-- For orthonormal `u` and `w`, the vectors with parameters `1` and `-1` form an orthonormal
pair. -/
lemma quantum_amplitude_amplification_theorem2_eigenvector_orthonormal
    (u w : E) (hu : inner ℂ u u = 1) (hw : inner ℂ w w = 1)
    (huw : inner ℂ u w = 0) :
    Orthonormal ℂ ![quantum_amplitude_amplification_theorem2_eigenvector u w 1,
      quantum_amplitude_amplification_theorem2_eigenvector u w (-1)] := by
  have hwu : inner ℂ w u = 0 := by rw [← inner_conj_symm, huw]; simp
  have h2 : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hinner (σ τ : ℂ) :
      inner ℂ (quantum_amplitude_amplification_theorem2_eigenvector u w σ)
        (quantum_amplitude_amplification_theorem2_eigenvector u w τ) =
        (1 + star σ * τ) / 2 := by
    simp only [quantum_amplitude_amplification_theorem2_eigenvector,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hu, hw, huw, hwu]
    simp
    field_simp
    ring_nf
    norm_num [Complex.I_sq, h2]
    ring
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    change inner ℂ (quantum_amplitude_amplification_theorem2_eigenvector u w _)
      (quantum_amplitude_amplification_theorem2_eigenvector u w _) = _
  all_goals rw [hinner]; norm_num

/-- Expresses a sine and cosine combination of `u` and `w` in the two complex rotation
eigenvectors. -/
lemma quantum_amplitude_amplification_theorem2_eigenbasis_expansion
    (u w : E) (α : ℝ) :
    (↑(Real.sin α) : ℂ) • u + (↑(Real.cos α) : ℂ) • w =
      (-Complex.I / (↑(Real.sqrt 2) : ℂ)) •
        (Complex.exp ((↑α : ℂ) * Complex.I) •
            quantum_amplitude_amplification_theorem2_eigenvector u w 1 -
          Complex.exp (-((↑α : ℂ) * Complex.I)) •
            quantum_amplitude_amplification_theorem2_eigenvector u w (-1)) := by
  have h2 : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [show -((↑α : ℂ) * Complex.I) = (↑(-α) : ℂ) * Complex.I by push_cast; ring]
  simp only [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_neg,
    quantum_amplitude_amplification_theorem2_eigenvector]
  match_scalars <;> field_simp <;> ring_nf <;> norm_num [Complex.I_sq, h2] <;> ring

/-- The stated rotation action on `u` and `w` gives eigenvalues `exp (2 * θ * I)` and `exp (-2 *
θ * I)` on the corresponding complex combinations. -/
lemma quantum_amplitude_amplification_theorem2_eigenvectors_of_rotation
    (A : E ≃ₗᵢ[ℂ] E) (e₀ : E) (P : E →L[ℂ] E) (u w : E) (θ : ℝ)
    (hu : step A e₀ P u = (↑(Real.cos (2 * θ)) : ℂ) • u -
      (↑(Real.sin (2 * θ)) : ℂ) • w)
    (hw : step A e₀ P w = (↑(Real.sin (2 * θ)) : ℂ) • u +
      (↑(Real.cos (2 * θ)) : ℂ) • w) :
    step A e₀ P (quantum_amplitude_amplification_theorem2_eigenvector u w 1) =
      Complex.exp ((↑(2 * θ) : ℂ) * Complex.I) •
        quantum_amplitude_amplification_theorem2_eigenvector u w 1 ∧
    step A e₀ P (quantum_amplitude_amplification_theorem2_eigenvector u w (-1)) =
      Complex.exp (-((↑(2 * θ) : ℂ) * Complex.I)) •
        quantum_amplitude_amplification_theorem2_eigenvector u w (-1) := by
  rw [show -((↑(2 * θ) : ℂ) * Complex.I) = (↑(-(2 * θ)) : ℂ) * Complex.I by
    push_cast; ring]
  simp only [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_neg,
    quantum_amplitude_amplification_theorem2_eigenvector, smul_add, smul_smul]
  constructor <;>
    rw [quantum_amplitude_amplification_theorem2_step_combination, hu, hw] <;>
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

variable [CompleteSpace E] {S : Set ℤ}

/-- The Grover step has the standard coefficient action on the good and bad parts of the
prepared state. See [Itakura2005]. -/
lemma quantum_amplitude_amplification_theorem2_component_actions
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    let a := ‖P ψ‖ ^ 2
    step A e₀ P (P ψ) = (1 - 2 * (a : ℂ)) • P ψ -
      (2 * (a : ℂ)) • (ψ - P ψ) ∧
    step A e₀ P (ψ - P ψ) = (2 * (1 - (a : ℂ))) • P ψ +
      (1 - 2 * (a : ℂ)) • (ψ - P ψ) := by
  simpa only [goodProjection, step, zeroSign, norm_sq_eq_re_inner (𝕜 := ℂ)] using!
    bhmt_amplitude_amplification_lemma1 S hzero E basis χ A

/-- The good projection of a linear combination of the good and bad components retains only the
good coefficient. -/
lemma quantum_amplitude_amplification_theorem2_projection_combination
    (basis : HilbertBasis S ℂ E) (χ : ℤ → Bool) (ψ : E) (z t : ℂ) :
    let P := goodProjection basis χ
    P (z • P ψ + t • (ψ - P ψ)) = z • P ψ := by
  intro P
  have hp : P (P ψ) = P ψ :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem _ ψ)
  simp only [map_add, map_smul, map_sub, hp, sub_self, smul_zero, add_zero]

/-- For an interior success angle, `j` Grover steps multiply the good and bad components by the
sine and cosine ratios at angle `(2 * j + 1) * θ`. See [BrassardEtAl2002]. -/
lemma quantum_amplitude_amplification_theorem2_rotation
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2)
    (j : ℕ) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    (step A e₀ P)^[j] ψ =
      (↑(Real.sin ((2 * (j : ℝ) + 1) * θ) / Real.sin θ) : ℂ) • P ψ +
      (↑(Real.cos ((2 * (j : ℝ) + 1) * θ) / Real.cos θ) : ℂ) • (ψ - P ψ) := by
  intro e₀ P ψ
  let a := ‖P ψ‖ ^ 2
  have hs : Real.sin θ ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩)
  have hsq : Real.cos θ ^ 2 = 1 - a := by
    have ht := Real.sin_sq_add_cos_sq θ
    change Real.sin θ ^ 2 = a at ha
    linarith
  obtain ⟨hq₁, hq₀⟩ :=
    quantum_amplitude_amplification_theorem2_component_actions hzero basis A χ
  change step A e₀ P (P ψ) = _ at hq₁
  change step A e₀ P (ψ - P ψ) = _ at hq₀
  induction j with
  | zero => simp [div_self hs, div_self hc]
  | succ j ih =>
    have hα : (2 * ((j + 1 : ℕ) : ℝ) + 1) * θ =
        (2 * (j : ℝ) + 1) * θ + 2 * θ := by push_cast; ring
    have hsin := zoo_counting_rankone_known_success_amplification_sin_rec
      (α := (2 * (j : ℝ) + 1) * θ) rfl rfl hsq rfl hs hc
    have hcos := zoo_counting_rankone_known_success_amplification_cos_rec
      (α := (2 * (j : ℝ) + 1) * θ) rfl rfl ha hsq hs hc
    rw [Function.iterate_succ_apply', ih,
      quantum_amplitude_amplification_theorem2_step_combination, hq₁, hq₀,
      hα, hsin, hcos]
    push_cast
    dsimp [a, ψ, P, e₀] at *
    module

/-- For an interior success angle, the good component after `j` Grover steps has squared norm
`sin ((2 * j + 1) * θ)^2`. See [BrassardEtAl2002]. -/
lemma quantum_amplitude_amplification_theorem2_success_sq
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2)
    (j : ℕ) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    ‖P ((step A e₀ P)^[j] ψ)‖ ^ 2 = Real.sin ((2 * (j : ℝ) + 1) * θ) ^ 2 := by
  intro e₀ P ψ
  rw [quantum_amplitude_amplification_theorem2_rotation hzero basis A χ θ hθ0 hθπ ha j,
    quantum_amplitude_amplification_theorem2_projection_combination,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, ← ha]
  have hs : Real.sin θ ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  exact div_mul_cancel₀ _ (pow_ne_zero 2 hs)

/-- The prepared state has unit norm, its good and bad parts are orthogonal, and their squared
norms sum to one. -/
lemma quantum_amplitude_amplification_theorem2_component_geometry
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) :
    let ψ := A (basis ⟨0, hzero⟩)
    let P := goodProjection basis χ
    ‖ψ‖ = 1 ∧ inner ℂ (P ψ) (ψ - P ψ) = 0 ∧
      ‖ψ - P ψ‖ ^ 2 = 1 - ‖P ψ‖ ^ 2 := by
  intro ψ P
  have hn : ‖ψ‖ = 1 := by
    exact (A.norm_map _).trans (basis.orthonormal.norm_eq_one ⟨0, hzero⟩)
  let G := (Submodule.span ℂ
    (Set.image (fun i : S => basis i) {i : S | χ i.1 = true})).topologicalClosure
  have ho : ψ - P ψ ∈ Gᗮ := Submodule.sub_starProjection_mem_orthogonal ψ
  have hi : inner ℂ (P ψ) (ψ - P ψ) = 0 :=
    (Submodule.mem_orthogonal G _).mp ho _ (Submodule.starProjection_apply_mem G ψ)
  refine ⟨hn, hi, ?_⟩
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P ψ) (ψ - P ψ) hi
  rw [add_sub_cancel, hn] at h
  linarith

/-- For `0 < θ < π / 2` and `sin θ^2 = a`, the nonnegative square roots of `a` and `1 - a` are
`sin θ` and `cos θ`. See [BrassardEtAl2002]. -/
lemma quantum_amplitude_amplification_theorem2_square_roots
    {θ a : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = a) :
    Real.sqrt a = Real.sin θ ∧ Real.sqrt (1 - a) = Real.cos θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩
  have hcsq : Real.cos θ ^ 2 = 1 - a := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  exact ⟨by rw [← ha, Real.sqrt_sq hs.le], by rw [← hcsq, Real.sqrt_sq hc.le]⟩

/-- Dividing the good and bad components by `sin θ` and `cos θ` yields an orthonormal pair under
the interior angle hypotheses. -/
lemma quantum_amplitude_amplification_theorem2_normalized_components
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2) :
    let ψ := A (basis ⟨0, hzero⟩)
    let P := goodProjection basis χ
    let u := (↑(1 / Real.sin θ) : ℂ) • P ψ
    let w := (↑(1 / Real.cos θ) : ℂ) • (ψ - P ψ)
    inner ℂ u u = 1 ∧ inner ℂ w w = 1 ∧ inner ℂ u w = 0 := by
  intro ψ P u w
  obtain ⟨_, hi, hb⟩ :=
    quantum_amplitude_amplification_theorem2_component_geometry hzero basis A χ
  have hs : Real.sin θ ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩)
  have hcsq : Real.cos θ ^ 2 = 1 - ‖P ψ‖ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hu : ‖u‖ ^ 2 = 1 := by
    change ‖(↑(1 / Real.sin θ) : ℂ) • P ψ‖ ^ 2 = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, ← ha]
    field_simp [hs]
  have hw : ‖w‖ ^ 2 = 1 := by
    change ‖(↑(1 / Real.cos θ) : ℂ) • (ψ - P ψ)‖ ^ 2 = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow,
      hb, ← hcsq]
    field_simp [hc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← inner_self_ofReal_re, ← norm_sq_eq_re_inner, hu]; rfl
  · rw [← inner_self_ofReal_re, ← norm_sq_eq_re_inner, hw]; rfl
  · change inner ℂ (P ψ) (ψ - P ψ) = 0 at hi
    simp only [u, w, inner_smul_left, inner_smul_right, hi, mul_zero]

/-- The Grover step rotates the normalized good and bad components through angle `2 * θ`. -/
lemma quantum_amplitude_amplification_theorem2_normalized_actions
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    let u := (↑(1 / Real.sin θ) : ℂ) • P ψ
    let w := (↑(1 / Real.cos θ) : ℂ) • (ψ - P ψ)
    step A e₀ P u = (↑(Real.cos (2 * θ)) : ℂ) • u -
      (↑(Real.sin (2 * θ)) : ℂ) • w ∧
    step A e₀ P w = (↑(Real.sin (2 * θ)) : ℂ) • u +
      (↑(Real.cos (2 * θ)) : ℂ) • w := by
  intro e₀ P ψ u w
  have hs : Real.sin θ ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩)
  have hsc : Complex.sin (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hs
  have hcc : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]; exact_mod_cast hc
  have hunit : Complex.cos (θ : ℂ) ^ 2 = 1 - Complex.sin (θ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    have h := Real.sin_sq_add_cos_sq θ
    exact_mod_cast (show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by linarith)
  have hmap (z : ℂ) (v : E) : step A e₀ P (z • v) = z • step A e₀ P v := by
    simpa only [zero_smul, add_zero] using
      quantum_amplitude_amplification_theorem2_step_combination A e₀ P z 0 v 0
  obtain ⟨hq₁, hq₀⟩ :=
    quantum_amplitude_amplification_theorem2_component_actions hzero basis A χ
  rw [← ha] at hq₁ hq₀
  change step A e₀ P (P ψ) = _ at hq₁
  change step A e₀ P (ψ - P ψ) = _ at hq₀
  constructor
  · change step A e₀ P ((↑(1 / Real.sin θ) : ℂ) • P ψ) = _
    rw [hmap, hq₁]
    dsimp only [u, w]
    simp only [Real.cos_two_mul_eq_one_sub, Real.sin_two_mul]
    push_cast
    match_scalars <;> field_simp [hsc, hcc]
  · change step A e₀ P ((↑(1 / Real.cos θ) : ℂ) • (ψ - P ψ)) = _
    rw [hmap, hq₀]
    dsimp only [u, w]
    simp only [Real.cos_two_mul_eq_one_sub, Real.sin_two_mul]
    push_cast
    match_scalars
    · field_simp [hsc, hcc]
      ring_nf
      rw [hunit]
      ring
    · ring

/-- The normalized component combinations give an orthonormal pair of eigenvectors with
eigenvalues `exp (±2 * θ * I)`. -/
lemma quantum_amplitude_amplification_theorem2_diagonalization
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    let a := ‖P ψ‖ ^ 2
    let u := (↑(1 / Real.sqrt a) : ℂ) • P ψ
    let w := (↑(1 / Real.sqrt (1 - a)) : ℂ) • (ψ - P ψ)
    let vp := quantum_amplitude_amplification_theorem2_eigenvector u w 1
    let vm := quantum_amplitude_amplification_theorem2_eigenvector u w (-1)
    Orthonormal ℂ ![vp, vm] ∧
      step A e₀ P vp = Complex.exp ((↑(2 * θ) : ℂ) * Complex.I) • vp ∧
      step A e₀ P vm = Complex.exp (-((↑(2 * θ) : ℂ) * Complex.I)) • vm := by
  intro e₀ P ψ a u w vp vm
  obtain ⟨hs, hc⟩ := quantum_amplitude_amplification_theorem2_square_roots hθ0 hθπ ha
  dsimp only [vp, vm, u, w, a]
  rw [hs, hc]
  obtain ⟨hu, hw, huw⟩ :=
    quantum_amplitude_amplification_theorem2_normalized_components hzero basis A χ θ hθ0 hθπ ha
  obtain ⟨hqu, hqw⟩ :=
    quantum_amplitude_amplification_theorem2_normalized_actions hzero basis A χ θ hθ0 hθπ ha
  exact ⟨quantum_amplitude_amplification_theorem2_eigenvector_orthonormal _ _ hu hw huw,
    quantum_amplitude_amplification_theorem2_eigenvectors_of_rotation A e₀ P _ _ θ hqu hqw⟩

/-- The prepared state after `j` Grover steps has the stated complex exponential expansion in
the two rotation eigenvectors. -/
lemma quantum_amplitude_amplification_theorem2_exponential_state
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2)
    (j : ℕ) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    let a := ‖P ψ‖ ^ 2
    let u := (↑(1 / Real.sqrt a) : ℂ) • P ψ
    let w := (↑(1 / Real.sqrt (1 - a)) : ℂ) • (ψ - P ψ)
    let α := (2 * (j : ℝ) + 1) * θ
    (step A e₀ P)^[j] ψ = (-Complex.I / (↑(Real.sqrt 2) : ℂ)) •
      (Complex.exp ((↑α : ℂ) * Complex.I) •
          quantum_amplitude_amplification_theorem2_eigenvector u w 1 -
        Complex.exp (-((↑α : ℂ) * Complex.I)) •
          quantum_amplitude_amplification_theorem2_eigenvector u w (-1)) := by
  intro e₀ P ψ a u w α
  rw [← quantum_amplitude_amplification_theorem2_eigenbasis_expansion]
  rw [quantum_amplitude_amplification_theorem2_rotation hzero basis A χ θ hθ0 hθπ ha j]
  obtain ⟨hs, hc⟩ := quantum_amplitude_amplification_theorem2_square_roots hθ0 hθπ ha
  dsimp only [u, w, a, α]
  rw [hs, hc]
  push_cast
  module

/-- For an interior success angle, every Grover iterate of the prepared state has squared norm
one. -/
lemma quantum_amplitude_amplification_theorem2_iterate_norm_sq
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2)
    (j : ℕ) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    ‖(step A e₀ P)^[j] ψ‖ ^ 2 = 1 := by
  intro e₀ P ψ
  obtain ⟨_, hi, hb⟩ :=
    quantum_amplitude_amplification_theorem2_component_geometry hzero basis A χ
  have hs : Real.sin θ ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩)
  have hcsq : Real.cos θ ^ 2 = 1 - ‖P ψ‖ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [quantum_amplitude_amplification_theorem2_rotation hzero basis A χ θ hθ0 hθπ ha j,
    pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _
      (by simp only [inner_smul_left, inner_smul_right, hi, mul_zero])]
  simp only [← pow_two, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow]
  rw [hb, ← hcsq, ← ha, div_mul_cancel₀ _ (pow_ne_zero 2 hs),
    div_mul_cancel₀ _ (pow_ne_zero 2 hc)]
  exact Real.sin_sq_add_cos_sq _

/-- When the initial success probability is zero, every Grover iterate fixes the prepared state
and has zero good component. See [BrassardEtAl2002]. -/
lemma quantum_amplitude_amplification_theorem2_zero_endpoint
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool)
    (ha : ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2 = 0) (j : ℕ) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    (step A e₀ P)^[j] ψ = ψ ∧ ‖P ((step A e₀ P)^[j] ψ)‖ ^ 2 = 0 := by
  intro e₀ P ψ
  have hp : P ψ = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp ha)
  obtain ⟨_, hq⟩ :=
    quantum_amplitude_amplification_theorem2_component_actions hzero basis A χ
  change step A e₀ P (ψ - P ψ) = _ at hq
  rw [ha] at hq
  change step A e₀ P (ψ - P ψ) =
    (2 * (1 - (0 : ℂ))) • P ψ + (1 - 2 * (0 : ℂ)) • (ψ - P ψ) at hq
  have hfix : step A e₀ P ψ = ψ := by
    simpa only [hp, sub_zero, Complex.ofReal_zero, mul_zero, sub_zero,
      smul_zero, zero_add, one_smul] using hq
  have hj := Function.iterate_fixed hfix j
  exact ⟨hj, by rw [hj]; exact ha⟩

/-- When the initial success probability is one, `j` Grover steps multiply the state by `(-1)^j`
and preserve success probability one. See [BrassardEtAl2002]. -/
lemma quantum_amplitude_amplification_theorem2_one_endpoint
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool)
    (ha : ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2 = 1) (j : ℕ) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    (step A e₀ P)^[j] ψ = (-1 : ℂ) ^ j • ψ ∧
      ‖P ((step A e₀ P)^[j] ψ)‖ ^ 2 = 1 := by
  intro e₀ P ψ
  obtain ⟨_, _, hb⟩ :=
    quantum_amplitude_amplification_theorem2_component_geometry hzero basis A χ
  rw [ha, sub_self] at hb
  have hbad : ψ - P ψ = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb)
  have hp : P ψ = ψ := (sub_eq_zero.mp hbad).symm
  obtain ⟨hq, _⟩ :=
    quantum_amplitude_amplification_theorem2_component_actions hzero basis A χ
  change step A e₀ P (P ψ) = _ at hq
  rw [ha] at hq
  change step A e₀ P (P ψ) =
    (1 - 2 * (1 : ℂ)) • P ψ - (2 * (1 : ℂ)) • (ψ - P ψ) at hq
  have hneg : step A e₀ P ψ = -ψ := by
    simpa only [hp, sub_self, smul_zero, sub_zero, Complex.ofReal_one,
      mul_one, show (1 - 2 : ℂ) = -1 by norm_num, neg_one_smul] using hq
  have hj : (step A e₀ P)^[j] ψ = (-1 : ℂ) ^ j • ψ := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      have hm := quantum_amplitude_amplification_theorem2_step_combination
        A e₀ P ((-1 : ℂ) ^ j) 0 ψ 0
      simp only [zero_smul, add_zero] at hm
      rw [hm, hneg, pow_succ, mul_smul, neg_one_smul]
  refine ⟨hj, ?_⟩
  rw [hj, map_smul, norm_smul, norm_pow]
  simpa only [norm_neg, norm_one, one_pow, one_mul] using ha

end

/-- For positive initial success probability `a = sin θ^2`, taking `floor (π / (4 * θ))` Grover
steps gives success probability at least `max (1 - a) a`, as in [Brassard et al., Theorem
2][BrassardEtAl2002]. -/
theorem quantum_amplitude_amplification_theorem2 :
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : Set ℤ) (hzero : (0 : ℤ) ∈ S)
    (basis : HilbertBasis S ℂ E) (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool),
  let e₀ : E := basis ⟨0, hzero⟩;
  let P : E →L[ℂ] E := AmplitudeAmplificationCore.goodProjection basis χ;
  let ψ : E := A e₀;
  let a : ℝ := ‖P ψ‖ ^ 2;
  ∀ (θ : ℝ),
    0 < a → 0 < θ → θ ≤ Real.pi / 2 → Real.sin θ ^ 2 = a →
    let m : ℕ := Nat.floor (Real.pi / (4 * θ));
    max (1 - a) a ≤
      ‖P (((AmplitudeAmplificationCore.step A e₀ P)^[m]) ψ)‖ ^ 2 := by
  intro E _ _ _ S hzero basis A χ e₀ P ψ a θ ha0 hθ0 hθπ ha m
  have hhalf : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  by_cases hsmall : θ ≤ Real.pi / 4
  · have hsnn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith [Real.pi_pos])
    have hsinle : Real.sin θ ≤ Real.sqrt 2 / 2 := by
      simpa only [Real.sin_pi_div_four] using
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hsmall
    have hale : a ≤ 1 / 2 := by
      have h := pow_le_pow_left₀ hsnn hsinle 2
      rwa [ha, hhalf] at h
    rw [quantum_amplitude_amplification_theorem2_success_sq hzero basis A χ θ
      hθ0 (by linarith [Real.pi_pos]) ha m, max_eq_left (by linarith : a ≤ 1 - a)]
    exact zoo_counting_rankone_known_success_amplification_floor_estimate hθ0 hsmall ha
  · have hm0 : m = 0 := Nat.floor_eq_zero.mpr (by
      rw [div_lt_one (by linarith : (0 : ℝ) < 4 * θ)]
      linarith)
    have hsinle : Real.sqrt 2 / 2 ≤ Real.sin θ := by
      simpa only [Real.sin_pi_div_four] using
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos]) hθπ (le_of_not_ge hsmall)
    have hale : 1 / 2 ≤ a := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2) hsinle 2
      rwa [ha, hhalf] at h
    rw [hm0, Function.iterate_zero_apply]
    exact max_le (by change 1 - a ≤ a; linarith) le_rfl

example : Theorem2SpeedupSpec.expected :=
  quantum_amplitude_amplification_theorem2

end Qatlib.Concepts.AmplitudeCore.AmplifyCore
