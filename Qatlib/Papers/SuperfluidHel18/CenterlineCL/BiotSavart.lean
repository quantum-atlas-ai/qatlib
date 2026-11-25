/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussLinking
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.KernelBounds
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Biot–Savart helicity of a continuous vorticity field

[Kedia2018SuperfluidHelicity], Section V, Eq. (7)–(8),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
This module develops the continuous-vorticity side of the classical limit: the
Biot–Savart helicity `∫ u ⬝ ω` of an `L¹` vorticity field on coordinate
`ℝ³ = Fin 3 → ℝ`, written through the two-point Gauss kernel
`dot3 (ω x) (cross3 (ω y) (x - y)) / (4π |x - y|³)`.

Concretely, it provides:

* the pairing kernel `bsPairKernel` and, for fields with `d`-separated supports, the
  pairing functional `crossPairing` — the exact analogue of the off-diagonal Gauss
  pairing between distinct filaments, needing no near-diagonal control because the
  singularity sits off the support;
* an explicit Lipschitz bound of the pairing in the `L¹` norm, hence `L¹`-continuity
  (`tendsto_crossPairing`) — the weak-convergence entry on the continuous side;
* the velocity-truncated helicity `bsHelicityTrunc ω δ` (Biot–Savart velocity with the
  `δ`-ball around the singularity excised), its Fubini rewriting as the double
  integral of the kernel over `|x - y| ≥ δ`, vanishing on parallel fields, and its
  convergence as `δ → 0⁺` to the full self-pairing under an explicit
  absolute-integrability hypothesis.

Honest boundary of what is proved here. The limit theorem `tendsto_bsHelicityTrunc`
assumes the full kernel absolutely integrable; this is the three-dimensional
counterpart of the writhe integrability of the filament side, and for bounded
compactly supported fields it follows from a spherical-shell estimate `1/r² · r² dr`
that is not formalized in this module. No statement connects convergence of the
(rescaled) filament pairings to `bsHelicityTrunc` or to the full pairing — that
Γ-continuity step of the classical limit is deliberately left open, as is any appeal
to Euler helicity conservation.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open MeasureTheory
open Filter
open scoped Real Topology

/-! ### Cartesian estimates in the sup norm -/

/-- Each coordinate of a vector is bounded by its sup norm. -/
theorem abs_le_norm_coord (w : Fin 3 → ℝ) (i : Fin 3) : |w i| ≤ ‖w‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mp le_rfl i

/-- The Euclidean length is nonnegative. -/
theorem euclideanLength_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanLength v :=
  norm_nonneg _

/-- Scaling the first argument of the cross product factors out. -/
theorem cross3_smul_left (c : ℝ) (u w : Fin 3 → ℝ) : cross3 (c • u) w = c • cross3 u w := by
  funext j
  fin_cases j <;> simp [cross3, Pi.smul_apply] <;> ring

/-- The cross product of a vector with itself vanishes. -/
theorem cross3_self_eq_zero (u : Fin 3 → ℝ) : cross3 u u = 0 := by
  funext j
  fin_cases j <;> simp [cross3] <;> ring

/-- The cross product with a zero first factor vanishes. -/
theorem cross3_zero_left (v : Fin 3 → ℝ) : cross3 0 v = 0 := by
  funext j
  fin_cases j <;> simp [cross3]

/-- Coordinate formulas for the cross product. -/
theorem cross3_val_zero (u v : Fin 3 → ℝ) : cross3 u v 0 = u 1 * v 2 - u 2 * v 1 := rfl

/-- Coordinate formula, second component. -/
theorem cross3_val_one (u v : Fin 3 → ℝ) : cross3 u v 1 = u 2 * v 0 - u 0 * v 2 := rfl

/-- Coordinate formula, third component. -/
theorem cross3_val_two (u v : Fin 3 → ℝ) : cross3 u v 2 = u 0 * v 1 - u 1 * v 0 := rfl

/-! ### The Biot–Savart pairing kernel -/

/-- The two-point Gauss kernel of the Biot–Savart helicity pairing of two vorticity
fields: the scalar triple product of the two field values and the chord, over the
Gauss denominator. -/
noncomputable def bsPairKernel (ω φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x y : Fin 3 → ℝ) : ℝ :=
  dot3 (ω x) (cross3 (φ y) (x - y)) / (4 * π * euclideanLength (x - y) ^ 3)

/-- Away from the diagonal, the pairing kernel is bounded by the explicit separated
constant `3 / (2π d²)` times the field norms: the triple product costs `3 · 2` sup-norm
factors, the chord contributes one power of length against the cubic denominator. -/
theorem abs_bsPairKernel_le_of_dist_le {ω φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {x y : Fin 3 → ℝ} {d : ℝ}
    (hd : 0 < d) (hxy : d ≤ euclideanLength (x - y)) :
    |bsPairKernel ω φ x y| ≤ 3 / (2 * π * d ^ 2) * (‖ω x‖ * ‖φ y‖) := by
  have hlen : 0 < euclideanLength (x - y) := lt_of_lt_of_le hd hxy
  have hsq : d ^ 2 ≤ euclideanLength (x - y) ^ 2 := by
    have hsum : (0 : ℝ) ≤ d + euclideanLength (x - y) := by
      have := euclideanLength_nonneg (x - y)
      linarith
    have hmul := mul_le_mul_of_nonneg_right hxy hsum
    nlinarith
  have hnum : |dot3 (ω x) (cross3 (φ y) (x - y))|
      ≤ 6 * ‖ω x‖ * ‖φ y‖ * euclideanLength (x - y) := by
    calc |dot3 (ω x) (cross3 (φ y) (x - y))|
        ≤ 3 * ‖ω x‖ * ‖cross3 (φ y) (x - y)‖ := abs_dot3_le _ _
      _ ≤ 3 * ‖ω x‖ * (2 * ‖φ y‖ * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (norm_cross3_le_mul _ _) (by positivity)
      _ ≤ 3 * ‖ω x‖ * (2 * ‖φ y‖ * euclideanLength (x - y)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (norm_le_euclideanLength _) (by positivity)
      _ = 6 * ‖ω x‖ * ‖φ y‖ * euclideanLength (x - y) := by ring
  have hden : 0 < 4 * π * euclideanLength (x - y) ^ 3 := by positivity
  have hstep2 : euclideanLength (x - y) ≤ euclideanLength (x - y) ^ 3 / d ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < d ^ 2)]
    have h1 : euclideanLength (x - y) * d ^ 2
        ≤ euclideanLength (x - y) * euclideanLength (x - y) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt hlen)
    have h2 : euclideanLength (x - y) * euclideanLength (x - y) ^ 2
        = euclideanLength (x - y) ^ 3 := by ring
    linarith
  rw [bsPairKernel, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |dot3 (ω x) (cross3 (φ y) (x - y))|
      ≤ 6 * ‖ω x‖ * ‖φ y‖ * euclideanLength (x - y) := hnum
    _ ≤ 6 * ‖ω x‖ * ‖φ y‖ * (euclideanLength (x - y) ^ 3 / d ^ 2) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = 3 / (2 * π * d ^ 2) * (‖ω x‖ * ‖φ y‖) * (4 * π * euclideanLength (x - y) ^ 3) := by
        field_simp [Real.pi_pos.ne', hd.ne']
        ring

/-- Continuity of the cross product as a function of both arguments. -/
private theorem continuous_cross3_pair :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => cross3 p.1 p.2 := by
  refine continuous_pi fun j => ?_
  have h0 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 1 * p.2 2 - p.1 2 * p.2 1 := by
    fun_prop
  have h1 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 2 * p.2 0 - p.1 0 * p.2 2 := by
    fun_prop
  have h2 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 0 * p.2 1 - p.1 1 * p.2 0 := by
    fun_prop
  fin_cases j
  · show Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 1 * p.2 2 - p.1 2 * p.2 1
    exact h0
  · show Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 2 * p.2 0 - p.1 0 * p.2 2
    exact h1
  · show Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 0 * p.2 1 - p.1 1 * p.2 0
    exact h2

/-- Continuity of the dot product as a function of both arguments. -/
private theorem continuous_dot3_pair :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => dot3 p.1 p.2 := by
  have h : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      p.1 0 * p.2 0 + p.1 1 * p.2 1 + p.1 2 * p.2 2 := by fun_prop
  simpa only [dot3] using h

/-- Measurability of the pairing kernel on the product space. -/
theorem measurable_bsPairKernel {ω φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hmω : Measurable ω) (hmφ : Measurable φ) :
    Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => bsPairKernel ω φ p.1 p.2 := by
  have h1 : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => ω p.1 := hmω.comp measurable_fst
  have h2 : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => φ p.2 := hmφ.comp measurable_snd
  have hsub : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 - p.2 :=
    measurable_fst.sub measurable_snd
  have h3 : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => cross3 (φ p.2) (p.1 - p.2) :=
    (continuous_cross3_pair.measurable).comp (h2.prodMk hsub)
  have hnum : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dot3 (ω p.1) (cross3 (φ p.2) (p.1 - p.2)) :=
    (continuous_dot3_pair.measurable).comp (h1.prodMk h3)
  have hlen : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      euclideanLength (p.1 - p.2) := continuous_euclideanLength.measurable.comp hsub
  have hconst : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (4 * π : ℝ) :=
    measurable_const
  have hrw : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => bsPairKernel ω φ p.1 p.2)
      = fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        dot3 (ω p.1) (cross3 (φ p.2) (p.1 - p.2))
          * (4 * π * euclideanLength (p.1 - p.2) ^ 3)⁻¹ := by
    funext p
    rw [bsPairKernel, div_eq_inv_mul, mul_comm]
  have hlen3 : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (4 : ℝ) * π * euclideanLength (p.1 - p.2) ^ 3 :=
    measurable_const.mul (hlen.pow_const 3)
  have hdenm : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ((4 : ℝ) * π * euclideanLength (p.1 - p.2) ^ 3)⁻¹ := hlen3.inv
  rw [hrw]
  exact hnum.mul hdenm

/-- On the support of a `d`-separated pair of fields the pairing kernel is dominated by
the explicit separable tensor `3/(2π d²) · ‖ω x‖ ‖φ y‖`; off the support the kernel
vanishes identically because one field value is zero. -/
theorem abs_bsPairKernel_le_of_support {ω φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {d : ℝ} (hd : 0 < d)
    (A B : Set (Fin 3 → ℝ))
    (hωs : ∀ x, ω x ≠ 0 → x ∈ A) (hφs : ∀ y, φ y ≠ 0 → y ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ euclideanLength (x - y)) (x y : Fin 3 → ℝ) :
    |bsPairKernel ω φ x y| ≤ 3 / (2 * π * d ^ 2) * (‖ω x‖ * ‖φ y‖) := by
  by_cases hx : ω x = 0
  · have hdot : dot3 (ω x) (cross3 (φ y) (x - y)) = 0 := by
      rw [hx]
      simp [dot3]
    have hz : bsPairKernel ω φ x y = 0 := by
      rw [bsPairKernel, hdot, zero_div]
    rw [hz, abs_zero]
    positivity
  · by_cases hy : φ y = 0
    · have hdot : dot3 (ω x) (cross3 (φ y) (x - y)) = 0 := by
        rw [hy, cross3_zero_left]
        simp [dot3]
      have hz : bsPairKernel ω φ x y = 0 := by
        rw [bsPairKernel, hdot, zero_div]
      rw [hz, abs_zero]
      positivity
    · exact abs_bsPairKernel_le_of_dist_le hd (hsep x (hωs x hx) y (hφs y hy))

/-- The pairing kernel of an `L¹` pair of `d`-separated fields is integrable on the
product space. -/
theorem integrable_bsPairKernel {ω φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {d : ℝ} (hd : 0 < d)
    (A B : Set (Fin 3 → ℝ))
    (hmω : Measurable ω) (hmφ : Measurable φ)
    (hωs : ∀ x, ω x ≠ 0 → x ∈ A) (hφs : ∀ y, φ y ≠ 0 → y ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ euclideanLength (x - y))
    (hω : Integrable ω) (hφ : Integrable φ) :
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => bsPairKernel ω φ p.1 p.2)
      (volume.prod volume) := by
  have htensor : Integrable
      (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        3 / (2 * π * d ^ 2) * (‖ω p.1‖ * ‖φ p.2‖)) (volume.prod volume) :=
    Integrable.congr ((hω.norm.const_mul (3 / (2 * π * d ^ 2))).smul_prod hφ.norm)
      (Filter.Eventually.of_forall fun p => by simp only [smul_eq_mul]; ring)
  exact Integrable.mono' htensor
    (Measurable.aestronglyMeasurable (measurable_bsPairKernel hmω hmφ))
    (Filter.Eventually.of_forall fun p =>
      abs_bsPairKernel_le_of_support hd A B hωs hφs hsep p.1 p.2)

/-- The pairing functional: the double integral of the Biot–Savart pairing kernel over
the whole space, the continuous-vorticity analogue of the off-diagonal Gauss pairing
between distinct filaments. -/
noncomputable def crossPairing (ω φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : ℝ :=
  ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), bsPairKernel ω φ p.1 p.2 ∂(volume.prod volume)

/-- The pairing of a `d`-separated `L¹` pair is bounded by the explicit constant times
the product of the `L¹` norms. -/
theorem abs_crossPairing_le {ω φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {d : ℝ} (hd : 0 < d)
    (A B : Set (Fin 3 → ℝ))
    (hmω : Measurable ω) (hmφ : Measurable φ)
    (hωs : ∀ x, ω x ≠ 0 → x ∈ A) (hφs : ∀ y, φ y ≠ 0 → y ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ euclideanLength (x - y))
    (hω : Integrable ω) (hφ : Integrable φ) :
    |crossPairing ω φ| ≤ 3 / (2 * π * d ^ 2) * (∫ x, ‖ω x‖) * ∫ y, ‖φ y‖ := by
  have hint := integrable_bsPairKernel hd A B hmω hmφ hωs hφs hsep hω hφ
  have htensor : Integrable
      (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        3 / (2 * π * d ^ 2) * (‖ω p.1‖ * ‖φ p.2‖)) (volume.prod volume) :=
    Integrable.congr ((hω.norm.const_mul (3 / (2 * π * d ^ 2))).smul_prod hφ.norm)
      (Filter.Eventually.of_forall fun p => by simp only [smul_eq_mul]; ring)
  rw [crossPairing]
  calc |∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), bsPairKernel ω φ p.1 p.2 ∂(volume.prod volume)|
      ≤ ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), |bsPairKernel ω φ p.1 p.2| ∂(volume.prod volume) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
          3 / (2 * π * d ^ 2) * (‖ω p.1‖ * ‖φ p.2‖) ∂(volume.prod volume) :=
        integral_mono hint.abs htensor
          (fun p => abs_bsPairKernel_le_of_support hd A B hωs hφs hsep p.1 p.2)
    _ = 3 / (2 * π * d ^ 2) * (∫ x, ‖ω x‖) * ∫ y, ‖φ y‖ := by
        have h1 : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
              3 / (2 * π * d ^ 2) * (‖ω p.1‖ * ‖φ p.2‖))
            = fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
              (3 / (2 * π * d ^ 2) * ‖ω p.1‖) * ‖φ p.2‖ := by
          funext p
          ring
        rw [h1, integral_prod_mul (fun x => 3 / (2 * π * d ^ 2) * ‖ω x‖)
          (fun y => ‖φ y‖), integral_const_mul]

/-- The indicator of a function vanishes off the set, packaged for rewriting. -/
private theorem indicator_of_not_mem0 {α : Type*} {β : Type*} [Zero β] (s : Set α)
    (f : α → β) {a : α} (h : a ∉ s) : s.indicator f a = 0 := by
  simp [h]

/-- Subtraction of equal-denominator quotients, valid also at a vanishing denominator
where real division totalizes to zero. -/
private theorem sub_div_same (a b c : ℝ) : a / c - b / c = (a - b) / c := by
  by_cases hc : c = 0
  · simp [hc]
  · field_simp

/-- The pairing is linear in its first argument in the strong sense that the difference
of pairings is the pairing of the differences, whenever both pairings are integrable. -/
theorem crossPairing_sub_eq {ω₁ ω₂ φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {d : ℝ} (hd : 0 < d)
    (A B : Set (Fin 3 → ℝ))
    (hmω₁ : Measurable ω₁) (hmω₂ : Measurable ω₂) (hmφ : Measurable φ)
    (hω₁s : ∀ x, ω₁ x ≠ 0 → x ∈ A) (hω₂s : ∀ x, ω₂ x ≠ 0 → x ∈ A)
    (hφs : ∀ y, φ y ≠ 0 → y ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ euclideanLength (x - y))
    (hω₁ : Integrable ω₁) (hω₂ : Integrable ω₂) (hφ : Integrable φ) :
    crossPairing ω₁ φ - crossPairing ω₂ φ = crossPairing (ω₁ - ω₂) φ := by
  have hint₁ := integrable_bsPairKernel hd A B hmω₁ hmφ hω₁s hφs hsep hω₁ hφ
  have hint₂ := integrable_bsPairKernel hd A B hmω₂ hmφ hω₂s hφs hsep hω₂ hφ
  have hsub : ∀ x : Fin 3 → ℝ, (ω₁ - ω₂) x ≠ 0 → x ∈ A := by
    intro x hx
    by_cases h1 : ω₁ x = 0
    · refine hω₂s x ?_
      intro h2
      apply hx
      rw [Pi.sub_apply, h1, h2]
      simp
    · exact hω₁s x h1
  have hintd := integrable_bsPairKernel hd A B (hmω₁.sub hmω₂) hmφ hsub hφs hsep
    (hω₁.sub hω₂) hφ
  have hpt : ∀ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      bsPairKernel ω₁ φ p.1 p.2 - bsPairKernel ω₂ φ p.1 p.2
        = bsPairKernel (ω₁ - ω₂) φ p.1 p.2 := by
    intro p
    rw [bsPairKernel, bsPairKernel, bsPairKernel, sub_div_same, ← dot3_sub_left, Pi.sub_apply]
  rw [crossPairing, crossPairing, crossPairing, ← integral_sub hint₁ hint₂]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- Explicit Lipschitz bound for the pairing in the `L¹` norm: changing the first field
within a fixed support region `A`, while the second field stays `d`-separated from `A`,
changes the pairing by at most the separated constant times the `L¹` norm of the
difference times the `L¹` norm of the second field. -/
theorem abs_crossPairing_sub_le {ω₁ ω₂ φ : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {d : ℝ} (hd : 0 < d)
    (A B : Set (Fin 3 → ℝ))
    (hmω₁ : Measurable ω₁) (hmω₂ : Measurable ω₂) (hmφ : Measurable φ)
    (hω₁s : ∀ x, ω₁ x ≠ 0 → x ∈ A) (hω₂s : ∀ x, ω₂ x ≠ 0 → x ∈ A)
    (hφs : ∀ y, φ y ≠ 0 → y ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ euclideanLength (x - y))
    (hω₁ : Integrable ω₁) (hω₂ : Integrable ω₂) (hφ : Integrable φ) :
    |crossPairing ω₁ φ - crossPairing ω₂ φ|
      ≤ 3 / (2 * π * d ^ 2) * (∫ x, ‖ω₁ x - ω₂ x‖) * ∫ y, ‖φ y‖ := by
  rw [crossPairing_sub_eq hd A B hmω₁ hmω₂ hmφ hω₁s hω₂s hφs hsep hω₁ hω₂ hφ]
  have hsub : ∀ x, (ω₁ - ω₂) x ≠ 0 → x ∈ A := by
    intro x hx
    by_cases h1 : ω₁ x = 0
    · refine hω₂s x ?_
      intro h2
      apply hx
      rw [Pi.sub_apply, h1, h2]
      simp
    · exact hω₁s x h1
  exact abs_crossPairing_le hd A B (hmω₁.sub hmω₂) hmφ hsub hφs hsep (hω₁.sub hω₂) hφ

/-- Squeeze helper: if the absolute difference of a real family from a constant is
dominated by a family tending to zero, the family tends to the constant. -/
private theorem tendsto_of_abs_le_zero {ι : Type*} {l : Filter ι} {g : ι → ℝ} {L : ℝ}
    {h : ι → ℝ} (habs : ∀ i, |g i - L| ≤ h i) (h0 : Tendsto h l (𝓝 0)) :
    Tendsto g l (𝓝 L) := by
  have hsq : Tendsto (fun i => |g i - L|) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _)
      (Eventually.of_forall habs) h0
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using hsq

/-- `L¹`-continuity of the pairing — the weak-convergence entry on the continuous side:
a family of integrable fields supported in a fixed region `A`, converging in `L¹` to a
field also supported in `A`, pairs against any fixed integrable field `d`-separated
from `A` convergently. No truncation or near-diagonal control is needed because the
supports are separated. -/
theorem tendsto_crossPairing {ι : Type*} {l : Filter ι}
    (F : ι → ((Fin 3 → ℝ) → (Fin 3 → ℝ))) (ω φ : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    {d : ℝ} (hd : 0 < d)
    (A B : Set (Fin 3 → ℝ))
    (hmF : ∀ i, Measurable (F i)) (hmω : Measurable ω) (hmφ : Measurable φ)
    (hFs : ∀ i x, F i x ≠ 0 → x ∈ A) (hωs : ∀ x, ω x ≠ 0 → x ∈ A)
    (hφs : ∀ y, φ y ≠ 0 → y ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, d ≤ euclideanLength (x - y))
    (hF : ∀ i, Integrable (F i)) (hω : Integrable ω) (hφ : Integrable φ)
    (hL1 : Tendsto (fun i => ∫ x, ‖F i x - ω x‖) l (𝓝 0)) :
    Tendsto (fun i => crossPairing (F i) φ) l (𝓝 (crossPairing ω φ)) := by
  refine tendsto_of_abs_le_zero (fun i =>
    abs_crossPairing_sub_le hd A B (hmF i) hmω hmφ (hFs i) hωs hφs hsep (hF i) hω hφ) ?_
  have hc : Tendsto (fun _ : ι => 3 / (2 * π * d ^ 2)) l (𝓝 (3 / (2 * π * d ^ 2))) :=
    tendsto_const_nhds
  have h1 : Tendsto (fun i => 3 / (2 * π * d ^ 2) * (∫ x, ‖F i x - ω x‖)) l (𝓝 0) := by
    simpa using hc.mul hL1
  have hd2 : Tendsto (fun _ : ι => ∫ y, ‖φ y‖) l (𝓝 (∫ y, ‖φ y‖)) := tendsto_const_nhds
  simpa using h1.mul hd2

/-! ### The truncated Biot–Savart velocity and helicity -/

/-- The Biot–Savart velocity integrand with the `δ`-ball around the singularity
excised: on the region `|x - y| ≥ δ` it is the cross product of the vorticity with the
chord scaled by the Gauss denominator, and zero elsewhere. -/
noncomputable def bsVelocityKernel (ω : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (δ : ℝ)
    (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Set.indicator {r : Fin 3 → ℝ | δ ≤ euclideanLength (x - r)}
    (fun r => (4 * π * euclideanLength (x - r) ^ 3)⁻¹ • cross3 (ω r) (x - r)) y

/-- The velocity kernel at positive truncation level is dominated by the explicit
constant `1/(2π δ²)` times the vorticity norm. -/
theorem norm_bsVelocityKernel_le {ω : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {δ : ℝ} (hδ : 0 < δ)
    (x y : Fin 3 → ℝ) :
    ‖bsVelocityKernel ω δ x y‖ ≤ (2 * π * δ ^ 2)⁻¹ * ‖ω y‖ := by
  rw [bsVelocityKernel]
  by_cases hle : δ ≤ euclideanLength (x - y)
  · have hmem : y ∈ {r : Fin 3 → ℝ | δ ≤ euclideanLength (x - r)} := hle
    have hlen0 : 0 < euclideanLength (x - y) := lt_of_lt_of_le hδ hle
    have hbase : (0 : ℝ) < 4 * π * euclideanLength (x - y) ^ 3 :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hlen0 3)
    rw [Set.indicator_of_mem hmem, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hbase)]
    have h1 : ‖cross3 (ω y) (x - y)‖ ≤ 2 * ‖ω y‖ * euclideanLength (x - y) := by
      refine le_trans (norm_cross3_le_mul _ _) ?_
      exact mul_le_mul_of_nonneg_left (norm_le_euclideanLength _) (by positivity)
    have hsq : δ ^ 2 ≤ euclideanLength (x - y) ^ 2 := by
      have hnn := euclideanLength_nonneg (x - y)
      have hsum : (0 : ℝ) ≤ δ + euclideanLength (x - y) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hle hsum
      nlinarith
    have hinv : (4 * π * euclideanLength (x - y) ^ 3)⁻¹ * (2 * euclideanLength (x - y))
        ≤ (2 * π * δ ^ 2)⁻¹ := by
      have hle2 : 2 * π * δ ^ 2 ≤ 2 * π * euclideanLength (x - y) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have heq : (4 * π * euclideanLength (x - y) ^ 3)⁻¹ * (2 * euclideanLength (x - y))
          = (2 * π * euclideanLength (x - y) ^ 2)⁻¹ := by
        field_simp [Real.pi_pos.ne', hlen0.ne']
        ring
      rw [heq, inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) hle2
    calc (4 * π * euclideanLength (x - y) ^ 3)⁻¹ * ‖cross3 (ω y) (x - y)‖
        ≤ (4 * π * euclideanLength (x - y) ^ 3)⁻¹
            * (2 * ‖ω y‖ * euclideanLength (x - y)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hbase.le)
      _ = (4 * π * euclideanLength (x - y) ^ 3)⁻¹ * (2 * euclideanLength (x - y)) * ‖ω y‖ := by
          ring
      _ ≤ (2 * π * δ ^ 2)⁻¹ * ‖ω y‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  · have hmem : ¬(y ∈ {r : Fin 3 → ℝ | δ ≤ euclideanLength (x - r)}) := hle
    rw [indicator_of_not_mem0 _ _ hmem, norm_zero]
    positivity

/-- For a measurable `L¹` vorticity and positive truncation level the velocity kernel
is integrable in its second argument. -/
theorem integrable_bsVelocityKernel {ω : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hmω : Measurable ω)
    (hω : Integrable ω) {δ : ℝ} (hδ : 0 < δ) (x : Fin 3 → ℝ) :
    Integrable (fun y => bsVelocityKernel ω δ x y) := by
  have hlen : Measurable fun r : Fin 3 → ℝ => euclideanLength (x - r) :=
    continuous_euclideanLength.measurable.comp (measurable_const.sub measurable_id)
  have hset : MeasurableSet {r : Fin 3 → ℝ | δ ≤ euclideanLength (x - r)} :=
    MeasurableSet.preimage (measurableSet_Ici (a := δ)) hlen
  have hsub : Measurable fun r : Fin 3 → ℝ => x - r :=
    measurable_const.sub measurable_id
  have hcross : Measurable fun r : Fin 3 → ℝ => cross3 (ω r) (x - r) :=
    continuous_cross3_pair.measurable.comp (hmω.prodMk hsub)
  have hlen3 : Measurable fun r : Fin 3 → ℝ => (4 : ℝ) * π * euclideanLength (x - r) ^ 3 :=
    measurable_const.mul (hlen.pow_const 3)
  have hinner : Measurable fun r : Fin 3 → ℝ =>
      ((4 : ℝ) * π * euclideanLength (x - r) ^ 3)⁻¹ • cross3 (ω r) (x - r) :=
    hlen3.inv.smul hcross
  exact Integrable.mono' (hω.norm.const_mul (2 * π * δ ^ 2)⁻¹)
    (Measurable.aestronglyMeasurable (hinner.indicator hset))
    (Filter.Eventually.of_forall fun y => norm_bsVelocityKernel_le hδ x y)

/-- The truncated Biot–Savart velocity field. -/
noncomputable def bsVelocityTrunc (ω : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (δ : ℝ)
    (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∫ y, bsVelocityKernel ω δ x y ∂volume

/-- The truncated Biot–Savart helicity: the pairing of the truncated velocity with
the vorticity. -/
noncomputable def bsHelicityTrunc (ω : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (δ : ℝ) : ℝ :=
  ∫ x, dot3 (bsVelocityTrunc ω δ x) (ω x) ∂volume

/-- Measurability of the chord length on the product space. -/
private theorem hlenq_meas :
    Measurable fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => euclideanLength (q.1 - q.2) :=
  continuous_euclideanLength.measurable.comp (measurable_fst.sub measurable_snd)

/-- Measurability of the truncated-region set on the product space. -/
private theorem hsetT_meas (δ : ℝ) :
    MeasurableSet {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)} :=
  MeasurableSet.preimage (measurableSet_Ici (a := δ)) hlenq_meas

/-- Measurability of the velocity kernel as a product-space function: it is the
indicator of the measurable truncated region applied to a measurable scaled cross
product. -/
private theorem measurable_bsVelocityKernel_prod {ω : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hmω : Measurable ω) {δ : ℝ} :
    Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => bsVelocityKernel ω δ p.1 p.2 := by
  have hsubq : Measurable fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => q.1 - q.2 :=
    measurable_fst.sub measurable_snd
  have hcross : Measurable fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      cross3 (ω q.2) (q.1 - q.2) :=
    continuous_cross3_pair.measurable.comp ((hmω.comp measurable_snd).prodMk hsubq)
  have hlen3 : Measurable fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (4 : ℝ) * π * euclideanLength (q.1 - q.2) ^ 3 :=
    measurable_const.mul (hlenq_meas.pow_const 3)
  have hfm : Measurable fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ((4 : ℝ) * π * euclideanLength (q.1 - q.2) ^ 3)⁻¹ • cross3 (ω q.2) (q.1 - q.2) :=
    hlen3.inv.smul hcross
  have hrw : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => bsVelocityKernel ω δ p.1 p.2)
      = fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
          (fun q => ((4 : ℝ) * π * euclideanLength (q.1 - q.2) ^ 3)⁻¹
            • cross3 (ω q.2) (q.1 - q.2)) p := rfl
  rw [hrw]
  exact hfm.indicator (hsetT_meas δ)

/-- Fubini form of the truncated Biot–Savart helicity: for a measurable `L¹`
vorticity and positive truncation level, the truncated helicity equals the double
integral of the pairing kernel over the truncated region `|x - y| ≥ δ`. -/
theorem bsHelicityTrunc_eq {ω : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hmω : Measurable ω)
    (hω : Integrable ω) {δ : ℝ} (hδ : 0 < δ) :
    bsHelicityTrunc ω δ = ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
        (fun q => bsPairKernel ω ω q.1 q.2) p ∂(volume.prod volume) := by
  have hker := measurable_bsVelocityKernel_prod hmω (δ := δ)
  have hvint : ∀ x : Fin 3 → ℝ, Integrable (fun y => bsVelocityKernel ω δ x y) :=
    fun x => integrable_bsVelocityKernel hmω hω hδ x
  have hdot : ∀ x : Fin 3 → ℝ, dot3 (bsVelocityTrunc ω δ x) (ω x)
      = ∫ y, dot3 (ω x) (bsVelocityKernel ω δ x y) ∂volume := by
    intro x
    rw [bsVelocityTrunc, dot3_comm, ← dot3CLM_apply (ω x),
      ← ContinuousLinearMap.integral_comp_comm (dot3CLM (ω x)) (hvint x)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => (dot3CLM_apply (ω x) _))
  have h2int : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dot3 (ω p.1) (bsVelocityKernel ω δ p.1 p.2)) (volume.prod volume) := by
    have htensor : Integrable
        (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
          (3 * (2 * π * δ ^ 2)⁻¹) * (‖ω p.1‖ * ‖ω p.2‖)) (volume.prod volume) :=
      Integrable.congr ((hω.norm.const_mul (3 * (2 * π * δ ^ 2)⁻¹)).smul_prod hω.norm)
        (Filter.Eventually.of_forall fun p => by simp only [smul_eq_mul]; ring)
    refine Integrable.mono' htensor ?_ ?_
    · exact Measurable.aestronglyMeasurable
        ((continuous_dot3_pair.measurable.comp
          ((hmω.comp measurable_fst).prodMk hker)))
    · exact Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        calc |dot3 (ω p.1) (bsVelocityKernel ω δ p.1 p.2)|
            ≤ 3 * ‖ω p.1‖ * ‖bsVelocityKernel ω δ p.1 p.2‖ := abs_dot3_le _ _
          _ ≤ 3 * ‖ω p.1‖ * ((2 * π * δ ^ 2)⁻¹ * ‖ω p.2‖) :=
              mul_le_mul_of_nonneg_left (norm_bsVelocityKernel_le hδ p.1 p.2) (by positivity)
          _ = (3 * (2 * π * δ ^ 2)⁻¹) * (‖ω p.1‖ * ‖ω p.2‖) := by ring
  have hL : bsHelicityTrunc ω δ
      = ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
        dot3 (ω p.1) (bsVelocityKernel ω δ p.1 p.2) ∂(volume.prod volume) := by
    rw [bsHelicityTrunc,
      show (∫ x, dot3 (bsVelocityTrunc ω δ x) (ω x) ∂volume)
        = ∫ x, (∫ y, dot3 (ω x) (bsVelocityKernel ω δ x y) ∂volume) ∂volume from
        integral_congr_ae (Filter.Eventually.of_forall fun x => hdot x)]
    exact (integral_prod
      (fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => dot3 (ω q.1) (bsVelocityKernel ω δ q.1 q.2))
      h2int).symm
  rw [hL]
  refine integral_congr_ae (f := fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dot3 (ω p.1) (bsVelocityKernel ω δ p.1 p.2))
    (g := fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
        (fun q => bsPairKernel ω ω q.1 q.2) p) (Filter.Eventually.of_forall ?_)
  intro p
  show dot3 (ω p.1) (bsVelocityKernel ω δ p.1 p.2)
      = Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
        (fun q => bsPairKernel ω ω q.1 q.2) p
  by_cases hp : δ ≤ euclideanLength (p.1 - p.2)
  · have h1 : p.2 ∈ {r : Fin 3 → ℝ | δ ≤ euclideanLength (p.1 - r)} := hp
    have hvel : bsVelocityKernel ω δ p.1 p.2
        = (4 * π * euclideanLength (p.1 - p.2) ^ 3)⁻¹ • cross3 (ω p.2) (p.1 - p.2) :=
      Set.indicator_of_mem
        (f := fun r : Fin 3 → ℝ =>
          (4 * π * euclideanLength (p.1 - r) ^ 3)⁻¹ • cross3 (ω r) (p.1 - r)) h1
    have h2 : p ∈ {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)} := hp
    rw [hvel, dot3_smul_right, Set.indicator_of_mem h2, bsPairKernel, div_eq_inv_mul, mul_comm]
  · have h1 : ¬(p.2 ∈ {r : Fin 3 → ℝ | δ ≤ euclideanLength (p.1 - r)}) := hp
    have h2 : ¬(p ∈ {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}) := hp
    have hz : bsVelocityKernel ω δ p.1 p.2 = 0 := indicator_of_not_mem0 _ _ h1
    rw [hz, indicator_of_not_mem0 _ _ h2]
    simp [dot3]

/-- The truncated Biot–Savart helicity of a parallel field vanishes identically: for
`ω = g • n` with constant direction `n`, the kernel is the scalar triple product of a
triple containing `n` twice, which vanishes before any regularization is needed. -/
theorem bsHelicityTrunc_parallel_eq_zero (g : (Fin 3 → ℝ) → ℝ) (n : Fin 3 → ℝ)
    (hmg : Measurable g) (hg : Integrable fun x => g x • n) {δ : ℝ} (hδ : 0 < δ) :
    bsHelicityTrunc (fun x => g x • n) δ = 0 := by
  have hmfield : Measurable fun x => g x • n := hmg.smul measurable_const
  have hK0 : ∀ x y : Fin 3 → ℝ,
      bsPairKernel (fun x => g x • n) (fun y => g y • n) x y = 0 := by
    intro x y
    rw [bsPairKernel, cross3_smul_left, dot3_smul_right, dot3_smul_left,
      dot3_comm n (cross3 n (x - y)), dot_cross_left]
    simp
  rw [bsHelicityTrunc_eq hmfield hg hδ]
  have hzero : ∀ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
        (fun q => bsPairKernel (fun x => g x • n) (fun y => g y • n) q.1 q.2) p = 0 := by
    intro p
    by_cases hp : δ ≤ euclideanLength (p.1 - p.2)
    · have hp' : p ∈ {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)} := hp
      rw [Set.indicator_of_mem hp', hK0]
    · have hp' : ¬(p ∈ {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}) := hp
      rw [indicator_of_not_mem0 _ _ hp']
  rw [integral_congr_ae (Filter.Eventually.of_forall hzero)]
  simp

/-- Convergence of the truncated Biot–Savart helicity to the full self-pairing as
`δ → 0⁺`, under the explicit hypothesis that the full pairing kernel is absolutely
integrable — the three-dimensional counterpart of writhe integrability. This is a
statement about the regularization, not about any filament pairing converging to this
limit. -/
theorem tendsto_bsHelicityTrunc {ω : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hmω : Measurable ω)
    (hω : Integrable ω)
    (hfull : Integrable
      (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => bsPairKernel ω ω p.1 p.2) (volume.prod volume)) :
    Tendsto (fun δ => bsHelicityTrunc ω δ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (crossPairing ω ω)) := by
  have hpos : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  have hKm : Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => bsPairKernel ω ω p.1 p.2 :=
    measurable_bsPairKernel hmω hmω
  have hdct : Tendsto (fun δ => ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
        (fun q => bsPairKernel ω ω q.1 q.2) p ∂(volume.prod volume))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (crossPairing ω ω)) := by
    rw [crossPairing]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => |bsPairKernel ω ω p.1 p.2|) ?_ ?_ hfull.abs ?_
    · filter_upwards with δ
      exact AEStronglyMeasurable.indicator
        (Measurable.aestronglyMeasurable hKm) (hsetT_meas δ)
    · filter_upwards with δ
      exact Filter.Eventually.of_forall fun p => by
        by_cases hp : δ ≤ euclideanLength (p.1 - p.2)
        · have hp' : p ∈ {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)} := hp
          rw [Set.indicator_of_mem hp', Real.norm_eq_abs]
        · have hp' : ¬(p ∈ {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}) := hp
          rw [indicator_of_not_mem0 _ _ hp', norm_zero]
          positivity
    · refine Filter.Eventually.of_forall fun p => ?_
      by_cases hp : 0 < euclideanLength (p.1 - p.2)
      · have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < euclideanLength (p.1 - p.2) :=
          isOpen_Iio.mem_nhds hp
        have h2 : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
            bsPairKernel ω ω p.1 p.2
              = Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
                (fun q => bsPairKernel ω ω q.1 q.2) p := by
          filter_upwards [(h1.mono fun δ hδ => le_of_lt hδ).filter_mono
            (nhdsWithin_le_nhds)] with δ hδ
          exact (Set.indicator_of_mem
            (f := fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => bsPairKernel ω ω q.1 q.2)
            (show p ∈ {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)} from hδ)).symm
        exact Filter.Tendsto.congr' h2 tendsto_const_nhds
      · have hlen0 : euclideanLength (p.1 - p.2) = 0 := by
          have hnn := euclideanLength_nonneg (p.1 - p.2)
          linarith
        have hK0 : bsPairKernel ω ω p.1 p.2 = 0 := by
          rw [bsPairKernel, hlen0]
          simp
        have h2 : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
            bsPairKernel ω ω p.1 p.2
              = Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
                (fun q => bsPairKernel ω ω q.1 q.2) p := by
          filter_upwards [hpos] with δ hδ
          have hz : Set.indicator {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | δ ≤ euclideanLength (q.1 - q.2)}
              (fun q => bsPairKernel ω ω q.1 q.2) p = 0 := by
            refine indicator_of_not_mem0 _ _ ?_
            simp only [Set.mem_ofPred_eq, hlen0]
            linarith
          rw [hK0]
          exact hz.symm
        exact Filter.Tendsto.congr' h2 tendsto_const_nhds
  refine Filter.Tendsto.congr' ?_ hdct
  filter_upwards [hpos] with δ hδ
  exact (bsHelicityTrunc_eq hmω hω hδ).symm

/-- A scalar multiple of a fixed vector by a measurable `L¹` coefficient function is
a measurable `L¹` vorticity field. -/
theorem integrable_smul_const_field {g : (Fin 3 → ℝ) → ℝ} (n : Fin 3 → ℝ)
    (hmg : Measurable g) (hg : Integrable g) :
    Integrable fun x => g x • n := by
  refine Integrable.mono' (hg.norm.const_mul ‖n‖) ?_ ?_
  · exact Measurable.aestronglyMeasurable (hmg.smul measurable_const)
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact le_of_eq (mul_comm _ _)

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
