/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NilpotentHSP07.MainResults.HidingSet
public import Qatlib.Papers.NilpotentHSP07.MainResults.CharPhase
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Euclidean normalization of coset states and the Lemma 4 superposition

Fixed source: [Ivanyos, Sanselme, Santha 2007](https://arxiv.org/abs/0707.1260), Lemmas 4 and 6.
The public library represents a coset state as a complex amplitude function on a finite group and
proves normalization for the abstract pairing `inner`, which sums `ψ x * conj (ψ x)`.

This module transports those statements to the true complex Euclidean norm of the amplitude
vector, and then normalizes an untwisted superposition over a finite Fourier index set `U`: the
amplitudes `(1 / sqrt |U|) * cosetState (K u) a` form a unit vector in
`EuclideanSpace ℂ (U × G)`.  The constant `1` is uniform and independent of `G`, `U`, the
subgroup family, and the coset representative.  The index type is required to be nonempty, which
excludes the degenerate empty register.

For the phase-weighted state in Lemma 4, the Fourier register indexes characters of the central
coordinates. Given those coordinates on the coset support, multiplying by the paper's
negative character phase preserves the Euclidean norm. The state preparation procedure and
the group-theoretic identification of the support and its coordinates are outside this module.

## Main statements

* `sum_norm_sq_eq_inner_re` identifies the Euclidean squared mass of an amplitude function with
  the real part of the library pairing.
* `norm_cosetState_sqrt` proves that the normalized coset amplitude has Euclidean norm one.
* `norm_fourierCosetVector` proves that the untwisted superposition has Euclidean norm one.
* `norm_characterCosetSuperposition` proves normalization with the character phase of Lemma 4.

## References

* [Ivanyos et al., 2007][IvanyosSanselmeSantha2007a], Lemmas 4 and 6
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NilpotentHSP07.CosetFourier

open Qatlib.Papers.NilpotentHSP07.MainResults

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The amplitude function of a complex-valued state, regarded as a vector in the complex
Euclidean space indexed by the group. -/
def toEuclidean (ψ : G → ℂ) : EuclideanSpace ℂ G :=
  WithLp.toLp 2 ψ

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Evaluation of the Euclidean amplitude vector agrees with the original function. -/
@[simp] theorem toEuclidean_apply (ψ : G → ℂ) (x : G) : toEuclidean ψ x = ψ x := rfl

omit [Group G] [DecidableEq G] in
/-- The Euclidean squared mass of an amplitude function is the real part of the library
pairing with itself. -/
theorem sum_norm_sq_eq_inner_re (ψ : G → ℂ) :
    (∑ x, ‖ψ x‖ ^ 2) =
      (Qatlib.Papers.NilpotentHSP07.MainResults.inner ψ ψ).re := by
  have hterm : ∀ x : G, (ψ x * star (ψ x)).re = ‖ψ x‖ ^ 2 := by
    intro x
    have h : ψ x * star (ψ x) = ((‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
      rw [show star (ψ x) = (starRingEnd ℂ) (ψ x) from rfl]
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [h, Complex.ofReal_re]
  rw [Qatlib.Papers.NilpotentHSP07.MainResults.inner]
  calc
    (∑ x, ‖ψ x‖ ^ 2) = ∑ x, (ψ x * star (ψ x)).re :=
      Finset.sum_congr rfl fun x _ => (hterm x).symm
    _ = (∑ x, ψ x * star (ψ x)).re := by rw [Complex.re_sum]

omit [Group G] [DecidableEq G] in
/-- The Euclidean norm squared of an amplitude vector is its total squared mass. -/
theorem norm_toEuclidean_sq (ψ : G → ℂ) :
    ‖toEuclidean ψ‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

omit [Group G] [DecidableEq G] in
/-- The Euclidean norm of an amplitude vector is the square root of its total squared mass. -/
theorem norm_toEuclidean (ψ : G → ℂ) :
    ‖toEuclidean ψ‖ =
      Real.sqrt (Qatlib.Papers.NilpotentHSP07.MainResults.inner ψ ψ).re := by
  rw [← sum_norm_sq_eq_inner_re, ← norm_toEuclidean_sq,
    Real.sqrt_sq (norm_nonneg (toEuclidean ψ))]

/-- The Euclidean squared norm of a constant-amplitude coset state is the subgroup cardinality
times the squared amplitude. -/
theorem norm_sq_cosetState (K : Subgroup G) (a : G) (c : ℂ) :
    ‖toEuclidean (cosetState K a c)‖ ^ 2 = (Nat.card K : ℝ) * ‖c‖ ^ 2 := by
  rw [norm_toEuclidean_sq, sum_norm_sq_eq_inner_re, inner_cosetState_self]
  have hc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star c = (starRingEnd ℂ) c from rfl]
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [hc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The coset state with amplitude equal to the inverse square root of the subgroup cardinality
is a unit vector in the complex Euclidean space.  This is the Euclidean form of the
normalization used in [Ivanyos et al., Lemma 6][IvanyosSanselmeSantha2007a]. -/
theorem norm_cosetState_sqrt (K : Subgroup G) (a : G) :
    ‖toEuclidean (cosetState K a (((Real.sqrt (Nat.card K) : ℂ))⁻¹))‖ = 1 := by
  have hne : Nat.card K ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hcard : (0 : ℝ) < Nat.card K := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hsqrt : 0 < Real.sqrt (Nat.card K : ℝ) := Real.sqrt_pos.2 hcard
  have hc : ‖(((Real.sqrt (Nat.card K) : ℂ))⁻¹)‖ = (Real.sqrt (Nat.card K : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
  have hsq : ‖toEuclidean (cosetState K a (((Real.sqrt (Nat.card K) : ℂ))⁻¹))‖ ^ 2 = 1 := by
    rw [norm_sq_cosetState, hc, inv_pow, Real.sq_sqrt hcard.le, mul_inv_cancel₀ hcard.ne']
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

variable {U : Type*} [Fintype U] [Nonempty U]

/-- Uniform register amplitudes over `U` tensored with untwisted normalized coset states
indexed by a family of subgroups. -/
def fourierCosetVector (K : U → Subgroup G) (a : G) : EuclideanSpace ℂ (U × G) :=
  WithLp.toLp 2 fun ug =>
    ((Real.sqrt (Fintype.card U) : ℂ))⁻¹ *
      cosetState (K ug.1) a (((Real.sqrt (Nat.card (K ug.1)) : ℂ))⁻¹) ug.2

/-- The squared mass of each Fourier slice is the reciprocal of the Fourier register size. -/
theorem sum_slice_norm_sq (K : U → Subgroup G) (a : G) (u : U) :
    (∑ x, ‖(((Real.sqrt (Fintype.card U) : ℂ))⁻¹ *
      cosetState (K u) a (((Real.sqrt (Nat.card (K u)) : ℂ))⁻¹) x)‖ ^ 2)
      = (Fintype.card U : ℝ)⁻¹ := by
  have hcard : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast Fintype.card_pos (α := U)
  have hsqrt : 0 < Real.sqrt (Fintype.card U : ℝ) := Real.sqrt_pos.2 hcard
  have hc : ‖(((Real.sqrt (Fintype.card U) : ℂ))⁻¹)‖ =
      (Real.sqrt (Fintype.card U : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
  have hcos : (∑ x, ‖cosetState (K u) a
      (((Real.sqrt (Nat.card (K u)) : ℂ))⁻¹) x‖ ^ 2) = 1 := by
    rw [← norm_toEuclidean_sq, norm_cosetState_sqrt, one_pow]
  simp only [norm_mul, mul_pow]
  rw [← Finset.mul_sum, hcos, hc, inv_pow, Real.sq_sqrt hcard.le, mul_one]

/-- The untwisted superposition is a unit vector in the complex Euclidean norm. The constant
`1` is uniform in the group, the Fourier index type, the subgroup family, and the coset
representative. -/
theorem norm_fourierCosetVector (K : U → Subgroup G) (a : G) :
    ‖fourierCosetVector K a‖ = 1 := by
  have hcard : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast Fintype.card_pos (α := U)
  have hsq : ‖fourierCosetVector K a‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ ug : U × G,
      ‖(((Real.sqrt (Fintype.card U) : ℂ))⁻¹ *
        cosetState (K ug.1) a (((Real.sqrt (Nat.card (K ug.1)) : ℂ))⁻¹) ug.2)‖ ^ 2) = 1
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [sum_slice_norm_sq]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

/-- Uniform form of `norm_cosetState_sqrt`: the constant `1` is fixed before the group, the
subgroup, and the coset representative. -/
theorem norm_cosetState_sqrt_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G]
        (K : Subgroup G) (a : G),
        ‖toEuclidean (cosetState K a (((Real.sqrt (Nat.card K) : ℂ))⁻¹))‖ = C := by
  refine ⟨1, one_pos, ?_⟩
  intro G _ _ _ K a
  exact norm_cosetState_sqrt K a

/-- Uniform normalization of the untwisted superposition: the constant `1` is fixed before the group, the
nonempty Fourier index type, the subgroup family, and the coset representative. -/
theorem lemma4_superposition_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G]
        (U : Type*) [Fintype U] [Nonempty U]
        (K : U → Subgroup G) (a : G),
        ‖fourierCosetVector (G := G) (U := U) K a‖ = C := by
  refine ⟨1, one_pos, ?_⟩
  intro G _ _ _ U _ _ K a
  exact norm_fourierCosetVector K a

/-- The character-weighted superposition from [IvanyosSanselmeSantha2007a], Lemma 4, on a
specified coset `aK`. The function `z` supplies the central coordinates on that coset:
for the paper's factorization `x = a * h * z₀`, it returns the vector representing `z₀`.
Its values outside the coset do not affect the amplitudes. -/
def characterCosetSuperposition {p d : ℕ} [Fact p.Prime]
    (K : Subgroup G) (a : G) (z : G → Fin d → ZMod p) :
    EuclideanSpace ℂ ((Fin d → ZMod p) × G) :=
  WithLp.toLp 2 fun ux =>
    fourierCosetVector (U := Fin d → ZMod p) (fun _ => K) a ux *
      charFun ux.1 (-z ux.2)

/-- Weighting the Fourier-register slices by the negative character phase of Lemma 4
preserves unit Euclidean norm. -/
theorem norm_characterCosetSuperposition {p d : ℕ} [Fact p.Prime]
    (K : Subgroup G) (a : G) (z : G → Fin d → ZMod p) :
    ‖characterCosetSuperposition K a z‖ = 1 := by
  have hω : ‖omega p‖ = 1 := by
    rw [omega, Complex.norm_exp]
    simp [Complex.div_re, Complex.mul_re]
  have hphase (u v : Fin d → ZMod p) : ‖charFun u v‖ = 1 := by
    rw [charFun, norm_pow, hω, one_pow]
  have hsq : ‖characterCosetSuperposition K a z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ ux : (Fin d → ZMod p) × G,
      ‖fourierCosetVector (U := Fin d → ZMod p) (fun _ => K) a ux *
        charFun ux.1 (-z ux.2)‖ ^ 2) = 1
    simp only [norm_mul, hphase, mul_one]
    rw [← EuclideanSpace.norm_sq_eq, norm_fourierCosetVector, one_pow]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

/-- One positive constant normalizes all the character-weighted superpositions, independently
of the group, prime, register dimension, coset, and choice of central coordinates. -/
theorem characterCosetSuperposition_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G]
        (p d : ℕ) [Fact p.Prime] (K : Subgroup G) (a : G)
        (z : G → Fin d → ZMod p), ‖characterCosetSuperposition K a z‖ = C := by
  refine ⟨1, one_pos, ?_⟩
  intro G _ _ _ p d _ K a z
  exact norm_characterCosetSuperposition K a z

end Qatlib.Papers.NilpotentHSP07.CosetFourier
