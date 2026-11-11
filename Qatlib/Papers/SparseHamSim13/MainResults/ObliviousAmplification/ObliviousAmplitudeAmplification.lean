/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseHamSim13.MainResults.ObliviousAmplification.TwoDSubspace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.6 (Oblivious amplitude amplification)

Fixed source: arXiv:1312.1414 (Berry, Childs, Cleve, Kothari, Somma, *Exponential
improvement in precision for simulating sparse Hamiltonians*), Lemma 3.6, page 9,
Eqs. (6), (7), proved on page 10 using Lemma 3.7.

Abstract inner-product-space formulation (cf. `TwoDSubspace.lean`):

* `A : E →ₗᵢ[ℂ] H` is the isometry `|ψ⟩ ↦ |0^µ⟩|ψ⟩`;
* `U : H ≃ₗᵢ[ℂ] H`, `V : E ≃ₗᵢ[ℂ] E` are the unitaries of Eq. (6);
* `Φ : E →ₗ[ℂ] H` is the branch `|Φ^⊥⟩` of Eq. (6);
* `R : H ≃ₗᵢ[ℂ] H` is the reflection `2Π - 1`: it fixes `range A` and negates
  the complementary branch (`hRA`, `hRPhi`, `hRperp`, which are the three facts
  about `Π` used in the proof);
* `S : H ≃ₗᵢ[ℂ] H` is `-U R U† R` (Eq. (6)); `hS` records the defining action.

The conclusion is Eq. (7): `S^ℓ U |0^µ⟩|ψ⟩ = sin((2ℓ+1)θ)|0^µ⟩V|ψ⟩ +
cos((2ℓ+1)θ)|Φ^⊥⟩` for every `ℓ ∈ ℤ`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators InnerProductSpace

namespace Qatlib.Papers.SparseHamSim13.MainResults

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Lemma 3.6 (Oblivious amplitude amplification), arXiv:1312.1414 p. 9,
Eq. (7).  Proof: `S` preserves the two-dimensional space `span{A ψ, Φ ψ}` and
acts there as rotation by `2θ`; induction on `ℓ ≥ 0` plus the `zpow` inverse for
`ℓ < 0` gives Eq. (7).  The range `θ ∈ (0, π/2)` and the orthogonality/isometry
hypotheses are recorded for fidelity to the paper but are not needed for the
algebraic induction. -/
theorem lemma_3_6_oblivious_amplitude_amplification
    (A : E →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) (V : E ≃ₗᵢ[ℂ] E)
    (Φ : E →ₗ[ℂ] H) (R : H ≃ₗᵢ[ℂ] H) (S : H ≃ₗᵢ[ℂ] H) (θ : ℝ)
    (_hθ0 : 0 < θ) (_hθ1 : θ < Real.pi / 2)
    (hU : ∀ ψ, U (A ψ) = (Real.sin θ : ℂ) • A (V ψ) + (Real.cos θ : ℂ) • Φ ψ)
    (_horth : ∀ ψ w, ⟪A w, Φ ψ⟫_ℂ = 0)
    (_hPhiIso : ∀ ψ w, ⟪Φ ψ, Φ w⟫_ℂ = ⟪ψ, w⟫_ℂ)
    (hRA : ∀ ψ, R (A ψ) = A ψ)
    (hRPhi : ∀ ψ, R (Φ ψ) = - Φ ψ)
    (hRperp : ∀ ψ, R (U.symm ((Real.cos θ : ℂ) • A (V ψ) -
      (Real.sin θ : ℂ) • Φ ψ)) =
        - U.symm ((Real.cos θ : ℂ) • A (V ψ) - (Real.sin θ : ℂ) • Φ ψ))
    (hS : ∀ x, S x = - U (R (U.symm (R x)))) :
    ∀ (ℓ : ℤ) (ψ : E),
      (S ^ ℓ) (U (A ψ)) =
        (Real.sin ((2 * (ℓ : ℝ) + 1) * θ) : ℂ) • A (V ψ) +
          (Real.cos ((2 * (ℓ : ℝ) + 1) * θ) : ℂ) • Φ ψ := by
  intro ℓ ψ
  let s : ℂ := (Real.sin θ : ℂ)
  let c : ℂ := (Real.cos θ : ℂ)
  let x : H := A (V ψ)
  let y : H := Φ ψ
  let z : H := A ψ
  let p : H := U.symm (c • x - s • y)
  have hUz : U z = s • x + c • y := by
    simpa [z, x, y, s, c] using hU ψ
  have hUp : U p = c • x - s • y := by simp [p]
  have hRp : R p = -p := by simpa [p, s, c] using hRperp ψ
  have hRx : R x = x := by simpa [x] using hRA (V ψ)
  have hRy : R y = -y := by simpa [y] using hRPhi ψ
  have hsc : s ^ 2 + c ^ 2 = 1 := by
    simpa [s, c, pow_two] using Complex.sin_sq_add_cos_sq (θ : ℂ)
  have hUx_inv : U.symm x = s • z + c • p := by
    apply U.injective
    rw [U.apply_symm_apply, map_add, map_smul, map_smul, hUz, hUp]
    simp only [smul_add, smul_sub, smul_smul]
    rw [show (s * s) • x + (s * c) • y + ((c * c) • x - (c * s) • y)
        = (s * s + c * c) • x + (s * c - c * s) • y by module]
    rw [show s * s + c * c = 1 by simpa [pow_two] using hsc,
        show s * c - c * s = 0 by ring]
    simp
  have hUy_inv : U.symm y = c • z - s • p := by
    apply U.injective
    rw [U.apply_symm_apply, map_sub, map_smul, map_smul, hUz, hUp]
    simp only [smul_add, smul_sub, smul_smul]
    rw [show (c * s) • x + (c * c) • y - ((s * c) • x - (s * s) • y)
        = (c * s - s * c) • x + (c * c + s * s) • y by module]
    rw [show c * s - s * c = 0 by ring,
        show c * c + s * s = 1 by rw [show c * c = c ^ 2 by ring, show s * s = s ^ 2 by ring, add_comm, hsc]]
    simp
  have hSx : S x = (Real.cos (2 * θ) : ℂ) • x - (Real.sin (2 * θ) : ℂ) • y := by
    rw [hS x, hRx, hUx_inv]
    have hRlin : R (s • z + c • p) = s • z - c • p := by
      rw [map_add, map_smul, map_smul]
      rw [show R z = z from by simpa [z] using hRA ψ, hRp]
      simp [sub_eq_add_neg]
    rw [hRlin, map_sub, map_smul, map_smul, hUz, hUp]
    simp only [smul_add, smul_sub, smul_smul]
    rw [show (Real.cos (2 * θ) : ℂ) = c * c - s * s by
      rw [Real.cos_two_mul]; simp only [s, c]; norm_cast; nlinarith [Real.sin_sq_add_cos_sq θ]]
    rw [show (Real.sin (2 * θ) : ℂ) = 2 * s * c by
      rw [Real.sin_two_mul]; simp only [s, c]; norm_cast]
    module
  have hSy : S y = (Real.sin (2 * θ) : ℂ) • x + (Real.cos (2 * θ) : ℂ) • y := by
    rw [hS y, hRy]
    simp only [map_neg, neg_neg]
    rw [hUy_inv]
    have hRlin : R (c • z - s • p) = c • z + s • p := by
      rw [map_sub, map_smul, map_smul]
      rw [show R z = z from by simpa [z] using hRA ψ, hRp]
      simp [sub_eq_add_neg]
    rw [hRlin, map_add, map_smul, map_smul, hUz, hUp]
    simp only [smul_add, smul_sub, smul_smul]
    rw [show (Real.sin (2 * θ) : ℂ) = 2 * s * c by
      rw [Real.sin_two_mul]; simp only [s, c]; norm_cast]
    rw [show (Real.cos (2 * θ) : ℂ) = c * c - s * s by
      rw [Real.cos_two_mul]; simp only [s, c]; norm_cast; nlinarith [Real.sin_sq_add_cos_sq θ]]
    module
  have hrot : ∀ n : ℕ, ∀ α : ℝ,
      (S ^ n) ((Real.sin α : ℂ) • x + (Real.cos α : ℂ) • y) =
        (Real.sin (α + 2 * (n : ℝ) * θ) : ℂ) • x +
          (Real.cos (α + 2 * (n : ℝ) * θ) : ℂ) • y := by
    intro n
    induction n with
    | zero =>
        intro α
        rw [pow_zero, show α + 2 * ((0 : ℕ) : ℝ) * θ = α by norm_num]
        rfl
    | succ n ih =>
        intro α
        rw [pow_succ']
        change S ((S ^ n) ((Real.sin α : ℂ) • x + (Real.cos α : ℂ) • y)) = _
        rw [ih α]
        rw [map_add, map_smul, map_smul, hSx, hSy]
        simp only [smul_add, smul_sub, smul_smul]
        have hsin : ((Real.sin (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.cos (2 * θ) : ℂ) +
              (Real.cos (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.sin (2 * θ) : ℂ)) =
            (Real.sin ((α + 2 * (n : ℝ) * θ) + 2 * θ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]; conv_rhs => rw [Real.sin_add]
        have hcos : ((Real.cos (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.cos (2 * θ) : ℂ) -
              (Real.sin (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.sin (2 * θ) : ℂ)) =
            (Real.cos ((α + 2 * (n : ℝ) * θ) + 2 * θ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]; conv_rhs => rw [Real.cos_add]
        rw [show ((Real.sin (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.cos (2 * θ) : ℂ)) • x -
              ((Real.sin (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.sin (2 * θ) : ℂ)) • y +
              (((Real.cos (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.sin (2 * θ) : ℂ)) • x +
                ((Real.cos (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.cos (2 * θ) : ℂ)) • y)
            = ((Real.sin (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.cos (2 * θ) : ℂ) +
                (Real.cos (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.sin (2 * θ) : ℂ)) • x +
              ((Real.cos (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.cos (2 * θ) : ℂ) -
                (Real.sin (α + 2 * (n : ℝ) * θ) : ℂ) * (Real.sin (2 * θ) : ℂ)) • y by module]
        rw [hsin, hcos]
        congr 2 <;> (congr 1; push_cast; ring_nf)
  have hpos : ∀ n : ℕ, (S ^ n) (U z) =
      (Real.sin ((2 * (n : ℝ) + 1) * θ) : ℂ) • x +
        (Real.cos ((2 * (n : ℝ) + 1) * θ) : ℂ) • y := by
    intro n
    have h := hrot n θ
    rw [show θ + 2 * (n : ℝ) * θ = (2 * (n : ℝ) + 1) * θ by ring] at h
    rwa [← hUz] at h
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg ℓ
  · rw [hk]
    simpa using hpos k
  · rw [hk]
    have hangle : ((2 * (((-↑k : ℤ) : ℝ)) + 1) * θ) = ((2 * (-(k : ℝ)) + 1) * θ) := by
      push_cast; ring
    rw [hangle]
    rw [zpow_neg, zpow_natCast, LinearIsometryEquiv.inv_def]
    have hkS : (S ^ k) ((Real.sin ((2 * (-(k : ℝ)) + 1) * θ) : ℂ) • x +
        (Real.cos ((2 * (-(k : ℝ)) + 1) * θ) : ℂ) • y) = s • x + c • y := by
      have h := hrot k ((2 * (-(k : ℝ)) + 1) * θ)
      rw [show (2 * (-(k : ℝ)) + 1) * θ + 2 * (k : ℝ) * θ = θ by ring] at h
      exact h
    rw [show U z = (S ^ k) ((Real.sin ((2 * (-(k : ℝ)) + 1) * θ) : ℂ) • x +
        (Real.cos ((2 * (-(k : ℝ)) + 1) * θ) : ℂ) • y) from hUz.trans hkS.symm]
    exact LinearIsometryEquiv.symm_apply_apply _ _
end Qatlib.Papers.SparseHamSim13.MainResults
