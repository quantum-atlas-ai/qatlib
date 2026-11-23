/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.InvariantLift

/-!
# Faithfulness of the actual invariant-frame representation

The frame has independent columns at every positive compression sine. Thus
its two-dimensional characteristic roots transport to the actual amplified
Hamiltonian, rather than merely describing unrelated numerical matrices.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.SpectrumLift

open Matrix
open InvariantLift

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A nonzero compression sine forces the actual residual to be nonzero. -/
theorem residual_ne_zero (U : Matrix I I ℂ) (v : I → ℂ) (gamma sine : ℂ)
    (hU : U * U = 1) (hv : v ≠ 0)
    (hnorm : gamma ^ 2 + sine ^ 2 = 1) (hsine : sine ≠ 0) :
    residual U v gamma ≠ 0 := by
  intro hw
  have h := residual_reflected U v gamma hU
  rw [hw, Matrix.mulVec_zero, smul_zero, sub_zero] at h
  have hgamma : gamma ^ 2 = 1 - sine ^ 2 := (eq_sub_iff_add_eq).2 hnorm
  have hsquare : 1 - gamma ^ 2 = sine ^ 2 := by rw [hgamma]; ring
  rw [hsquare] at h
  have hz : sine ^ 2 = 0 := (smul_eq_zero.1 h.symm).resolve_right hv
  exact (pow_ne_zero 2 hsine) hz

omit [DecidableEq I] in
/-- Matrix-vector application of the actual two-column invariant frame. -/
theorem spanFrame_mulVec (U : Matrix I I ℂ) (v : I → ℂ) (gamma sine : ℂ)
    (z : Fin 2 → ℂ) :
    spanFrame U v gamma sine *ᵥ z =
      (z 0) • v + (sine⁻¹ * z 1) • residual U v gamma := by
  funext i
  simp [spanFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The constructed invariant frame is injective; a nonzero block vector
therefore becomes a nonzero vector of the actual Hamiltonian. -/
theorem spanFrame_injective (P U : Matrix I I ℂ) (v : I → ℂ) (gamma sine : ℂ)
    (hU : U * U = 1) (hPv : P *ᵥ v = v)
    (hPUv : P *ᵥ (U *ᵥ v) = gamma • v) (hv : v ≠ 0)
    (hnorm : gamma ^ 2 + sine ^ 2 = 1) (hsine : sine ≠ 0) :
    Function.Injective (spanFrame U v gamma sine).mulVec := by
  have hw := residual_ne_zero U v gamma sine hU hv hnorm hsine
  have hPw := residual_projected P U v gamma hPv hPUv
  have hker : ∀ z : Fin 2 → ℂ, spanFrame U v gamma sine *ᵥ z = 0 → z = 0 := by
    intro z hz
    rw [spanFrame_mulVec] at hz
    have hpz := congrArg (fun x : I → ℂ => P *ᵥ x) hz
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hPv, hPw, smul_zero, add_zero, Matrix.mulVec_zero] at hpz
    have hz0 : z 0 = 0 := (smul_eq_zero.1 hpz).resolve_right hv
    rw [hz0, zero_smul, zero_add] at hz
    have hz1prod : sine⁻¹ * z 1 = 0 := (smul_eq_zero.1 hz).resolve_right hw
    have hz1 : z 1 = 0 := (mul_eq_zero.1 hz1prod).resolve_left (inv_ne_zero hsine)
    funext j
    fin_cases j
    · exact hz0
    · exact hz1
  intro x y hxy
  apply sub_eq_zero.1
  apply hker
  rw [Matrix.mulVec_sub, hxy, sub_self]

omit [DecidableEq I] in
/-- An injective matrix intertwiner transports genuine eigenvectors. -/
theorem eigenvector_transport (H : Matrix I I ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (T : Matrix I (Fin 2) ℂ) (hinter : H * T = T * B)
    (hinj : Function.Injective T.mulVec) (z : Fin 2 → ℂ) (mu : ℂ)
    (hz : z ≠ 0) (heigen : B *ᵥ z = mu • z) :
    T *ᵥ z ≠ 0 ∧ H *ᵥ (T *ᵥ z) = mu • (T *ᵥ z) := by
  constructor
  · intro hzero
    apply hz
    apply hinj
    simpa only [Matrix.mulVec_zero] using hzero
  · rw [Matrix.mulVec_mulVec, hinter, ← Matrix.mulVec_mulVec,
      heigen, Matrix.mulVec_smul]

/-- Every characteristic root of a finite block has an actual nonzero
eigenvector; this is an algebraic existence theorem, not an oracle output. -/
theorem characteristic_eigenvector (B : Matrix (Fin 2) (Fin 2) ℂ) (mu : ℂ)
    (hchar : (B - mu • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0) :
    ∃ z : Fin 2 → ℂ, z ≠ 0 ∧ B *ᵥ z = mu • z := by
  classical
  let A := B - mu • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hker : ∃ z : Fin 2 → ℂ, z ≠ 0 ∧ A *ᵥ z = 0 := by
    by_contra hnone
    have hinj : Function.Injective A.mulVec := by
      intro x y hxy
      by_contra hne
      apply hnone
      refine ⟨x - y, sub_ne_zero.2 hne, ?_⟩
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.1 hinj
    have hdet := (Matrix.isUnit_iff_isUnit_det A).1 hunit
    have hzero : A.det = 0 := hchar
    simp [hzero] at hdet
  obtain ⟨z, hz, hAz⟩ := hker
  refine ⟨z, hz, ?_⟩
  dsimp [A] at hAz
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hAz
  exact sub_eq_zero.1 hAz

end

end Qatlib.Papers.SpectralGap11.MainResults.SpectrumLift
