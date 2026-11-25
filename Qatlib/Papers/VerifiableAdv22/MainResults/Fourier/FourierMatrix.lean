/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VerifiableAdv22.MainResults.Fourier.FiniteFieldFourier
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

/-!
# The `n`-fold character Fourier transform as a unitary matrix

Section 2.2 of [BrakerskiCanettiQian2022VerifiableAdv] introduces the Fourier transform of a
function on the alphabet `Σ` and its `n`-fold tensor power `QFT_Σ^⊗n`, writing the latter as
`QFT_Σ^⊗n |f⟩ = Σ_z f̂(z) |z⟩`; Section 6 then applies `QFT_Σ^⊗n` and its inverse to register
states. The Public module it extends,
`Qatlib.Papers.VerifiableAdv22.MainResults.Fourier`, records `fhat` only as an amplitude
formula.
This module supplies the matrix of that transform, proves that it acts on state vectors by
`fhat`, and proves that it is unitary, so `QFT_Σ^⊗n` can be used as a gate.

The companion construction `Qatlib.Concepts.QuditTeleport.TeleportCore.characterQFTGate` proves
the same facts for cyclic registers `ZMod N` and their product characters. The present module
works for any finite abelian alphabet carrying a perfect bicharacter, which is the generality of
the paper's Section 2.2, and it does not depend on the cyclic case.

Paper: [arXiv:2204.02063v3](https://arxiv.org/abs/2204.02063v3), Section 2.2 (definition of
`QFT_{F_q}` and `QFT_Σ^⊗n`) and Section 6.

## Main statements

* `fourierMatrix_mulVec`: the matrix acts on a state vector by `fhat`.
* `fourierMatrix_mem_unitaryGroup`: the matrix is unitary.
* `exists_fourierMatrix_unitary_mulVec`: a unitary matrix realises `QFT_Σ^⊗n`.

## References

* [Brakerski, Canetti, and Qian, 2022][BrakerskiCanettiQian2022VerifiableAdv], Section 2.2.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix
open Qatlib.Papers.VerifiableAdv22.MainResults.Fourier

namespace Qatlib.Papers.VerifiableAdv22.MainResults.Fourier

variable {Alph : Type*} [AddCommGroup Alph] [Fintype Alph] [DecidableEq Alph]

/-- The normalisation `|Σ^n|^{-1/2}` multiplying the character sum of the `n`-symbol Fourier
transform; it is the scalar that appears in
`Qatlib.Papers.VerifiableAdv22.MainResults.Fourier.fhat`. -/
def fourierScale (Alph : Type*) [Fintype Alph] (n : ℕ) : ℂ :=
  ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ))⁻¹

omit [AddCommGroup Alph] [DecidableEq Alph] in
/-- The Fourier scale is a real number, so star conjugation fixes it. -/
@[simp] theorem star_fourierScale (n : ℕ) :
    star (fourierScale Alph n) = fourierScale Alph n := by
  simp [fourierScale]

omit [DecidableEq Alph] in
/-- The square of the Fourier scale times the cardinality `|Σ^n|` is one. -/
theorem fourierScale_mul_self_mul_card (n : ℕ) :
    fourierScale Alph n * fourierScale Alph n * (Fintype.card (Space Alph n) : ℂ) = 1 := by
  have : Nonempty Alph := ⟨0⟩
  have hcardpos : (0 : ℝ) < (Fintype.card (Space Alph n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcast : ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)) *
      ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)) =
        (Fintype.card (Space Alph n) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hcardpos.le, Complex.ofReal_natCast]
  have hne : ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hcardpos).ne'
  rw [fourierScale, ← mul_inv, ← hcast]
  exact inv_mul_cancel₀ (mul_ne_zero hne hne)

/-- The matrix of the `n`-symbol Fourier transform: the entry in frequency row `z` and register
column `x` is `|Σ^n|^{-1/2} · χ_z(x)`, where `χ_z` is the product character of
`Qatlib.Papers.VerifiableAdv22.MainResults.Fourier.Bichar.chi`. -/
def fourierMatrix (ω : Bichar Alph) (n : ℕ) :
    Matrix (Space Alph n) (Space Alph n) ℂ :=
  fun z x => fourierScale Alph n * ω.chi n z x

omit [DecidableEq Alph] in
/-- The Fourier matrix acts on a state vector by the `n`-symbol transform `fhat`. -/
theorem fourierMatrix_mulVec (ω : Bichar Alph) (n : ℕ) (ψ : Space Alph n → ℂ) :
    fourierMatrix ω n *ᵥ ψ = fhat ω n ψ := by
  funext z
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [fourierMatrix, fhat, fourierScale]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Orthogonality of the Fourier matrix rows: the sum of `χ_z(x)` against `star (χ_w(x))` over the
register group is the group cardinality when `z = w` and vanishes otherwise. -/
theorem sum_chi_mul_star_chi (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ)
    (z w : Space Alph n) :
    (∑ x : Space Alph n, ω.chi n z x * star (ω.chi n w x)) =
      if z = w then (Fintype.card (Space Alph n) : ℂ) else 0 := by
  simpa only [starRingEnd_apply] using Bichar.sum_chi_mul_conj ω hperf n z w

/-- The Fourier matrix times its conjugate transpose is the identity: its rows are
orthonormal, which is the matrix form of the orthogonality relation of the product
characters. -/
theorem fourierMatrix_mul_conjTranspose (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ) :
    fourierMatrix ω n * (fourierMatrix ω n)ᴴ = 1 := by
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ x : Space Alph n,
      fourierMatrix ω n k x * (fourierMatrix ω n)ᴴ x l =
        fourierScale Alph n * fourierScale Alph n *
          (ω.chi n k x * star (ω.chi n l x)) := by
    intro x
    rw [Matrix.conjTranspose_apply]
    simp only [fourierMatrix, star_mul, star_fourierScale]
    ring
  simp_rw [hterm]
  have hfac : (∑ x : Space Alph n, fourierScale Alph n * fourierScale Alph n *
      (ω.chi n k x * star (ω.chi n l x))) =
      fourierScale Alph n * fourierScale Alph n *
        ∑ x : Space Alph n, ω.chi n k x * star (ω.chi n l x) := by
    rw [Finset.mul_sum]
  rw [hfac, sum_chi_mul_star_chi ω hperf n k l]
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, ite_eq_left rfl, fourierScale_mul_self_mul_card]
  · rw [ite_eq_right hkl, ite_eq_right hkl, mul_zero]

/-- The Fourier matrix is unitary. -/
theorem fourierMatrix_mem_unitaryGroup (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ) :
    fourierMatrix ω n ∈ Matrix.unitaryGroup (Space Alph n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact fourierMatrix_mul_conjTranspose ω hperf n

/-- The `n`-fold character Fourier transform of Section 2.2 of arXiv:2204.02063v3 is realised by
a unitary matrix acting on state vectors of `Σ^n` by `fhat`. -/
theorem exists_fourierMatrix_unitary_mulVec (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ) :
    ∃ G : Matrix (Space Alph n) (Space Alph n) ℂ,
      G ∈ Matrix.unitaryGroup (Space Alph n) ℂ ∧
        ∀ (ψ : Space Alph n → ℂ) (z : Space Alph n), G.mulVec ψ z = fhat ω n ψ z :=
  ⟨fourierMatrix ω n, fourierMatrix_mem_unitaryGroup ω hperf n, fun _ _ => by
    rw [fourierMatrix_mulVec]⟩

end Qatlib.Papers.VerifiableAdv22.MainResults.Fourier
