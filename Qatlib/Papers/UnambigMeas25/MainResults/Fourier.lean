/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Fourier analysis over `F₂ⁿ` for Buzet--Chailloux,
"Fine-Grained Unambiguous Measurements", arXiv:2510.07298v2 (2025), §2.1.

This file establishes the Fourier facts used by the main results:

* orthogonality of characters over the full space `F₂ⁿ` (`char_sum_full`);
* the quantum Fourier transform `H^{⊗n}` is a self-adjoint involution,
  hence unitary (`qft_sq`, `qft_conjTranspose`, `qft_mul_conjTranspose`);
* the explicit shape of Fourier kets (`hatKet_apply`) and their
  orthonormality (`innerVec_hatKet`);
* Fourier kets are simultaneous eigenvectors of all shift operators
  (`prop5_eigenvector`), the eigenvalue form of Proposition 5.
-/
import Qatlib.Papers.UnambigMeas25.MainResults.Preliminaries

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.UnambigMeas25.MainResults

/-! ### Character orthogonality over the full space -/

/-- In `F₂ⁿ`, `x + y = 0` iff `x = y`. -/
lemma add_eq_zero_iff_eq {n : ℕ} (x y : F2Vec n) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have hy : y = x := by
      calc y = (x + x) + y := by rw [addSelf_zero, zero_add]
        _ = x + (x + y) := add_assoc x x y
        _ = x + 0 := by rw [h]
        _ = x := add_zero x
    exact hy.symm
  · intro h
    rw [h, addSelf_zero]

/-- Pairing lemma: if some `s` pairs nontrivially with `w`, then the
full character sum `∑_z (−1)^{w·z}` vanishes. -/
lemma char_sum_zero_of {n : ℕ} (w s : F2Vec n) (hs : dotF2 w s = 1) :
    ∑ z : F2Vec n, phase (dotF2 w z) = 0 := by
  have key : (∑ z, phase (dotF2 w z)) = -(∑ z, phase (dotF2 w z)) := by
    set e : F2Vec n ≃ F2Vec n :=
      { toFun := fun z => z + s
        invFun := fun z => z + s
        left_inv := by
          intro z
          show (z + s) + s = z
          rw [add_assoc, addSelf_zero, add_zero]
        right_inv := by
          intro z
          show (z + s) + s = z
          rw [add_assoc, addSelf_zero, add_zero] } with he
    calc (∑ z, phase (dotF2 w z))
        = ∑ z, phase (dotF2 w (z + s)) :=
          (Equiv.sum_comp e (fun z => phase (dotF2 w z))).symm
      _ = ∑ z, phase (dotF2 w z) * phase (dotF2 w s) := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [← phase_mul, dotF2_add_right]
      _ = (∑ z, phase (dotF2 w z)) * phase (dotF2 w s) :=
          (Finset.sum_mul _ _ _).symm
      _ = -(∑ z, phase (dotF2 w z)) := by
          rw [hs, phase_one]
          ring
  have hss : (∑ z, phase (dotF2 w z)) + (∑ z, phase (dotF2 w z)) = 0 := by
    have h0 := congrArg (fun t => t + (∑ z, phase (dotF2 w z))) key
    simp only [neg_add_cancel] at h0
    exact h0
  have h2S : (2 : ℂ) * (∑ z, phase (dotF2 w z)) = 0 := by
    rw [two_mul]
    exact hss
  exact ((mul_eq_zero.mp h2S).resolve_left two_ne_zero)

/-- The full character sum over `F₂ⁿ`: `∑_z (−1)^{w·z}` equals `2ⁿ`
if `w = 0` and vanishes otherwise (orthogonality of characters, §2.2). -/
theorem char_sum_full {n : ℕ} (w : F2Vec n) :
    ∑ z, phase (dotF2 w z) = if w = 0 then ((2 ^ n : ℕ) : ℂ) else 0 := by
  by_cases hw : w = 0
  · rw [if_pos hw, hw]
    have hz : ∀ z : F2Vec n, dotF2 (0 : F2Vec n) z = 0 := by
      intro z
      simp [dotF2]
    rw [Finset.sum_congr rfl (fun z _ => by rw [hz z, phase_zero])]
    simp
  · rw [if_neg hw]
    have hwi : ∃ i, w i ≠ 0 := by
      by_contra h
      push Not at h
      apply hw
      funext i
      simpa using h i
    obtain ⟨i, hi⟩ := hwi
    have h1 : w i = 1 := by
      rcases zmod2_cases (w i) with h0 | h1
      · exact absurd h0 hi
      · exact h1
    have hd : dotF2 w (fun j => if j = i then (1 : ZMod 2) else 0) = 1 := by
      simp only [dotF2]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, h1, one_mul]
      · intro j _ hj
        rw [if_neg hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    exact char_sum_zero_of w (fun j => if j = i then (1 : ZMod 2) else 0) hd

/-! ### The Fourier transform as a self-adjoint involution -/

/-- The squared prefactor of `H^{⊗n}` is `2^{−n}`. -/
lemma qft_coeff_sq (n : ℕ) :
    ((Real.sqrt 2)⁻¹ ^ n : ℝ) * ((Real.sqrt 2)⁻¹ ^ n : ℝ) = (2 : ℝ)⁻¹ ^ n := by
  rw [← mul_pow, ← mul_inv, Real.mul_self_sqrt (by norm_num)]

/-- `2^{−n} · 2ⁿ = 1`, stated in `ℂ` with the casts appearing in
`H^{⊗n} · H^{⊗n}`. -/
lemma inv_two_pow_mul_two_pow (n : ℕ) :
    (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * ((2 ^ n : ℕ) : ℂ) = 1 := by
  have key : ((2 : ℝ)⁻¹ ^ n) * ((2 ^ n : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow,
      inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
  exact_mod_cast key

/-- Coerced version of `qft_coeff_sq`: the product of the two Fourier
prefactors in `ℂ` is `2^{−n}`. -/
lemma qft_coeff_sq_coe (n : ℕ) :
    (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)
      = (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, qft_coeff_sq]

/-- The Fourier transform `H^{⊗n}` is an involution (§2.1). -/
theorem qft_sq (n : ℕ) : qftMat n * qftMat n = 1 := by
  ext x y
  simp only [Matrix.mul_apply, qftMat, Matrix.one_apply]
  have hterm : ∀ z : F2Vec n,
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 x z) : ℂ))
          * (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 z y))
      = (((Real.sqrt 2)⁻¹ ^ n : ℝ) * ((Real.sqrt 2)⁻¹ ^ n : ℝ))
          * phase (dotF2 (x + y) z) := by
    intro z
    rw [dotF2_comm z y, dotF2_add_left, phase_mul]
    ring
  rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.mul_sum, char_sum_full (x + y)]
  by_cases hxy : x + y = 0
  · rw [if_pos hxy, if_pos (add_eq_zero_iff_eq x y |>.mp hxy)]
    rw [qft_coeff_sq_coe]
    exact inv_two_pow_mul_two_pow n
  · rw [if_neg hxy]
    by_cases hxdy : x = y
    · exact absurd (by rw [hxdy, addSelf_zero]) hxy
    · rw [if_neg hxdy]
      ring

/-- Conjugation fixes the phase `(−1)^z`, which is real. -/
lemma star_phase (z : ZMod 2) : starRingEnd ℂ (phase z) = phase z := by
  rcases zmod2_cases z with rfl | rfl <;> simp [phase]

/-- The Fourier transform is symmetric with real phases, hence
self-adjoint: `(H^{⊗n})ᴴ = H^{⊗n}`. -/
theorem qft_conjTranspose (n : ℕ) : (qftMat n)ᴴ = qftMat n := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  simp only [qftMat]
  rw [Complex.star_def, map_mul, Complex.conj_ofReal, star_phase, dotF2_comm]

/-- Corollary: `H^{⊗n}` is unitary, being a self-adjoint involution. -/
theorem qft_mul_conjTranspose (n : ℕ) : qftMat n * (qftMat n)ᴴ = 1 := by
  rw [qft_conjTranspose, qft_sq]

/-! ### Fourier kets -/

/-- The Fourier ket: `|x̂⟩_i = 2^{−n/2} (−1)^{i·x}` (Definition 8). -/
theorem hatKet_apply {n : ℕ} (x i : F2Vec n) :
    hatKet x i = (((Real.sqrt 2)⁻¹ ^ n : ℝ)) * phase (dotF2 i x) := by
  simp only [hatKet, Matrix.mulVec, dotProduct, qftMat, Pi.single_apply]
  have h : ∀ j : F2Vec n,
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 i j) : ℂ))
          * (if j = x then (1 : ℂ) else 0)
      = if j = x then (((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 i j) : ℂ) else 0 := by
    intro j
    by_cases h : j = x <;> simp [h]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  simp

/-- **Fourier kets are shift eigenvectors** (Proposition 5, eigenvalue
form): `X_b |x̂⟩ = (−1)^{x·b} |x̂⟩`. -/
theorem prop5_eigenvector {n : ℕ} (b x : F2Vec n) :
    shiftX b *ᵥ hatKet x = phase (dotF2 x b) • hatKet x := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : (shiftX b *ᵥ hatKet x) i = hatKet x (i + b) := by
    simp only [Matrix.mulVec, dotProduct, shiftX]
    rw [Finset.sum_eq_single (i + b)]
    · rw [if_pos (by rw [add_assoc, addSelf_zero, add_zero]), one_mul]
    · intro j _ hjne
      have hi : ¬(i = j + b) := by
        intro h
        apply hjne
        rw [h, add_assoc, addSelf_zero, add_zero]
      rw [if_neg hi, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h1, hatKet_apply x (i + b), hatKet_apply x i]
  have hd : dotF2 (i + b) x = dotF2 i x + dotF2 x b := by
    rw [dotF2_add_left, dotF2_comm b x]
  rw [hd, phase_mul]
  ring

/-- Fourier kets form an orthonormal family: `⟨x̂|ŷ⟩ = δ_{x,y}`. -/
theorem innerVec_hatKet {n : ℕ} (x y : F2Vec n) :
    innerVec (hatKet x) (hatKet y) = if x = y then 1 else 0 := by
  have h : ∀ i : F2Vec n,
      starRingEnd ℂ (hatKet x i) * hatKet y i
      = (((Real.sqrt 2)⁻¹ ^ n : ℝ) * ((Real.sqrt 2)⁻¹ ^ n : ℝ))
          * phase (dotF2 i (x + y)) := by
    intro i
    rw [hatKet_apply x i, hatKet_apply y i, map_mul, Complex.conj_ofReal, star_phase]
    rw [dotF2_add_right, phase_mul]
    ring
  rw [innerVec, Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum]
  have hflip : ∀ i : F2Vec n, phase (dotF2 i (x + y)) = phase (dotF2 (x + y) i) :=
    fun i => by rw [dotF2_comm i (x + y)]
  rw [Finset.sum_congr rfl (fun i _ => hflip i), char_sum_full (x + y)]
  by_cases hxy : x + y = 0
  · rw [if_pos hxy, if_pos (add_eq_zero_iff_eq x y |>.mp hxy), qft_coeff_sq_coe]
    exact inv_two_pow_mul_two_pow n
  · rw [if_neg hxy]
    by_cases hxdy : x = y
    · exact absurd (by rw [hxdy, addSelf_zero]) hxy
    · rw [if_neg hxdy]
      ring

end Qatlib.Papers.UnambigMeas25.MainResults
