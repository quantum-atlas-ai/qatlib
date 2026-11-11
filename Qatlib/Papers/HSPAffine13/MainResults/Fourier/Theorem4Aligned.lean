/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HSPAffine13.MainResults.Fourier.OrbitLine
import Qatlib.Papers.HSPAffine13.MainResults.Wavelet.WaveletStates
import Mathlib.NumberTheory.MulChar.Lemmas

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4, aligned case

The paper's Fourier transform `F_M` is written on the basis `|u^k>` of `Fˣ`.
We use the equivalent character basis: `F_M f` is the function on the
multiplicative characters `χ` of `F` given by

```
(F_M f)(χ) = (1 / sqrt (q - 1)) * ∑_{a ∈ Fˣ} χ(a) * f(a).
```

Under the canonical identification `u^k ↔ χ_u^k` this is exactly the paper's
transform.  In the aligned case `g = (a₀, b / (1 - u))`, the orbit state
`1 / sqrt (q - 1) ∑_{c ∈ C_b} |c g⟩` is uniform on the first coordinate and
supported at `g.b` on the second.  Its Fourier transform is therefore
`|1⟩ ⊗ |g.b⟩`, the first case of Theorem 4.

The generic case (`x ≠ b / (1 - u)`) is not proved in this module.
-/

set_option autoImplicit false

open scoped Classical

namespace Qatlib.Papers.HSPAffine13.MainResults

open AffineGroup

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Membership in the orbit `C_b · g`. -/
def InOrbit (u : Fˣ) (b : F) (g h : AffineGroup F) : Prop :=
  ∃ c ∈ C u b, c * g = h

/-- The orbit state `1 / sqrt (q - 1) ∑_{c ∈ C_b} |c g⟩`, written on the
coordinate space `Fˣ × F`. -/
noncomputable def orbitState (u : Fˣ) (b : F) (g : AffineGroup F) : Fˣ × F → ℂ :=
  fun p => if InOrbit u b g (⟨p.1, p.2⟩ : AffineGroup F) then waveletNorm F else 0

/-- The multiplicative Fourier transform on the character basis. -/
noncomputable def fourierCoeff (f : Fˣ → ℂ) (χ : MulChar F ℂ) : ℂ :=
  waveletNorm F * ∑ a : Fˣ, χ (a : F) * f a

/-- Summing over `Fˣ` is the same as summing over all field elements, because
a nontrivial multiplicative character vanishes at `0`. -/
theorem sum_units_eq_sum (χ : MulChar F ℂ) :
    (∑ a : Fˣ, χ (a : F)) = ∑ x : F, χ x := by
  have hnonzero : ((Finset.univ.filter (fun x : F => x ≠ 0)).sum (fun x => χ x)) =
      ∑ x : F, χ x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · simp [hx]
  rw [← hnonzero]
  refine Finset.sum_bij (fun a _ => (a : F)) ?_ ?_ ?_ ?_
  · intro a _; simp [a.ne_zero]
  · intro a1 _ a2 _ h; exact Units.ext h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨Units.mk0 x hx, by simp, rfl⟩
  · intro a _; rfl

/-- The Fourier transform is homogeneous in its input. -/
theorem fourierCoeff_smul (c : ℂ) (f : Fˣ → ℂ) (χ : MulChar F ℂ) :
    fourierCoeff (c • f) χ = c * fourierCoeff f χ := by
  unfold fourierCoeff
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The Fourier transform of the uniform state is the delta state at the
trivial character. -/
theorem fourierCoeff_uniform (χ : MulChar F ℂ) :
    fourierCoeff (fun _ : Fˣ => waveletNorm F) χ = if χ = 1 then 1 else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst hχ
    unfold fourierCoeff
    simp only [MulChar.one_apply_coe, one_mul, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_units]
    have hcard : 1 < Fintype.card F :=
      Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    have hq1 : (0 : ℝ) < ((Fintype.card F - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hcard
    have hsqrt : (((Real.sqrt ((Fintype.card F - 1 : ℕ) : ℝ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr hq1)
    unfold waveletNorm
    field_simp [hsqrt]
    simp only [if_true, mul_one]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hq1)]
    norm_num
  · rw [if_neg hχ]
    unfold fourierCoeff
    have hsum : (∑ a : Fˣ, χ (a : F)) = 0 := by
      rw [sum_units_eq_sum, MulChar.sum_eq_zero_of_ne_one hχ]
    rw [show (∑ a : Fˣ, χ (a : F) * waveletNorm F) =
        (∑ a : Fˣ, χ (a : F)) * waveletNorm F by
      rw [Finset.sum_mul]]
    rw [hsum]
    simp

/-- On the aligned orbit, every horizontal slice is a constant multiple of the
uniform state. -/
theorem orbitState_slice_aligned (u : Fˣ) (b : F) (hu : (u : F) ≠ 1)
    (hgen : Subgroup.zpowers u = ⊤) (g : AffineGroup F)
    (hg : g.b = b / (1 - (u : F))) (y : F) :
    (fun a : Fˣ => orbitState u b g (a, y)) =
      (if y = g.b then (1 : ℂ) else 0) • (fun _ : Fˣ => waveletNorm F) := by
  classical
  ext a
  have h := mem_orbit_iff_second_eq u b hu hgen g (⟨a, y⟩ : AffineGroup F) hg
  by_cases hy : y = g.b
  · have hmem : InOrbit u b g (⟨a, y⟩ : AffineGroup F) := h.mpr (by simpa using hy)
    simp only [orbitState, hmem, if_true, Pi.smul_apply, smul_eq_mul, if_pos hy, one_mul]
  · have hnot : ¬ InOrbit u b g (⟨a, y⟩ : AffineGroup F) :=
      fun hh => hy (by simpa using h.mp hh)
    simp only [orbitState, hnot, if_false, Pi.smul_apply, smul_eq_mul, if_neg hy, zero_mul]

/-- **Theorem 4, aligned case.**  If `g.b = b / (1 - u)` and `u` generates
`Fˣ`, then the Fourier transform of the orbit state is the product state
`|1⟩ ⊗ |g.b⟩`. -/
theorem theorem4_aligned (u : Fˣ) (b : F) (hu : (u : F) ≠ 1)
    (hgen : Subgroup.zpowers u = ⊤) (g : AffineGroup F)
    (hg : g.b = b / (1 - (u : F))) :
    (fun p : MulChar F ℂ × F => fourierCoeff (fun a => orbitState u b g (a, p.2)) p.1) =
      fun p : MulChar F ℂ × F =>
        (if p.1 = 1 then 1 else 0) * (if p.2 = g.b then 1 else 0) := by
  classical
  funext p
  rcases p with ⟨χ, y⟩
  rw [orbitState_slice_aligned u b hu hgen g hg y, fourierCoeff_smul,
    fourierCoeff_uniform]
  by_cases hχ : χ = 1 <;> by_cases hy : y = g.b <;> simp [hχ, hy]

end Qatlib.Papers.HSPAffine13.MainResults
