/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HSPAffine13.MainResults.Wavelet.WaveletStates

@[expose] public section

/-!
# Nontrivial eigenspaces of the affine generator

In Section 3, the multiplier generates the multiplicative group. Its
inverse acts transitively away from the fixed point, so one amplitude
determines the entire eigenfunction. A nontrivial character makes the
amplitude at the fixed point vanish.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HSPAffine13.MainResults

open Qatlib.Papers.HSPAffine13.MainResults

/-- For a generating multiplier, the nontrivial character eigenspace of the
affine action is the span of the corresponding wavelet. -/
theorem wavelet_line {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (u : Fˣ) (b v : F) (hχ : χ ≠ 1)
    (hgen : ∀ a : Fˣ, ∃ j : ℕ, (u⁻¹)^j = a) (hv : b + (u : F) * v = v)
    (f : F → ℂ) (hf : pi0 u b f = χ ((u⁻¹ : Fˣ) : F) • f) :
    ∃ z : ℂ, f = z • phi χ v := by
  let a : F := ((u⁻¹ : Fˣ) : F)
  have hpow (x : F) (hx : x ≠ 0) : ∃ j : ℕ, a ^ j = x := by
    obtain ⟨j, hj⟩ := hgen (Units.mk0 x hx)
    exact ⟨j, by simpa [a] using congrArg (fun z : Fˣ => (z : F)) hj⟩
  have hvalue : χ a ≠ 1 := by
    intro ha
    apply hχ
    apply MulChar.ext
    intro x
    obtain ⟨j, hj⟩ := hpow x x.ne_zero
    rw [MulChar.one_apply_coe, ← hj, map_pow, ha, one_pow]
  have hstep (y : F) : f (v + a * y) = χ a * f (v + y) := by
    have harg := pi0_phi_argument u b v hv (v + y)
    have harg' : (v + y - b) / (u : F) = v + a * y := by
      change (v + y - b) / (u : F) - v = a * (v + y - v) at harg
      rw [show v + y - v = y by ring] at harg
      linear_combination harg
    have he := congrFun hf (v + y)
    simpa only [pi0, harg', Pi.smul_apply, smul_eq_mul] using he
  have hfixed : f v = 0 := by
    have he := hstep 0
    simp only [mul_zero, add_zero] at he
    have hzero : (1 - χ a) * f v = 0 := by linear_combination he
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (Ne.symm hvalue))
  have horbit (j : ℕ) (y : F) :
      f (v + a ^ j * y) = χ (a ^ j) * f (v + y) := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_assoc, hstep, ih, map_mul, mul_assoc]
  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  have hcard' : (0 : ℝ) < ((Fintype.card F - 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt hcard)
  have hnorm : waveletNorm F ≠ 0 := by
    unfold waveletNorm
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hcard').ne')
  refine ⟨f (v + 1) / waveletNorm F, ?_⟩
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, phi, ← mul_assoc, div_mul_cancel₀ _ hnorm]
  by_cases hx : x = v
  · subst x
    simp [hfixed, χ.map_zero]
  · obtain ⟨j, hj⟩ := hpow (x - v) (sub_ne_zero.mpr hx)
    have he := horbit j 1
    rwa [hj, mul_one, show v + (x - v) = x by ring, mul_comm] at he

end Qatlib.Papers.HSPAffine13.MainResults
