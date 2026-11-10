/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs
import Qatlib.Papers.QuadChar00.MainResults.Lemma1FullAmplitude
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators

theorem theorem2_amplitude_uniform_units (n : ℕ) [NeZero n] (hn : Odd n)
    (hsq : Squarefree n) (h1 : 1 < n) (s : ZMod n) (y : ZMod n) (hy : IsUnit y) :
    ‖modularFourier n (fun x => ((jacobiCharZMod n (x + s) : ℤ) : ℂ)) y‖
      = ‖(Real.sqrt n : ℂ)⁻¹ * jacobiGaussSum n‖ := by
  classical
  have hJ : ‖((jacobiCharZMod n y : ℤ) : ℂ)‖ = 1 := by
    rcases jacobiCharZMod_unit_eq_one_or_neg_one n hy.unit with h | h
    · have hyy : y = (hy.unit : ZMod n) := (IsUnit.unit_spec hy).symm
      rw [hyy, h]; norm_num
    · have hyy : y = (hy.unit : ZMod n) := (IsUnit.unit_spec hy).symm
      rw [hyy, h]; norm_num
  rw [modularFourier, lemma1_amplitude_all n hn hsq h1 s y]
  conv_lhs =>
    rw [show (Real.sqrt n : ℂ)⁻¹ *
          (jacobiGaussSum n * ZMod.stdAddChar (-(s * y)) *
            ((jacobiCharZMod n y : ℤ) : ℂ))
        = ((Real.sqrt n : ℂ)⁻¹ * jacobiGaussSum n) *
            ZMod.stdAddChar (-(s * y)) * ((jacobiCharZMod n y : ℤ) : ℂ) by ring]
  rw [norm_mul, norm_mul, AddChar.norm_apply, hJ, mul_one, mul_one]

theorem theorem2_unit_fraction_den (n y : ℕ) (hn : 0 < n) (hcop : Nat.Coprime y n) :
    Rat.den ((y : ℚ) / n) = n := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdg : (y : ℤ).gcd (n : ℤ) = 1 := by
    rw [Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
    exact hcop
  rw [Rat.natCast_div_eq_divInt y n, Rat.den_divInt, if_neg hn0, Int.natAbs_natCast]
  have hgn : (n : ℤ).gcd (y : ℤ) = 1 := by
    rw [Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast, Nat.gcd_comm]
    exact hcop
  rw [hgn]
  simp

theorem theorem2_periodic_fourier_off_support (n k : ℕ) [NeZero n] [NeZero k]
    [NeZero (k * n)] (g : ZMod n → ℂ) (y : ZMod (k * n))
    (hy : ¬ (k : ℕ) ∣ y.val) :
    ∑ x : ZMod (k * n),
        g (ZMod.castHom (dvd_mul_left n k) (ZMod n) x) *
          ZMod.stdAddChar (x * y) = 0 := by
  classical
  set c : ZMod (k * n) →+* ZMod n := ZMod.castHom (dvd_mul_left n k) (ZMod n) with hc
  set φ : ZMod (k * n) → ℂ := fun x => ZMod.stdAddChar (x * y) with hφ
  set t : ZMod (k * n) := ((n : ℕ) : ZMod (k * n)) with ht
  set S : ℂ := ∑ x : ZMod (k * n), g (c x) * φ x with hS
  change S = 0
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hcn : c t = 0 := by
    rw [ht, hc, map_natCast, ZMod.natCast_self]

  have hstep : S = S * φ t := by
    rw [hS]
    have hterm : ∀ x : ZMod (k * n),
        g (c (x + t)) * φ (x + t) = (g (c x) * φ x) * φ t := by
      intro x
      have hcx : c (x + t) = c x := by rw [map_add, hcn, add_zero]
      have hφx : φ (x + t) = φ x * φ t := by
        have h1 : φ (x + t) = ZMod.stdAddChar ((x + t) * y) := by simp only [hφ]
        have h2 : φ x * φ t = ZMod.stdAddChar (x * y) * ZMod.stdAddChar (t * y) := by
          simp only [hφ]
        rw [h1, h2, show (x + t) * y = x * y + t * y by ring,
          AddChar.map_add_eq_mul]
      rw [hcx, hφx]
      ring
    have hre : (∑ x : ZMod (k * n), g (c x) * φ x)
        = ∑ x : ZMod (k * n), g (c (x + t)) * φ (x + t) := by
      simpa using (Equiv.sum_comp (Equiv.addRight t)
        (fun x => g (c x) * φ x)).symm
    calc (∑ x : ZMod (k * n), g (c x) * φ x)
        = ∑ x : ZMod (k * n), g (c (x + t)) * φ (x + t) := hre
      _ = ∑ x : ZMod (k * n), (g (c x) * φ x) * φ t :=
            Finset.sum_congr rfl (fun x _ => hterm x)
      _ = (∑ x : ZMod (k * n), g (c x) * φ x) * φ t := (Finset.sum_mul ..).symm

  have hφt_ne : φ t ≠ 1 := by
    intro h
    have hzero : t * y = 0 := by
      have ht' : φ t = ZMod.stdAddChar (t * y) := by simp only [hφ]
      rw [← (ZMod.injective_stdAddChar (N := k * n)).eq_iff,
        AddChar.map_zero_eq_one]
      rw [← ht']
      exact h
    have htval : t * y = ((n * y.val : ℕ) : ZMod (k * n)) := by
      rw [ht]
      conv_lhs => rw [← ZMod.natCast_zmod_val y]
      push_cast
      ring
    have hdvd : (k * n) ∣ n * y.val := by
      apply (ZMod.natCast_eq_zero_iff (n * y.val) (k * n)).mp
      rw [← htval]
      exact hzero
    have hdvd' : n * k ∣ n * y.val := by
      rcases hdvd with ⟨c, hc⟩
      exact ⟨c, by rw [Nat.mul_comm n k]; exact hc⟩
    exact hy ((Nat.mul_dvd_mul_iff_left hnpos).mp hdvd')

  have hmul : S * (φ t - 1) = 0 := by
    rw [mul_sub, mul_one, ← hstep, sub_self]
  rcases mul_eq_zero.mp hmul with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hφt_ne

end Qatlib.Papers.QuadChar00.MainResults
