/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.FiniteAbelian
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Fourier identities on finite abelian groups

This module records linearity, translation covariance, and preservation of the sum of squared
norms for the normalized Fourier transform on a finite abelian group. The translation formula
`fourier_shift` expresses a hidden shift as an additive-character phase.

The development follows [VanDamHallgrenIp2006].

## Main statements

* `fourier_shift`: Translating the argument of `g` by `s` multiplies its Fourier coefficient at
  `ψ` by `ψ s`.
* `sum_normSq_fourier`: The sum of squared norms of all Fourier coefficients equals the sum of
  squared norms of the original function values.

## References

* [van Dam et al., 2006][VanDamHallgrenIp2006]
-/

set_option autoImplicit false

open Qatlib.Concepts.WalshMoment.Forrelation
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.HiddenShift02.MainResults.FourierCore

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The normalized Fourier transform preserves pointwise addition. -/
theorem fourier_add (f g : G → ℂ) : fourier (f + g) = fourier f + fourier g := by
  funext ψ
  simp only [fourier, Pi.add_apply, Matrix.mulVec_add]

/-- The normalized Fourier transform commutes with multiplication by a complex scalar. -/
theorem fourier_smul (c : ℂ) (f : G → ℂ) : fourier (c • f) = c • fourier f := by
  funext ψ
  simp only [fourier, Pi.smul_apply, Matrix.mulVec_smul]

/-- Translating the argument of `g` by `s` multiplies its Fourier coefficient at `ψ` by `ψ s`. -/
theorem fourier_shift (g : G → ℂ) (s : G) (ψ : AddChar G ℂ) :
    fourier (fun x => g (x + s)) ψ = ψ s * fourier g ψ := by
  classical

  have hstep : ∀ x : G, conj (ψ x) = conj (ψ (-s)) * conj (ψ (x + s)) := by
    intro x
    have hx : ψ x = ψ (-s) * ψ (x + s) := by
      have harg : x = -s + (x + s) := by abel
      conv_lhs => rw [harg]
      rw [AddChar.map_add_eq_mul]
    rw [hx, map_mul]
  have hreindex :
      (∑ x : G, conj (ψ (x + s)) * g (x + s)) = ∑ u : G, conj (ψ u) * g u :=
    Fintype.sum_equiv (Equiv.addRight s)
      (fun x => conj (ψ (x + s)) * g (x + s)) (fun u => conj (ψ u) * g u)
      (fun x => rfl)
  have hconjneg : conj (ψ (-s)) = ψ s := by
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  calc
    fourier (fun x => g (x + s)) ψ
        = fourierScale G * ∑ x : G, conj (ψ x) * g (x + s) := fourier_apply _ _
    _ = fourierScale G * ∑ x : G, (conj (ψ (-s)) * conj (ψ (x + s))) * g (x + s) := by
          rw [Finset.sum_congr rfl (fun x _ => by rw [hstep x])]
    _ = fourierScale G * (conj (ψ (-s)) *
          ∑ x : G, conj (ψ (x + s)) * g (x + s)) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
    _ = fourierScale G * (conj (ψ (-s)) * ∑ u : G, conj (ψ u) * g u) := by
          rw [hreindex]
    _ = ψ s * fourier g ψ := by
          rw [hconjneg, fourier_apply]
          ring

/-- The sum of squared norms of all Fourier coefficients equals the sum of squared norms of the
original function values. -/
theorem sum_normSq_fourier (f : G → ℂ) :
    (∑ ψ : AddChar G ℂ, ‖fourier f ψ‖ ^ 2) = ∑ x : G, ‖f x‖ ^ 2 := by
  classical
  set S : AddChar G ℂ → ℂ := fun ψ => ∑ x : G, conj (ψ x) * f x with hS
  have hq : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hscale : ‖fourierScale G‖ ^ 2 = ((Fintype.card G : ℝ))⁻¹ := by
    rw [fourierScale, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hq.le]
  have hterm : ∀ ψ : AddChar G ℂ, ‖fourier f ψ‖ ^ 2 =
      ((Fintype.card G : ℝ))⁻¹ * ‖S ψ‖ ^ 2 := by
    intro ψ
    rw [fourier_apply, norm_mul, mul_pow, hscale]
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = (z * conj z).re := by
    intro z
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hinner : (∑ ψ : AddChar G ℂ, S ψ * conj (S ψ))
      = (Fintype.card G : ℂ) * ∑ x : G, f x * conj (f x) := by
    have hconj : ∀ ψ : AddChar G ℂ, conj (S ψ) = ∑ y : G, ψ y * conj (f y) := by
      intro ψ
      unfold S
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [map_mul, Complex.conj_conj]
    calc
      (∑ ψ : AddChar G ℂ, S ψ * conj (S ψ))
          = ∑ ψ : AddChar G ℂ, ∑ x : G, ∑ y : G,
              (conj (ψ x) * f x) * (ψ y * conj (f y)) := by
            refine Finset.sum_congr rfl ?_
            intro ψ _
            rw [hconj, Finset.sum_mul_sum]
      _ = ∑ x : G, ∑ y : G,
            (∑ ψ : AddChar G ℂ, conj (ψ x) * ψ y) * (f x * conj (f y)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [Finset.sum_congr rfl (fun ψ (_ : ψ ∈ Finset.univ) => by
              show (conj (ψ x) * f x) * (ψ y * conj (f y))
                  = (conj (ψ x) * ψ y) * (f x * conj (f y))
              ring)]
            rw [← Finset.sum_mul]
      _ = ∑ x : G, ∑ y : G,
            (if y = x then (Fintype.card G : ℂ) else 0) * (f x * conj (f y)) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            refine Finset.sum_congr rfl ?_
            intro y _
            congr 1
            calc (∑ ψ : AddChar G ℂ, conj (ψ x) * ψ y)
                = ∑ ψ : AddChar G ℂ, ψ y * conj (ψ x) := by
                  refine Finset.sum_congr rfl ?_
                  intro ψ _
                  ring
              _ = if y = x then (Fintype.card G : ℂ) else 0 := sum_dual_mul_conj y x
      _ = (Fintype.card G : ℂ) * ∑ x : G, f x * conj (f x) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Finset.sum_eq_single x]
            · simp
            · intro y _ hyx
              simp [hyx]
            · intro hx
              simp at hx
  calc
    (∑ ψ : AddChar G ℂ, ‖fourier f ψ‖ ^ 2)
        = ∑ ψ : AddChar G ℂ, ((Fintype.card G : ℝ))⁻¹ * ‖S ψ‖ ^ 2 :=
          Finset.sum_congr rfl (fun ψ _ => hterm ψ)
    _ = ((Fintype.card G : ℝ))⁻¹ * ∑ ψ : AddChar G ℂ, ‖S ψ‖ ^ 2 := by
          rw [Finset.mul_sum]
    _ = ((Fintype.card G : ℝ))⁻¹ * ∑ ψ : AddChar G ℂ, (S ψ * conj (S ψ)).re := by
          congr 1
          exact Finset.sum_congr rfl (fun ψ _ => hsq (S ψ))
    _ = ((Fintype.card G : ℝ))⁻¹ *
          ((∑ ψ : AddChar G ℂ, S ψ * conj (S ψ)).re) := by
          congr 1
          rw [Complex.re_sum]
    _ = ((Fintype.card G : ℝ))⁻¹ *
          (((Fintype.card G : ℂ) * ∑ x : G, f x * conj (f x)).re) := by
          rw [hinner]
    _ = ∑ x : G, ‖f x‖ ^ 2 := by
          have hZ : ∀ x : G, f x * conj (f x) = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
            intro x
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          have hSsum : (∑ x : G, f x * conj (f x))
              = ((∑ x : G, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
            rw [Finset.sum_congr rfl (fun x _ => hZ x), Complex.ofReal_sum]
          rw [hSsum]
          have hEq : ((Fintype.card G : ℂ) * ((∑ x : G, ‖f x‖ ^ 2 : ℝ) : ℂ))
              = (((Fintype.card G : ℝ) * ∑ x : G, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
            push_cast
            ring
          rw [hEq, Complex.ofReal_re, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hq), one_mul]

end Qatlib.Papers.HiddenShift02.MainResults.FourierCore
