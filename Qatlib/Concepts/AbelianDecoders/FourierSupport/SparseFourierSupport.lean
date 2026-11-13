/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Sparse support bounds for the cyclic Fourier transform

This module defines `sparseFourierSupport` and proves support-sensitive bounds for `zmodQFT`. It
combines cyclic-window nonvanishing, preservation of squared norm, and a pointwise Fourier
weight estimate to obtain the support-product uncertainty inequality. For background, see
[Cornwell2014].

## Main statements

* `sparse_fourier_circular_window`: Every cyclic Fourier window of length equal to the support
  size of a nonzero state contains a nonzero Fourier coefficient.
* `sparse_fourier_support_product`: For a nonzero state on `ZMod N`, the product of its support
  size and its Fourier support size is at least `N`.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.AbelianDecoders.FourierSupport

open scoped Classical

/-- The finite set of coordinates where the state `ψ` has nonzero amplitude. -/
noncomputable def sparseFourierSupport {I : Type*} [Fintype I] (ψ : QState I) : Finset I :=
  Finset.univ.filter (fun x => ψ x ≠ 0)

/-- A coordinate belongs to `sparseFourierSupport ψ` exactly when its amplitude is nonzero. -/
@[simp] theorem mem_sparseFourierSupport {I : Type*} [Fintype I]
    (ψ : QState I) (x : I) : x ∈ sparseFourierSupport ψ ↔ ψ x ≠ 0 := by
  simp [sparseFourierSupport]

/-- A nonzero state has strictly positive support cardinality. -/
theorem sparseFourierSupport_card_pos {I : Type*} [Fintype I]
    {ψ : QState I} (hψ : ψ ≠ 0) : 0 < (sparseFourierSupport ψ).card := by
  rw [Finset.card_pos]
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 0 := by
    by_contra h
    apply hψ
    funext x
    simpa using (not_exists.mp h x)
  exact ⟨x, (mem_sparseFourierSupport ψ x).mpr hx⟩

/-- A weighted sum against `ψ` may be restricted to the nonzero support of `ψ`. -/
theorem sum_mul_sparseFourierSupport {I : Type*} [Fintype I]
    (ψ c : QState I) : ∑ x, c x * ψ x = ∑ x ∈ sparseFourierSupport ψ, c x * ψ x := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  have hzero : ψ x = 0 := by simpa using hx
  simp [hzero]

/-- The standard additive character of `ZMod N` is injective. -/
theorem stdAddChar_injective {N : ℕ} [NeZero N] :
    Function.Injective (ZMod.stdAddChar (N := N)) := by
  intro x y h
  rw [stdAddChar_eq_primRoot_zpow, stdAddChar_eq_primRoot_zpow,
    zpow_natCast, zpow_natCast] at h
  exact ZMod.val_injective (n := N) ((isPrimitiveRoot_primRoot (NeZero.ne N)).pow_inj
    (ZMod.val_lt x) (ZMod.val_lt y) h)

/-- Every cyclic Fourier window of length equal to the support size of a nonzero state contains
a nonzero Fourier coefficient. -/
theorem sparse_fourier_circular_window {N : ℕ} [NeZero N]
    (ψ : QState (ZMod N)) (hψ : ψ ≠ 0) (a : ZMod N) :
    ∃ t : Fin (sparseFourierSupport ψ).card,
      zmodQFT ψ (a + (t.val : ZMod N)) ≠ 0 := by
  let S := sparseFourierSupport ψ
  let e : Fin S.card ≃ ↥S := (Finset.equivFin S).symm
  let s : Fin S.card → ZMod N := fun j => (e j).val
  let f : Fin S.card → ℂ := fun j => ZMod.stdAddChar (s j)
  let v : Fin S.card → ℂ := fun j => ZMod.stdAddChar (s j * a) * ψ (s j)
  by_contra h
  have hz : ∀ t : Fin S.card, zmodQFT ψ (a + (t.val : ZMod N)) = 0 := by
    simpa only [not_exists, not_not] using h
  have hsum : ∀ t : Fin S.card, ∑ j, v j * f j ^ t.val = 0 := by
    intro t
    have ht := hz t
    rw [zmodQFT_apply] at ht
    have hsqrt : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < N by exact_mod_cast NeZero.pos N)).ne'
    have ht' := (mul_eq_zero.mp ht).resolve_left (inv_ne_zero hsqrt)
    rw [sum_mul_sparseFourierSupport] at ht'
    have he : (∑ x ∈ S, ZMod.stdAddChar (x * (a + (t.val : ZMod N))) * ψ x) =
        ∑ j : Fin S.card, ZMod.stdAddChar (s j * (a + (t.val : ZMod N))) * ψ (s j) := by
      rw [← Finset.sum_coe_sort]
      exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    rw [he] at ht'
    convert ht' using 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [v, f]
    rw [mul_add, AddChar.map_add_eq_mul,
      show s j * (t.val : ZMod N) = t.val • s j by simp [nsmul_eq_mul, mul_comm],
      AddChar.map_nsmul_eq_pow]
    ring
  have hf : Function.Injective f := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact stdAddChar_injective hij
  have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hsum
  obtain ⟨j⟩ : Nonempty (Fin S.card) := Fin.pos_iff_nonempty.mp (sparseFourierSupport_card_pos hψ)
  have hj : ψ (s j) ≠ 0 := (mem_sparseFourierSupport ψ (s j)).mp (e j).property
  have hc : ZMod.stdAddChar (s j * a) ≠ 0 := by
    intro hzero
    have hn := norm_stdAddChar (s j * a)
    rw [hzero, norm_zero] at hn
    norm_num at hn
  exact (mul_ne_zero hc hj) (congrFun hv j)

/-- Summing the squared coordinate norms over the support gives the same result as summing over
all coordinates. -/
theorem sum_sq_norm_sparseFourierSupport {I : Type*} [Fintype I] (ψ : QState I) :
    ∑ x ∈ sparseFourierSupport ψ, ‖ψ x‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2 := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  have hzero : ψ x = 0 := by simpa using hx
  simp [hzero]

/-- The cyclic quantum Fourier transform preserves the sum of squared coordinate norms. -/
theorem sum_sq_norm_zmodQFT {N : ℕ} [NeZero N] (ψ : QState (ZMod N)) :
    ∑ y, ‖zmodQFT ψ y‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2 := by
  simp_rw [← Complex.normSq_eq_norm_sq, ← applyGate_zmodQFTGate]
  exact sum_normSq_mulVec_of_mem_unitaryGroup (zmodQFTGate_unitary (NeZero.pos N)) ψ

/-- Each Fourier coefficient satisfies `N * ‖zmodQFT ψ k‖² ≤ |supp ψ| * ∑ x, ‖ψ x‖²`. -/
theorem sparse_fourier_point_weight {N : ℕ} [NeZero N]
    (ψ : QState (ZMod N)) (k : ZMod N) :
    (N : ℝ) * ‖zmodQFT ψ k‖ ^ 2 ≤
      ((sparseFourierSupport ψ).card : ℝ) * ∑ x, ‖ψ x‖ ^ 2 := by
  let S := sparseFourierSupport ψ
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN
  have hscale : Real.sqrt (N : ℝ) * ‖zmodQFT ψ k‖ =
      ‖∑ x ∈ S, ZMod.stdAddChar (x * k) * ψ x‖ := by
    rw [zmodQFT_apply, sum_mul_sparseFourierSupport, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have htriangle : Real.sqrt (N : ℝ) * ‖zmodQFT ψ k‖ ≤ ∑ x ∈ S, ‖ψ x‖ := by
    rw [hscale]
    calc
      _ ≤ ∑ x ∈ S, ‖ZMod.stdAddChar (x * k) * ψ x‖ := norm_sum_le _ _
      _ = ∑ x ∈ S, ‖ψ x‖ := by simp_rw [norm_mul, norm_stdAddChar, one_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun x => ‖ψ x‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [sum_sq_norm_sparseFourierSupport] at hcs
  have hsum : 0 ≤ ∑ x ∈ S, ‖ψ x‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq := Real.sq_sqrt hN.le
  have hb := norm_nonneg (zmodQFT ψ k)
  have hsquare := mul_self_le_mul_self (mul_nonneg hs.le hb) htriangle
  nlinarith

/-- For a nonzero state on `ZMod N`, the product of its support size and its Fourier support
size is at least `N`. -/
theorem sparse_fourier_support_product {N : ℕ} [NeZero N]
    (ψ : QState (ZMod N)) (hψ : ψ ≠ 0) :
    N ≤ (sparseFourierSupport ψ).card * (sparseFourierSupport (zmodQFT ψ)).card := by
  let T := sparseFourierSupport ψ
  let U := sparseFourierSupport (zmodQFT ψ)
  let q : ℝ := ∑ x, ‖ψ x‖ ^ 2
  have hq : 0 < q := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (sparseFourierSupport_card_pos hψ)
    have hpx : 0 < ‖ψ x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr
      ((mem_sparseFourierSupport ψ x).mp hx))
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨x, Finset.mem_univ x, hpx⟩
  have hbound : (N : ℝ) * q ≤ (U.card : ℝ) * ((T.card : ℝ) * q) := by
    calc
      (N : ℝ) * q = ∑ y ∈ U, (N : ℝ) * ‖zmodQFT ψ y‖ ^ 2 := by
        rw [← Finset.mul_sum, sum_sq_norm_sparseFourierSupport, sum_sq_norm_zmodQFT]
      _ ≤ ∑ _y ∈ U, (T.card : ℝ) * q := by
        exact Finset.sum_le_sum (fun y _ => sparse_fourier_point_weight ψ y)
      _ = (U.card : ℝ) * ((T.card : ℝ) * q) := by simp
  have hreal : (N : ℝ) ≤ (T.card : ℝ) * U.card := by nlinarith
  exact_mod_cast hreal

end Qatlib.Concepts.AbelianDecoders.FourierSupport
