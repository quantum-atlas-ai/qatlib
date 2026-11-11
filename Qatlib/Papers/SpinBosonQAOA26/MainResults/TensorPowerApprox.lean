/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3 — approximation of a tensor power

Fixed source: arXiv:2505.07929v2, Lemma 3, Appendix VI, PDF p. 39, eqs. (B125)–(B127).

For any Hilbert space, vectors `u, v` and a tensor power of order `D`,

  `‖(u + v)^{⊗D} - u^{⊗D}‖₂ ≤ D ‖v‖₂ (‖u‖₂ + ‖v‖₂)^{D-1}`  (B125),

and, when `u ⟂ v`, the tighter bound

  `‖(u + v)^{⊗D} - u^{⊗D}‖₂ ≤ √D ‖v‖₂ ‖u + v‖₂^{D-1}
     = √D ‖v‖₂ (‖u‖₂² + ‖v‖₂²)^{(D-1)/2}`  (B126)–(B127).

The tensor powers are Mathlib's `PiTensorProduct` over `Fin D`, whose `Norm` is the
projective seminorm (`PiTensorProduct.projectiveSeminorm_tprod_le`).

The numerical core of the estimate is the power-difference bound
`norm_pow_add_sub_pow_le`, proved below for any normed ring: it is the algebraic
content of the telescoping in the paper's proof of (B125).
Only the polynomial bound (B125) is formalized.  The orthogonal-case bound (B126) is not
included: it refers to the Hilbert tensor norm, whereas Mathlib's `PiTensorProduct` norm is
the projective seminorm, for which the bound fails already for `D = 2` with orthonormal
`u, v` (the difference has nuclear norm `√((3+√5)/2) + √((3-√5)/2) ≈ 2.236 > √2·√2 = 2`).

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.TensorPowerApprox

/-- Telescoping power-difference estimate (the numerical core of eq. (B125)): in any normed
ring with commuting `a, b`,

  `‖(a + b)^n - a^n‖ ≤ n ‖b‖ (‖a‖ + ‖b‖)^{n-1}`.

Proof: `(a+b)^n - a^n = (∑_{i<n} (a+b)^i a^{n-1-i}) · b` by
`Commute.geom_sum₂_mul`, then bound every summand by the common value
`(‖a‖ + ‖b‖)^{n-1}`. -/
theorem norm_pow_add_sub_pow_le {A : Type*} [NormedRing A] [NormOneClass A] (a b : A)
    (hab : Commute a b) (n : ℕ) :
    ‖(a + b) ^ n - a ^ n‖ ≤ (n : ℝ) * ‖b‖ * (‖a‖ + ‖b‖) ^ (n - 1) := by
  rcases n with _ | m
  · simp
  · have hgeom : ((a + b) ^ (m + 1) - a ^ (m + 1))
        = (∑ i ∈ Finset.range (m + 1), (a + b) ^ i * a ^ (m - i)) * b := by
      have h := Commute.geom_sum₂_mul (Commute.add_left (Commute.refl a) hab.symm) (m + 1)
      simpa [add_sub_cancel_left] using h.symm
    rw [hgeom]
    have hsum :
        ‖∑ i ∈ Finset.range (m + 1), (a + b) ^ i * a ^ (m - i)‖
          ≤ (m + 1 : ℝ) * (‖a‖ + ‖b‖) ^ m := by
      calc ‖∑ i ∈ Finset.range (m + 1), (a + b) ^ i * a ^ (m - i)‖
          ≤ ∑ i ∈ Finset.range (m + 1), ‖(a + b) ^ i * a ^ (m - i)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range (m + 1), (‖a‖ + ‖b‖) ^ m := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i ≤ m := by
              simpa using Finset.mem_range.mp hi
            have hna : (0 : ℝ) ≤ ‖a‖ + ‖b‖ := by positivity
            calc ‖(a + b) ^ i * a ^ (m - i)‖
                ≤ ‖(a + b) ^ i‖ * ‖a ^ (m - i)‖ := norm_mul_le _ _
              _ ≤ (‖a‖ + ‖b‖) ^ i * (‖a‖ + ‖b‖) ^ (m - i) := by
                  refine mul_le_mul ?_ ?_ (norm_nonneg _) (pow_nonneg hna _)
                  · calc ‖(a + b) ^ i‖ ≤ ‖a + b‖ ^ i := norm_pow_le _ i
                      _ ≤ (‖a‖ + ‖b‖) ^ i :=
                          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) i
                  · calc ‖a ^ (m - i)‖ ≤ ‖a‖ ^ (m - i) := norm_pow_le _ _
                      _ ≤ (‖a‖ + ‖b‖) ^ (m - i) :=
                          pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg b)) (m - i)
              _ = (‖a‖ + ‖b‖) ^ (i + (m - i)) := (pow_add _ _ _).symm
              _ = (‖a‖ + ‖b‖) ^ m := by rw [Nat.add_sub_cancel' hi']
        _ = (m + 1 : ℝ) * (‖a‖ + ‖b‖) ^ m := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_cast
    calc ‖(∑ i ∈ Finset.range (m + 1), (a + b) ^ i * a ^ (m - i)) * b‖
        ≤ ‖∑ i ∈ Finset.range (m + 1), (a + b) ^ i * a ^ (m - i)‖ * ‖b‖ :=
          norm_mul_le _ _
      _ ≤ ((m + 1 : ℝ) * (‖a‖ + ‖b‖) ^ m) * ‖b‖ :=
          mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
      _ = ((m + 1 : ℕ) : ℝ) * ‖b‖ * (‖a‖ + ‖b‖) ^ ((m + 1) - 1) := by
          rw [Nat.add_sub_cancel]
          push_cast
          ring

/-- **Lemma 3**, eq. (B125) of arXiv:2505.07929v2 (PDF p. 39): the `D`-th tensor power of
`u + v` approximates the `D`-th tensor power of `u` with error at most
`D ‖v‖ (‖u‖ + ‖v‖)^{D-1}`, measured in the projective tensor norm. -/
theorem lemma3_tensor_power_bound
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (u v : M) (D : ℕ) :
    ‖PiTensorProduct.tprod ℂ (fun _ : Fin D => u + v) - PiTensorProduct.tprod ℂ (fun _ : Fin D => u)‖
      ≤ (D : ℝ) * ‖v‖ * (‖u‖ + ‖v‖) ^ (D - 1) := by
  let f : MultilinearMap ℂ (fun _ : Fin D => M) (⨂[ℂ] (i : Fin D), M) := PiTensorProduct.tprod ℂ
  let g : ℕ → (⨂[ℂ] (i : Fin D), M) := fun k => f (fun i : Fin D => if i.val < k then u + v else u)
  have hg0 : g 0 = PiTensorProduct.tprod ℂ (fun _ : Fin D => u) := by
    simp [g, f]
  have hgD : g D = PiTensorProduct.tprod ℂ (fun _ : Fin D => u + v) := by
    simp [g, f]
  have hstep : ∀ k ∈ Finset.range D,
      g (k + 1) - g k
        = f (fun i : Fin D => if i.val < k then u + v else if i.val = k then v else u) := by
    intro k hk
    have hkD : k < D := Finset.mem_range.mp hk
    have hm1 : (fun i : Fin D => if i.val < k + 1 then u + v else u)
        = Function.update (fun i : Fin D => if i.val < k then u + v else u) ⟨k, hkD⟩ (u + v) := by
      funext i
      by_cases hi : i = ⟨k, hkD⟩
      · rw [hi]
        simp
      · have hne : i.val ≠ k := fun h => hi (Fin.ext h)
        simp [Function.update, hi]
        by_cases hlt : i.val < k
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega)]
    have hm0 : Function.update (fun i : Fin D => if i.val < k then u + v else u) ⟨k, hkD⟩ u
        = (fun i : Fin D => if i.val < k then u + v else u) := by
      funext i
      by_cases hi : i = ⟨k, hkD⟩
      · rw [hi]
        simp
      · simp [Function.update, hi]
    have hsub : (u + v) - u = v := by abel
    calc g (k + 1) - g k
        = f (fun i : Fin D => if i.val < k + 1 then u + v else u)
            - f (fun i : Fin D => if i.val < k then u + v else u) := rfl
      _ = f (Function.update (fun i : Fin D => if i.val < k then u + v else u) ⟨k, hkD⟩ (u + v))
            - f (Function.update (fun i : Fin D => if i.val < k then u + v else u) ⟨k, hkD⟩ u) := by
            rw [hm1, hm0]
      _ = f (Function.update (fun i : Fin D => if i.val < k then u + v else u) ⟨k, hkD⟩ v) := by
            rw [← MultilinearMap.map_update_sub, hsub]
      _ = f (fun i : Fin D => if i.val < k then u + v else if i.val = k then v else u) := by
            congr 1
            funext i
            by_cases hi : i = ⟨k, hkD⟩
            · rw [hi]
              simp [Function.update]
            · have hne : i.val ≠ k := fun h => hi (Fin.ext h)
              simp [Function.update, hi, hne]
  have htel : PiTensorProduct.tprod ℂ (fun _ : Fin D => u + v) - PiTensorProduct.tprod ℂ (fun _ : Fin D => u)
      = ∑ k ∈ Finset.range D, f (fun i : Fin D => if i.val < k then u + v else if i.val = k then v else u) := by
    rw [← hgD, ← hg0, ← Finset.sum_range_sub]
    exact Finset.sum_congr rfl fun k hk => hstep k hk
  rw [htel]
  have hterm_le : ∀ k ∈ Finset.range D,
      ‖f (fun i : Fin D => if i.val < k then u + v else if i.val = k then v else u)‖
        ≤ ‖v‖ * (‖u‖ + ‖v‖) ^ (D - 1) := by
    intro k hk
    have hkD : k < D := Finset.mem_range.mp hk
    set m : Fin D → M := fun i => if i.val < k then u + v else if i.val = k then v else u with hm
    have hnorm : ‖f m‖ ≤ ∏ i : Fin D, ‖m i‖ := by
      simpa only [f] using PiTensorProduct.projectiveSeminorm_tprod_le m
    have hprod : ∏ i : Fin D, ‖m i‖
        = ‖v‖ * ∏ i ∈ (Finset.univ.erase ⟨k, hkD⟩), ‖m i‖ := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => ‖m i‖) (Finset.mem_univ ⟨k, hkD⟩)]
      congr 1
      rw [hm]
      simp
    have hrest : ∏ i ∈ (Finset.univ.erase ⟨k, hkD⟩), ‖m i‖ ≤ (‖u‖ + ‖v‖) ^ (D - 1) := by
      have hle : ∀ i ∈ Finset.univ.erase ⟨k, hkD⟩, ‖m i‖ ≤ ‖u‖ + ‖v‖ := by
        intro i hi
        have hne : i ≠ ⟨k, hkD⟩ := Finset.ne_of_mem_erase hi
        have hnek : i.val ≠ k := fun h => hne (Fin.ext h)
        rw [hm]
        simp only [hnek, if_false]
        by_cases hlt : i.val < k
        · rw [if_pos hlt]
          exact norm_add_le u v
        · rw [if_neg hlt]
          exact le_add_of_nonneg_right (norm_nonneg v)
      calc ∏ i ∈ Finset.univ.erase ⟨k, hkD⟩, ‖m i‖
          ≤ ∏ _i ∈ Finset.univ.erase (⟨k, hkD⟩ : Fin D), (‖u‖ + ‖v‖) :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hle
        _ = (‖u‖ + ‖v‖) ^ (D - 1) := by
            rw [Finset.prod_const]
            congr 1
            rw [Finset.card_erase_of_mem (Finset.mem_univ (⟨k, hkD⟩ : Fin D)),
              Finset.card_univ, Fintype.card_fin]
    calc ‖f m‖ ≤ ∏ i : Fin D, ‖m i‖ := hnorm
      _ = ‖v‖ * ∏ i ∈ Finset.univ.erase ⟨k, hkD⟩, ‖m i‖ := hprod
      _ ≤ ‖v‖ * (‖u‖ + ‖v‖) ^ (D - 1) :=
          mul_le_mul_of_nonneg_left hrest (norm_nonneg v)
  calc ‖∑ k ∈ Finset.range D, f (fun i : Fin D => if i.val < k then u + v else if i.val = k then v else u)‖
      ≤ ∑ k ∈ Finset.range D, ‖f (fun i : Fin D => if i.val < k then u + v else if i.val = k then v else u)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range D, ‖v‖ * (‖u‖ + ‖v‖) ^ (D - 1) := Finset.sum_le_sum hterm_le
    _ = (D : ℝ) * ‖v‖ * (‖u‖ + ‖v‖) ^ (D - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring


end Qatlib.Papers.SpinBosonQAOA26.MainResults.TensorPowerApprox
