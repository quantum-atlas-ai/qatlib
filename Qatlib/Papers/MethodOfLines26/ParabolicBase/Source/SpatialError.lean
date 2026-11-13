/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Spatial Discretization Error Bound for Parabolic Method of Lines

This module formalizes Theorem 6 of [Liang and Liu, 2026][LiangLiu2026], bounding the overall
spatial discretization error `meanL2Norm (u T - v T)` of the method-of-lines ODE system for
parabolic PDEs when the spatial operator `A` is symmetric positive semidefinite and the local
truncation error `τ` is uniformly bounded in the mean `ℓ₂` norm on `[0, T]`.

## Main statements

* `theorem6_spatial_error`: stability and accumulated truncation-error bound `meanL2Norm (u T - v T) ≤ εN`
  under `δ * T ≤ εN`.

## References

* [Liang and Liu, 2026][LiangLiu2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

open Matrix
open scoped BigOperators

/-- **Theorem 6** (arXiv:2606.03407v1, §3.4, PDF p.19).  If the semi-discrete
solution `v` and the sampled PDE solution `u` satisfy the method-of-lines
systems with truncation error `τ`, the truncation error is bounded by `δ` on
`[0,T]`, and the grid condition (32) yields `δ · T ≤ ε_N`, then the overall
spatial error satisfies `‖[u(x,T)]_x − v(T)‖⋆ ≤ ε_N`.

`A` is the symmetric positive semidefinite discretised operator (the
similarity-transformed difference matrix of Lemmas 19–21). -/
theorem theorem6_spatial_error
    (N : ℕ) (hN : 0 < N) (T εN δ : ℝ) (hT : 0 < T) (hε : 0 < εN) (hδ : 0 ≤ δ)
    (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : Aᵀ = A) (hApsd : ∀ v, 0 ≤ quadForm A v)
    (u v b τ : ℝ → Fin N → ℝ)
    (hode : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt v (-(A *ᵥ v t) + b t) t)
    (hsample : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt u (-(A *ᵥ u t) + b t + τ t) t)
    (hinit : v 0 = u 0)
    (htrunc : ∀ t ∈ Set.Icc (0 : ℝ) T, meanL2Norm (τ t) ≤ δ)
    (hscale : δ * T ≤ εN) :
    meanL2Norm (u T - v T) ≤ εN := by
  let e : ℝ → Fin N → ℝ := fun t => u t - v t
  have he0 : e 0 = 0 := by simp [e, ← hinit]
  have he (t : ℝ) (ht : t ∈ Set.Icc 0 T) (i : Fin N) :
      HasDerivAt (fun s => e s i) (-(A *ᵥ e t) i + τ t i) t := by
    convert ((hasDerivAt_pi.mp (hsample t ht) i).sub
      (hasDerivAt_pi.mp (hode t ht) i)) using 1
    simp [e, Matrix.mulVec_sub]
    ring
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hτ (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      Real.sqrt (∑ i, (τ t i) ^ 2) ≤ (N : ℝ) * δ := by
    simpa [meanL2Norm, ← mul_assoc, ne_of_gt hNr] using
      mul_le_mul_of_nonneg_left (htrunc t ht) hNr.le
  have hbound : Real.sqrt (∑ i, (e T i) ^ 2) ≤ (N : ℝ) * δ * T := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    let g : ℝ → ℝ := fun t => Real.sqrt ((∑ i, (e t i) ^ 2) + η ^ 2)
    let dg : ℝ → ℝ := fun t =>
      (∑ i, e t i * (-(A *ᵥ e t) i + τ t i)) / g t
    have hpos (t : ℝ) : 0 < (∑ i, (e t i) ^ 2) + η ^ 2 :=
      add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => sq_nonneg (e t i))
        (sq_pos_of_pos hη)
    have hgpos (t : ℝ) : 0 < g t := Real.sqrt_pos.mpr (hpos t)
    have hgder (t : ℝ) (ht : t ∈ Set.Icc 0 T) : HasDerivAt g (dg t) t := by
      have hsq : HasDerivAt (fun s => ∑ i, (e s i) ^ 2)
          (∑ i, 2 * e t i * (-(A *ᵥ e t) i + τ t i)) t := by
        simpa using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (he t ht i).pow 2)
      convert (hsq.add_const (η ^ 2)).sqrt (ne_of_gt (hpos t)) using 1
      dsimp [dg, g]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      field_simp
    have hg_le (t : ℝ) (ht : t ∈ Set.Icc 0 T) : dg t ≤ (N : ℝ) * δ := by
      have henergy : 0 ≤ ∑ i, e t i * (A *ᵥ e t) i := by
        change 0 ≤ quadForm A (e t)
        rw [← hA]
        simpa only [hA] using hApsd (e t)
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (e t) (τ t)
      have hsqrt : Real.sqrt (∑ i, (e t i) ^ 2) ≤ g t :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg η))
      have hnum : (∑ i, e t i * (-(A *ᵥ e t) i + τ t i)) ≤
          g t * ((N : ℝ) * δ) := by
        calc
          (∑ i, e t i * (-(A *ᵥ e t) i + τ t i)) =
              -(∑ i, e t i * (A *ᵥ e t) i) + ∑ i, e t i * τ t i := by
                simp [mul_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
          _ ≤ ∑ i, e t i * τ t i := by linarith
          _ ≤ Real.sqrt (∑ i, (e t i) ^ 2) * Real.sqrt (∑ i, (τ t i) ^ 2) := hcs
          _ ≤ g t * ((N : ℝ) * δ) :=
            mul_le_mul hsqrt (hτ t ht) (Real.sqrt_nonneg _) (hgpos t).le
      exact (div_le_iff₀ (hgpos t)).mpr (by simpa [mul_comm] using hnum)
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g dg hT
      (fun t ht => (hgder t ht).continuousAt.continuousWithinAt)
      (fun t ht => hgder t ⟨ht.1.le, ht.2.le⟩)
    have hdiff : g T - g 0 ≤ ((N : ℝ) * δ) * T := by
      apply (div_le_iff₀ hT).mp
      simpa only [hslope, sub_zero] using hg_le c ⟨hc.1.le, hc.2.le⟩
    have hg0 : g 0 = η := by simp [g, he0, Real.sqrt_sq hη.le]
    have hsqrt : Real.sqrt (∑ i, (e T i) ^ 2) ≤ g T :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg η))
    linarith
  have hmean : meanL2Norm (u T - v T) ≤ δ * T := by
    rw [meanL2Norm, one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ hNr).mpr
    simpa [e, mul_assoc, mul_comm, mul_left_comm] using hbound
  have hbudget : max (δ * T) 0 ≤ εN := max_le hscale hε.le
  rw [max_eq_left (mul_nonneg hδ hT.le)] at hbudget
  exact hmean.trans hbudget

end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
