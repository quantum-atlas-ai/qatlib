/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite character sums and orthonormal response states

`vecChar` is the standard character of a dot product over vectors in `ZMod A`. Character
orthogonality and the normalization factor `normC` show that the amplitude functions `stateAmp`
form an orthonormal family for the finite inner product defined here. See [TerhalSmolin1998] for
the source development.

## Main statements

* `sum_vecChar`: evaluates the full character sum, vanishing away from the zero label.
* `proj_family_diagonal`: evaluates the rank-one maps associated with an orthonormal family.
* `inner_stateAmp`: proves the normalized response states have Kronecker-delta inner products.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

namespace Qatlib.Papers.SingleQuery97.MainResults.CharacterSum

open Finset

/-- An additive character maps a finite sum to the product of its values on the summands. -/
theorem map_finsetSum_eq_prod {ι A M : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The complex standard additive character evaluated on the dot product of two vectors over
`ZMod A`. -/
noncomputable def vecChar {A m : ℕ} [NeZero A] (z s : Fin m → ZMod A) : ℂ :=
  ZMod.stdAddChar (∑ i, s i * z i)

/-- The vector character with zero label is identically one. -/
theorem vecChar_zero_left {A m : ℕ} [NeZero A] (s : Fin m → ZMod A) :
    vecChar (0 : Fin m → ZMod A) s = 1 := by
  simp [vecChar]

/-- For a fixed label, the vector character maps addition of arguments to multiplication of
values. -/
theorem vecChar_add' {A m : ℕ} [NeZero A] (z s t : Fin m → ZMod A) :
    vecChar z (s + t) = vecChar z s * vecChar z t := by
  unfold vecChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Pi.add_apply, add_mul]

/-- Multiplying the character labeled by `z` by the character labeled by `-z'` gives the
character labeled by `z - z'`. -/
theorem vecChar_sub_mul {A m : ℕ} [NeZero A] (z z' s : Fin m → ZMod A) :
    vecChar z s * vecChar (-z') s = vecChar (z - z') s := by
  unfold vecChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Pi.sub_apply, Pi.neg_apply, mul_sub]
  ring

/-- The standard complex additive character of `ZMod A` has norm one at every argument. -/
theorem norm_stdAddChar {A : ℕ} [NeZero A] (t : ZMod A) :
    ‖ZMod.stdAddChar t‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Complex conjugation of the standard additive character is evaluation at the negated
argument. -/
theorem star_stdAddChar {A : ℕ} [NeZero A] (t : ZMod A) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  have h := AddChar.map_neg_eq_inv (ZMod.stdAddChar (N := A)) t
  rw [Complex.star_def, ← Complex.inv_eq_conj (norm_stdAddChar t), h]

/-- Complex conjugation of a vector character negates its label. -/
theorem star_vecChar {A m : ℕ} [NeZero A] (z s : Fin m → ZMod A) :
    star (vecChar z s) = vecChar (-z) s := by
  unfold vecChar
  rw [star_stdAddChar]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Pi.neg_apply]
  ring

/-- The sum of a vector character over all arguments is `A ^ m` for the zero label and zero
otherwise. -/
theorem sum_vecChar {A m : ℕ} [NeZero A] (z : Fin m → ZMod A) :
    (∑ s : Fin m → ZMod A, vecChar z s) = if z = 0 then ((A : ℂ) ^ m) else 0 := by
  classical
  have hprod : ∀ s : Fin m → ZMod A,
      vecChar z s = ∏ i, ZMod.stdAddChar (s i * z i) := by
    intro s
    unfold vecChar
    exact map_finsetSum_eq_prod _ _ _
  simp_rw [hprod]
  rw [← Fintype.prod_sum (κ := fun _ => ZMod A)
    (f := fun i (a : ZMod A) => ZMod.stdAddChar (a * z i))]
  have hfac : ∀ i : Fin m, (∑ a : ZMod A, ZMod.stdAddChar (a * z i))
      = if z i = 0 then (A : ℂ) else 0 := by
    intro i
    rw [AddChar.sum_mulShift (z i) (ZMod.isPrimitive_stdAddChar A)]
    simp [ZMod.card]
  simp_rw [hfac]
  by_cases hz : z = 0
  · subst hz
    simp [Finset.prod_const]
  · have hex : ∃ i, z i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hz (funext h)
    obtain ⟨i, hi⟩ := hex
    rw [if_neg hz]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [hi]

/-- The complex reciprocal of the square root of the natural number `q`, used to normalize
finite amplitude vectors. -/
noncomputable def normC (q : ℕ) : ℂ := ((Real.sqrt (q : ℝ) : ℝ) : ℂ)⁻¹

/-- For positive `q`, the square of `normC q` is the complex reciprocal of `q`. -/
theorem normC_mul_self {q : ℕ} (hq : 0 < q) : normC q * normC q = ((q : ℂ))⁻¹ := by
  unfold normC
  rw [← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp

/-- The normalization factor `normC q` is nonzero when `q > 0`. -/
theorem normC_ne_zero {q : ℕ} (hq : 0 < q) : normC q ≠ 0 := by
  intro h
  have hm := normC_mul_self hq
  rw [h, zero_mul] at hm
  exact (inv_ne_zero (by exact_mod_cast (ne_of_gt hq))) hm.symm

/-- The finite complex inner product obtained by summing `star (u x) * v x` over all
coordinates. -/
noncomputable def inner {ι : Type*} [Fintype ι] (u v : ι → ℂ) : ℂ := ∑ x, star (u x) * v x

/-- The rank-one map sending `v` to `inner φ v` times `φ`. -/
noncomputable def proj {ι : Type*} [Fintype ι] (φ v : ι → ℂ) : ι → ℂ :=
  fun x => inner φ v * φ x

/-- For an orthonormal family, the rank-one map associated with one member fixes that member and
sends every differently indexed member to zero. -/
theorem proj_family_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (state : ι → ι → ℂ)
    (horth : ∀ i j, inner (state i) (state j) = if i = j then (1 : ℂ) else 0) :
    ∀ i j, proj (state i) (state j) = if i = j then state j else 0 := by
  intro i j
  unfold proj
  rw [horth i j]
  by_cases h : i = j
  · simp [h]
  · simp only [if_neg h]
    funext x
    simp

/-- The vector character multiplied by the normalization factor `normC (A ^ m)`. -/
noncomputable def stateAmp {A m : ℕ} [NeZero A] (z s : Fin m → ZMod A) : ℂ :=
  normC (A ^ m) * vecChar z s

/-- For positive `A`, each normalized character amplitude vector is nonzero. -/
theorem stateAmp_ne_zero {A m : ℕ} [NeZero A] (hA : 0 < A)
    (z : Fin m → ZMod A) : stateAmp z ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin m → ZMod A)
  have hz : vecChar z (0 : Fin m → ZMod A) = 1 := by simp [vecChar]
  simp only [stateAmp, hz, mul_one] at h0
  exact normC_ne_zero (pow_pos hA m) h0

set_option maxHeartbeats 1000000 in

/-- For positive `A`, the inner product of two normalized character states is one when their
labels coincide and zero otherwise. -/
theorem inner_stateAmp {A m : ℕ} [NeZero A] (hA : 0 < A) (z z' : Fin m → ZMod A) :
    inner (stateAmp z) (stateAmp z') = if z = z' then 1 else 0 := by
  classical
  unfold inner
  simp only [stateAmp]
  have hnc : star (normC (A ^ m)) = normC (A ^ m) := by
    unfold normC
    simp
  have hstar : ∀ s, star (normC (A ^ m) * vecChar z s) =
      normC (A ^ m) * vecChar (-z) s := by
    intro s
    rw [star_mul, star_vecChar, hnc]
    ring
  simp_rw [hstar]
  have hsub : ∀ s, vecChar (-z) s * vecChar z' s = vecChar (z' - z) s := by
    intro s
    have h := vecChar_sub_mul (z := -z) (z' := -z') s
    have hz' : (-(-z') : Fin m → ZMod A) = z' := by
      funext i
      simp
    have harg : (-z - -z' : Fin m → ZMod A) = z' - z := by
      funext i
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rwa [hz', harg] at h
  have hterm : ∀ s,
      (normC (A ^ m) * vecChar (-z) s) * (normC (A ^ m) * vecChar z' s)
        = (normC (A ^ m) * normC (A ^ m)) * vecChar (z' - z) s := by
    intro s
    calc
      (normC (A ^ m) * vecChar (-z) s) * (normC (A ^ m) * vecChar z' s)
          = (normC (A ^ m) * normC (A ^ m)) *
              (vecChar (-z) s * vecChar z' s) := by ring
      _ = (normC (A ^ m) * normC (A ^ m)) * vecChar (z' - z) s := by rw [hsub s]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [sum_vecChar, normC_mul_self (pow_pos hA m)]
  by_cases h : z' - z = 0
  · have hzz : z' = z := sub_eq_zero.mp h
    rw [if_pos h, if_pos hzz.symm]
    have hA0 : ((A : ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt hA)
    rw [Nat.cast_pow]
    exact inv_mul_cancel₀ (pow_ne_zero m hA0)
  · rw [if_neg h]
    have hzz : z' ≠ z := fun he => h (by rw [he, sub_self])
    rw [if_neg (fun he => hzz he.symm), mul_zero]

end Qatlib.Papers.SingleQuery97.MainResults.CharacterSum
