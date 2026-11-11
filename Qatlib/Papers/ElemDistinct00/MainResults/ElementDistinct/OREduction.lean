/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Boolean reduction to element distinctness

The map `edReduction` sends a true input bit to zero, a false bit at index `i` to `i + 1`, and
an additional final index to zero. Thus a true bit creates a collision with the final index,
while an all-false input gives an injective map.

The equivalences `hasCollision_edReduction_iff` and `elementDistinct_edReduction_iff` supply the
logical reduction used in the element distinctness discussion of [BuhrmanEtAl2005]. The
real-power identity `ed_upper_exponent` separately factors the exponent appearing in the stated
upper cost scale.

## Main statements

* `hasCollision_edReduction_iff`: the reduction has a collision exactly when some input bit is
  true.
* `elementDistinct_edReduction_iff`: the reduction is element distinct exactly when every input
  bit is false.
* `ed_upper_exponent`: for positive real `N`, `N^(3/4) = N^(1/2) * N^(1/4)`.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005], *Quantum Algorithms for Element Distinctness*,
  arXiv:quant-ph/0007016 (2000 preprint).
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.ElemDistinct00.MainResults.ElementDistinct

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

/-- Encode a Boolean input as a function on `N + 1` indices by sending true bits and the final
index to zero, and a false bit at index `i` to `i + 1`. -/
def edReduction {N : ℕ} (X : Fin N → Bool) (i : Fin (N + 1)) : ℕ :=
  if h : (i : ℕ) < N then ((i : ℕ) + 1) * (if X ⟨(i : ℕ), h⟩ then 0 else 1) else 0

/-- At an original input index, `edReduction` is zero for a true bit and `i + 1` for a false
bit. -/
theorem edReduction_castSucc {N : ℕ} (X : Fin N → Bool) (i : Fin N) :
    edReduction X (Fin.castSucc i) = (i.val + 1) * (if X i then 0 else 1) := by
  unfold edReduction
  simp only [Fin.val_castSucc]
  rw [dif_pos i.isLt]

/-- The additional final index of `edReduction` always maps to zero. -/
@[simp] theorem edReduction_last {N : ℕ} (X : Fin N → Bool) :
    edReduction X (Fin.last N) = 0 := by
  unfold edReduction
  rw [dif_neg (by simp)]

/-- At an original input index, the reduction takes value zero exactly when the corresponding
Boolean bit is true. -/
theorem edReduction_castSucc_eq_zero_iff {N : ℕ} (X : Fin N → Bool) (i : Fin N) :
    edReduction X (Fin.castSucc i) = 0 ↔ X i = true := by
  rw [edReduction_castSucc]
  cases h : X i <;> simp [h]

/-- If every input bit is false, the reduction is injective, since the original indices receive
distinct positive values and the final index receives zero. -/
theorem edReduction_injective_of_all_false {N : ℕ} {X : Fin N → Bool}
    (h : ∀ i, X i = false) : Function.Injective (edReduction X) := by
  intro a b hab
  unfold edReduction at hab
  by_cases ha : (a : ℕ) < N
  · by_cases hb : (b : ℕ) < N
    · rw [dif_pos ha, dif_pos hb] at hab
      simp [h] at hab
      apply Fin.ext
      omega
    · rw [dif_pos ha, dif_neg hb] at hab
      simp [h] at hab
  · by_cases hb : (b : ℕ) < N
    · rw [dif_neg ha, dif_pos hb] at hab
      simp [h] at hab
    · rw [dif_neg ha, dif_neg hb] at hab
      apply Fin.ext
      have haN : (a : ℕ) = N := by omega
      have hbN : (b : ℕ) = N := by omega
      omega

/-- The reduced function has a collision exactly when at least one Boolean input bit is true.
This is the logical OR reduction used for the element distinctness setting of
[BuhrmanEtAl2005]. -/
theorem hasCollision_edReduction_iff {N : ℕ} (X : Fin N → Bool) :
    HasCollision (edReduction X) ↔ ∃ i : Fin N, X i = true := by
  constructor
  · rintro ⟨a, b, hab_ne, hab_eq⟩
    by_contra h
    have hfalse : ∀ i, X i = false := by
      intro i
      by_contra hi
      exact h ⟨i, by cases hx : X i <;> simp_all⟩
    exact hab_ne (edReduction_injective_of_all_false hfalse hab_eq)
  · rintro ⟨i, hi⟩
    refine ⟨Fin.castSucc i, Fin.last N, ?_, ?_⟩
    · intro hEq
      have hval := congrArg Fin.val hEq
      simp only [Fin.val_castSucc, Fin.val_last] at hval
      omega
    · rw [edReduction_castSucc, edReduction_last, hi]
      simp

/-- The reduced function is element distinct exactly when all Boolean input bits are false. This
is the distinctness form of the OR reduction associated with [BuhrmanEtAl2005]. -/
theorem elementDistinct_edReduction_iff {N : ℕ} (X : Fin N → Bool) :
    ElementDistinct (edReduction X) ↔ ∀ i : Fin N, X i = false := by
  unfold ElementDistinct
  rw [hasCollision_edReduction_iff]
  constructor
  · intro h i
    by_contra hi
    exact h ⟨i, by cases hx : X i <;> simp_all⟩
  · rintro h ⟨i, hi⟩
    rw [h i] at hi
    exact Bool.noConfusion hi

/-- For positive real `N`, factor `N^(3/4)` as `N^(1/2) * N^(1/4)`. This is an algebraic
identity for the element distinctness cost scale in [BuhrmanEtAl2005]. -/
theorem ed_upper_exponent {N : ℝ} (hN : 0 < N) :
    N ^ (3 / 4 : ℝ) = N ^ (1 / 2 : ℝ) * N ^ (1 / 4 : ℝ) := by
  rw [← Real.rpow_add hN]
  norm_num

end Qatlib.Papers.ElemDistinct00.MainResults.ElementDistinct
