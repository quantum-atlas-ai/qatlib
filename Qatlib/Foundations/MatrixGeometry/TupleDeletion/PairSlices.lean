/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.FullCarrier
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.PairResampling

/-!
# Two-coordinate slices and invalid repairs

Defines `pairSlice` by varying two coordinates of a tuple and evaluating zero-extended
injective-tuple amplitudes. Row and column resampling become coordinate replacement sums; if the
resulting tuple is noninjective, `pairSlice_invalid_output` proves that at least one resampling
output vanishes. See [MagniezZur2026] for related background.

## Main statements

* `pairSlice_entry`: For distinct coordinates, the zero-extended entry of a pair slice equals
  the zero-extended tuple amplitude after the two specified updates, including when the
  replacement labels coincide.
* `pairSlice_invalid_output`: For distinct coordinates, if the tuple produced by a distinct
  label pair is noninjective, at least one of the column- and row-resampling outputs at that
  pair is zero.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]
omit [Fintype I] [Fintype L] in

/-- For distinct coordinates with different values, if updating either coordinate separately can
make a tuple injective, then the original tuple is injective. -/
theorem injective_of_two_repairs (f : I → L) (i j : I) (hij : i ≠ j) (hne : f i ≠ f j)
    (a b : L) (ha : Function.Injective (Function.update f i a))
    (hb : Function.Injective (Function.update f j b)) : Function.Injective f := by
  intro r s hrs
  by_cases hri : r=i
  · subst r
    by_cases hsj : s=j
    · subst s
      exact False.elim (hne hrs)
    · apply hb
      simpa only [Function.update_of_ne hij,Function.update_of_ne hsj] using hrs
  · by_cases hsi : s=i
    · subst s
      by_cases hrj : r=j
      · subst r
        exact False.elim (hne hrs.symm)
      · apply hb
        simpa only [Function.update_of_ne hrj,Function.update_of_ne hij] using hrs
    · apply ha
      simpa only [Function.update_of_ne hri,Function.update_of_ne hsi] using hrs
omit [Fintype I] [Fintype L] in

/-- For a noninjective tuple with distinct values at two distinct coordinates, either no update
of the first coordinate is injective or no update of the second coordinate is injective. -/
theorem invalid_repairs (f : I → L) (i j : I) (hij : i ≠ j) (hne : f i ≠ f j)
    (hf : ¬ Function.Injective f) :
    (∀ a,¬ Function.Injective (Function.update f i a)) ∨
      (∀ b,¬ Function.Injective (Function.update f j b)) := by
  by_cases h : ∃ a,Function.Injective (Function.update f i a)
  · obtain ⟨a,ha⟩ := h
    exact Or.inr (fun b hb => hf (injective_of_two_repairs f i j hij hne a b ha hb))
  · exact Or.inl (by simpa using h)

/-- The amplitude function on distinct label pairs obtained by updating two coordinates of `f`
and evaluating the zero extension of `v`. -/
def pairSlice (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) : EuclideanSpace ℂ (Pair L) :=
  WithLp.toLp 2 (fun p => extend v (Function.update (Function.update f i p.val.1) j p.val.2))
omit [Fintype L] in

/-- For distinct coordinates, the zero-extended entry of a pair slice equals the zero-extended
tuple amplitude after the two specified updates, including when the replacement labels
coincide. -/
theorem pairSlice_entry (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j) (x y : L) :
    entry (pairSlice v f i j) x y=extend v (Function.update (Function.update f i x) j y) := by
  by_cases hxy : x ≠ y
  · change (if h : x ≠ y then extend v (Function.update (Function.update f i x) j y) else 0)=_
    rw [dif_pos hxy]
  · have he : x=y := not_ne_iff.mp hxy
    have hn : ¬ Function.Injective (Function.update (Function.update f i x) j y) := by
      intro h
      apply hij
      apply h
      simp [Function.update_of_ne hij,he]
    simp [entry,hxy,extend,hn]

/-- For distinct coordinates, column resampling of a pair slice is the sum over all replacement
labels at the first coordinate with the second replacement fixed. -/
theorem pairSlice_R (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j) (p : Pair L) :
    R (pairSlice v f i j) p=∑ x : L,extend v (Function.update (Function.update f i x) j p.val.2) := by
  change (∑ x : L,entry (pairSlice v f i j) x p.val.2)=_
  simp_rw [pairSlice_entry v f i j hij]

/-- For distinct coordinates, row resampling of a pair slice is the sum over all replacement
labels at the second coordinate with the first replacement fixed. -/
theorem pairSlice_S (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j) (p : Pair L) :
    S (pairSlice v f i j) p=∑ y : L,extend v (Function.update (Function.update f i p.val.1) j y) := by
  change (∑ y : L,entry (pairSlice v f i j) p.val.1 y)=_
  simp_rw [pairSlice_entry v f i j hij]

/-- For distinct coordinates, if the tuple produced by a distinct label pair is noninjective, at
least one of the column- and row-resampling outputs at that pair is zero. -/
theorem pairSlice_invalid_output (v : InjectiveTuple I L → ℂ) (f : I → L) (i j : I) (hij : i ≠ j)
    (p : Pair L) (hf : ¬ Function.Injective (Function.update (Function.update f i p.val.1) j p.val.2)) :
    R (pairSlice v f i j) p=0 ∨ S (pairSlice v f i j) p=0 := by
  let g := Function.update (Function.update f i p.val.1) j p.val.2
  have hne : g i ≠ g j := by
    simpa [g,Function.update_of_ne hij] using p.property
  rcases invalid_repairs g i j hij hne hf with hi | hj
  · left
    rw [pairSlice_R v f i j hij]
    apply Finset.sum_eq_zero
    intro x hx
    have hux : Function.update g i x=Function.update (Function.update f i x) j p.val.2 := by
      dsimp [g]
      rw [Function.update_comm hij.symm,Function.update_idem]
    have hn := hi x
    rw [hux] at hn
    simp [extend,hn]
  · right
    rw [pairSlice_S v f i j hij]
    apply Finset.sum_eq_zero
    intro y hy
    have hn := hj y
    dsimp [g] at hn
    rw [Function.update_idem] at hn
    simp [extend,hn]
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
