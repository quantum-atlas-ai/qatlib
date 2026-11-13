/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Convert

set_option backward.isDefEq.respectTransparency false

/-!
# Coons Boundary Lifting for Parabolic PDEs

This module formalizes the operator source-transfer identity and the inclusion-exclusion
face-trace cancellation underlying Theorem 4 (Coons boundary lifting for parabolic PDEs
with mixed boundary conditions).

## Main statements

* `coons_source_transfer`: first-order time-evolution source transfer for `u + S`.
* `alternating_coons_cancellation`: alternating powerset cancellation yielding `-τ {l}`.
* `theorem4_boundary_lifting`: combined operator and homogeneous-boundary lifting statement.

## References

* [Liang and Liu, 2026][LiangLiu2026], Theorem 4, Section 3.1 and Appendix A, pp. 13-14, 59-60.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

open scoped Real

/-- **Theorem 4 (operator/source half)**: if `u` solves `∂_t u = L u + f` for a continuous
linear operator `L` and `S` has time derivative `dS`, then `u + S` solves
`∂_t (u + S) = L (u + S) + (f + dS - L S)`. -/
theorem coons_source_transfer
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] V) (u S : ℝ → V) (f dS : ℝ → V)
    (hu : ∀ t, HasDerivAt u (L (u t) + f t) t)
    (hS : ∀ t, HasDerivAt S (dS t) t) :
    ∀ t, HasDerivAt (fun t => u t + S t)
      (L (u t + S t) + (f t + dS t - L (S t))) t := by
  intro t
  have h := (hu t).add (hS t)
  convert h using 1
  rw [ContinuousLinearMap.map_add]
  abel

/-- **Theorem 4 (combinatorial boundary half)**: for `l ∈ S`, if `τ (insert l A) = τ A`
whenever `A ⊆ S` and `l ∉ A`, then the alternating sum of `(-1)^{|A|} • τ A` over all
nonempty subsets `A ⊆ S` equals `-τ {l}`. -/
theorem alternating_coons_cancellation
    {ι V : Type*} [AddCommGroup V] [DecidableEq ι]
    (S : Finset ι) (l : ι) (hl : l ∈ S) (τ : Finset ι → V)
    (hpair : ∀ A, A ⊆ S → l ∉ A → τ (insert l A) = τ A) :
    (∑ A ∈ S.powerset.filter (fun A => A.Nonempty), ((-1 : ℤ) ^ A.card) • τ A)
      = - τ {l} := by
  let P := S.powerset.filter (fun A => A.Nonempty)
  let Q := P.erase {l}
  let f := fun A : Finset ι => ((-1 : ℤ) ^ A.card) • τ A
  have h_singleton_mem : {l} ∈ P :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hl),
        Finset.singleton_nonempty l⟩
  have mem_out (B : Finset ι) :
      B ∈ Q.filter (fun A => l ∉ A) ↔ B ⊆ S ∧ B.Nonempty ∧ l ∉ B := by
    simp only [Q, P, Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨_, hsub, hne⟩, hnot⟩
      exact ⟨hsub, hne, hnot⟩
    · rintro ⟨hsub, hne, hnot⟩
      refine ⟨⟨?_, hsub, hne⟩, hnot⟩
      rintro rfl
      exact hnot (Finset.mem_singleton_self l)
  have mem_in (A : Finset ι) :
      A ∈ Q.filter (fun A => l ∈ A) ↔ A ⊆ S ∧ l ∈ A ∧ (A.erase l).Nonempty := by
    simp only [Q, P, Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hne, hsub, _⟩, hlA⟩
      refine ⟨hsub, hlA, ?_⟩
      by_contra h
      have he : A.erase l = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      apply hne
      simpa [he] using (Finset.insert_erase hlA).symm
    · rintro ⟨hsub, hlA, hne⟩
      refine ⟨⟨?_, hsub, ⟨l, hlA⟩⟩, hlA⟩
      rintro rfl
      simp at hne
  have hsum :
      (∑ B ∈ Q.filter (fun A => l ∉ A), - f B) =
        ∑ A ∈ Q.filter (fun A => l ∈ A), f A := by
    refine Finset.sum_bij' (fun B _ => insert l B) (fun A _ => A.erase l)
      ?_ ?_ ?_ ?_ ?_
    · intro B hB
      obtain ⟨hsub, hne, hnot⟩ := (mem_out B).mp hB
      apply (mem_in _).mpr
      exact ⟨Finset.insert_subset_iff.mpr ⟨hl, hsub⟩, Finset.mem_insert_self _ _,
        by simpa [Finset.erase_insert hnot] using hne⟩
    · intro A hA
      obtain ⟨hsub, _, hne⟩ := (mem_in A).mp hA
      exact (mem_out _).mpr
        ⟨(Finset.erase_subset _ _).trans hsub, hne, Finset.notMem_erase _ _⟩
    · intro B hB
      exact Finset.erase_insert ((mem_out B).mp hB).2.2
    · intro A hA
      exact Finset.insert_erase ((mem_in A).mp hA).2.1
    · intro B hB
      obtain ⟨hsub, _, hnot⟩ := (mem_out B).mp hB
      dsimp [f]
      rw [Finset.card_insert_of_notMem hnot, hpair B hsub hnot, pow_succ]
      simp
  have hcancel : (∑ A ∈ Q, f A) = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun A => l ∈ A) f,
      ← hsum, Finset.sum_neg_distrib, neg_add_cancel]
  change (∑ A ∈ P, f A) = - τ {l}
  rw [← Finset.add_sum_erase P f h_singleton_mem]
  change f {l} + (∑ A ∈ Q, f A) = - τ {l}
  simp [hcancel, f]

/-- **Theorem 4 (boundary lifting via Coons interpolation)**: combines the first-order
operator source transfer with the face-trace alternating cancellation. -/
theorem theorem4_boundary_lifting
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] V) (u S : ℝ → V) (f dS : ℝ → V)
    (hu : ∀ t, HasDerivAt u (L (u t) + f t) t)
    (hS : ∀ t, HasDerivAt S (dS t) t) :
    (∀ t, HasDerivAt (fun t => u t + S t)
      (L (u t + S t) + (f t + dS t - L (S t))) t) ∧
    (∀ {ι : Type*} [DecidableEq ι] (Sset : Finset ι) (l : ι), l ∈ Sset →
      ∀ (τ : Finset ι → V), (∀ A, A ⊆ Sset → l ∉ A → τ (insert l A) = τ A) →
      (∑ A ∈ Sset.powerset.filter (fun A => A.Nonempty),
        ((-1 : ℤ) ^ A.card) • τ A) = - τ {l}) := by
  refine ⟨coons_source_transfer L u S f dS hu hS, ?_⟩
  intro ι _ Sset l hl τ hpair
  exact alternating_coons_cancellation Sset l hl τ hpair

end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
