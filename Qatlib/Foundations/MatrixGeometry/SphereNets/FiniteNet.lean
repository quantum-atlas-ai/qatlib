/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.SphereNets.Packing

/-!
# Finite nets on the unit sphere

Constructs an ε-covering subset of a finite set with pairwise distances strictly greater than ε.
In a finite-dimensional real normed space, `sphere_quantitative_net` gives a finite net on the
unit sphere with cardinality at most `(1 + 4 / ε)^dim` for `ε > 0`. See [GohMuller2026] for
related background.

## Main statements

* `finite_greedy_net`: For `ε > 0`, every finite set contains a subset whose distinct points
  have distance greater than `ε` and which covers the original set by closed balls of radius
  `ε`.
* `sphere_quantitative_net`: For `ε > 0`, the unit sphere of a finite-dimensional real normed
  space has a finite ε-net on the sphere of cardinality at most `((1 + ε / 4) / (ε / 4))^finrank
  ℝ E`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open Metric Set Module MeasureTheory
open scoped Classical NNReal
namespace Qatlib.Foundations.MatrixGeometry.SphereNets.FiniteNet
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in

/-- For `ε > 0`, every finite set contains a subset whose distinct points have distance greater
than `ε` and which covers the original set by closed balls of radius `ε`. -/
theorem finite_greedy_net (C : Finset E) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset E,s⊆C ∧
      (∀ x∈s,∀ y∈s,x≠y→ε<dist x y) ∧
      ∀ x∈C,∃ y∈s,dist x y≤ε := by
  let P (s : Finset E) := ∀ x∈s,∀ y∈s,x≠y→ε<dist x y
  let F := C.powerset.filter P
  have hF : F.Nonempty := ⟨∅,by simp [F,P]⟩
  obtain ⟨s,hs,hmax⟩ := F.exists_max_image Finset.card hF
  have hsC : s⊆C := (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1)
  have hsP : P s := (Finset.mem_filter.mp hs).2
  refine ⟨s,hsC,hsP,?_⟩
  intro x hxC
  by_contra! hbad
  have hxs : x∉s := by
    intro h
    have := hbad x h
    simp only [dist_self] at this
    linarith
  have hins : P (insert x s) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax|haS
    · subst a
      rcases Finset.mem_insert.mp hb with hbx|hbS
      · exact (hab hbx.symm).elim
      · exact hbad b hbS
    · rcases Finset.mem_insert.mp hb with hbx|hbS
      · subst b
        simpa only [dist_comm] using hbad a haS
      · exact hsP a haS b hbS hab
  have hiF : insert x s ∈ F := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hxC hsC),hins⟩
  have := hmax _ hiF
  rw [Finset.card_insert_of_notMem hxs] at this
  omega

/-- For `ε > 0`, the unit sphere of a finite-dimensional real normed space has a finite ε-net on
the sphere of cardinality at most `((1 + ε / 4) / (ε / 4))^finrank ℝ E`. -/
theorem sphere_quantitative_net (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset E,
      (∀ y∈s,‖y‖=1) ∧
      (∀ x : E,‖x‖=1→∃ y∈s,dist x y≤ε) ∧
      (s.card : ℝ) ≤ ((1+ε/4)/(ε/4))^finrank ℝ E := by
  let δ : ℝ≥0 := ⟨ε/2,by positivity⟩
  obtain ⟨C,hC,hfin,hcover⟩ := Metric.exists_finite_isCover_of_isCompact
    (show δ≠0 from ne_of_gt (show 0<δ from by exact_mod_cast (show 0<ε/2 by positivity))) (isCompact_sphere (0:E) 1)
  obtain ⟨s,hsC,hsep,hnet⟩ := finite_greedy_net hfin.toFinset (ε/2) (by positivity)
  have hunit : ∀ y∈s,‖y‖=1 := by
    intro y hy
    have := hC (hfin.mem_toFinset.mp (hsC hy))
    simpa only [mem_sphere,dist_zero_right] using this
  refine ⟨s,hunit,?_,?_⟩
  · intro x hx
    obtain ⟨z,hz,hxz⟩ := hcover (show x∈sphere (0:E) 1 by simpa using hx)
    obtain ⟨y,hy,hzy⟩ := hnet z (hfin.mem_toFinset.mpr hz)
    refine ⟨y,hy,le_trans (dist_triangle x z y) ?_⟩
    have hxz' : dist x z≤ε/2 := by
      exact_mod_cast hxz
    linarith
  · have hbound := Qatlib.Foundations.MatrixGeometry.SphereNets.Packing.separated_card_bound s (ε/2) (by positivity)
      (fun y hy => (hunit y hy).le)
      (fun x hx y hy hxy => by simpa only [dist_eq_norm] using (hsep x hx y hy hxy).le)
    have hε4 : ε/2/2=ε/4 := by ring
    simpa only [hε4] using hbound
end Qatlib.Foundations.MatrixGeometry.SphereNets.FiniteNet
