/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformResidual
import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.UniquePole

/-!
# Locating the lowest eigenvalues at the crossing

When the diagonal cost has one zero entry and all other entries are at least one, the module
excludes zero as an eigenvalue of a nonzero rank-one perturbation and classifies all eigenvalues
below one using two secular roots. At the inverse-first-moment parameter,
`crossing_actual_lowest_pair` locates the two lowest ordered eigenvalues in explicit intervals
around zero [ZhouAnLiu2026].

## Main statements

* `rankOne_classify_below_one`: Every eigenvalue below one equals one of the specified secular
  roots.
* `crossing_actual_lowest_pair`: The two lowest eigenvalues lie on opposite sides of zero within
  the moment-dependent bracket.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix
open Qatlib.Papers.ProjectorQAOA26.StageStability
open Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- If exactly one diagonal cost is zero and all others are at least one, zero is not an
eigenvalue of the rank-one operator with nonzero parameter. -/
theorem rankOne_zero_not_eigenvalue (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (a : ℝ) (ha : a≠0) :
    ¬hasRealEigenvalue (rankOneOperator E a) 0 := by
  apply unique_pole_not_eigenvalue E uniformReference a 0 zero hzero _ ha
  · intro h
    have hw:=uniformReference_weight zero
    rw [h,Complex.normSq_zero] at hw
    have hL : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
    exact (ne_of_gt (one_div_pos.mpr hL)) hw.symm
  · intro i hi
    linarith [hE i hi]

/-- Given a negative secular root `lo` and a secular root `hi` in `(0, 1)`, every eigenvalue
below one is either `lo` or `hi` under the stated cost hypotheses. -/
theorem rankOne_classify_below_one (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (a : ℝ) (ha : a≠0)
    (lo hi : ℝ) (hlo : lo<0) (hhi : hi∈Set.Ioo (0:ℝ) 1)
    (hloEq : a*uniformCurve E lo=1) (hhiEq : a*uniformCurve E hi=1) :
    ∀ z,hasRealEigenvalue (rankOneOperator E a) z → z<1 → z=lo ∨ z=hi := by
  have hnonneg : ∀ i,0≤E i := by
    intro i
    by_cases h : i=zero
    · subst i;rw [hzero]
    · linarith [hE i h]
  intro z hz hz1
  rcases lt_trichotomy z 0 with hz0|hz0|hz0
  · have hp:=negative_nonpole E hnonneg z hz0
    have he:=(actual_secular_iff_eigenvalue E a z hp).mpr hz
    have hcurve : uniformCurve E z=uniformCurve E lo := mul_left_cancel₀ ha (he.trans hloEq.symm)
    exact Or.inl ((uniformCurve_strictMono_negative E hnonneg).injOn hz0 hlo hcurve)
  · subst z
    exact False.elim (rankOne_zero_not_eigenvalue E zero hzero hE a ha hz)
  · have hp:=small_positive_nonpole E zero hzero hE z ⟨hz0,hz1⟩
    have he:=(actual_secular_iff_eigenvalue E a z hp).mpr hz
    have hcurve : uniformCurve E z=uniformCurve E hi := mul_left_cancel₀ ha (he.trans hhiEq.symm)
    exact Or.inr ((uniformCurve_strictMono_positive E zero hzero 1 (by norm_num) hE).injOn
      ⟨hz0,hz1⟩ hhi hcurve)

/-- At rank-one parameter `1 / ec3A1`, the two lowest ordered eigenvalues lie in `[-b, 0)` and
`(0, b]` when `0 < b ≤ 1 / 2` and `b² * ec3A2 = 4 / card I` [ZhouAnLiu2026]. -/
theorem crossing_actual_lowest_pair (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (hL : 2≤Fintype.card I)
    (hA : ec3A1 zero E≠0) (b : ℝ) (hb : 0<b) (hbhalf : b≤1/2)
    (hscale : b^2*ec3A2 zero E=4/(Fintype.card I:ℝ)) :
    ∃ lo hi : ℝ,lo∈Set.Ico (-b) 0 ∧ hi∈Set.Ioc 0 b ∧
      (rankOneOperator_hermitian E (ec3A1 zero E)⁻¹).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩=lo ∧
      (rankOneOperator_hermitian E (ec3A1 zero E)⁻¹).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩=hi := by
  obtain ⟨lo,hi,hlo,hhi,heLo,heHi⟩:=moment_crossing_roots E zero hE b hb hbhalf hscale
  have hn : ∀ i,0≤E i := by
    intro i
    by_cases h : i=zero
    · subst i;rw [hzero]
    · linarith [hE i h]
  have hnz : ∀ i,i≠zero → E i≠0 := fun i hi => ne_of_gt (by linarith [hE i hi])
  have hpLo:=negative_nonpole E hn lo hlo.2
  have hhi' : hi∈Set.Ioo (0:ℝ) 1 := ⟨hhi.1,by linarith [hhi.2]⟩
  have hpHi:=small_positive_nonpole E zero hzero hE hi hhi'
  have hsLo:=crossingRoot_secular E zero hzero hnz lo (ne_of_lt hlo.2)
    (fun i _ =>hpLo i) hA heLo
  have hsHi:=crossingRoot_secular E zero hzero hnz hi (ne_of_gt hhi.1)
    (fun i _ =>hpHi i) hA heHi
  have heigLo:=(actual_secular_iff_eigenvalue E _ lo hpLo).mp hsLo
  have heigHi:=(actual_secular_iff_eigenvalue E _ hi hpHi).mp hsHi
  have hpair:=lowest_pair_of_eigenpairs (rankOneOperator_hermitian E (ec3A1 zero E)⁻¹)
    hL lo hi 1 (by linarith [hlo.2,hhi.1]) hhi'.2 heigLo heigHi
    (rankOne_classify_below_one E zero hzero hE _ (inv_ne_zero hA) lo hi hlo.2 hhi' hsLo hsHi)
    (resolventVector E uniformReference lo) (actual_nonpole_line E _ lo hpLo)
  exact ⟨lo,hi,hlo,hhi,hpair.1,hpair.2⟩
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
