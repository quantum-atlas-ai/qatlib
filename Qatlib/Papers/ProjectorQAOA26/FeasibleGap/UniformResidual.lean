/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformSecular
import Qatlib.Papers.ProjectorQAOA26.StageStability.EC3FeasibleGap

/-!
# Regular secular terms and crossing roots

This module separates the zero-cost pole from `uniformCurve` using `regularSecond` and defines
`crossingResidual`. Continuity and moment bounds locate residual roots on either side of zero
for the secular analysis in [ZhouAnLiu2026].

## Main statements

* `uniformCurve_regular`: Away from the stated poles, the uniform secular curve splits into the
  zero-cost pole, `ec3A1`, and `z * regularSecond E zero z`. This is the regular decomposition
  used in [ZhouAnLiu2026].
* `crossingRoot_secular`: A nonzero root of the crossing residual away from the cost poles
  satisfies the secular equation with coupling `(ec3A1 zero E)⁻¹`.
* `moment_crossing_roots`: If `0 < b ≤ 1 / 2` and `b ^ 2 * ec3A2 zero E = 4 / L`, the crossing
  residual has roots in `[-b, 0)` and `(0, b]`.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical BigOperators
open Qatlib.Papers.ProjectorQAOA26.StageStability
open Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The cardinality-normalized sum of `1 / (E i * (E i - z))` over indices other than the
distinguished zero-cost index. -/
def regularSecond (E : I → ℝ) (zero : I) (z : ℝ) : ℝ :=
  (Fintype.card I:ℝ)⁻¹ * ∑ i ∈ Finset.univ.erase zero, (E i*(E i-z))⁻¹

/-- The crossing residual `z ^ 2 * regularSecond E zero z - 1 / L`, where `L` is the index
cardinality. -/
def crossingResidual (E : I → ℝ) (zero : I) (z : ℝ) : ℝ :=
  z^2*regularSecond E zero z-(Fintype.card I:ℝ)⁻¹

/-- If all other costs are at least one, `regularSecond` is continuous on `[-1 / 2, 1 / 2]`. -/
theorem regularSecond_continuous (E : I → ℝ) (zero : I)
    (hE : ∀ i,i≠zero → 1≤E i) : ContinuousOn (regularSecond E zero) (Set.Icc (-(1/2):ℝ) (1/2)) := by
  unfold regularSecond
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro i hi
  have hiE:=hE i (Finset.ne_of_mem_erase hi)
  apply ContinuousOn.inv₀ (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
  intro z hz
  exact mul_ne_zero (by linarith) (by dsimp; linarith [hz.2])

/-- If all other costs are at least one, the crossing residual is continuous on `[-1 / 2, 1 /
2]`. -/
theorem crossingResidual_continuous (E : I → ℝ) (zero : I)
    (hE : ∀ i,i≠zero → 1≤E i) :
    ContinuousOn (crossingResidual E zero) (Set.Icc (-(1/2):ℝ) (1/2)) :=
  (continuousOn_id.pow 2 |>.mul (regularSecond_continuous E zero hE)).sub continuousOn_const

/-- Away from the stated poles, the uniform secular curve splits into the zero-cost pole,
`ec3A1`, and `z * regularSecond E zero z`. This is the regular decomposition used in
[ZhouAnLiu2026]. -/
theorem uniformCurve_regular (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → E i≠0) (z : ℝ) (_hz : z≠0)
    (hpole : ∀ i,i≠zero → E i≠z) :
    uniformCurve E z= -(Fintype.card I:ℝ)⁻¹/z+ec3A1 zero E+z*regularSecond E zero z := by
  have he : ∑ i,(E i-z)⁻¹ = -z⁻¹+∑ i ∈ Finset.univ.erase zero, ((E i)⁻¹+z*(E i*(E i-z))⁻¹) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ zero),hzero]
    simp only [zero_sub,inv_neg]
    have hp : ∀ i ∈ Finset.univ.erase zero,(E i-z)⁻¹=(E i)⁻¹+z*(E i*(E i-z))⁻¹ := by
      intro i hi
      have hi0:=hE i (Finset.ne_of_mem_erase hi)
      have hiz:=sub_ne_zero.mpr (hpole i (Finset.ne_of_mem_erase hi))
      field_simp
      ring
    rw [Finset.sum_congr rfl hp]
    ring
  unfold uniformCurve ec3A1 regularSecond
  rw [he,Finset.sum_add_distrib,← Finset.mul_sum]
  simp only [one_div]
  ring

/-- A nonzero root of the crossing residual away from the cost poles satisfies the secular
equation with coupling `(ec3A1 zero E)⁻¹`. -/
theorem crossingRoot_secular (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → E i≠0) (z : ℝ) (hz : z≠0)
    (hpole : ∀ i,i≠zero → E i≠z) (hA : ec3A1 zero E≠0)
    (hroot : crossingResidual E zero z=0) : (ec3A1 zero E)⁻¹*uniformCurve E z=1 := by
  rw [uniformCurve_regular E zero hzero hE z hz hpole]
  have he : z^2*regularSecond E zero z=(Fintype.card I:ℝ)⁻¹ := sub_eq_zero.mp hroot
  have hzrel : z*regularSecond E zero z=(Fintype.card I:ℝ)⁻¹/z := by
    apply (eq_div_iff hz).mpr
    nlinarith [he]
  rw [hzrel]
  field_simp
  ring

/-- If the crossing residual is positive at both endpoints `-b` and `b`, with `0 < b ≤ 1 / 2`,
it has roots in `[-b, 0)` and `(0, b]`. -/
theorem crossing_roots (E : I → ℝ) (zero : I) (hE : ∀ i,i≠zero → 1≤E i)
    (b : ℝ) (hb : 0<b) (hbhalf : b≤1/2)
    (hneg : 0<crossingResidual E zero (-b)) (hpos : 0<crossingResidual E zero b) :
    ∃ lo hi : ℝ,lo∈Set.Ico (-b) 0 ∧ hi∈Set.Ioc 0 b ∧
      crossingResidual E zero lo=0 ∧ crossingResidual E zero hi=0 := by
  have hL : (0:ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨zero⟩
  have h0 : crossingResidual E zero 0<0 := by
    simpa only [crossingResidual,zero_pow (by norm_num : 2≠0),zero_mul,zero_sub] using!
      neg_neg_of_pos (inv_pos.mpr hL)
  have hc:=crossingResidual_continuous E zero hE
  have hcn : ContinuousOn (crossingResidual E zero) (Set.Icc (-b) 0) :=
    hc.mono (fun x hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩)
  have hcp : ContinuousOn (crossingResidual E zero) (Set.Icc 0 b) :=
    hc.mono (fun x hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩)
  obtain ⟨lo,hlo,heLo⟩:=intermediate_value_Icc' (show -b≤0 by linarith) hcn ⟨h0.le,hneg.le⟩
  obtain ⟨hi,hhi,heHi⟩:=intermediate_value_Icc hb.le hcp ⟨h0.le,hpos.le⟩
  refine ⟨lo,hi,⟨hlo.1,?_⟩,⟨?_,hhi.2⟩,heLo,heHi⟩
  · have hne : lo≠0 := by intro h;subst lo;linarith
    exact lt_of_le_of_ne hlo.2 hne
  · have hne : hi≠0 := by intro h;subst hi;linarith
    exact lt_of_le_of_ne hhi.1 (Ne.symm hne)

/-- On `|z| ≤ 1 / 2`, costs at least one away from the distinguished index imply `regularSecond
E zero z ≥ ec3A2 zero E / 2`. -/
theorem regularSecond_lower (E : I → ℝ) (zero : I)
    (hE : ∀ i,i≠zero → 1≤E i) (z : ℝ) (hz : |z|≤1/2) :
    ec3A2 zero E/2≤regularSecond E zero z := by
  unfold ec3A2 regularSecond
  rw [mul_div_assoc,Finset.sum_div]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro i hi
  have he:=hE i (Finset.ne_of_mem_erase hi)
  have hzl : -(1/2:ℝ)≤z := (abs_le.mp hz).1
  have hzu : z≤(1/2:ℝ) := (abs_le.mp hz).2
  have hEi : 0<E i := by linarith
  have hden : 0<E i*(E i-z) := mul_pos hEi (by linarith)
  have hsq : 0<(E i)^2 := sq_pos_of_pos hEi
  have hcomp : E i*(E i-z)≤2*(E i)^2 := by nlinarith
  have hh:=one_div_le_one_div_of_le hden hcomp
  convert! hh using 1 <;> field_simp

/-- If `0 < b ≤ 1 / 2` and `b ^ 2 * ec3A2 zero E = 4 / L`, the crossing residual has roots in
`[-b, 0)` and `(0, b]`. -/
theorem moment_crossing_roots (E : I → ℝ) (zero : I)
    (hE : ∀ i,i≠zero → 1≤E i) (b : ℝ) (hb : 0<b) (hbhalf : b≤1/2)
    (hscale : b^2*ec3A2 zero E=4/(Fintype.card I:ℝ)) :
    ∃ lo hi : ℝ,lo∈Set.Ico (-b) 0 ∧ hi∈Set.Ioc 0 b ∧
      crossingResidual E zero lo=0 ∧ crossingResidual E zero hi=0 := by
  have hL : (0:ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨zero⟩
  apply crossing_roots E zero hE b hb hbhalf
  · have hh:=regularSecond_lower E zero hE (-b) (by simpa [abs_of_pos hb] using! hbhalf)
    unfold crossingResidual
    have hm:=mul_le_mul_of_nonneg_left hh (sq_nonneg (-b))
    have hw : 0<(Fintype.card I:ℝ)⁻¹ := inv_pos.mpr hL
    simp only [neg_sq] at *
    rw [div_eq_mul_inv] at hscale
    nlinarith
  · have hh:=regularSecond_lower E zero hE b (by simpa [abs_of_pos hb] using! hbhalf)
    unfold crossingResidual
    have hm:=mul_le_mul_of_nonneg_left hh (sq_nonneg b)
    have hw : 0<(Fintype.card I:ℝ)⁻¹ := inv_pos.mpr hL
    rw [div_eq_mul_inv] at hscale
    nlinarith
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
