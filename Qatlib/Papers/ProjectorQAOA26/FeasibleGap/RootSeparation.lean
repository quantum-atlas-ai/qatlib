/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.CrossingSpectrum

/-!
# Separation of uniform secular roots

This module compares negative and positive arguments with the same value of the uniform secular
curve. The identity `two_root_identity` yields a finite lower bound on their separation for the
feasible-gap analysis in [ZhouAnLiu2026].

## Main statements

* `two_root_identity`: If the uniform secular curve has equal values at `-x` and `y`, with `x >
  0` and `0 < y < 1`, then `x * y` times the indicated sum over nonzero-cost indices equals one.
* `two_root_separation`: Under the stated cost bounds, equal secular-curve values at `-x` and
  `y`, with `0 < y ≤ 1 / 2`, imply `x + y ≥ 1 / (2 * sqrt L)`, where `L` is the index
  cardinality.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical BigOperators
open Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- If the uniform secular curve has equal values at `-x` and `y`, with `x > 0` and `0 < y < 1`,
then `x * y` times the indicated sum over nonzero-cost indices equals one. -/
theorem two_root_identity (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (x y : ℝ) (hx : 0<x) (hy : 0<y) (hy1 : y<1)
    (heq : uniformCurve E (-x)=uniformCurve E y) :
    1=x*y*∑ i ∈ Finset.univ.erase zero, ((E i-y)*(E i+x))⁻¹ := by
  have hL : (Fintype.card I:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have hsum : ∑ i,(E i+x)⁻¹=∑ i,(E i-y)⁻¹ := by
    apply mul_left_cancel₀ (inv_ne_zero hL)
    simpa [uniformCurve,one_div] using! heq
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ zero),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ zero),hzero] at hsum
  have hp : ∀ i ∈ Finset.univ.erase zero,
      (E i-y)⁻¹-(E i+x)⁻¹=(x+y)*((E i-y)*(E i+x))⁻¹ := by
    intro i hi
    have hiE:=hE i (Finset.ne_of_mem_erase hi)
    have h1 : E i-y≠0 := by linarith
    have h2 : E i+x≠0 := by linarith
    field_simp
    ring
  have hd : (x+y)*∑ i ∈ Finset.univ.erase zero,((E i-y)*(E i+x))⁻¹ = x⁻¹+y⁻¹ := by
    rw [Finset.mul_sum,← Finset.sum_congr rfl hp,Finset.sum_sub_distrib]
    simp only [zero_add,zero_sub,inv_neg] at hsum
    linarith
  have hxy : x+y≠0 := by linarith
  apply (mul_left_cancel₀ hxy)
  have hden := congrArg (fun z : ℝ => x*y*z) hd
  field_simp at hden
  simp only [one_div] at hden
  nlinarith [hden]

/-- Under the stated cost bounds, equal secular-curve values at `-x` and `y`, with `0 < y ≤ 1 /
2`, imply `x + y ≥ 1 / (2 * sqrt L)`, where `L` is the index cardinality. -/
theorem two_root_separation (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (x y : ℝ) (hx : 0<x) (hy : 0<y) (hyhalf : y≤1/2)
    (heq : uniformCurve E (-x)=uniformCurve E y) :
    1/(2*Real.sqrt (Fintype.card I:ℝ))≤x+y := by
  have hid:=two_root_identity E zero hzero hE x y hx hy (by linarith) heq
  have hsum : ∑ i ∈ Finset.univ.erase zero,((E i-y)*(E i+x))⁻¹≤2*(Fintype.card I:ℝ) := by
    calc _ ≤ ∑ _i ∈ Finset.univ.erase zero,(2:ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have he:=hE i (Finset.ne_of_mem_erase hi)
          have hd : 1/2≤(E i-y)*(E i+x) := by nlinarith
          have hh:=one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hd
          simpa using! hh
      _ ≤ 2*(Fintype.card I:ℝ) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        have hc : ((Finset.univ.erase zero).card:ℝ)≤Fintype.card I := by
          exact_mod_cast Finset.card_le_card (Finset.erase_subset zero Finset.univ)
        linarith
  have hxy : 0<x*y := mul_pos hx hy
  have hbound : 1≤2*(Fintype.card I:ℝ)*(x*y) := by
    have hh:=mul_le_mul_of_nonneg_left hsum hxy.le
    rw [← hid] at hh
    nlinarith
  have hL : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hs : 0<Real.sqrt (Fintype.card I:ℝ) := Real.sqrt_pos.mpr hL
  have hs2:=Real.sq_sqrt hL.le
  apply (div_le_iff₀ (by positivity : 0<2*Real.sqrt (Fintype.card I:ℝ))).mpr
  by_contra h
  have hh : (x+y)*Real.sqrt (Fintype.card I:ℝ)<1/2 := by linarith
  have hhn : 0≤(x+y)*Real.sqrt (Fintype.card I:ℝ) := by positivity
  have hhsq : ((x+y)*Real.sqrt (Fintype.card I:ℝ))^2<1/4 := by nlinarith
  have hprod:=mul_nonneg (sq_nonneg (x-y)) hL.le
  nlinarith
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
