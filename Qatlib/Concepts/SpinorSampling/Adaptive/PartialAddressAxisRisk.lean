/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressPlan

set_option backward.isDefEq.respectTransparency false

/-!
Analysis of the literal normalized estimated Bloch axis, including the zero
estimate convention. A unit compiled axis with a proved overlap bound obeys
the stated minority-risk bound. No real-valued axis is supplied as a free
physical gate; connection to the actual finite-word compiler remains separate.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.AxisRisk
open scoped BigOperators

/-- Construction for dot in the partial address axis risk model. -/
def dot (r a : Fin 3 → ℝ) : ℝ := ∑ i,r i*a i
/-- Construction for dist Sq in the partial address axis risk model. -/
def distSq (r s : Fin 3 → ℝ) : ℝ := ∑ i,(r i-s i)^2

/-- Complete original `dist_sq_nonneg` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem dist_sq_nonneg (r s : Fin 3 → ℝ) : 0 ≤ distSq r s := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (r i-s i)

/-- Complete original `dist_sq_triangle` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem dist_sq_triangle (r s a : Fin 3 → ℝ) :
    distSq r a ≤ 2*distSq r s+2*distSq s a := by
  calc
    _ ≤ ∑ i : Fin 3,(2*(r i-s i)^2+2*(s i-a i)^2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_nonneg (r i-2*s i+a i)]
    _ = _ := by simp only [distSq,Finset.sum_add_distrib,Finset.mul_sum]

/-- Complete original `robust_axis_risk` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem robust_axis_risk (R : ℝ) (r s a v : Fin 3 → ℝ)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hr : ∀ i,r i=R*v i) (ha : dot a a=1) (hv : dot v v=1)
    (hnearest : distSq a s ≤ distSq v s) :
    (1-dot r a)/2 ≤ 2*(1-R)+2*distSq s r := by
  have hd := dist_sq_triangle a s r
  have he := dist_sq_triangle v r s
  have hsym : distSq r s=distSq s r := by
    unfold distSq
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrad : distSq v r=(1-R)^2 := by
    simp only [distSq,hr]
    calc
      _ = (1-R)^2*(∑ i : Fin 3,v i*v i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by change (1-R)^2*dot v v=_; rw [hv]; ring
  have hid : distSq a r=1+R^2-2*dot r a := by
    have hh : distSq a r=dot a a+R^2*dot v v-2*dot r a := by
      simp only [distSq,dot,hr,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hh,ha,hv]
    ring
  rw [hsym] at he
  rw [hrad] at he
  rw [hid] at hd
  have hpos := dist_sq_nonneg s r
  nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hR1)]

/-- Complete original `unit_dot_le_one` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem unit_dot_le_one (a v : Fin 3 → ℝ) (ha : dot a a=1) (hv : dot v v=1) :
    dot a v ≤ 1 := by
  have h := dist_sq_nonneg a v
  have he : distSq a v=dot a a+dot v v-2*dot a v := by
    simp only [distSq,dot,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,ha,hv] at h
  linarith

/-- Complete original `nearest_scaled_axis` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem nearest_scaled_axis (s a v : Fin 3 → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ i,s i=L*a i) (ha : dot a a=1) (hv : dot v v=1) :
    distSq a s ≤ distSq v s := by
  have hd : distSq v s-distSq a s=2*L*(1-dot a v) := by
    calc
      _ = ∑ i : Fin 3,((v i-s i)^2-(a i-s i)^2) := by
        simp only [distSq,Finset.sum_sub_distrib]
      _ = dot v v-dot a a+2*L*(dot a a-dot a v) := by
        simp only [dot,hs,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [ha,hv]; ring
  have hp := mul_nonneg (by positivity : 0 ≤ 2*L)
    (sub_nonneg.mpr (unit_dot_le_one a v ha hv))
  linarith

/-- Construction for length in the partial address axis risk model. -/
noncomputable def length (s : Fin 3 → ℝ) : ℝ := Real.sqrt (dot s s)
/-- Construction for axis in the partial address axis risk model. -/
noncomputable def axis (s : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if length s=0 then fun i => if i=2 then 1 else 0 else fun i => s i/length s

/-- Complete original `dot_self_nonneg` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem dot_self_nonneg (s : Fin 3 → ℝ) : 0 ≤ dot s s :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (s i)

/-- Complete original `length_sq` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem length_sq (s : Fin 3 → ℝ) : length s^2=dot s s :=
  Real.sq_sqrt (dot_self_nonneg s)

/-- Complete original `zero_length` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem zero_length (s : Fin 3 → ℝ) (h : length s=0) (i : Fin 3) : s i=0 := by
  have hs := length_sq s
  rw [h] at hs
  have ht : s i*s i ≤ dot s s :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (s j)) (Finset.mem_univ i)
  nlinarith [sq_nonneg (s i)]

/-- Complete original `length_axis` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem length_axis (s : Fin 3 → ℝ) (i : Fin 3) : s i=length s*axis s i := by
  by_cases h : length s=0
  · simp only [h,zero_mul]
    exact zero_length s h i
  · simp only [axis,ite_eq_right h]
    field_simp

/-- Complete original `axis_unit` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem axis_unit (s : Fin 3 → ℝ) : dot (axis s) (axis s)=1 := by
  by_cases h : length s=0
  · simp [axis,h,dot]
  · have he : dot (axis s) (axis s)=dot s s/(length s)^2 := by
      simp only [dot,axis,ite_eq_right h]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he,← length_sq s]
    exact div_self (pow_ne_zero 2 h)

/-- Complete original `estimated_axis_risk` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem estimated_axis_risk (r s : Fin 3 → ℝ) (hr : length r ≤ 1) :
    (1-dot r (axis s))/2 ≤ 2*(1-length r)+2*distSq s r := by
  apply robust_axis_risk (length r) r s (axis s) (axis r)
    (Real.sqrt_nonneg _) hr (length_axis r) (axis_unit s) (axis_unit r)
  exact nearest_scaled_axis s (axis s) (axis r) (length s) (Real.sqrt_nonneg _)
    (length_axis s) (axis_unit s) (axis_unit r)

/-- Complete original `dist_sq_expand` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem dist_sq_expand (r s : Fin 3 → ℝ) :
    distSq r s=dot r r-2*dot r s+dot s s := by
  simp only [distSq,dot,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Complete original `dot_length` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem dot_length (r a : Fin 3 → ℝ) : dot r a=length r*dot (axis r) a := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [length_axis r i]
  ring

/-- Complete original `approximate_axis_risk` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem approximate_axis_risk (r a b : Fin 3 → ℝ) (hr : length r ≤ 1)
    (ha : dot a a=1) (hb : dot b b=1) :
    (1-dot r b)/2 ≤ 2*((1-dot r a)/2)+(1-dot a b) := by
  have ht := dist_sq_triangle (axis r) a b
  rw [dist_sq_expand,dist_sq_expand,dist_sq_expand,axis_unit,ha,hb] at ht
  have hmul := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (dot r r))
  have hrem := mul_nonneg (sub_nonneg.mpr hr)
    (sub_nonneg.mpr (unit_dot_le_one a b ha hb))
  rw [dot_length r b,dot_length r a]
  change 0 ≤ (1-length r)*(1-dot a b) at hrem
  change length r*(1-2*dot (axis r) b+1) ≤
    length r*(2*(1-2*dot (axis r) a+1)+2*(1-2*dot a b+1)) at hmul
  nlinarith

/-- Complete original `compiled_axis_risk` guarantee for `PartialAddressAxisRisk`; all source hypotheses and output obligations are retained. -/
theorem compiled_axis_risk (r s b : Fin 3 → ℝ) (τ : ℝ)
    (hr : length r ≤ 1) (hb : dot b b=1) (hclose : 1-dot (axis s) b ≤ τ/32) :
    (1-dot r b)/2 ≤ 8*((1-length r)/2)+4*distSq s r+τ/32 := by
  have h1 := approximate_axis_risk r (axis s) b hr (axis_unit s) hb
  have h2 := estimated_axis_risk r s hr
  linarith

#print axioms dist_sq_nonneg
#print axioms dist_sq_triangle
#print axioms robust_axis_risk
#print axioms unit_dot_le_one
#print axioms nearest_scaled_axis
#print axioms dot_self_nonneg
#print axioms length_sq
#print axioms zero_length
#print axioms length_axis
#print axioms axis_unit
#print axioms estimated_axis_risk
#print axioms dist_sq_expand
#print axioms dot_length
#print axioms approximate_axis_risk
#print axioms compiled_axis_risk
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.AxisRisk
