/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.GlobalLower
import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.CrossingSpectrum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix Matrix.Norms.L2Operator
open Qatlib.Papers.ProjectorQAOA26.StageStability
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem spectralGap_moment_upper (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R)
    (hL : 2≤Fintype.card I) (hlarge : 16≤(Fintype.card I:ℝ)*ec3A2 zero E) :
    spectralGap E hL (ec3A1 zero E/(1+ec3A1 zero E)) ≤
      4/Real.sqrt (Fintype.card I:ℝ) := by
  have hE1 : ∀ i,i≠zero → 1≤E i := fun i hi => (hE i hi).1
  have hER : ∀ i,i≠zero → E i≤R := fun i hi => (hE i hi).2
  have hL1 : 1≤Fintype.card I := by omega
  have hLp : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hL2 : (1:ℝ)<Fintype.card I := by exact_mod_cast (show 1<Fintype.card I by omega)
  have hA1ge := ec3A1_ge hR hER hE1 hL1
  have hA1 : 0<ec3A1 zero E := lt_of_lt_of_le (div_pos (by linarith)
    (mul_pos hLp (by linarith))) hA1ge
  have hA2 := ec3A2_pos hR hER hE1 hL
  let X := Real.sqrt (Fintype.card I:ℝ)
  let Y := Real.sqrt (ec3A2 zero E)
  let b := 2/(X*Y)
  let s := ec3A1 zero E/(1+ec3A1 zero E)
  have hX : 0<X := Real.sqrt_pos.mpr hLp
  have hY : 0<Y := Real.sqrt_pos.mpr hA2
  have hXsq : X^2=(Fintype.card I:ℝ) := Real.sq_sqrt hLp.le
  have hYsq : Y^2=ec3A2 zero E := Real.sq_sqrt hA2.le
  have hXYsq : (X*Y)^2=(Fintype.card I:ℝ)*ec3A2 zero E := by rw [mul_pow,hXsq,hYsq]
  have hXY : 4≤X*Y := by nlinarith [mul_pos hX hY]
  have hb : 0<b := div_pos (by norm_num) (mul_pos hX hY)
  have hbhalf : b≤1/2 := by
    apply (div_le_iff₀ (mul_pos hX hY)).mpr
    linarith
  have hscale : b^2*ec3A2 zero E=4/(Fintype.card I:ℝ) := by
    dsimp only [b]
    rw [div_pow,mul_pow,hXsq,hYsq]
    field_simp
    norm_num
  obtain ⟨lo,hi,hlo,hhi,hloEv,hhiEv⟩ :=
    crossing_actual_lowest_pair E zero hzero hE1 hL hA1.ne' b hb hbhalf hscale
  have hs : 0<s := div_pos hA1 (by linarith)
  have hs1 : s<1 := (div_lt_one (by linarith : 0<1+ec3A1 zero E)).mpr (by linarith)
  have hcoef : (1-s)/s=(ec3A1 zero E)⁻¹ := by
    dsimp only [s]
    field_simp
    ring
  have hg := actual_spectralGap_rankOne E hL s hs
  rw [hcoef,hloEv,hhiEv] at hg
  have hCS := ec3A1_sq_le (xstar := zero) (E := E) hL1
  have hf : ((Fintype.card I:ℝ)-1)/(Fintype.card I:ℝ)≤1 := (div_le_one hLp).mpr (by linarith)
  have hCS' : (ec3A1 zero E)^2≤ec3A2 zero E := by
    exact hCS.trans ((mul_le_mul_of_nonneg_right hf hA2.le).trans_eq (one_mul _))
  have hAY : ec3A1 zero E≤Y := by
    calc ec3A1 zero E = Real.sqrt ((ec3A1 zero E)^2) := (Real.sqrt_sq hA1.le).symm
         _ ≤ Real.sqrt (ec3A2 zero E) := Real.sqrt_le_sqrt hCS'
  have hsA : s≤ec3A1 zero E := div_le_self hA1.le (by linarith)
  have hsY : s≤Y := hsA.trans hAY
  have hbound : s*(2*b)≤4/X := by
    have he : s*(2*b)=(4/X)*(s/Y) := by dsimp only [b];field_simp;ring
    rw [he]
    calc (4/X)*(s/Y) ≤ (4/X)*1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hY).mpr hsY) (by positivity)
         _ = 4/X := mul_one _
  change spectralGap E hL s≤4/X
  rw [hg]
  exact (mul_le_mul_of_nonneg_left (by linarith [hlo.1,hhi.2] : hi-lo≤2*b) hs.le).trans hbound

theorem moment_bracket_of_bounded_cost (E : I → ℝ) (zero : I)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R)
    (hL : 2≤Fintype.card I) (hlarge : 1+16*R^2≤(Fintype.card I:ℝ)) :
    16≤(Fintype.card I:ℝ)*ec3A2 zero E := by
  have hLp : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hR2 : 0<R^2 := sq_pos_of_pos (by linarith)
  have ha :=
      ec3A2_ge hR (fun i hi => (hE i hi).2) (fun i hi => (hE i hi).1) (by omega : 1≤Fintype.card I)
  have ha' := (div_le_iff₀ (mul_pos hLp hR2)).mp ha
  by_contra hn
  have hp := mul_pos (show 0<16-(Fintype.card I:ℝ)*ec3A2 zero E by linarith) hR2
  nlinarith

theorem minimumGap_crossing_upper (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R)
    (hL : 2≤Fintype.card I) (hlarge : 1+16*R^2≤(Fintype.card I:ℝ)) :
    minimumGap E hL ≤ 4/Real.sqrt (Fintype.card I:ℝ) := by
  have hA := ec3A1_nonneg (fun i hi => (hE i hi).1)
  have hs0 : 0≤ec3A1 zero E/(1+ec3A1 zero E) := div_nonneg hA (by linarith)
  have hs1 : ec3A1 zero E/(1+ec3A1 zero E)≤1 :=
    (div_le_one (by linarith : 0<1+ec3A1 zero E)).mpr (by linarith)
  exact (minimumGap_le E hL _ ⟨hs0,hs1⟩).trans
    (spectralGap_moment_upper E zero hzero R hR hE hL
      (moment_bracket_of_bounded_cost E zero R hR hE hL hlarge))

theorem actual_minimumGap_bounds (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (R : ℝ) (hR : 1≤R) (hE : ∀ i,i≠zero → 1≤E i ∧ E i≤R)
    (hL : 2≤Fintype.card I) (hlarge : 1+16*R^2≤(Fintype.card I:ℝ)) :
    1/(8*(R+1)*Real.sqrt (Fintype.card I:ℝ)) ≤ minimumGap E hL ∧
      minimumGap E hL ≤ 4/Real.sqrt (Fintype.card I:ℝ) :=
  ⟨minimumGap_global_lower E zero hzero R hR hE hL,
    minimumGap_crossing_upper E zero hzero R hR hE hL hlarge⟩

end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
