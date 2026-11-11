/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressTrainedOriginal

set_option backward.isDefEq.respectTransparency false

/-!
Actual two-color targets and the same nested rational clipping output.
Color 1's left endpoint is color 0's right endpoint, including wrap. Their
average is the original directional Bell mean. These are label/target and
postprocessing identities, not a native address-translation circuit.
Zero-side, zero-promise and midpoint branches need no quantum samples.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.TwoColor
noncomputable section
open scoped BigOperators
open RetainedSpin FiniteAxisWord UniformMatching TrainedGrid

/-- Construction for offset in the partial address two color model. -/
def offset (C m d : ℕ) [NeZero (C*(2*m))] (axis : Fin d) (color : Fin 2) : Fin d → Fin (C*(2*m)) :=
  MatchedGrid.matchingOffset C (2*m) d axis color (by omega)

/-- Complete original `color_one_left` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem color_one_left (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (axis : Fin d) (e : Edge C m d axis) :
    (matchingEquiv C m d r hN (offset C m d axis 1) axis).symm (e,false)=
      (matchingEquiv C m d r hN (offset C m d axis 0) axis).symm (e,true) := by
  rw [matching_inverse,matching_inverse]
  funext j
  change Fin.cast hN.symm
    ((GridPatch.coordinateEquiv C (2*m) (offset C m d axis 1 j)).symm
      (e.1 j,(localEquiv m d axis).symm (e.2,false) j))=
    Fin.cast hN.symm
    ((GridPatch.coordinateEquiv C (2*m) (offset C m d axis 0 j)).symm
      (e.1 j,(localEquiv m d axis).symm (e.2,true) j))
  by_cases hj : j=axis
  · subst j
    change Fin.cast hN.symm
      (finProdFinEquiv (finProdFinEquiv ((e.1 axis).2,(localEquiv m d axis).symm (e.2,false) axis)+
        offset C m d axis 1 axis,(e.1 axis).1))=
      Fin.cast hN.symm
      (finProdFinEquiv (finProdFinEquiv ((e.1 axis).2,(localEquiv m d axis).symm (e.2,true) axis)+
        offset C m d axis 0 axis,(e.1 axis).1))
    apply congrArg (fun q : Fin (C*(2*m)) => Fin.cast hN.symm
      (finProdFinEquiv (q,(e.1 axis).1)))
    apply Fin.ext
    simp only [Fin.val_add]
    change (((localEquiv m d axis).symm (e.2,false) axis).val+(2*m)*(e.1 axis).2.val+
      (offset C m d axis 1 axis).val)%(C*(2*m))=
      (((localEquiv m d axis).symm (e.2,true) axis).val+(2*m)*(e.1 axis).2.val+
        (offset C m d axis 0 axis).val)%(C*(2*m))
    rw [local_left_axis,local_right_axis]
    have h1 : (offset C m d axis 1 axis).val=1 := by
      simpa only [offset,ite_true,mul_one, Fin.val_one] using MatchedGrid.matching_offset_value C (2*m) d axis 1 (by omega) axis
    have h0 : (offset C m d axis 0 axis).val=0 := by
      simpa [offset] using MatchedGrid.matching_offset_value C (2*m) d axis 0 (by omega) axis
    rw [h1,h0]
    congr 1
    omega
  · have ho : offset C m d axis 1 j=offset C m d axis 0 j := by
      simp only [offset,MatchedGrid.matchingOffset,MatchedGrid.colorOffset,ite_eq_right hj]
    have hl : (localEquiv m d axis).symm (e.2,false) j=(localEquiv m d axis).symm (e.2,true) j := by
      simp [localEquiv,hj]
    rw [ho,hl]

/-- Complete original `color_average` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem color_average (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) :
    (TrainedOriginal.target C m d r hN (offset C m d axis 0) axis a b c k+
      TrainedOriginal.target C m d r hN (offset C m d axis 1) axis a b c k)/2=
      bellMean a b c k (periodicDoubleShift d (2^r) axis) := by
  let g := matchingEquiv C m d r hN (offset C m d axis 0) axis
  let f := fun x => bellProbability (complexSpinor a b c k x)
    (complexSpinor a b c k (MatchedGrid.right d r axis x))
  have h0 : TrainedOriginal.target C m d r hN (offset C m d axis 0) axis a b c k=
      average (fun e => f (g.symm (e,false))) := by
    unfold TrainedOriginal.target
    apply congrArg average
    funext e
    dsimp only [TrainedOriginal.endpointSpin,f,g]
    rw [matching_right]
  have h1 : TrainedOriginal.target C m d r hN (offset C m d axis 1) axis a b c k=
      average (fun e => f (g.symm (e,true))) := by
    unfold TrainedOriginal.target
    apply congrArg average
    funext e
    dsimp only [TrainedOriginal.endpointSpin,f,g]
    rw [← color_one_left C m d r hN axis e,matching_right]
  rw [h0,h1]
  calc
    _ = (∑ e : Edge C m d axis,(f (g.symm (e,false))+f (g.symm (e,true)))/2)/
        (Fintype.card (Edge C m d axis) : ℝ) := by
      simp only [average,← Finset.sum_div,Finset.sum_add_distrib]
      ring
    _ = (∑ x : Fin d → Fin (2^r),f x)/(Fintype.card (Fin d → Fin (2^r)) : ℝ) := pair_mean g f
    _ = _ := by simp only [bellMean,populationMean,f,BoxGridEnergy.right_eq_periodic]

/-- Complete original `target_range` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem target_range (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (axis : Fin d) (color : Fin 2)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) :
    0≤TrainedOriginal.target C m d r hN (offset C m d axis color) axis a b c k ∧
      TrainedOriginal.target C m d r hN (offset C m d axis color) axis a b c k≤1/2 := by
  have hr (e : Edge C m d axis) := bell_probability_range
    (TrainedOriginal.endpointSpin C m d r hN (offset C m d axis color) axis a b c k false e)
    (TrainedOriginal.endpointSpin C m d r hN (offset C m d axis color) axis a b c k true e)
    (TrainedOriginal.endpoint_mass C m d r hN _ axis a b c k hz false e)
    (TrainedOriginal.endpoint_mass C m d r hN _ axis a b c k hz true e)
  constructor
  · exact average_nonneg _ (fun e => (hr e).1)
  · have h := average_mono _ (fun _ => (1/2 : ℝ)) (fun e => (hr e).2)
    have hc : (Fintype.card (Edge C m d axis) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
    have ha : average (fun _ : Edge C m d axis => (1/2 : ℝ))=1/2 := by
      unfold average
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp
    exact h.trans_eq ha

/-- Complete original `target_cap` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem target_cap (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (axis : Fin d) (color : Fin 2)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℝ)
    (hp : bellMean a b c k (periodicDoubleShift d (2^r) axis)≤p0) :
    0≤TrainedOriginal.target C m d r hN (offset C m d axis color) axis a b c k ∧
      TrainedOriginal.target C m d r hN (offset C m d axis color) axis a b c k ≤ min (1/2) (2*p0) := by
  have h0 := target_range C m d r hN axis 0 a b c k hz
  have h1 := target_range C m d r hN axis 1 a b c k hz
  have hm := color_average C m d r hN axis a b c k
  have h := target_range C m d r hN axis color a b c k hz
  refine ⟨h.1,le_min h.2 ?_⟩
  fin_cases color
  · change TrainedOriginal.target C m d r hN (offset C m d axis 0) axis a b c k≤2*p0
    linarith [h1.1]
  · change TrainedOriginal.target C m d r hN (offset C m d axis 1) axis a b c k≤2*p0
    linarith [h0.1]

/-- Construction for clipped Value Q in the partial address two color model. -/
def clippedValueQ {d : ℕ} (p0 : ℚ) (raw : Fin d → Fin 2 → ℚ) : ℚ :=
  intervalClipQ 0 ((d : ℚ)*p0)
    ((∑ j : Fin d,∑ color : Fin 2,intervalClipQ 0 (min (1/2) (2*p0)) (raw j color))/2)

/-- Construction for full Target in the partial address two color model. -/
def fullTarget (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ) : ℝ :=
  ∑ j : Fin d,bellMean a b c k (periodicDoubleShift d (2^r) j)

/-- Complete original `full_target_range` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem full_target_range (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℝ)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤p0) :
    0≤fullTarget d r a b c k ∧ fullTarget d r a b c k≤(d : ℝ)*p0 := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => bell_mean_nonneg a b c k hz _)
  · calc
      _ ≤ ∑ _ : Fin d,p0 := Finset.sum_le_sum (fun j _ => hp j)
      _ = _ := by simp

/-- Complete original `zero_promise` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem zero_promise (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤0) : fullTarget d r a b c k=0 := by
  have h := full_target_range d r a b c k hz 0 hp
  linarith [h.1,h.2]

/-- Complete original `zero_side` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem zero_side (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hs : 2^r≤2) : fullTarget d r a b c k=0 := by
  have hp : 0<2^r := by positivity
  have hside : 2^r=1 ∨ 2^r=2 := by omega
  have htwo : (2 : Fin (2^r))=0 := by
    apply Fin.ext
    change 2%(2^r)=0
    rcases hside with h|h <;> rw [h]
  have hshift (j : Fin d) (x : Fin d → Fin (2^r)) : periodicDoubleShift d (2^r) j x=x := by
    rw [← BoxGridEnergy.right_eq_periodic]
    simp only [MatchedGrid.right,htwo,add_zero,Function.update_eq_self]
  have hself (x : Fin d → Fin (2^r)) :
      bellProbability (complexSpinor a b c k x) (complexSpinor a b c k x)=0 := by
    unfold bellProbability determinant
    rw [mul_comm (complexSpinor a b c k x false) (complexSpinor a b c k x true),sub_self]
    norm_num
  simp [fullTarget,bellMean,populationMean,hshift,hself]

/-- Complete original `midpoint_error` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem midpoint_error (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℚ)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p0 : ℝ))
    (ε : ℝ) (hguard : (d : ℝ)*(p0 : ℝ)≤2*ε) :
    |(((d : ℚ)*p0/2 : ℚ) : ℝ)-fullTarget d r a b c k|≤ε := by
  have h := full_target_range d r a b c k hz (p0 : ℝ) hp
  norm_num only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
  apply abs_le.mpr
  constructor <;> linarith [h.1,h.2]

/-- Complete original `clipped_value_error` guarantee for `PartialAddressTwoColor`; all source hypotheses and output obligations are retained. -/
theorem clipped_value_error (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (hd : 0<d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℚ)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p0 : ℝ))
    (raw : Fin d → Fin 2 → ℚ) (ε : ℝ)
    (hraw : ∀ j color, |(raw j color : ℝ)-
      TrainedOriginal.target C m d r hN (offset C m d j color) j a b c k|≤ε/(d : ℝ)) :
    |(clippedValueQ p0 raw : ℝ)-fullTarget d r a b c k|≤ε := by
  let μ := fun j color => TrainedOriginal.target C m d r hN (offset C m d j color) j a b c k
  let z := fun j color => intervalClipQ 0 (min (1/2) (2*p0)) (raw j color)
  have hd0 : (d : ℝ)≠0 := by exact_mod_cast (by omega : d≠0)
  have hcenter : (∑ j : Fin d,∑ color : Fin 2,μ j color)/2=fullTarget d r a b c k := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    simpa [μ,Fin.sum_univ_succ] using color_average C m d r hN j a b c k
  have hclip (j : Fin d) (color : Fin 2) : |(z j color : ℝ)-μ j color|≤ε/(d : ℝ) := by
    have hr : 0≤μ j color ∧ μ j color≤((min (1/2) (2*p0) : ℚ) : ℝ) := by
      convert target_cap C m d r hN j color a b c k hz (p0 : ℝ) (hp j) using 1
      norm_num [μ]
    have h := interval_clip_contract 0 ((min (1/2) (2*p0) : ℚ) : ℝ)
      (raw j color : ℝ) (μ j color) hr.1 hr.2
    simpa only [z,interval_clip_cast,Rat.cast_zero] using h.trans (hraw j color)
  have hs := finite_sum_error_bound (fun i : Fin d × Fin 2 => (z i.1 i.2 : ℝ))
    (fun i : Fin d × Fin 2 => μ i.1 i.2) (ε/(d : ℝ)) (fun i => hclip i.1 i.2)
  simp only [Fintype.sum_prod_type,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hs
  have havg : |(∑ j : Fin d,∑ color : Fin 2,(z j color : ℝ))/2-fullTarget d r a b c k|≤ε := by
    rw [← hcenter,← sub_div,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    calc
      _ ≤ ((d : ℝ)*2*(ε/(d : ℝ)))/2 := div_le_div_of_nonneg_right hs (by norm_num)
      _ = ε := by field_simp
  have hF0 : 0≤fullTarget d r a b c k :=
    Finset.sum_nonneg (fun j _ => bell_mean_nonneg a b c k hz _)
  have hF1 : fullTarget d r a b c k≤(d : ℝ)*(p0 : ℝ) := by
    calc
      _ ≤ ∑ _ : Fin d,(p0 : ℝ) := Finset.sum_le_sum (fun j _ => hp j)
      _ = _ := by simp
  have hc : (clippedValueQ p0 raw : ℝ)=intervalClip 0 ((d : ℝ)*(p0 : ℝ))
      ((∑ j : Fin d,∑ color : Fin 2,(z j color : ℝ))/2) := by
    simp only [clippedValueQ,z,interval_clip_cast,Rat.cast_zero,Rat.cast_mul,
      Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sum]
  rw [hc]
  exact (interval_clip_contract 0 _ _ _ hF0 hF1).trans havg

#print axioms offset
#print axioms color_one_left
#print axioms color_average
#print axioms target_range
#print axioms target_cap
#print axioms clippedValueQ
#print axioms full_target_range
#print axioms zero_promise
#print axioms zero_side
#print axioms midpoint_error
#print axioms clipped_value_error
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.TwoColor
