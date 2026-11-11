/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.MarkedHalmosRange
import Mathlib.Order.Interval.Finset.Nat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TranslatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TruncatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.ExpectedCost
import Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.MarkedColumns
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.BudgetTruncation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputReadout
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.PreparedRepeat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.SourceWordTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! A finite rational Cayley-arc adversary for the actual Jordan/Halmos
matrix family. True numerical-range support determines a stronger classical
label oracle, whose known decoder returns the exact point-support value.
The finite grid count retains its endpoint term. Its combination with the
actual controlled input oracles derives a complete-record hybrid for the
fixed finite adaptive protocol model; it does not compile arbitrary output
circuit descriptions into that model or finish the block-output reduction. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.MarkedHalmos
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder

/-- Construction for phase Den in the rational phase support model. -/
private def phaseDen (t : ℝ) : ℂ := 1-Complex.I*(t : ℂ)
/-- Construction for rational Phase in the rational phase support model. -/
def rationalPhase (t : ℝ) : ℂ := star (phaseDen t)/phaseDen t

/-- The restricted-access construction satisfies `phaseDen_re` under the complete displayed premises. -/
private theorem phaseDen_re (t : ℝ) : (phaseDen t).re=1 := by simp [phaseDen,Complex.mul_re]
/-- The restricted-access construction satisfies `phaseDen_ne` under the complete displayed premises. -/
private theorem phaseDen_ne (t : ℝ) : phaseDen t≠0 := by
  intro hh
  have he := congrArg Complex.re hh
  rw [phaseDen_re] at he
  norm_num at he

/-- The restricted-access construction satisfies `rationalPhase_norm` under the complete displayed premises. -/
theorem rationalPhase_norm (t : ℝ) : ‖rationalPhase t‖=1 := by
  rw [rationalPhase,norm_div,norm_star]
  exact div_self (norm_ne_zero_iff.mpr (phaseDen_ne t))

/-- The restricted-access construction satisfies `phaseDen_norm_sq` under the complete displayed premises. -/
private theorem phaseDen_norm_sq (t : ℝ) : ‖phaseDen t‖^2=1+t^2 := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp [phaseDen,Complex.mul_re,Complex.mul_im]
  ring

/-- The restricted-access construction satisfies `phaseDen_product_bound` under the complete displayed premises. -/
private theorem phaseDen_product_bound (t s : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1/2)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/2) : ‖phaseDen t*phaseDen s‖ ≤ 5/4 := by
  have ht2 : t^2 ≤ 1/4 := by nlinarith [mul_le_mul_of_nonneg_right ht1 ht]
  have hs2 : s^2 ≤ 1/4 := by nlinarith [mul_le_mul_of_nonneg_right hs1 hs]
  have hmul := mul_le_mul (by linarith : 1+t^2 ≤ (5/4 : ℝ))
    (by linarith : 1+s^2 ≤ (5/4 : ℝ)) (by positivity : 0 ≤ 1+s^2) (by norm_num : (0 : ℝ) ≤ 5/4)
  apply le_of_sq_le_sq _ (by norm_num)
  rw [norm_mul,mul_pow,phaseDen_norm_sq,phaseDen_norm_sq]
  nlinarith

/-- The restricted-access construction satisfies `rationalPhase_difference` under the complete displayed premises. -/
theorem rationalPhase_difference (t s : ℝ) :
    rationalPhase t-rationalPhase s=(2*Complex.I*((t-s : ℝ) : ℂ))/(phaseDen t*phaseDen s) := by
  unfold rationalPhase
  field_simp [phaseDen_ne t,phaseDen_ne s]
  simp [phaseDen]
  ring

/-- The restricted-access construction satisfies `phase_chord_identity` under the complete displayed premises. -/
private theorem phase_chord_identity (t s : ℝ) :
    ‖rationalPhase t-rationalPhase s‖*‖phaseDen t*phaseDen s‖=2*|t-s| := by
  rw [rationalPhase_difference,norm_div,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (mul_ne_zero (phaseDen_ne t) (phaseDen_ne s)))]
  simp only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs]
  norm_num

/-- Separation on one bounded rational Cayley arc. This does not assert a
uniform distribution around the entire circle or omit a grid endpoint term. -/
theorem rationalPhase_separation (t s : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1/2)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/2) : |t-s| ≤ (5/8 : ℝ)*‖rationalPhase t-rationalPhase s‖ := by
  have hd := phase_chord_identity t s
  have hp := phaseDen_product_bound t s ht ht1 hs hs1
  have hh := mul_le_mul_of_nonneg_left hp (norm_nonneg (rationalPhase t-rationalPhase s))
  nlinarith


/-- Construction for phase Parameter in the rational phase support model. -/
def phaseParameter (H : ℕ) (k : Fin H) : ℝ := (k.val : ℝ)/(2*(H : ℝ))
/-- Construction for grid Phase in the rational phase support model. -/
def gridPhase (H : ℕ) (k : Fin H) : ℂ := rationalPhase (phaseParameter H k)

/-- The restricted-access construction satisfies `phaseParameter_bounds` under the complete displayed premises. -/
theorem phaseParameter_bounds (H : ℕ) (hH : 0<H) (k : Fin H) :
    0 ≤ phaseParameter H k ∧ phaseParameter H k ≤ 1/2 := by
  have hHr : (0 : ℝ)<H := by exact_mod_cast hH
  have hk : (k.val : ℝ)<H := by exact_mod_cast k.isLt
  constructor
  · dsimp [phaseParameter]; positivity
  · dsimp [phaseParameter]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*H)).mpr
    linarith

/-- The restricted-access construction satisfies `grid_hit_span` under the complete displayed premises. -/
theorem grid_hit_span (H : ℕ) (hH : 0<H) (τ : ℝ) (center : ℂ) (i j : Fin H)
    (hi : ‖gridPhase H i-center‖ ≤ 2*Real.sqrt τ)
    (hj : ‖gridPhase H j-center‖ ≤ 2*Real.sqrt τ) :
    |(i.val : ℝ)-(j.val : ℝ)| ≤ 5*(H : ℝ)*Real.sqrt τ := by
  have hHr : (0 : ℝ)<H := by exact_mod_cast hH
  have hti := phaseParameter_bounds H hH i
  have htj := phaseParameter_bounds H hH j
  have hs := rationalPhase_separation (phaseParameter H i) (phaseParameter H j) hti.1 hti.2 htj.1 htj.2
  have ht := dist_triangle (gridPhase H i) center (gridPhase H j)
  simp only [dist_eq_norm] at ht
  rw [norm_sub_rev center (gridPhase H j)] at ht
  have hd : ‖gridPhase H i-gridPhase H j‖ ≤ 4*Real.sqrt τ := by linarith
  have hp : |phaseParameter H i-phaseParameter H j| ≤ (5/2 : ℝ)*Real.sqrt τ := by
    change |phaseParameter H i-phaseParameter H j| ≤ _
    change |phaseParameter H i-phaseParameter H j| ≤ (5/8 : ℝ)*‖gridPhase H i-gridPhase H j‖ at hs
    linarith
  rw [phaseParameter,phaseParameter,←sub_div,abs_div,abs_of_pos (by positivity : (0 : ℝ)<2*H)] at hp
  have hh := (div_le_iff₀ (by positivity : (0 : ℝ)<2*H)).mp hp
  nlinarith

/-- The restricted-access construction satisfies `natset_card_span` under the complete displayed premises. -/
private theorem natset_card_span (T : Finset ℕ) (hne : T.Nonempty) :
    (T.card : ℝ) ≤ (T.max' hne : ℝ)-(T.min' hne : ℝ)+1 := by
  have hsub : T⊆Finset.Icc (T.min' hne) (T.max' hne) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le T n hn,Finset.le_max' T n hn⟩
  have hc : T.card ≤ T.max' hne+1-T.min' hne := by
    simpa only [Nat.card_Icc] using Finset.card_le_card hsub
  have hmm : T.min' hne ≤ T.max' hne := Finset.min'_le T _ (Finset.max'_mem T hne)
  have hp : T.min' hne ≤ T.max' hne+1 := by omega
  have hr : (T.card : ℝ) ≤ ((T.max' hne+1-T.min' hne : ℕ) : ℝ) := by exact_mod_cast hc
  rw [Nat.cast_sub hp,Nat.cast_add,Nat.cast_one] at hr
  linarith

/-- Construction for ball Hits in the rational phase support model. -/
def ballHits (H : ℕ) (τ : ℝ) (center : ℂ) : Finset (Fin H) :=
  Finset.univ.filter (fun k => ‖gridPhase H k-center‖ ≤ 2*Real.sqrt τ)

/-- Uniform finite visibility on a bounded Cayley arc. The +1/H endpoint
term is retained even when the ball contains a single grid point. -/
theorem grid_ball_visibility (H : ℕ) (hH : 0<H) (τ : ℝ) (center : ℂ) :
    ((ballHits H τ center).card : ℝ)/(H : ℝ) ≤ 5*Real.sqrt τ+1/(H : ℝ) := by
  have hHr : (0 : ℝ)<H := by exact_mod_cast hH
  by_cases he : ballHits H τ center=∅
  · simp only [he,Finset.card_empty,Nat.cast_zero,zero_div]
    positivity
  have hne : (ballHits H τ center).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  let T := (ballHits H τ center).image (fun k => k.val)
  have hT : T.Nonempty := by
    obtain ⟨k,hk⟩ := hne
    exact ⟨k.val,Finset.mem_image.mpr ⟨k,hk,rfl⟩⟩
  have hcard : T.card=(ballHits H τ center).card := Finset.card_image_of_injective _ Fin.val_injective
  obtain ⟨i,hi,hival⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
  obtain ⟨j,hj,hjval⟩ := Finset.mem_image.mp (Finset.max'_mem T hT)
  have hp := grid_hit_span H hH τ center i j
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  rw [hival,hjval] at hp
  have hminmax : T.min' hT ≤ T.max' hT := Finset.min'_le T _ (Finset.max'_mem T hT)
  have hminmaxr : (T.min' hT : ℝ) ≤ T.max' hT := by exact_mod_cast hminmax
  rw [abs_of_nonpos (by linarith : (T.min' hT : ℝ)-(T.max' hT : ℝ) ≤ 0)] at hp
  have hc := natset_card_span T hT
  rw [hcard] at hc
  apply (div_le_iff₀ hHr).mpr
  rw [add_mul,div_mul_cancel₀ _ hHr.ne']
  nlinarith



/-- Construction for actual Support in the rational phase support model. -/
def actualSupport {N : ℕ} (w : Fin N) (z u : ℂ) : ℝ :=
  sSup ((fun a : ℂ => (star u*a).re) '' Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w z))

/-- The restricted-access construction satisfies `actualSupport_eq` under the complete displayed premises. -/
theorem actualSupport_eq {N : ℕ} (w : Fin N) (z u : ℂ) (hu : ‖u‖=1) :
    actualSupport w z u=max 1 (star u*(2*z)).re :=
  (target_actual_support w z u hu).csSup_eq

/-- The restricted-access construction satisfies `gridPhase_norm` under the complete displayed premises. -/
theorem gridPhase_norm (H : ℕ) (k : Fin H) : ‖gridPhase H k‖=1 := rationalPhase_norm _

/-- Construction for spike Point in the rational phase support model. -/
def spikePoint (H : ℕ) (τ : ℝ) (k : Fin H) : ℂ :=
  (((1+2*τ)/2 : ℝ) : ℂ)*gridPhase H k

/-- The restricted-access construction satisfies `spikePoint_norm` under the complete displayed premises. -/
theorem spikePoint_norm (H : ℕ) (τ : ℝ) (k : Fin H) (hτ : 0 ≤ τ) :
    ‖spikePoint H τ k‖=(1+2*τ)/2 := by
  rw [spikePoint,norm_mul,gridPhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

/-- The restricted-access construction satisfies `spikePoint_normSq_le_one` under the complete displayed premises. -/
theorem spikePoint_normSq_le_one (H : ℕ) (τ : ℝ) (k : Fin H) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1/4) :
    Complex.normSq (spikePoint H τ k) ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq,spikePoint_norm H τ k hτ]
  have h0 : 0 ≤ (1+2*τ)/2 := by positivity
  have h1 : (1+2*τ)/2 ≤ 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 h0]

/-- The restricted-access construction satisfies `spike_actual_maximum` under the complete displayed premises. -/
theorem spike_actual_maximum {H N : ℕ} (w : Fin N) (τ : ℝ) (k : Fin H) (hτ : 0 ≤ τ) :
    IsGreatest ((fun a : ℂ => ‖a‖) '' Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w (spikePoint H τ k))) (1+2*τ) := by
  have hh := target_actual_maximum w (spikePoint H τ k)
  have hm : max 1 (2*‖spikePoint H τ k‖)=1+2*τ := by
    rw [spikePoint_norm H τ k hτ]
    have hs : 2*((1+2*τ)/2)=1+2*τ := by ring
    rw [hs,max_eq_right (by linarith)]
  rwa [hm] at hh

/-- The restricted-access construction satisfies `spike_support_value` under the complete displayed premises. -/
theorem spike_support_value {H N : ℕ} (w : Fin N) (τ : ℝ) (k : Fin H) (u : ℂ) (hu : ‖u‖=1) :
    actualSupport w (spikePoint H τ k) u=max 1 ((1+2*τ)*(star u*gridPhase H k).re) := by
  have hs : 2*spikePoint H τ k=(((1+2*τ : ℝ) : ℂ))*gridPhase H k := by
    unfold spikePoint
    push_cast
    ring
  rw [actualSupport_eq w _ u hu,hs]
  have he : star u*((((1+2*τ : ℝ) : ℂ))*gridPhase H k)=
      (((1+2*τ : ℝ) : ℂ))*(star u*gridPhase H k) := by ring
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- The restricted-access construction satisfies `unit_chord_sq` under the complete displayed premises. -/
private theorem unit_chord_sq (u v : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖u-v‖^2=2-2*(star u*v).re := by
  have huq : Complex.normSq u=1 := by rw [Complex.normSq_eq_norm_sq,hu]; norm_num
  have hvq : Complex.normSq v=1 := by rw [Complex.normSq_eq_norm_sq,hv]; norm_num
  rw [Complex.normSq_apply] at huq hvq
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp [Complex.mul_re,RCLike.star_def]
  nlinarith

/-- A changed TRUE matrix support answer is contained in the counted phase
ball. The count is not assumed to be a visibility property of an enclosure. -/
theorem visible_in_ball {H N : ℕ} (w : Fin N) (τ : ℝ) (hτ : 0 ≤ τ) (k : Fin H)
    (u : ℂ) (hu : ‖u‖=1) (hv : 1<actualSupport w (spikePoint H τ k) u) :
    k∈ballHits H τ u := by
  rw [spike_support_value w τ k u hu] at hv
  have hc : (star u*gridPhase H k).re ≤ 1 := by
    have hh := Complex.re_le_norm (star u*gridPhase H k)
    simpa [hu,gridPhase_norm] using hh
  have hp : 1<(1+2*τ)*(star u*gridPhase H k).re := by
    simpa only [lt_max_iff,lt_self_iff_false,false_or] using hv
  have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2*τ)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  apply le_of_sq_le_sq _ (by positivity)
  rw [norm_sub_rev (gridPhase H k) u,unit_chord_sq u _ hu (gridPhase_norm H k),mul_pow,Real.sq_sqrt hτ]
  nlinarith



/-- Stronger than a classical point-value answer: disclose the hidden grid
index exactly when the TRUE support exceeds the baseline. It is never used
coherently by the finite protocol. -/
def labelResponse {H N : ℕ} (τ : ℝ) (normal : ℝ → ℂ) (h : Fin H × Fin N) (a : ℝ) : Fin (H+1) :=
  if 1<actualSupport h.2 (spikePoint H τ h.1) (normal a) then h.1.succ else 0

/-- Known decoding of the stronger label; this does not discover an unknown
matrix parameter without a support-oracle call. -/
def decodeLabel (H : ℕ) (τ : ℝ) (u : ℂ) : Fin (H+1) → ℝ :=
  Fin.cases 1 (fun k : Fin H => max 1 ((1+2*τ)*(star u*gridPhase H k).re))

/-- The restricted-access construction satisfies `label_decode_exact` under the complete displayed premises. -/
theorem label_decode_exact {H N : ℕ} (τ : ℝ) (normal : ℝ → ℂ) (h : Fin H × Fin N) (a : ℝ)
    (hu : ‖normal a‖=1) :
    decodeLabel H τ (normal a) (labelResponse τ normal h a)=
      actualSupport h.2 (spikePoint H τ h.1) (normal a) := by
  unfold labelResponse
  split_ifs with hvis
  · simpa only [decodeLabel,Fin.cases_succ] using (spike_support_value h.2 τ h.1 (normal a) hu).symm
  · change (1 : ℝ)=_
    have hh : actualSupport h.2 (spikePoint H τ h.1) (normal a) ≤ 1 := le_of_not_gt hvis
    have hl : 1 ≤ actualSupport h.2 (spikePoint H τ h.1) (normal a) := by
      rw [spike_support_value h.2 τ h.1 (normal a) hu]
      exact le_max_left _ _
    exact le_antisymm hl hh

/-- The restricted-access construction satisfies `label_outside_ball` under the complete displayed premises. -/
theorem label_outside_ball {H N : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (normal : ℝ → ℂ)
    (h : Fin H × Fin N) (a : ℝ) (hu : ‖normal a‖=1) (hn : h.1∉ballHits H τ (normal a)) :
    labelResponse τ normal h a=0 := by
  have hh : ¬1<actualSupport h.2 (spikePoint H τ h.1) (normal a) := by
    intro hv
    exact hn (visible_in_ball h.2 τ hτ h.1 (normal a) hu hv)
  simp [labelResponse,hh]

/-- Nuisance and mark are kept jointly. Summing the independent mark gives
exactly the counted uniform phase probability, including its endpoint term. -/
theorem joint_ball_visibility (H : ℕ) (hH : 0<H) (N : ℕ) (hN : 0<N) (τ : ℝ) (center : ℂ) :
    (∑ h∈Finset.univ.filter (fun h : Fin H × Fin N => h.1∈ballHits H τ center),
      (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.markLaw H hH) N hN).prob h) ≤
      5*Real.sqrt τ+1/(H : ℝ) := by
  have hNr : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  have hHr : (H : ℝ)≠0 := by exact_mod_cast hH.ne'
  have he : (∑ h∈Finset.univ.filter (fun h : Fin H × Fin N => h.1∈ballHits H τ center),
      (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.markLaw H hH) N hN).prob h)=
      ((ballHits H τ center).card : ℝ)/(H : ℝ) := by
    rw [Finset.sum_filter]
    change (∑ h : Fin H × Fin N,if h.1∈ballHits H τ center then (1/(H : ℝ))*(1/(N : ℝ)) else 0)=_
    rw [Fintype.sum_prod_type]
    have hx (k : Fin H) : (∑ w : Fin N,if k∈ballHits H τ center then (1/(H : ℝ))*(1/(N : ℝ)) else 0)=
        if k∈ballHits H τ center then 1/(H : ℝ) else 0 := by
      by_cases hk : k∈ballHits H τ center
      · simp only [hk,ite_eq_left,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        field_simp
      · simp [hk]
    simp_rw [hx]
    rw [←Finset.sum_filter]
    have hy : (Finset.univ.filter (fun k : Fin H => k∈ballHits H τ center))=ballHits H τ center := by
      ext k
      simp
    rw [hy,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he]
  exact grid_ball_visibility H hH τ center

/-- The explicit matrix family and stronger classical label oracle have the
full finite-protocol hybrid bound, with no supplied geometry/distance fields.
The decoder theorem relates labels to the TRUE point-support values. -/
theorem rational_family_support_hybrid {W : Type} [Fintype W] [DecidableEq W]
    (H : ℕ) (hH : 0<H) (N : ℕ) (hN : 0<N) (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1/4)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program (queryDim W N) (H+1))
    (ρ : Operator (queryDim W N)) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1)
    (s : ℕ) (hc : ∀ p : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Path P, (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathCharge P p).2 ≤ s) :
    (∑ hp,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.markLaw H hH) N hN)
      (fun h => Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathLaw
        (fun mode => Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.oracleChannel (finiteOracle W h.2 (spikePoint H τ h.1) mode)
          (finiteOracle_unitary W h.2 (spikePoint H τ h.1) (spikePoint_normSq_le_one H τ h.1 hτ hτ1) mode))
        (labelResponse τ normal h) P ρ hρ htrace)).prob hp-
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.markLaw H hH) N hN)
        (fun _ => Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathLaw
          (fun mode => Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.oracleChannel (finiteBaseline W N mode) (finiteBaseline_unitary W N hN mode))
          (fun _ => 0) P ρ hρ htrace)).prob hp|)/2 ≤
      4*(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.queryDepth P : ℝ)/Real.sqrt N+(s : ℝ)*(5*Real.sqrt τ+1/(H : ℝ)) := by
  exact actual_joint_support_bound (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.markLaw H hH) hN (spikePoint H τ)
    (fun k => spikePoint_normSq_le_one H τ k hτ hτ1)
    (labelResponse τ normal) (fun _ => 0) P ρ hρ htrace
    (fun h a => h.1∈ballHits H τ (normal a))
    (fun h a hn => label_outside_ball τ hτ normal h a (hnormal a) hn) s (5*Real.sqrt τ+1/(H : ℝ))
    (fun a => by
      convert joint_ball_visibility H hH N hN τ (normal a) using 1
      apply Finset.sum_congr
      · ext h
        simp
      · intro h _
        rfl) hc



/-- The restricted-access construction satisfies `decode_zero_is_baseline` under the complete displayed premises. -/
theorem decode_zero_is_baseline {H N : ℕ} (w : Fin N) (τ : ℝ) (u : ℂ) (hu : ‖u‖=1) :
    decodeLabel H τ u 0=actualSupport w 0 u := by
  change (1 : ℝ)=actualSupport w 0 u
  rw [actualSupport_eq w 0 u hu]
  simp

end Qatlib.Papers.CrouzeixLS26.AccessLower.MarkedHalmos
