/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.CoordinateFiber
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Mathlib.Analysis.Real.Pi.Bounds
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

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Papers.CrouzeixLS26.AccessLower.Coordinate
open Qatlib.Concepts.BlockEncoding
/-! Readout of a literal fixed-normalization block on a known frame. The
unknown entry is used only in the guarantee, not by the estimator or threshold.
M denotes the AE grid here, not the matrix normalizer. These lemmas do not
prove the adaptive support hybrid or the complete query lower bound. -/
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout
open Qatlib Matrix
open scoped Matrix.Norms.L2Operator

/-- The restricted-access construction satisfies `scalar_probability_error` under the complete displayed premises. -/
theorem scalar_probability_error (z : ℂ) (a e : ℝ) (ha : 0≤a) (ha1 : a≤1)
    (he1 : e≤1) (he : ‖z-(a : ℂ)‖≤e) : |‖z‖^2-a^2|≤3*e := by
  have he0 : 0≤e := (norm_nonneg _).trans he
  have hd : |‖z‖-a|≤e := by
    have hh := abs_norm_sub_norm_le z (a : ℂ)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha] at hh
    exact hh.trans he
  have hz : ‖z‖≤a+e := by linarith [(abs_le.mp hd).2]
  have hs : ‖z‖+a≤2+e := by linarith
  have hfactor : ‖z‖^2-a^2=(‖z‖-a)*(‖z‖+a) := by ring
  rw [hfactor,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) ha)]
  calc
    _ ≤ e*(‖z‖+a) := mul_le_mul_of_nonneg_right hd (add_nonneg (norm_nonneg _) ha)
    _ ≤ e*(2+e) := mul_le_mul_of_nonneg_left hs he0
    _ ≤ 3*e := by nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]

/-- The restricted-access construction satisfies `block_entry_probability` under the complete displayed premises. -/
theorem block_entry_probability {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (i j : I) (a e : ℝ) (hb : BlockEncoding T U F F 1 e)
    (hentry : T i j=(a : ℂ)) (ha : 0≤a) (ha1 : a≤1) (he1 : e≤1) :
    |‖compress F U F i j‖^2-a^2|≤3*e := by
  have hm : ‖T-compress F U F‖≤e := by simpa only [one_smul] using hb.error_le
  have hh := (Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt.rectangular_entry_norm_le (T-compress F U F) i j).trans hm
  have he : ‖compress F U F i j-(a : ℂ)‖≤e := by
    simpa only [Matrix.sub_apply,hentry,norm_sub_rev] using hh
  exact scalar_probability_error _ a e ha ha1 he1 he

/-- Construction for base Probability in the block output readout model. -/
def baseProbability : ℝ := 16/25
/-- Construction for hidden Probability in the block output readout model. -/
def hiddenProbability (t : ℝ) : ℝ := 16/(25*(1+2*t)^2)

/-- The restricted-access construction satisfies `target_probability_gap` under the complete displayed premises. -/
theorem target_probability_gap (t : ℝ) (ht : 0<t) (ht1 : t≤1/4) :
    t≤baseProbability-hiddenProbability t := by
  have hd : 0<1+2*t := by linarith
  have heq : baseProbability-hiddenProbability t=64*t*(1+t)/(25*(1+2*t)^2) := by
    dsimp [baseProbability,hiddenProbability]
    field_simp [hd.ne']
    ring
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0<25*(1+2*t)^2)).mpr
  have ht2 : t^2≤t/4 := by nlinarith [mul_le_mul_of_nonneg_left ht1 ht.le]
  have hc : 25*(1+2*t)^2≤64*(1+t) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hc ht.le]


/-- The restricted-access construction satisfies `prepared_singleton_probability` under the complete displayed premises. -/
theorem prepared_singleton_probability {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (j i : H) :
    MeasureProb (preparedAAState U j) {i}=‖U i j‖^2 := by
  simp [MeasureProb,BornProb,preparedAAState,ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite]

/-- The restricted-access construction satisfies `ae_error_envelope` under the complete displayed premises. -/
theorem ae_error_envelope (a t : ℝ) (M : ℕ) (hM : 2≤M)
    (ha : 0≤a) (ha1 : a≤1) (ht : 0<t) (ht1 : t≤1) (hbudget : 1024/t≤(M : ℝ)) :
    2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2≤t/100 := by
  have hm0 : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hMt : 1024≤(M : ℝ)*t := (div_le_iff₀ ht).mp hbudget
  have hi : (1 : ℝ)/(M : ℝ)≤t/1024 := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  have hprod : 0≤a*(1-a) := mul_nonneg ha (sub_nonneg.mpr ha1)
  have hsqrt : Real.sqrt (a*(1-a))≤1 := by
    have he := Real.sq_sqrt hprod
    nlinarith [Real.sqrt_nonneg (a*(1-a)),sq_nonneg a]
  have hc : 2*Real.pi*Real.sqrt (a*(1-a))≤8 := by
    have hh := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0≤2*Real.pi)
    nlinarith [Real.pi_lt_four]
  have hpi2 : Real.pi^2≤16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
  have hinv0 : (0 : ℝ)≤1/(M : ℝ) := by positivity
  have hi2 : ((1 : ℝ)/(M : ℝ))^2≤(t/1024)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hi) (by positivity : 0≤t/1024+1/(M : ℝ))]
  have heq : 2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2=
      (2*Real.pi*Real.sqrt (a*(1-a)))*(1/(M : ℝ))+Real.pi^2*(1/(M : ℝ))^2 := by ring
  rw [heq]
  calc
    _ ≤ 8*(1/(M : ℝ))+16*(t/1024)^2 := add_le_add
      (mul_le_mul_of_nonneg_right hc hinv0)
      ((mul_le_mul_of_nonneg_right hpi2 (sq_nonneg _)).trans (mul_le_mul_of_nonneg_left hi2 (by norm_num)))
    _ ≤ 8*(t/1024)+16*(t/1024)^2 := add_le_add (mul_le_mul_of_nonneg_left hi (by norm_num)) (le_refl _)
    _ ≤ t/100 := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]

/-- The restricted-access construction satisfies `block_entry_ae_readout` under the complete displayed premises. -/
theorem block_entry_ae_readout {K I : Type} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) (U : Matrix (K × I) (K × I) ℂ)
    (k0 : K) (i j : I) (a t : ℝ) (M : ℕ) (hM : 2≤M)
    (hb : BlockEncoding T U (encodingFiber k0) (encodingFiber k0) 1 (t/100))
    (hentry : T i j=(a : ℂ)) (ha : 0≤a) (ha1 : a≤1)
    (ht : 0<t) (ht1 : t≤1/4) (hbudget : 1024/t≤(M : ℝ)) :
    let L := aeLaw M U (k0,j) {(k0,i)} hb.unitary hM
    (∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z-a^2|≤t/25),L.prob z)≥8/Real.pi^2 ∧
      aeForwardAccesses (aeAccessWord (I := K × I) M)=M ∧
      aeBackwardAccesses (aeAccessWord (I := K × I) M)=M-1 := by
  let p := MeasureProb (preparedAAState U (k0,j)) {(k0,i)}
  let L := aeLaw M U (k0,j) {(k0,i)} hb.unitary hM
  have hpEq : p=‖U (k0,i) (k0,j)‖^2 := prepared_singleton_probability U _ _
  have hp0 : 0≤p := by rw [hpEq]; positivity
  have hp1 : p≤1 := by
    rw [hpEq]
    have hh := entry_norm_bound_of_unitary hb.unitary (k0,i) (k0,j)
    nlinarith [norm_nonneg (U (k0,i) (k0,j))]
  have herr : |p-a^2|≤3*(t/100) := by
    have hh := block_entry_probability T U (encodingFiber k0) i j a (t/100) hb hentry ha ha1 (by linarith)
    rw [compress_encodingFiber_eq] at hh
    simpa only [hpEq] using hh
  have henv := ae_error_envelope p t M hM hp0 hp1 ht (by linarith) hbudget
  have hbase := (prepared_ae_bhmt_error_and_endpoints M hM U (k0,j) {(k0,i)} hb.unitary).1
  have hsub : (Finset.univ.filter (fun z : Fin M => |aeEstimate M z-p|≤
      2*Real.pi*Real.sqrt (p*(1-p))/(M : ℝ)+Real.pi^2/(M : ℝ)^2))⊆
      Finset.univ.filter (fun z : Fin M => |aeEstimate M z-a^2|≤t/25) := by
    intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    have hh := abs_sub_le (aeEstimate M z) p (a^2)
    linarith [hz.trans henv]
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => L.nonneg z)
  obtain ⟨hf,hbck,_⟩ := prepared_ae_separate_access_counts (I := K × I) M (by omega)
  exact ⟨hbase.trans hmass,hf,hbck⟩

/-- Construction for threshold in the block output readout model. -/
def threshold (t : ℝ) : ℝ := (baseProbability+hiddenProbability t)/2

/-- The restricted-access construction satisfies `baseline_separated` under the complete displayed premises. -/
theorem baseline_separated (t x : ℝ) (ht : 0<t) (ht1 : t≤1/4)
    (hx : |x-baseProbability|≤t/25) : threshold t<x := by
  have hg := target_probability_gap t ht ht1
  have hl := (abs_le.mp hx).1
  dsimp [threshold]
  linarith

/-- The restricted-access construction satisfies `hidden_separated` under the complete displayed premises. -/
theorem hidden_separated (t x : ℝ) (ht : 0<t) (ht1 : t≤1/4)
    (hx : |x-hiddenProbability t|≤t/25) : x<threshold t := by
  have hg := target_probability_gap t ht ht1
  have hu := (abs_le.mp hx).2
  dsimp [threshold]
  linarith

/-- The restricted-access construction satisfies `baseline_ae_decision` under the complete displayed premises. -/
theorem baseline_ae_decision {K I : Type} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) (U : Matrix (K × I) (K × I) ℂ)
    (k0 : K) (i j : I) (t : ℝ) (M : ℕ) (hM : 2≤M)
    (hb : BlockEncoding T U (encodingFiber k0) (encodingFiber k0) 1 (t/100))
    (hentry : T i j=(4/5 : ℂ)) (ht : 0<t) (ht1 : t≤1/4) (hbudget : 1024/t≤(M : ℝ)) :
    let L := aeLaw M U (k0,j) {(k0,i)} hb.unitary hM
    (∑ z ∈ Finset.univ.filter (fun z : Fin M => threshold t<aeEstimate M z),L.prob z)≥8/Real.pi^2 ∧
      aeForwardAccesses (aeAccessWord (I := K × I) M)=M ∧
      aeBackwardAccesses (aeAccessWord (I := K × I) M)=M-1 := by
  let L := aeLaw M U (k0,j) {(k0,i)} hb.unitary hM
  have hentry' : T i j=((4/5 : ℝ) : ℂ) := by simpa using hentry
  obtain ⟨hmass,hf,hbck⟩ := block_entry_ae_readout T U k0 i j (4/5) t M hM hb hentry'
    (by norm_num) (by norm_num) ht ht1 hbudget
  have hsq : (4/5 : ℝ)^2=baseProbability := by norm_num [baseProbability]
  rw [hsq] at hmass
  have hsub : (Finset.univ.filter (fun z : Fin M => |aeEstimate M z-baseProbability|≤t/25))⊆
      Finset.univ.filter (fun z : Fin M => threshold t<aeEstimate M z) := by
    intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact baseline_separated t _ ht ht1 hz
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => L.nonneg z)
  exact ⟨hmass.trans hh,hf,hbck⟩

/-- The restricted-access construction satisfies `hidden_ae_decision` under the complete displayed premises. -/
theorem hidden_ae_decision {K I : Type} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) (U : Matrix (K × I) (K × I) ℂ)
    (k0 : K) (i j : I) (t : ℝ) (M : ℕ) (hM : 2≤M)
    (hb : BlockEncoding T U (encodingFiber k0) (encodingFiber k0) 1 (t/100))
    (hentry : T i j=((4/(5*(1+2*t)) : ℝ) : ℂ))
    (ht : 0<t) (ht1 : t≤1/4) (hbudget : 1024/t≤(M : ℝ)) :
    let L := aeLaw M U (k0,j) {(k0,i)} hb.unitary hM
    (∑ z ∈ Finset.univ.filter (fun z : Fin M => aeEstimate M z<threshold t),L.prob z)≥8/Real.pi^2 ∧
      aeForwardAccesses (aeAccessWord (I := K × I) M)=M ∧
      aeBackwardAccesses (aeAccessWord (I := K × I) M)=M-1 := by
  let L := aeLaw M U (k0,j) {(k0,i)} hb.unitary hM
  have hd : 0<5*(1+2*t) := by positivity
  have ha : 0≤4/(5*(1+2*t)) := by positivity
  have ha1 : 4/(5*(1+2*t))≤1 := by apply (div_le_iff₀ hd).mpr; linarith
  obtain ⟨hmass,hf,hbck⟩ := block_entry_ae_readout T U k0 i j (4/(5*(1+2*t))) t M hM hb hentry
    ha ha1 ht ht1 hbudget
  have hsq : (4/(5*(1+2*t)))^2=hiddenProbability t := by
    dsimp [hiddenProbability]
    rw [div_pow,mul_pow]
    norm_num
  rw [hsq] at hmass
  have hsub : (Finset.univ.filter (fun z : Fin M => |aeEstimate M z-hiddenProbability t|≤t/25))⊆
      Finset.univ.filter (fun z : Fin M => aeEstimate M z<threshold t) := by
    intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact hidden_separated t _ ht ht1 hz
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => L.nonneg z)
  exact ⟨hmass.trans hh,hf,hbck⟩

/-- Construction for dyadic Tau in the block output readout model. -/
def dyadicTau (k : ℕ) : ℝ := 1/(2 : ℝ)^k
/-- Construction for ae Readout Grid in the block output readout model. -/
def aeReadoutGrid (k : ℕ) : ℕ := 2^(k+10)

/-- The restricted-access construction satisfies `dyadic_readout_budget` under the complete displayed premises. -/
theorem dyadic_readout_budget (k : ℕ) (hk : 2≤k) :
    0<dyadicTau k ∧ dyadicTau k≤1/4 ∧ 2≤aeReadoutGrid k ∧
      (aeReadoutGrid k : ℝ)=1024/dyadicTau k := by
  have hp : (0 : ℝ)<2^k := by positivity
  have hp2 : (2 : ℝ)^2≤(2 : ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hp4 : (4 : ℝ)≤2^k := by convert hp2 using 1; norm_num
  have hgrid : 2≤aeReadoutGrid k := by
    exact le_trans (by norm_num : 2≤(2 : ℕ)^1) (Nat.pow_le_pow_right (by decide) (by omega : 1≤k+10))
  refine ⟨by dsimp [dyadicTau]; positivity,?_,hgrid,?_⟩
  · dsimp [dyadicTau]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  · change ((2^(k+10) : ℕ) : ℝ)=1024/(1/(2 : ℝ)^k)
    push_cast
    rw [one_div,div_inv_eq_mul,pow_add]
    norm_num; ring

/-- The restricted-access construction satisfies `baseline_dyadic_decision` under the complete displayed premises. -/
theorem baseline_dyadic_decision {K I : Type} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) (U : Matrix (K × I) (K × I) ℂ)
    (k0 : K) (i j : I) (k : ℕ) (hk : 2≤k)
    (hb : BlockEncoding T U (encodingFiber k0) (encodingFiber k0) 1 (dyadicTau k/100))
    (hentry : T i j=(4/5 : ℂ)) :
    let hM := (dyadic_readout_budget k hk).2.2.1
    let L := aeLaw (aeReadoutGrid k) U (k0,j) {(k0,i)} hb.unitary hM
    (∑ z ∈ Finset.univ.filter (fun z : Fin (aeReadoutGrid k) => threshold (dyadicTau k)<aeEstimate (aeReadoutGrid k) z),L.prob z)≥8/Real.pi^2 ∧
      aeForwardAccesses (aeAccessWord (I := K × I) (aeReadoutGrid k))=aeReadoutGrid k ∧
      aeBackwardAccesses (aeAccessWord (I := K × I) (aeReadoutGrid k))=aeReadoutGrid k-1 := by
  obtain ⟨ht,ht1,hM,hbudget⟩ := dyadic_readout_budget k hk
  exact baseline_ae_decision T U k0 i j (dyadicTau k) (aeReadoutGrid k) hM hb hentry ht ht1 hbudget.symm.le

/-- The restricted-access construction satisfies `hidden_dyadic_decision` under the complete displayed premises. -/
theorem hidden_dyadic_decision {K I : Type} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) (U : Matrix (K × I) (K × I) ℂ)
    (k0 : K) (i j : I) (k : ℕ) (hk : 2≤k)
    (hb : BlockEncoding T U (encodingFiber k0) (encodingFiber k0) 1 (dyadicTau k/100))
    (hentry : T i j=((4/(5*(1+2*dyadicTau k)) : ℝ) : ℂ)) :
    let hM := (dyadic_readout_budget k hk).2.2.1
    let L := aeLaw (aeReadoutGrid k) U (k0,j) {(k0,i)} hb.unitary hM
    (∑ z ∈ Finset.univ.filter (fun z : Fin (aeReadoutGrid k) => aeEstimate (aeReadoutGrid k) z<threshold (dyadicTau k)),L.prob z)≥8/Real.pi^2 ∧
      aeForwardAccesses (aeAccessWord (I := K × I) (aeReadoutGrid k))=aeReadoutGrid k ∧
      aeBackwardAccesses (aeAccessWord (I := K × I) (aeReadoutGrid k))=aeReadoutGrid k-1 := by
  obtain ⟨ht,ht1,hM,hbudget⟩ := dyadic_readout_budget k hk
  exact hidden_ae_decision T U k0 i j (dyadicTau k) (aeReadoutGrid k) hM hb hentry ht ht1 hbudget.symm.le

/-- The restricted-access construction satisfies `ae_access_charge` under the complete displayed premises. -/
theorem ae_access_charge {H : Type} [Fintype H] [DecidableEq H]
    (M q : ℕ) (hM : 0<M) :
    aeForwardAccesses (aeAccessWord (I := H) M)*q+
      aeBackwardAccesses (aeAccessWord (I := H) M)*q=(2*M-1)*q := by
  obtain ⟨hf,hb,_⟩ := prepared_ae_separate_access_counts (I := H) M hM
  rw [hf,hb,←add_mul]
  congr 1
  omega
end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout
