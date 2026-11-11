/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.SupportAnswerTransport
import Mathlib.Analysis.SpecificLimits.Normed
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex
import Mathlib.Analysis.Normed.Module.Convex
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

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! Quantitative precision obstruction for the actual finite classical
point-support output model. N=t^12-2 makes the system size exactly t^12;
with t=2^k the unpadded system size is 2^(12k), and with Unit workspace
the oracle size is 2^(12k+2). General workspaces multiply by their cardinality. Actual same-
program correctness forces preparation + returned-word + support query caps
at least t/192192. The real numerical range contains the unit disk and lies
in the radius-3/2 disk, so this family does not hide thin geometric scales.

The uniform contradiction derives the exponential cost from actual per-input
block promises; its only asymptotic upper premise is a claimed eventual
polynomial bound. Finite workspaces and answer alphabets may vary with k.
No original-machine normal form, general-frame/branch-width transport,
expected-budget truncation or given-M impossibility is asserted. Original
G1–G4, known-source attributions and all positive-route obligations remain. -/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol MarkedHalmos
open scoped BigOperators Classical ComplexOrder

/-- Construction for precision Marks in the point support precision lower model. -/
def precisionMarks (t : ℕ) : ℕ := t^12-2
/-- Construction for precision Tau in the point support precision lower model. -/
def precisionTau (t : ℕ) : ℝ := 1/(t : ℝ)^2
/-- Construction for precision Samples in the point support precision lower model. -/
def precisionSamples (t : ℕ) : ℕ := 16*t^4

/-- The restricted-access construction satisfies `precisionMarks_bound` under the complete displayed premises. -/
theorem precisionMarks_bound (t : ℕ) (ht : 2 ≤ t) : t^10 ≤ precisionMarks t := by
  have ht1 : 1 ≤ t := by omega
  have h10 : 1 ≤ t^10 := one_le_pow₀ ht1
  have h2 : 4 ≤ t^2 := by nlinarith
  have he : t^12=t^10*t^2 := by ring
  have hm : 4*t^10 ≤ t^12 := by nlinarith [Nat.mul_le_mul_left (t^10) h2]
  unfold precisionMarks
  omega

/-- The restricted-access construction satisfies `precisionMarks_pos` under the complete displayed premises. -/
theorem precisionMarks_pos (t : ℕ) (ht : 2 ≤ t) : 0<precisionMarks t :=
  (pow_pos (by omega : 0<t) 10).trans_le (precisionMarks_bound t ht)

/-- The restricted-access construction satisfies `precisionMarks_add_two` under the complete displayed premises. -/
theorem precisionMarks_add_two (t : ℕ) (ht : 2 ≤ t) : precisionMarks t+2=t^12 := by
  have h10 : 1 ≤ t^10 := one_le_pow₀ (by omega : 1 ≤ t)
  have h2 : 4 ≤ t^2 := by nlinarith
  have he : t^12=t^10*t^2 := by ring
  have hm : 4*t^10 ≤ t^12 := by nlinarith [Nat.mul_le_mul_left (t^10) h2]
  unfold precisionMarks
  omega

/-- The restricted-access construction satisfies `precisionMarks_sqrt` under the complete displayed premises. -/
theorem precisionMarks_sqrt (t : ℕ) (ht : 2 ≤ t) : (t : ℝ)^5 ≤ Real.sqrt (precisionMarks t) := by
  apply Real.le_sqrt_of_sq_le
  rw [←pow_mul]
  exact_mod_cast precisionMarks_bound t ht

/-- The restricted-access construction satisfies `precisionTau_sqrt` under the complete displayed premises. -/
theorem precisionTau_sqrt (t : ℕ) : Real.sqrt (precisionTau t)=1/(t : ℝ) := by
  unfold precisionTau
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),Real.sqrt_one,Real.sqrt_sq (by positivity)]

/-- The restricted-access construction satisfies `precision_budget` under the complete displayed premises. -/
theorem precision_budget (t : ℕ) (ht : 2 ≤ t) :
    0<precisionTau t ∧ precisionTau t ≤ 1/4 ∧ 0<precisionSamples t ∧
      16/(precisionTau t)^2=(precisionSamples t : ℝ) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ)<t := by positivity
  have htn : t≠0 := by omega
  refine ⟨by unfold precisionTau; positivity,?_,by unfold precisionSamples; positivity,?_⟩
  · unfold precisionTau
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    nlinarith
  · simp only [precisionTau,precisionSamples,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp

/-- The restricted-access construction satisfies `precision_cost_of_budget` under the complete displayed premises. -/
theorem precision_cost_of_budget (t q0 quse s : ℕ) (ht : 2 ≤ t)
    (hb : 1/3 ≤ 4*((1001*(q0+precisionSamples t*quse) : ℕ) : ℝ)/Real.sqrt (precisionMarks t)+
      ((1001*s : ℕ) : ℝ)*(5*Real.sqrt (precisionTau t)+1/(t : ℝ))) :
    (t : ℝ)/192192 ≤ ((q0+quse+s : ℕ) : ℝ) := by
  have ht0 : (0 : ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have h4 : (1 : ℝ) ≤ (t : ℝ)^4 := one_le_pow₀ ht1
  have hsqrt := precisionMarks_sqrt t ht
  have hnum : 0 ≤ 4*((1001*(q0+precisionSamples t*quse) : ℕ) : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_left hnum (pow_pos ht0 5) hsqrt
  have hquant : 4*((1001*(q0+precisionSamples t*quse) : ℕ) : ℝ)/Real.sqrt (precisionMarks t) ≤
      64064*((q0+quse : ℕ) : ℝ)/(t : ℝ) := by
    apply hdiv.trans
    apply (div_le_div_iff₀ (pow_pos ht0 5) ht0).mpr
    simp only [precisionSamples,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    have hq : (q0 : ℝ) ≤ 16*(t : ℝ)^4*q0 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) ht0.le]
  rw [precisionTau_sqrt t] at hb
  have hsupport : ((1001*s : ℕ) : ℝ)*(5*(1/(t : ℝ))+1/(t : ℝ))=
      6006*(s : ℝ)/(t : ℝ) := by push_cast; ring
  rw [hsupport] at hb
  have htotal : 64064*((q0+quse : ℕ) : ℝ)/(t : ℝ)+6006*(s : ℝ)/(t : ℝ) ≤
      64064*((q0+quse+s : ℕ) : ℝ)/(t : ℝ) := by
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ ht0.le
    push_cast
    nlinarith
  have he := hb.trans ((add_le_add hquant le_rfl).trans htotal)
  have hm := (le_div_iff₀ ht0).mp he
  apply (div_le_iff₀ (by norm_num : (0 : ℝ)<192192)).mpr
  linarith

/-- The restricted-access construction satisfies `precision_dimensions` under the complete displayed premises. -/
theorem precision_dimensions (t : ℕ) (ht : 2 ≤ t) :
    Fintype.card (System (precisionMarks t))=t^12 ∧
    queryDim Unit (precisionMarks t)=4*t^12 := by
  have he := precisionMarks_add_two t ht
  constructor
  · simp only [System,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin]
    omega
  · simp only [queryDim,QueryBasis,Basis,Fintype.card_prod,Fintype.card_sum,
      Fintype.card_bool,Fintype.card_fin,Fintype.card_unit,mul_one]
    omega

/-- The restricted-access construction satisfies `precision_two_pow` under the complete displayed premises. -/
theorem precision_two_pow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ (2 : ℕ)^k := by
  have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hk
  simpa using h

/-- The restricted-access construction satisfies `precision_dyadic` under the complete displayed premises. -/
theorem precision_dyadic (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card (System (precisionMarks (2^k)))=2^(12*k) ∧
    queryDim Unit (precisionMarks (2^k))=2^(12*k+2) ∧
    precisionTau (2^k)=Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau (2*k) := by
  have h := precision_dimensions (2^k) (precision_two_pow k hk)
  have hp : ((2 : ℕ)^k)^12=2^(12*k) := by rw [←pow_mul,Nat.mul_comm k 12]
  refine ⟨h.1.trans hp,?_,?_⟩
  · rw [h.2,hp,pow_add]
    norm_num
    ring
  · unfold precisionTau Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau
    push_cast
    rw [←pow_mul,Nat.mul_comm k 2]

/-- Actual per-input output correctness only; no event-law, hybrid or cost
lower bound is included in this promise. The true M remains a specification. -/
def precisionPromise (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R) (normal : ℝ → ℂ)
    (P : Program (queryDim W (precisionMarks t)) R)
    (words : Path P → List (OutputGate (queryDim W (precisionMarks t))))
    (φ : Path P → System (precisionMarks t) → Fin (queryDim W (precisionMarks t)))
    (r0 : Fin (queryDim W (precisionMarks t))) : Prop :=
  constructorPromise (finiteBaseline W (precisionMarks t))
    (finiteBaseline_unitary W (precisionMarks t) (precisionMarks_pos t ht))
    (pointAnswer encode normal (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0)
    P words φ (literalOutput (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0)
      (precisionTau t) r0 ∧
  ∀ h : Fin t × Fin (precisionMarks t),constructorPromise (familyOracle W (precisionTau t) h)
    (familyOracle_unitary W (precisionTau t) (precision_budget t ht).1.le (precision_budget t ht).2.1 h)
    (pointAnswer encode normal h.2 (spikePoint t (precisionTau t) h.1)) P words φ
    (literalOutput h.2 (spikePoint t (precisionTau t) h.1)) (precisionTau t) r0

/-- With N=t^12-2 actual marked locations and true-M literal output accuracy
1/(100*t^2), the constructor preparation, returned-word use and point-support
caps cannot all be small. Correctness is the actual program promise. -/
theorem point_precision_cost_lower (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W (precisionMarks t)) R)
    (words : Path P → List (OutputGate (queryDim W (precisionMarks t))))
    (φ : Path P → System (precisionMarks t) → Fin (queryDim W (precisionMarks t)))
    (r0 : Fin (queryDim W (precisionMarks t))) (quse s : ℕ)
    (hq : ∀ p,wordQueries (words p) ≤ quse) (hs : ∀ p,(pathCharge P p).2 ≤ s)
    (hc : precisionPromise W t ht R encode normal P words φ r0) :
    (t : ℝ)/192192 ≤ ((queryDepth P+quse+s : ℕ) : ℝ) := by
  have hp := precision_budget t ht
  have hb := point_literal_block_output_budget W t (by omega) (precisionMarks t)
    (precisionMarks_pos t ht) (precisionTau t) hp.1 hp.2.1 R encode normal hnormal
    P words φ r0 (precisionSamples t) hp.2.2.1 hp.2.2.2.le quse s hq hs hc.1 hc.2
  exact precision_cost_of_budget t (queryDepth P) quse s ht hb

/-- Pure growth fact used after deriving, rather than assuming, the actual
constructor's exponential lower bound. No restriction on C is needed. -/
theorem exponential_cost_not_polynomial (cost : ℕ → ℕ)
    (hlower : ∀ k,1 ≤ k → (2 : ℝ)^k/192192 ≤ (cost k : ℝ))
    (C : ℝ) (d K : ℕ) (hpoly : ∀ k,K ≤ k → (cost k : ℝ) ≤ C*(k : ℝ)^d) : False := by
  open Filter Topology in
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1 : ℝ)<2)).const_mul (192192*C)
  have he : ∀ᶠ k : ℕ in Filter.atTop,192192*C*((k : ℝ)^d/(2 : ℝ)^k)<1 :=
    hlim.eventually (gt_mem_nhds (by simp))
  obtain ⟨k,⟨hsmall,hk⟩,hkK⟩ := ((he.and (Filter.eventually_ge_atTop 1)).and
    (Filter.eventually_ge_atTop K)).exists
  have hpow : (0 : ℝ)<2^k := by positivity
  have hl := (div_le_iff₀ (by norm_num : (0 : ℝ)<192192)).mp (hlower k hk)
  have hp := hpoly k hkK
  have hm : (2 : ℝ)^k ≤ 192192*C*(k : ℝ)^d := by nlinarith
  have hh : (1 : ℝ) ≤ (192192*C*(k : ℝ)^d)/(2 : ℝ)^k := (one_le_div hpow).mpr hm
  have hsmall' : (192192*C*(k : ℝ)^d)/(2 : ℝ)^k<1 := by
    simpa only [mul_div_assoc] using hsmall
  linarith

/-- Uniform finite known-frame constructors, even with precision-dependent
finite workspace and reply alphabets, cannot satisfy every hard input and
have polynomial total preparation/returned-word/support caps in k. General
machine normalization and expected-budget truncation are not inferred. -/
theorem no_polynomial_point_constructor (W : ℕ → Type)
    [∀ k,Fintype (W k)] [∀ k,DecidableEq (W k)]
    (R : ℕ → ℕ) (encode : ∀ k,ℝ → ℝ → Fin (R k))
    (normal : ℕ → ℝ → ℂ) (hnormal : ∀ k a,‖normal k a‖=1)
    (P : ∀ k,Program (queryDim (W k) (precisionMarks (2^k))) (R k))
    (words : ∀ k,Path (P k) → List (OutputGate (queryDim (W k) (precisionMarks (2^k)))))
    (φ : ∀ k,Path (P k) → System (precisionMarks (2^k)) → Fin (queryDim (W k) (precisionMarks (2^k))))
    (r0 : ∀ k,Fin (queryDim (W k) (precisionMarks (2^k))))
    (quse s : ℕ → ℕ)
    (hq : ∀ k p,wordQueries (words k p) ≤ quse k)
    (hs : ∀ k p,(pathCharge (P k) p).2 ≤ s k)
    (hc : ∀ k (hk : 1 ≤ k),precisionPromise (W k) (2^k) (precision_two_pow k hk)
      (R k) (encode k) (normal k) (P k) (words k) (φ k) (r0 k))
    (C : ℝ) (d K : ℕ)
    (hpoly : ∀ k,K ≤ k → ((queryDepth (P k)+quse k+s k : ℕ) : ℝ) ≤ C*(k : ℝ)^d) : False := by
  apply exponential_cost_not_polynomial (fun k => queryDepth (P k)+quse k+s k) _ C d K hpoly
  intro k hk
  have hb := point_precision_cost_lower (W k) (2^k) (precision_two_pow k hk) (R k)
    (encode k) (normal k) (hnormal k) (P k) (words k) (φ k) (r0 k) (quse k) (s k)
    (hq k) (hs k) (hc k hk)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hb

/-- The hard family does not hide poor inradius or outer-radius parameters:
its TRUE numerical range contains the unit disk and lies in the radius-3/2
disk. This geometry supplies no free description or support advice. -/
theorem precision_geometry (t : ℕ) (ht : 2 ≤ t) (w : Fin (precisionMarks t)) (k : Fin t) :
    Metric.closedBall (0 : ℂ) 1 ⊆ Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w (spikePoint t (precisionTau t) k)) ∧
    Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w (spikePoint t (precisionTau t) k)) ⊆ Metric.closedBall (0 : ℂ) (3/2) := by
  constructor
  · rw [←convexHull_sphere_eq_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1)]
    apply convexHull_min _ (Qatlib.Foundations.OpCalculus.ContourCalc.numericalRange_convex (Matrix.toEuclideanCLM (𝕜 := ℂ) (target w (spikePoint t (precisionTau t) k))))
    intro u hu
    apply target_unit_point
    simpa only [Metric.mem_sphere,dist_zero_right] using hu
  · intro u hu
    have hb := (spike_actual_maximum w (precisionTau t) k (precision_budget t ht).1.le).2 ⟨u,hu,rfl⟩
    have ht1 := (precision_budget t ht).2.1
    change dist u 0 ≤ 3/2
    rw [dist_zero_right]
    linarith

end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
