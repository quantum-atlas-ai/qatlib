/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.PointSupportPrecisionLower
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

/-! An explicit linear-bit classical point-support reply rule for the actual
precision obstruction. Offset fixed-point encoding uses only the known
scale-two support interval [-2,2], not M or hidden matrix data. On that
interval there is no modular wrap and the decoded error is <2^(-b).
Choosing b=2k+7 gives 2k+10 total reply bits and error <tau/100 on the actual
hard family. The uniform lower theorem is specialized to this same rule.

This is an oracle reply specification and accuracy proof, not a circuit
for computing support from an unknown matrix, a finite runtime guarantee
for real-number floor, or an arbitrary-algorithm normal form. -/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol MarkedHalmos
open scoped BigOperators Classical ComplexOrder

/-- Specified offset fixed-point reply with b fractional bits and three
integer bits. The known input scale two supplies the interval [-2,2], and
no hidden matrix data or free M is used by the encoding rule. -/
def supportBits (b : ℕ) (_a x : ℝ) : Fin (2^(b+3)) :=
  Fin.ofNat (2^(b+3)) ⌊(2 : ℝ)^b*(x+2)⌋₊

/-- Construction for support Value in the point support bits model. -/
def supportValue (b : ℕ) (l : Fin (2^(b+3))) : ℝ := (l : ℝ)/(2 : ℝ)^b-2

/-- The restricted-access construction satisfies `supportBits_accuracy` under the complete displayed premises. -/
theorem supportBits_accuracy (b : ℕ) (a x : ℝ) (hx : -2 ≤ x) (hx1 : x ≤ 2) :
    |supportValue b (supportBits b a x)-x|<1/(2 : ℝ)^b := by
  have h2 : (0 : ℝ)<2^b := by positivity
  have hs : 0 ≤ (2 : ℝ)^b*(x+2) := mul_nonneg h2.le (by linarith)
  have hr : (2 : ℝ)^b*(x+2)<((2^(b+3) : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]
    norm_num
    nlinarith
  have hfloor : ⌊(2 : ℝ)^b*(x+2)⌋₊<2^(b+3) := (Nat.floor_lt hs).mpr hr
  have hval : (supportBits b a x).val=⌊(2 : ℝ)^b*(x+2)⌋₊ := by
    simp only [supportBits,Fin.val_ofNat,Nat.mod_eq_of_lt hfloor]
  have hf := Nat.floor_le hs
  have hnext := Nat.lt_floor_add_one ((2 : ℝ)^b*(x+2))
  unfold supportValue
  rw [show ((supportBits b a x : Fin (2^(b+3))) : ℝ)=(⌊(2 : ℝ)^b*(x+2)⌋₊ : ℝ) by exact_mod_cast hval]
  have he : (⌊(2 : ℝ)^b*(x+2)⌋₊ : ℝ)/(2 : ℝ)^b-2-x=
      (⌊(2 : ℝ)^b*(x+2)⌋₊ : ℝ)/(2 : ℝ)^b-(x+2) := by ring
  rw [he,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ h2).mpr (by nlinarith [hf])))]
  apply (lt_div_iff₀ h2).mpr
  nlinarith [(div_mul_cancel₀ (⌊(2 : ℝ)^b*(x+2)⌋₊ : ℝ) h2.ne')]

/-- The restricted-access construction satisfies `precision_support_interval` under the complete displayed premises. -/
theorem precision_support_interval (t : ℕ) (ht : 2 ≤ t) (w : Fin (precisionMarks t))
    (k : Fin t) (u : ℂ) (hu : ‖u‖=1) :
    0 ≤ actualSupport w (spikePoint t (precisionTau t) k) u ∧
      actualSupport w (spikePoint t (precisionTau t) k) u ≤ 3/2 := by
  rw [spike_support_value w (precisionTau t) k u hu]
  have hp := precision_budget t ht
  have hreal : (star u*gridPhase t k).re ≤ 1 := by
    calc
      _ ≤ ‖star u*gridPhase t k‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_mul,norm_star,hu,gridPhase_norm]; norm_num
  constructor
  · exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  · apply max_le (by norm_num)
    have he := mul_le_mul_of_nonneg_left hreal (by linarith [hp.1] : 0 ≤ 1+2*precisionTau t)
    nlinarith [hp.2.1]

/-- Reply length 2k+10 is linear in k. Its actual fixed-point decoded answer
has error strictly below the block-output accuracy tau/100. -/
theorem dyadic_support_accuracy (k : ℕ) (hk : 1 ≤ k) (w : Fin (precisionMarks (2^k)))
    (j : Fin (2^k)) (a : ℝ) (u : ℂ) (hu : ‖u‖=1) :
    |supportValue (2*k+7) (supportBits (2*k+7) a
        (actualSupport w (spikePoint (2^k) (precisionTau (2^k)) j) u))-
      actualSupport w (spikePoint (2^k) (precisionTau (2^k)) j) u|<precisionTau (2^k)/100 := by
  have hi := precision_support_interval (2^k) (precision_two_pow k hk) w j u hu
  have he := supportBits_accuracy (2*k+7) a
    (actualSupport w (spikePoint (2^k) (precisionTau (2^k)) j) u) (by linarith [hi.1]) (by linarith [hi.2])
  have hsmall : 1/(2 : ℝ)^(2*k+7)<precisionTau (2^k)/100 := by
    unfold precisionTau
    push_cast
    rw [pow_add]
    have hp : (0 : ℝ)<2^(2*k) := by positivity
    rw [←pow_mul,Nat.mul_comm k 2]
    norm_num
    field_simp
    nlinarith
  exact he.trans hsmall

/-- The restricted-access construction satisfies `baseline_support_accuracy` under the complete displayed premises. -/
theorem baseline_support_accuracy (b : ℕ) {N : ℕ} (w : Fin N) (a : ℝ) (u : ℂ) (hu : ‖u‖=1) :
    |supportValue b (supportBits b a (actualSupport w 0 u))-actualSupport w 0 u|<1/(2 : ℝ)^b := by
  have he : actualSupport w 0 u=1 := by rw [actualSupport_eq w 0 u hu]; simp
  rw [he]
  exact supportBits_accuracy b a 1 (by norm_num) (by norm_num)

/-- The uniform obstruction for this explicitly certified linear-bit reply
rule, not merely an arbitrary finite alphabet. Error is certified separately
by supportBits_accuracy and dyadic_support_accuracy on the actual true support. -/
theorem no_polynomial_rounded_point_constructor (W : ℕ → Type)
    [∀ k,Fintype (W k)] [∀ k,DecidableEq (W k)]
    (normal : ℕ → ℝ → ℂ) (hnormal : ∀ k a,‖normal k a‖=1)
    (P : ∀ k,Program (queryDim (W k) (precisionMarks (2^k))) (2^(2*k+10)))
    (words : ∀ k,Path (P k) → List (OutputGate (queryDim (W k) (precisionMarks (2^k)))))
    (φ : ∀ k,Path (P k) → System (precisionMarks (2^k)) → Fin (queryDim (W k) (precisionMarks (2^k))))
    (r0 : ∀ k,Fin (queryDim (W k) (precisionMarks (2^k))))
    (quse s : ℕ → ℕ)
    (hq : ∀ k p,wordQueries (words k p) ≤ quse k)
    (hs : ∀ k p,(pathCharge (P k) p).2 ≤ s k)
    (hc : ∀ k (hk : 1 ≤ k),precisionPromise (W k) (2^k) (precision_two_pow k hk)
      (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (P k) (words k) (φ k) (r0 k))
    (C : ℝ) (d K : ℕ)
    (hpoly : ∀ k,K ≤ k → ((queryDepth (P k)+quse k+s k : ℕ) : ℝ) ≤ C*(k : ℝ)^d) : False :=
  no_polynomial_point_constructor W (fun k => 2^(2*k+10)) (fun k => supportBits (2*k+7)) normal hnormal
    P words φ r0 quse s hq hs hc C d K hpoly

end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
