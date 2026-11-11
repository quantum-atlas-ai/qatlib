/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.BlockOutputSupportLower
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TranslatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
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

open Qatlib.Concepts.AdaptiveCP.BranchTrace
/-! Classical finite point-answer transport for the actual literal output
lower bound. A fixed angle-dependent answer map compiles finite programs;
complete record laws push forward exactly despite many-to-one decoding.
All path charges and known returned words/frames are retained, while depth
can only decrease. Actual true support values are then encoded by any known
deterministic finite rule, including a fixed b-bit rounding rule.

No finite-cost implementation of real decoding, arbitrary-machine normal
form, variable-width/general-frame transport or expected-budget truncation
is asserted. Strong labels are classical, never coherent. No free M, global
boundary descriptor, matrix advice, relaxed output scale or original G1–G4
completion is inferred. -/

set_option autoImplicit false
noncomputable section


open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol MarkedHalmos
open scoped BigOperators Classical ComplexOrder


/-- A deterministic finite classical encoding of each true point support
value. Taking R=2^b includes a fixed b-bit rounding rule. This does not allow
matrix-dependent advice hidden in a choice of approximate answers. -/
def pointAnswer {N R : ℕ} (encode : ℝ → ℝ → Fin R) (normal : ℝ → ℂ)
    (w : Fin N) (z : ℂ) (a : ℝ) : Fin R := encode a (actualSupport w z (normal a))

/-- The actual literal output tradeoff for finite classical point answers.
A stronger-label execution simulates the specified known point encoding with
one support call, retaining its complete output law, good mass and query caps. -/
theorem point_literal_block_output_budget (W : Type) [Fintype W] [DecidableEq W]
    (H : ℕ) (hH : 0<H) (N : ℕ) (hN : 0<N) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (R : ℕ) (encode : ℝ → ℝ → Fin R)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W N) R)
    (words : Path P → List (OutputGate (queryDim W N)))
    (φ : Path P → System N → Fin (queryDim W N)) (r0 : Fin (queryDim W N))
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ)) (quse s : ℕ)
    (hq : ∀ p,wordQueries (words p) ≤ quse) (hs : ∀ p,(pathCharge P p).2 ≤ s)
    (hbase : constructorPromise (finiteBaseline W N) (finiteBaseline_unitary W N hN)
      (pointAnswer encode normal (⟨0,hN⟩ : Fin N) 0)
      P words φ (literalOutput (⟨0,hN⟩ : Fin N) 0) τ r0)
    (hhidden : ∀ h : Fin H × Fin N,constructorPromise (familyOracle W τ h)
      (familyOracle_unitary W τ hτ.le hτ1 h)
      (pointAnswer encode normal h.2 (spikePoint H τ h.1))
      P words φ (literalOutput h.2 (spikePoint H τ h.1)) τ r0) :
    1/3 ≤ 4*((1001*(queryDepth P+n*quse) : ℕ) : ℝ)/Real.sqrt N+
      ((1001*s : ℕ) : ℝ)*(5*Real.sqrt τ+1/(H : ℝ)) := by
  let decode := fun a l => encode a (decodeLabel H τ (normal a) l)
  let Q := translateAnswerMap decode P
  let wQ := fun q => words (translatedPath decode P q)
  let fQ := fun q => φ (translatedPath decode P q)
  have hb0 : (fun a => decode a (0 : Fin (H+1)))=
      pointAnswer encode normal (⟨0,hN⟩ : Fin N) 0 := by
    funext a
    exact congrArg (encode a) (decode_zero_is_baseline (⟨0,hN⟩ : Fin N) τ (normal a) (hnormal a))
  have hb : constructorPromise (finiteBaseline W N) (finiteBaseline_unitary W N hN) (fun _ => 0)
      Q wQ fQ (literalOutput (⟨0,hN⟩ : Fin N) 0) τ r0 := by
    apply translated_constructorPromise decode
    rw [hb0]
    exact hbase
  have hh : ∀ h : Fin H × Fin N,constructorPromise (familyOracle W τ h)
      (familyOracle_unitary W τ hτ.le hτ1 h) (labelResponse τ normal h)
      Q wQ fQ (literalOutput h.2 (spikePoint H τ h.1)) τ r0 := by
    intro h
    apply translated_constructorPromise decode
    have he : (fun a => decode a (labelResponse τ normal h a))=
        pointAnswer encode normal h.2 (spikePoint H τ h.1) := by
      funext a
      exact congrArg (encode a) (label_decode_exact τ normal h a (hnormal a))
    rw [he]
    exact hhidden h
  have hqQ : ∀ q,wordQueries (wQ q) ≤ quse := fun q => hq (translatedPath decode P q)
  have hsQ : ∀ q,(pathCharge Q q).2 ≤ s := by
    intro q
    change (pathCharge (translateAnswerMap decode P) q).2 ≤ s
    rw [translatedPath_charge]
    exact hs (translatedPath decode P q)
  have ht := literal_block_output_budget W H hH N hN τ hτ hτ1 normal hnormal Q wQ fQ r0
    n hn hbudget quse s hqQ hsQ hb hh
  have hd : ((1001*(queryDepth Q+n*quse) : ℕ) : ℝ) ≤ (1001*(queryDepth P+n*quse) : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left 1001 (Nat.add_le_add_right (translateAnswers_depth decode P) (n*quse))
  have he := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4)) (Real.sqrt_nonneg (N : ℝ))
  exact ht.trans (add_le_add he le_rfl)

end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
