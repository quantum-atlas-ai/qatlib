/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Answer Transport

Compile classical answers by a known angle-dependent map. Neither the map nor the source program may depend on the hidden instance.
-/

open Qatlib Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open scoped BigOperators Classical ComplexOrder
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
/-- Compile classical answers by a known angle-dependent map. Neither the
map nor the source program may depend on the hidden instance. -/
def translateAnswerMap {D R R' : ℕ} (decode : ℝ → Fin R' → Fin R) : Program D R → Program D R'
  | .halt => .halt
  | .query mode next => .query mode (translateAnswerMap decode next)
  | .measure I next => .measure I (fun o => translateAnswerMap decode (next o))
  | .support a next => .support a (fun o => translateAnswerMap decode (next (decode a o)))

/-- Construction for translated Path in the answer transport model. -/
def translatedPath {D R R' : ℕ} (decode : ℝ → Fin R' → Fin R) :
    (P : Program D R) → Path (translateAnswerMap decode P) → Path P
  | .halt, _ => ()
  | .query _ next, p => translatedPath decode next p
  | .measure _ next, p => ⟨p.1,translatedPath decode (next p.1) p.2⟩
  | .support a next, p => ⟨decode a p.1,translatedPath decode (next (decode a p.1)) p.2⟩

/-- The full finite record translation satisfies `translatedPath_charge` without requiring an injective answer map. -/
theorem translatedPath_charge {D R R' : ℕ} (decode : ℝ → Fin R' → Fin R)
    (P : Program D R) (p : Path (translateAnswerMap decode P)) :
    pathCharge (translateAnswerMap decode P) p=pathCharge P (translatedPath decode P p) := by
  induction P with
  | halt => rfl
  | query mode next ih =>
    change ((pathCharge (translateAnswerMap decode next) p).1+1,
      (pathCharge (translateAnswerMap decode next) p).2)=_
    rw [ih p]
    rfl
  | measure I next ih => exact ih p.1 p.2
  | support a next ih =>
    change ((pathCharge (translateAnswerMap decode (next (decode a p.1))) p.2).1,
      (pathCharge (translateAnswerMap decode (next (decode a p.1))) p.2).2+1)=_
    rw [ih (decode a p.1) p.2]
    rfl

/-- The full finite record translation satisfies `translateAnswers_depth` without requiring an injective answer map. -/
theorem translateAnswers_depth {D R R' : ℕ} (decode : ℝ → Fin R' → Fin R)
    (P : Program D R) : queryDepth (translateAnswerMap decode P) ≤ queryDepth P := by
  induction P with
  | halt => exact le_rfl
  | query mode next ih => exact Nat.add_le_add_right ih 1
  | measure I next ih =>
    exact Finset.sup_le fun o ho => (ih o).trans (Finset.le_sup (f := fun x => queryDepth (next x)) (Finset.mem_univ o))
  | support a next ih =>
    exact Finset.sup_le fun o ho => (ih (decode a o)).trans (Finset.le_sup (f := fun x => queryDepth (next x)) (Finset.mem_univ (decode a o)))

/-- The finite protocol identity or bound `support_weight_sum` holds under exactly the displayed hypotheses. -/
private theorem support_weight_sum {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (a : ℝ) (next : Fin R → Program D R) (ρ : Operator D) (f : Path (.support a next) → ℝ) :
    (∑ p,(Matrix.trace (pathMap O S (.support a next) p ρ)).re*f p)=
      ∑ p,(Matrix.trace (pathMap O S (next (S a)) p ρ)).re*f ⟨S a,p⟩ := by
  change (∑ p : (o : Fin R) × Path (next o),
    (Matrix.trace (pathMap O S (.support a next) p ρ)).re*f p)=_
  rw [Fintype.sum_sigma]
  have he (o : Fin R) : (∑ p : Path (next o),
      (Matrix.trace (pathMap O S (.support a next) ⟨o,p⟩ ρ)).re*f ⟨o,p⟩)=
      if o=S a then ∑ p : Path (next o),(Matrix.trace (pathMap O S (next o) p ρ)).re*f ⟨o,p⟩ else 0 := by
    by_cases ho : o=S a
    · simp only [pathMap_support_apply,ho,ite_true]
    · simp only [pathMap_support_apply,ho,ite_false,Matrix.trace_zero,Complex.zero_re,zero_mul,Finset.sum_const_zero]
  simp_rw [he]
  simp

/-- Exact pushforward of actual complete-record laws, allowing a many-to-one
answer map and zero-probability records. No path bijection is asserted. -/
theorem translated_weight_sum {D R R' : ℕ} (decode : ℝ → Fin R' → Fin R)
    (O : Bool → QuantumChannel D D) (S : ℝ → Fin R') (P : Program D R)
    (ρ : Operator D) (f : Path P → ℝ) :
    (∑ q,(Matrix.trace (pathMap O S (translateAnswerMap decode P) q ρ)).re*
      f (translatedPath decode P q))=
    ∑ p,(Matrix.trace (pathMap O (fun a => decode a (S a)) P p ρ)).re*f p := by
  induction P generalizing ρ with
  | halt => rfl
  | query mode next ih =>
    exact ih ((O mode).map ρ) f
  | measure I next ih =>
    change (∑ q : (o : _) × Path (translateAnswerMap decode (next o)),
      (Matrix.trace (pathMap O S (translateAnswerMap decode (next q.1)) q.2 (I.branch q.1 ρ))).re*
      f ⟨q.1,translatedPath decode (next q.1) q.2⟩)=
      ∑ p : (o : _) × Path (next o),
        (Matrix.trace (pathMap O (fun a => decode a (S a)) (next p.1) p.2 (I.branch p.1 ρ))).re*f p
    rw [Fintype.sum_sigma,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro o _
    exact ih o (I.branch o ρ) (fun p => f ⟨o,p⟩)
  | support a next ih =>
    change (∑ q,(Matrix.trace (pathMap O S (.support a (fun o => translateAnswerMap decode (next (decode a o)))) q ρ)).re*
      f ⟨decode a q.1,translatedPath decode (next (decode a q.1)) q.2⟩)=_
    rw [support_weight_sum,support_weight_sum]
    exact ih (decode a (S a)) ρ (fun p => f ⟨decode a (S a),p⟩)

/-- The full finite record translation satisfies `translated_event` without requiring an injective answer map. -/
theorem translated_event {D R R' : ℕ} (decode : ℝ → Fin R' → Fin R)
    (O : Bool → QuantumChannel D D) (S : ℝ → Fin R') (P : Program D R)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1)
    (G : Finset (Path P)) :
    (∑ q∈Finset.univ.filter (fun q => translatedPath decode P q∈G),
      (pathLaw O S (translateAnswerMap decode P) ρ hρ htrace).prob q)=
    ∑ p∈G,(pathLaw O (fun a => decode a (S a)) P ρ hρ htrace).prob p := by
  have he := translated_weight_sum decode O S P ρ (fun p => if p∈G then 1 else 0)
  simp only [pathLaw,Finset.sum_filter]
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_mem,Finset.univ_inter] using he


end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
