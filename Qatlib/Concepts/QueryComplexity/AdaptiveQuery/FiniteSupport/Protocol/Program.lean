/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
/-! Finite adaptive quantum-instrument protocols with classical support queries.
Paths are syntax-indexed and retain zero-weight outcomes. The selected CP maps
are compiled by recursion and assemble into an actual Instrument; their raw
trace masses define the full transcript law. No postselection is used.

This establishes the operational no-hit agreement and adaptive support union
bound. It does not derive the marked-input-oracle hybrid, geometric visibility,
a universal finite normal form, or a whole block-output lower bound. -/
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder

/-- Construction for selector in the program model. -/
private def selector {D R : ℕ} (a : Fin R) : Instrument (Fin R) D D :=
  let K := fun o : Fin R => if o=a then (1 : Operator D) else 0
  Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofKraus K (by
    have he (o : Fin R) : (K o).conjTranspose*K o=if o=a then (1 : Operator D) else 0 := by
      by_cases ho : o=a <;> simp [K,ho]
    simp_rw [he]
    simp)

/-- Finite classical support requests, general fixed finite instruments, and
an explicit query tag. Oracle channels are interpreted separately from syntax. -/
inductive Program (D R : ℕ) : Type where
  | halt : Program D R
  | query (mode : Bool) (next : Program D R) : Program D R
  | measure {s : ℕ} (I : Instrument (Fin s) D D) (next : Fin s → Program D R) : Program D R
  | support (angle : ℝ) (next : Fin R → Program D R) : Program D R

/-- Construction for Path in the program model. -/
def Path {D R : ℕ} : Program D R → Type
  | .halt => Unit
  | .query _ next => Path next
  | .measure (s := s) _ next => (o : Fin s) × Path (next o)
  | .support _ next => (o : Fin R) × Path (next o)

/-- Typeclass instance for path Fintype in the program model. -/
instance pathFintype {D R : ℕ} (P : Program D R) : Fintype (Path P) := by
  induction P with
  | halt => exact inferInstanceAs (Fintype Unit)
  | query _ _ ih => exact ih
  | measure I next ih => exact @Sigma.instFintype _ _ ih inferInstance
  | support angle next ih => exact @Sigma.instFintype _ _ ih inferInstance

/-- Construction for requests in the program model. -/
def requests {D R : ℕ} : (P : Program D R) → Path P → List ℝ
  | .halt, _ => []
  | .query _ next, p => requests next p
  | .measure _ next, p => requests (next p.1) p.2
  | .support a next, p => a :: requests (next p.1) p.2

/-- Construction for path Map in the program model. -/
def pathMap {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R) :
    (P : Program D R) → Path P → (Operator D →ₗ[ℂ] Operator D)
  | .halt, _ => LinearMap.id
  | .query mode next, p => (pathMap O S next p).comp (O mode).map
  | .measure I next, p => (pathMap O S (next p.1) p.2).comp (I.branch p.1)
  | .support a next, p => (pathMap O S (next p.1) p.2).comp ((selector (D := D) (S a)).branch p.1)

/-- The finite protocol map `pathMap_support_apply` preserves the stated branch semantics or positivity property. -/
theorem pathMap_support_apply {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (a : ℝ) (next : Fin R → Program D R) (p : Path (.support a next)) (ρ : Operator D) :
    pathMap O S (.support a next) p ρ=
      if p.1=S a then pathMap O S (next p.1) p.2 ρ else 0 := by
  change pathMap O S (next p.1) p.2 ((selector (D := D) (S a)).branch p.1 ρ)=_
  by_cases hp : p.1=S a <;> simp [selector,Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofKraus_branch,hp]

/-- The finite protocol map `pathMap_cp` preserves the stated branch semantics or positivity property. -/
theorem pathMap_cp {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (p : Path P) : CompletelyPositive (pathMap O S P p) := by
  induction P with
  | halt => exact (Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel.id D).completelyPositive
  | query mode next ih => exact (ih p).comp (O mode).completelyPositive
  | measure I next ih => exact (ih p.1 p.2).comp (I.cp p.1)
  | support a next ih => exact (ih p.1 p.2).comp ((selector (D := D) (S a)).cp p.1)

/-- Summing all actual finite protocol branches preserves the input trace, including zero-mass outcomes. -/
theorem path_trace_total {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (ρ : Operator D) :
    (∑ p : Path P,Matrix.trace (pathMap O S P p ρ))=Matrix.trace ρ := by
  induction P generalizing ρ with
  | halt =>
    change (∑ _ : Unit, Matrix.trace ρ) = Matrix.trace ρ
    simp
  | query mode next ih =>
    change (∑ p : Path next,Matrix.trace (pathMap O S next p ((O mode).map ρ)))=_
    rw [ih,(O mode).tracePreserving]
  | measure I next ih =>
    change (∑ p : (o : _) × Path (next o), Matrix.trace (pathMap O S (next p.1) p.2 (I.branch p.1 ρ)))=_
    rw [Fintype.sum_sigma]
    simp_rw [ih]
    rw [←Matrix.trace_sum]
    exact I.total ρ
  | support a next ih =>
    change (∑ p : (o : _) × Path (next o), Matrix.trace (pathMap O S (next p.1) p.2 ((selector (D := D) (S a)).branch p.1 ρ)))=_
    rw [Fintype.sum_sigma]
    simp_rw [ih]
    rw [←Matrix.trace_sum]
    exact (selector (D := D) (S a)).total ρ

/-- Construction for path Instrument in the program model. -/
def pathInstrument {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) : Instrument (Path P) D D :=
  Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofBranches (pathMap O S P) (pathMap_cp O S P) (by
    intro ρ
    rw [Matrix.trace_sum]
    exact path_trace_total O S P ρ)

/-- The finite protocol identity or bound `path_mass_total` holds under exactly the displayed hypotheses. -/
theorem path_mass_total {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (ρ : Operator D) :
    (∑ p : Path P,(Matrix.trace (pathMap O S P p ρ)).re)=(Matrix.trace ρ).re := by
  rw [←Complex.re_sum,path_trace_total]

/-- Construction for path Law in the program model. -/
def pathLaw {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (P : Program D R) (ρ : Operator D) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1) : FinDist (Path P) where
  prob p := (Matrix.trace (pathMap O S P p ρ)).re
  nonneg p := (RCLike.nonneg_iff.mp (((pathMap_cp O S P p).positive hρ).trace_nonneg)).1
  sum_one := (path_mass_total O S P ρ).trans htrace

/-- No coupling or equality of final laws is assumed. Selected CP maps agree
because the same syntactic path makes only equal classical support requests.
Quantum measurements and all zero-weight counterfactual branches are retained. -/
theorem pathMap_nohit {D R : ℕ} (O : Bool → QuantumChannel D D) (S B : ℝ → Fin R)
    (P : Program D R) (p : Path P) (hn : ∀ a∈requests P p,S a=B a) :
    pathMap O S P p=pathMap O B P p := by
  induction P with
  | halt => rfl
  | query mode next ih => exact congrArg (fun L => L.comp (O mode).map) (ih p hn)
  | measure I next ih => exact congrArg (fun L => L.comp (I.branch p.1)) (ih p.1 p.2 hn)
  | support a next ih =>
    have ha : S a=B a := hn a (by simp [requests])
    have ht : ∀ b∈requests (next p.1) p.2,S b=B b := by
      intro b hb
      exact hn b (by simp [requests,hb])
    change (pathMap O S (next p.1) p.2).comp _=(pathMap O B (next p.1) p.2).comp _
    rw [ih p.1 p.2 ht,ha]


/-- A hit is determined from the analysis-only hidden instance and the full
syntactic request path, including zero branches; it is not just an output event. -/
def hitSet {D R : ℕ} (P : Program D R) (bad : ℝ → Prop) : Finset (Path P) :=
  Finset.univ.filter (fun p => ∃ a∈requests P p,bad a)

/-- The finite protocol identity or bound `nohit_variation` holds under exactly the displayed hypotheses. -/
theorem nohit_variation {D R : ℕ} (O : Bool → QuantumChannel D D) (S B : ℝ → Fin R)
    (P : Program D R) (ρ : Operator D) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1)
    (bad : ℝ → Prop) (hS : ∀ a, ¬bad a → S a=B a) :
    (∑ p,|(pathLaw O S P ρ hρ htrace).prob p-(pathLaw O B P ρ hρ htrace).prob p|)/2≤
      ∑ p∈hitSet P bad,(pathLaw O B P ρ hρ htrace).prob p := by
  apply Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.first_hit_variation
  intro p hp
  have hn : ∀ a∈requests P p,S a=B a := by
    intro a ha
    apply hS a
    intro hb
    exact hp (by simp [hitSet]; exact ⟨a,ha,hb⟩)
  change (Matrix.trace (pathMap O S P p ρ)).re=(Matrix.trace (pathMap O B P p ρ)).re
  rw [pathMap_nohit O S B P p hn]



/-- Construction for joint Hit Set in the program model. -/
def jointHitSet {H : Type} [Fintype H] {D R : ℕ}
    (P : Program D R) (bad : H → ℝ → Prop) : Finset (H × Path P) :=
  Finset.univ.filter (fun hp => ∃ a∈requests P hp.2,bad hp.1 a)

/-- The operational outside-hit equality for the complete finite-instrument
model is derived here. The sole remaining distance premise concerns the
actual input-oracle hybrid, not classical support coupling. -/
theorem joint_first_hit_hybrid {H : Type} [Fintype H] [DecidableEq H] {D R : ℕ}
    (μ : FinDist H) (O : H → Bool → QuantumChannel D D) (O0 : Bool → QuantumChannel D D)
    (S : H → ℝ → Fin R) (B : ℝ → Fin R) (P : Program D R)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1)
    (bad : H → ℝ → Prop) (hS : ∀ h a,¬bad h a → S h a=B a) (δ v : ℝ)
    (hd : (∑ h,μ.prob h*((∑ p,|(pathLaw (O h) B P ρ hρ htrace).prob p-
      (pathLaw O0 B P ρ hρ htrace).prob p|)/2))≤δ)
    (hv : (∑ hp∈jointHitSet P bad,(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ
      (fun _ => pathLaw O0 B P ρ hρ htrace)).prob hp)≤v) :
    (∑ hp,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun h => pathLaw (O h) (S h) P ρ hρ htrace)).prob hp-
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => pathLaw O0 B P ρ hρ htrace)).prob hp|)/2≤2*δ+v := by
  apply Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.joint_first_hit_bound μ
    (fun h => pathLaw (O h) (S h) P ρ hρ htrace)
    (fun h => pathLaw (O h) B P ρ hρ htrace)
    (fun _ => pathLaw O0 B P ρ hρ htrace) (jointHitSet P bad) δ v hd hv
  intro hp hn
  have he : ∀ a∈requests P hp.2,S hp.1 a=B a := by
    intro a ha
    apply hS hp.1 a
    intro hb
    exact hn (by simp [jointHitSet]; exact ⟨a,ha,hb⟩)
  dsimp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw,pathLaw]
  rw [pathMap_nohit (O hp.1) (S hp.1) B P hp.2 he]

/-- Query/support charges are counted along the same full syntax path,
including counterfactual branches. They are not quantum gate or bit time. -/
def pathCharge {D R : ℕ} : (P : Program D R) → Path P → ℕ × ℕ
  | .halt, _ => (0,0)
  | .query _ next, p => ((pathCharge next p).1+1,(pathCharge next p).2)
  | .measure _ next, p => pathCharge (next p.1) p.2
  | .support _ next, p => ((pathCharge (next p.1) p.2).1,(pathCharge (next p.1) p.2).2+1)

/-- The finite protocol identity or bound `support_charge_eq_requests_length` holds under exactly the displayed hypotheses. -/
theorem support_charge_eq_requests_length {D R : ℕ} (P : Program D R) (p : Path P) :
    (pathCharge P p).2=(requests P p).length := by
  induction P with
  | halt => rfl
  | query mode next ih => exact ih p
  | measure I next ih => exact ih p.1 p.2
  | support a next ih =>
    change (pathCharge (next p.1) p.2).2+1=(requests (next p.1) p.2).length+1
    rw [ih p.1 p.2]



/-- The finite protocol identity or bound `request_union_bound` holds under exactly the displayed hypotheses. -/
private theorem request_union_bound {H : Type} [Fintype H] (μ : FinDist H)
    (bad : H → ℝ → Prop) (v : ℝ)
    (hv : ∀ a,(∑ h∈Finset.univ.filter (fun h => bad h a),μ.prob h)≤v) (l : List ℝ) :
    (∑ h,if ∃ a∈l,bad h a then μ.prob h else 0)≤(l.length : ℝ)*v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hp (h : H) : (if ∃ b∈a::l,bad h b then μ.prob h else 0)≤
        (if bad h a then μ.prob h else 0)+(if ∃ b∈l,bad h b then μ.prob h else 0) := by
      by_cases ha : bad h a <;> by_cases hl : ∃ b∈l,bad h b <;>
        simp [ha,hl,μ.nonneg h]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hp h)
    rw [Finset.sum_add_distrib] at hs
    have hf : (∑ h,if bad h a then μ.prob h else 0)≤v := by
      simpa only [Finset.sum_filter] using hv a
    have hc : ((a::l).length : ℝ)=(l.length : ℝ)+1 := by simp
    rw [hc]
    nlinarith

/-- Baseline paths are independent of the hidden parameter. This supplies the
adaptive support union bound from actual recorded requests and a one-angle
visibility bound, without assuming independence between successive requests. -/
theorem baseline_hit_bound {H : Type} [Fintype H] {D R : ℕ}
    (μ : FinDist H) (P : Program D R) (L : FinDist (Path P)) (bad : H → ℝ → Prop)
    (s : ℕ) (v : ℝ) (hv : ∀ a,(∑ h∈Finset.univ.filter (fun h => bad h a),μ.prob h)≤v)
    (hc : ∀ p : Path P, (pathCharge P p).2 ≤ s) :
    (∑ hp∈jointHitSet P bad,(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => L)).prob hp)≤(s : ℝ)*v := by
  have hv0 : 0≤v := (Finset.sum_nonneg (fun h _ => μ.nonneg h)).trans (hv 0)
  have he : (∑ hp∈jointHitSet P bad,(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => L)).prob hp)=
      ∑ p,L.prob p*(∑ h,if ∃ a∈requests P p,bad h a then μ.prob h else 0) := by
    simp only [jointHitSet,Finset.sum_filter,Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> ring
  rw [he]
  calc
    _ ≤ ∑ p,L.prob p*((s : ℝ)*v) := by
      apply Finset.sum_le_sum
      intro p _
      have hh := request_union_bound μ bad v hv (requests P p)
      have hlen : ((requests P p).length : ℝ)≤ s := by
        exact_mod_cast (show (requests P p).length≤ s from (support_charge_eq_requests_length P p) ▸ hc p)
      exact mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_right hlen hv0)) (L.nonneg p)
    _ = (s : ℝ)*v := by rw [←Finset.sum_mul,L.sum_one,one_mul]



/-- The full finite-instrument support argument, with both no-hit agreement
and the adaptive union bound derived from execution. The input-oracle hybrid
and the geometric one-angle visibility estimate are still explicit premises. -/
theorem finite_protocol_support_bound {H : Type} [Fintype H] [DecidableEq H] {D R : ℕ}
    (μ : FinDist H) (O : H → Bool → QuantumChannel D D) (O0 : Bool → QuantumChannel D D)
    (S : H → ℝ → Fin R) (B : ℝ → Fin R) (P : Program D R)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1)
    (bad : H → ℝ → Prop) (hS : ∀ h a,¬bad h a → S h a=B a)
    (δ v : ℝ) (s : ℕ)
    (hd : (∑ h,μ.prob h*((∑ p,|(pathLaw (O h) B P ρ hρ htrace).prob p-
      (pathLaw O0 B P ρ hρ htrace).prob p|)/2))≤δ)
    (hv : ∀ a,(∑ h∈Finset.univ.filter (fun h => bad h a),μ.prob h)≤v)
    (hc : ∀ p : Path P, (pathCharge P p).2 ≤ s) :
    (∑ hp,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun h => pathLaw (O h) (S h) P ρ hρ htrace)).prob hp-
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => pathLaw O0 B P ρ hρ htrace)).prob hp|)/2≤2*δ+(s : ℝ)*v := by
  exact joint_first_hit_hybrid μ O O0 S B P ρ hρ htrace bad hS δ ((s : ℝ)*v) hd
    (baseline_hit_bound μ P (pathLaw O0 B P ρ hρ htrace) bad s v hv hc)

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
