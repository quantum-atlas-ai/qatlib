/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.MixedInstrumentClock
import Qatlib.Concepts.AdversaryBounds.AdvDuality.StoppingReferenceTransport
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorLeft
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MixedInstrument.ClockBridge

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
open Matrix
open scoped Classical ComplexOrder BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

variable {C L O : Type} [Fintype L] {D : ℕ}

def Leaf (dest : C→L→O⊕C) : ℕ→C→Type
  | 0,_ => Unit
  | n+1,c => (l : L) × (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c')

@[reducible] def leafFintype (dest : C→L→O⊕C) : (n : ℕ) → (c : C) → Fintype (Leaf dest n c)
  | 0,_ => inferInstanceAs (Fintype Unit)
  | n+1,c => by
    change Fintype ((l : L) × (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c'))
    letI : ∀ l : L, Fintype (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c') :=
      fun l => match dest c l with
        | .inl _ => inferInstanceAs (Fintype Unit)
        | .inr c' => leafFintype dest n c'
    infer_instance

instance (dest : C→L→O⊕C) (n : ℕ) (c : C) : Fintype (Leaf dest n c) := leafFintype dest n c

@[reducible] def childFintype (dest : C→L→O⊕C) (n : ℕ) (b : O⊕C) :
    Fintype (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') :=
  match b with
  | .inl _ => inferInstanceAs (Fintype Unit)
  | .inr c' => leafFintype dest n c'

def identityInstrument (D : ℕ) : Instrument Unit D D :=
  Instrument.ofKraus (fun _ => (1 : Operator D)) (by simp)

@[simp] theorem identityInstrument_branch (ρ : Operator D) : (identityInstrument D).branch () ρ=ρ := by
  simp [identityInstrument,Instrument.ofKraus_branch]

def pathInstrument (I : C→Instrument L D D) (dest : C→L→O⊕C) :
    (n : ℕ) → (c : C) → Instrument (Leaf dest n c) D D
  | 0,_ => identityInstrument D
  | n+1,c => by
    letI : ∀ l : L, Fintype (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c') :=
      fun l => childFintype dest n (dest c l)
    exact (I c).feedForward (fun l => match (motive := ∀ b : O⊕C,
        @Instrument (match b with | .inl _ => Unit | .inr c' => Leaf dest n c')
          (childFintype dest n b) D D) dest c l with
      | .inl _ => identityInstrument D
      | .inr c' => pathInstrument I dest n c')

def leafResult (dest : C→L→O⊕C) : (n : ℕ)→(c : C)→Leaf dest n c→O⊕C
  | 0,c,_ => .inr c
  | n+1,c,⟨l,p⟩ =>
    (match (motive := ∀ b : O⊕C, (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → O⊕C) dest c l with
      | .inl out => fun _ => .inl out
      | .inr c' => leafResult dest n c') p

def leafCharge (dest : C→L→O⊕C) (price : C→L→ℕ) : (n : ℕ)→(c : C)→Leaf dest n c→ℕ
  | 0,_,_ => 0
  | n+1,c,⟨l,p⟩ => price c l +
    (match (motive := ∀ b : O⊕C, (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ℕ) dest c l with
      | .inl _ => fun _ => 0
      | .inr c' => leafCharge dest price n c') p

def leafHistory (dest : C→L→O⊕C) : (n : ℕ)→(c : C)→Leaf dest n c→List L
  | 0,_,_ => []
  | n+1,c,⟨l,p⟩ => l::
    (match (motive := ∀ b : O⊕C, (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → List L) dest c l with
      | .inl _ => fun _ => []
      | .inr c' => leafHistory dest n c') p

def pathPost (I : C→Instrument L D D) (dest : C→L→O⊕C) :
    (n : ℕ)→(c : C)→ClockDensity D→Leaf dest n c→ClockDensity D
  | 0,_,ρ,_ => ρ
  | n+1,c,ρ,⟨l,p⟩ =>
    (match (motive := ∀ b : O⊕C, (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ClockDensity D) dest c l with
      | .inl _ => fun _ => clockConditional (I c) ρ l
      | .inr c' => pathPost I dest n c' (clockConditional (I c) ρ l)) p

def pathProbability (I : C→Instrument L D D) (dest : C→L→O⊕C) :
    (n : ℕ)→(c : C)→ClockDensity D→Leaf dest n c→ℝ
  | 0,_,_,_ => 1
  | n+1,c,ρ,⟨l,p⟩ => instrumentProb (I c) ρ.val l *
    (match (motive := ∀ b : O⊕C, (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ℝ) dest c l with
      | .inl _ => fun _ => 1
      | .inr c' => pathProbability I dest n c' (clockConditional (I c) ρ l)) p

theorem path_reconstruct (I : C→Instrument L D D) (dest : C→L→O⊕C)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (p : Leaf dest n c) :
    (pathProbability I dest n c ρ p : ℂ) • (pathPost I dest n c ρ p).val =
      (pathInstrument I dest n c).branch p ρ.val := by
  induction n generalizing c ρ with
  | zero => cases p; simp [pathProbability,pathPost,pathInstrument]
  | succ n ih =>
    obtain ⟨l,p⟩ := p
    simp only [pathProbability,pathPost,pathInstrument,Instrument.feedForward,LinearMap.comp_apply]
    rw [← clockConditional_reconstruct (I c) ρ l, map_smul]
    let J (b : O⊕C) : @Instrument
        (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') (childFintype dest n b) D D :=
      match b with | .inl _ => identityInstrument D | .inr c' => pathInstrument I dest n c'
    have hchild (b : O⊕C) (q : match b with | .inl _ => Unit | .inr c' => Leaf dest n c') :
        ((instrumentProb (I c) ρ.val l *
          (match (motive := ∀ b : O⊕C, (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ℝ) b with
            | .inl _ => fun _ => 1
            | .inr c' => pathProbability I dest n c' (clockConditional (I c) ρ l)) q : ℝ) : ℂ) •
          ((match (motive := ∀ b : O⊕C, (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ClockDensity D) b with
            | .inl _ => fun _ => clockConditional (I c) ρ l
            | .inr c' => pathPost I dest n c' (clockConditional (I c) ρ l)) q).val =
          (instrumentProb (I c) ρ.val l : ℂ) •
            (@Instrument.branch _ (childFintype dest n b) D D (J b) q (clockConditional (I c) ρ l).val) := by
      cases b with
      | inl out => cases q; simp only [J,identityInstrument_branch,mul_one]
      | inr c' =>
        dsimp only [J]
        rw [Complex.ofReal_mul,mul_smul,ih c' (clockConditional (I c) ρ l) q]
    exact hchild (dest c l) p

theorem pathProbability_eq (I : C→Instrument L D D) (dest : C→L→O⊕C)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (p : Leaf dest n c) :
    pathProbability I dest n c ρ p = instrumentProb (pathInstrument I dest n c) ρ.val p := by
  have h := congrArg Matrix.trace (path_reconstruct I dest n c ρ p)
  rw [Matrix.trace_smul,(pathPost I dest n c ρ p).property.2,smul_eq_mul,mul_one] at h
  exact congrArg Complex.re h

theorem path_conditional (I : C→Instrument L D D) (dest : C→L→O⊕C)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (p : Leaf dest n c)
    (hp : 0 < instrumentProb (pathInstrument I dest n c) ρ.val p) :
    (pathInstrument I dest n c).conditionalState ρ.val p hp = (pathPost I dest n c ρ p).val := by
  rw [Instrument.conditionalState,← path_reconstruct, pathProbability_eq]
  have hn : (instrumentProb (pathInstrument I dest n c) ρ.val p : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hp
  rw [smul_smul,inv_mul_cancel₀ hn,one_smul]

open Qatlib

def leafRecord (dest : C→L→O⊕C) (price : C→L→ℕ) (n : ℕ) (c : C) (p : Leaf dest n c) : (O⊕C)×ℕ :=
  (leafResult dest n c p,leafCharge dest price n c p)

def finiteEventMap (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) : Operator D→ₗ[ℂ]Operator D :=
  eventBranchMap (pathInstrument I dest n c) (fun p => Ev (leafRecord dest price n c p))

def finiteEventProb (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : Operator D) (Ev : (O⊕C)×ℕ→Prop) : ℝ :=
  eventProb (pathInstrument I dest n c) ρ (fun p => Ev (leafRecord dest price n c p))

def finitePost (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : Operator D) (Ev : (O⊕C)×ℕ→Prop) : Operator D :=
  normalizedPost (pathInstrument I dest n c) ρ (fun p => Ev (leafRecord dest price n c p))

theorem finitePost_path_mixture (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (Ev : (O⊕C)×ℕ→Prop) :
    finitePost I dest price n c ρ.val Ev =
      ∑ p ∈ Finset.univ.filter (fun p => Ev (leafRecord dest price n c p)),
        if 0 < pathProbability I dest n c ρ p then
          ((pathProbability I dest n c ρ p / finiteEventProb I dest price n c ρ.val Ev : ℝ) : ℂ) •
            (pathPost I dest n c ρ p).val
        else 0 := by
  rw [finitePost,walkGoal_mixture _ _ _ _ _ ρ.property]
  apply Finset.sum_congr rfl
  intro p _
  rw [pathProbability_eq]
  split_ifs with h
  · rw [path_conditional I dest n c ρ p h]
    rfl
  · rfl

theorem finite_event_correspondence (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (Ev : (O⊕C)×ℕ→Prop) :
    finiteEventMap I dest price n c Ev ρ.val =
      (finiteEventProb I dest price n c ρ.val Ev : ℂ) • finitePost I dest price n c ρ.val Ev ∧
    (Matrix.trace (finiteEventMap I dest price n c Ev ρ.val)).re = finiteEventProb I dest price n c ρ.val Ev ∧
    (finiteEventProb I dest price n c ρ.val Ev=0 →
      finiteEventMap I dest price n c Ev ρ.val=0 ∧ finitePost I dest price n c ρ.val Ev=0) ∧
    (0 < finiteEventProb I dest price n c ρ.val Ev → IsDensityOperator (finitePost I dest price n c ρ.val Ev)) :=
  walkGoal_correspondence _ _ _ _ _ ρ.property _

theorem finite_event_cp (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) : CompletelyPositive (finiteEventMap I dest price n c Ev) := by
  unfold finiteEventMap eventBranchMap
  apply CompletelyPositive.sum
  intro p _
  exact (pathInstrument I dest n c).cp p

theorem finite_event_tni (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) : TraceNonIncreasing (finiteEventMap I dest price n c Ev) := by
  intro ρ hρ
  simp only [finiteEventMap,eventBranchMap,LinearMap.sum_apply,Matrix.trace_sum,Complex.re_sum]
  change (∑ p ∈ Finset.univ.filter (fun p => Ev (leafRecord dest price n c p)),
    instrumentProb (pathInstrument I dest n c) ρ p) ≤ (Matrix.trace ρ).re
  rw [← sum_instrumentProb (pathInstrument I dest n c) ρ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => instrumentProb_nonneg (pathInstrument I dest n c) hρ p)

theorem finiteEventMap_succ (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) :
    finiteEventMap I dest price (n+1) c Ev =
      ∑ l : L, match dest c l with
        | .inl out => if Ev (.inl out,price c l) then (I c).branch l else 0
        | .inr c' => (finiteEventMap I dest price n c' (fun z => Ev (z.1,price c l+z.2))).comp ((I c).branch l) := by
  apply LinearMap.ext
  intro ρ
  simp only [finiteEventMap,eventBranchMap,LinearMap.sum_apply,Finset.sum_filter]
  letI : ∀ l : L, Fintype (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c') :=
    fun l => childFintype dest n (dest c l)
  change (∑ p : (l : L) × (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c'),
    (if Ev (leafRecord dest price (n+1) c p) then (pathInstrument I dest (n+1) c).branch p else 0) ρ) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l _
  let J (b : O⊕C) : @Instrument
      (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') (childFintype dest n b) D D :=
    match b with | .inl _ => identityInstrument D | .inr c' => pathInstrument I dest n c'
  let R (b : O⊕C) : (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → O⊕C :=
    match b with | .inl out => fun _ => .inl out | .inr c' => leafResult dest n c'
  let K (b : O⊕C) : (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ℕ :=
    match b with | .inl _ => fun _ => 0 | .inr c' => leafCharge dest price n c'
  have hchild (b : O⊕C) :
      (∑ p ∈ @Finset.univ (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') (childFintype dest n b),
        if Ev (R b p,price c l+K b p) then
          @Instrument.branch _ (childFintype dest n b) D D (J b) p ((I c).branch l ρ) else 0) =
        (match b with
          | .inl out => if Ev (.inl out,price c l) then (I c).branch l ρ else 0
          | .inr c' => finiteEventMap I dest price n c' (fun z => Ev (z.1,price c l+z.2)) ((I c).branch l ρ)) := by
    cases b with
    | inl out => simp [J,R,K,identityInstrument_branch]
    | inr c' =>
      dsimp only [J,R,K]
      simp only [finiteEventMap,eventBranchMap,LinearMap.sum_apply,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      dsimp only [leafRecord]
      change (if Ev (leafResult dest n c' p,price c l+leafCharge dest price n c' p) then _ else _) = _
      split_ifs <;> rfl
  convert! hchild (dest c l) using 1
  · apply Finset.sum_congr rfl
    intro p _
    dsimp only [J,R,K,leafRecord,leafResult,leafCharge,pathInstrument,Instrument.feedForward]
    split_ifs <;> rfl
  · cases he : dest c l with
    | inl out => (try dsimp only); split_ifs <;> rfl
    | inr c' =>
      (try dsimp only)
      simp only [finiteEventMap,eventBranchMap,LinearMap.sum_apply,Finset.sum_filter,LinearMap.comp_apply]

theorem finite_event_mixedHaltMap [DecidableEq O] (I : C→Instrument L D D) (dest : C→L→O⊕C)
    (price : C→L→ℕ) (n : ℕ) (c : C) (o : O) (k : ℕ) :
    finiteEventMap I dest price n c (fun z => z=(Sum.inl o,k)) = mixedHaltMap I dest price n c o k := by
  induction n generalizing c k with
  | zero =>
    simp only [finiteEventMap,eventBranchMap,Finset.sum_filter]
    change (∑ p : Leaf dest 0 c,
      if leafRecord dest price 0 c p=(Sum.inl o,k) then (pathInstrument I dest 0 c).branch p else 0)=0
    apply Finset.sum_eq_zero
    intro p _
    simp [leafRecord,leafResult,leafCharge]
  | succ n ih =>
    apply LinearMap.ext
    intro ρ
    simp only [finiteEventMap,eventBranchMap,LinearMap.sum_apply,Finset.sum_filter]
    letI : ∀ l : L, Fintype (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c') :=
      fun l => childFintype dest n (dest c l)
    change (∑ p : (l : L) × (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c'),
      (if leafRecord dest price (n+1) c p=(Sum.inl o,k) then
        (pathInstrument I dest (n+1) c).branch p else 0) ρ) = _
    rw [Fintype.sum_sigma]
    simp only [mixedHaltMap,LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro l _
    let J (b : O⊕C) : @Instrument
        (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') (childFintype dest n b) D D :=
      match b with | .inl _ => identityInstrument D | .inr c' => pathInstrument I dest n c'
    let R (b : O⊕C) : (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → O⊕C :=
      match b with | .inl out => fun _ => .inl out | .inr c' => leafResult dest n c'
    let K (b : O⊕C) : (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ℕ :=
      match b with | .inl _ => fun _ => 0 | .inr c' => leafCharge dest price n c'
    have hchild (b : O⊕C) :
        (∑ p ∈ @Finset.univ (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') (childFintype dest n b),
          if (R b p,price c l+K b p)=(Sum.inl o,k) then
            @Instrument.branch _ (childFintype dest n b) D D (J b) p ((I c).branch l ρ) else 0) =
          (if price c l≤k then match b with
            | .inl out => if out=o ∧ price c l=k then (I c).branch l ρ else 0
            | .inr c' => mixedHaltMap I dest price n c' o (k-price c l) ((I c).branch l ρ)
          else 0) := by
      cases b with
      | inl out =>
        dsimp only [J,R,K]
        by_cases hfit : price c l≤k
        · simp [hfit,identityInstrument_branch]
        · have hk : price c l≠k := by omega
          simp [hfit,hk]
      | inr c' =>
        dsimp only [J,R,K]
        by_cases hfit : price c l≤k
        · rw [if_pos hfit]
          have hc (p : Leaf dest n c') : price c l+leafCharge dest price n c' p=k ↔
              leafCharge dest price n c' p=k-price c l := by omega
          have hh :=
              congrArg (fun T : Operator D→ₗ[ℂ]Operator D => T ((I c).branch l ρ))
              (ih c' (k-price c l))
          simp only [finiteEventMap,eventBranchMap,LinearMap.sum_apply,Finset.sum_filter] at hh
          rw [← hh]
          apply Finset.sum_congr rfl
          intro p _
          by_cases hz : leafRecord dest price n c' p=(Sum.inl o,k-price c l)
          · rw [if_pos hz]
            have hz' : (leafResult dest n c' p,price c l+leafCharge dest price n c' p)=(Sum.inl o,k) := by
              have hz1 := congrArg Prod.fst hz
              have hz2 := congrArg Prod.snd hz
              apply Prod.ext
              · exact hz1
              · exact (hc p).mpr hz2
            rw [if_pos hz']
          · rw [if_neg hz]
            have hz' : ¬ (leafResult dest n c' p,price c l+leafCharge dest price n c' p)=(Sum.inl o,k) := by
              intro hh
              apply hz
              change (leafResult dest n c' p,leafCharge dest price n c' p)=(Sum.inl o,k-price c l)
              have hh1 := congrArg (fun z : (O⊕C)×ℕ => z.1) hh
              have hh2 := congrArg (fun z : (O⊕C)×ℕ => z.2) hh
              exact Prod.ext hh1 ((hc p).mp hh2)
            simp only [if_neg hz',LinearMap.zero_apply]
        · rw [if_neg hfit]
          apply Finset.sum_eq_zero
          intro p _
          have hbad : ¬ (leafResult dest n c' p,price c l+leafCharge dest price n c' p)=(Sum.inl o,k) := by
            intro hz
            have hcost := congrArg Prod.snd hz
            omega
          simp only [if_neg hbad]
    convert! hchild (dest c l) using 1
    · apply Finset.sum_congr rfl
      intro p _
      dsimp only [J,R,K,leafRecord,leafResult,leafCharge,pathInstrument,Instrument.feedForward]
      split_ifs <;> rfl
    · by_cases hfit : price c l≤k
      · simp only [if_pos hfit]
        cases he : dest c l with
        | inl out => (try dsimp only); split_ifs <;> rfl
        | inr c' => rfl
      · simp only [if_neg hfit,LinearMap.zero_apply]

def haltPredicate (E : O×ℕ→Prop) (z : (O⊕C)×ℕ) : Prop :=
  match z.1 with | .inl o => E (o,z.2) | .inr _ => False

def finiteHaltEvent (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (E : O×ℕ→Prop) : Operator D→ₗ[ℂ]Operator D :=
  finiteEventMap I dest price n c (haltPredicate E)

theorem finiteHaltEvent_zero (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) : finiteHaltEvent I dest price 0 c E=0 := by
  simp only [finiteHaltEvent,finiteEventMap,eventBranchMap,Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro p _
  simp [haltPredicate,leafRecord,leafResult]

theorem finiteHaltEvent_succ (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (E : O×ℕ→Prop) :
    finiteHaltEvent I dest price (n+1) c E =
      ∑ l : L, match dest c l with
        | .inl out => if E (out,price c l) then (I c).branch l else 0
        | .inr c' => (finiteHaltEvent I dest price n c' (fun z => E (z.1,price c l+z.2))).comp ((I c).branch l) := by
  rw [finiteHaltEvent,finiteEventMap_succ]
  apply Finset.sum_congr rfl
  intro l _
  cases he : dest c l <;> rfl

def exactEventLayer (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ) :
    ℕ→C→(O×ℕ→Prop)→(Operator D→ₗ[ℂ]Operator D)
  | 0,c,E => ∑ l : L, match dest c l with
      | .inl out => if E (out,price c l) then (I c).branch l else 0
      | .inr _ => 0
  | n+1,c,E => ∑ l : L, match dest c l with
      | .inl _ => 0
      | .inr c' => (exactEventLayer I dest price n c' (fun z => E (z.1,price c l+z.2))).comp ((I c).branch l)

theorem cp_zero : CompletelyPositive (0 : Operator D→ₗ[ℂ]Operator D) := by
  intro r X _
  change (0 : Matrix (Fin r×Fin D) (Fin r×Fin D) ℂ).PosSemidef
  exact Matrix.PosSemidef.zero

theorem exactEventLayer_cp (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (E : O×ℕ→Prop) : CompletelyPositive (exactEventLayer I dest price n c E) := by
  induction n generalizing c E with
  | zero =>
    simp only [exactEventLayer]
    apply CompletelyPositive.sum
    intro l _
    cases he : dest c l with
    | inl out =>
      (try dsimp only)
      split_ifs
      · exact (I c).cp l
      · exact cp_zero
    | inr c' => exact cp_zero
  | succ n ih =>
    simp only [exactEventLayer]
    apply CompletelyPositive.sum
    intro l _
    cases he : dest c l with
    | inl out => exact cp_zero
    | inr c' => exact (ih c' (fun z => E (z.1,price c l+z.2))).comp ((I c).cp l)

theorem exactEventLayer_sum (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (N : ℕ) (c : C) (E : O×ℕ→Prop) :
    (∑ n ∈ Finset.range N, exactEventLayer I dest price n c E) = finiteHaltEvent I dest price N c E := by
  induction N generalizing c E with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,finiteHaltEvent_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ',finiteHaltEvent_succ]
    simp only [exactEventLayer]
    rw [Finset.sum_comm,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    cases dest c l with
    | inl out => simp
    | inr c' =>
      apply LinearMap.ext
      intro ρ
      have hh := congrArg (fun T : Operator D→ₗ[ℂ]Operator D => T ((I c).branch l ρ))
        (ih c' (fun z => E (z.1,price c l+z.2)))
      simpa only [add_zero,LinearMap.sum_apply,LinearMap.comp_apply] using! hh

theorem exactEventLayer_bound (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) :
    MixedClockSeries.TraceSeriesBound (fun n => exactEventLayer I dest price n c E) := by
  intro N ρ hρ
  have hh := congrArg (fun T : Operator D→ₗ[ℂ]Operator D => (Matrix.trace (T ρ)).re)
    (exactEventLayer_sum I dest price N c E)
  (try dsimp only at hh)
  rw [LinearMap.sum_apply,Matrix.trace_sum,Complex.re_sum] at hh
  rw [hh]
  exact finite_event_tni I dest price N c (haltPredicate E) hρ

def haltEventLimit (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) : Operator D→ₗ[ℂ]Operator D :=
  MixedClockSeries.cpSeriesLimit (fun n => exactEventLayer I dest price n c E)
    (fun n => exactEventLayer_cp I dest price n c E) (exactEventLayer_bound I dest price c E)

theorem haltEventLimit_cp (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) : CompletelyPositive (haltEventLimit I dest price c E) :=
  MixedClockSeries.cpSeriesLimit_completelyPositive _ _ _

theorem haltEventLimit_tendsto (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (ρ : Operator D) :
    Filter.Tendsto (fun N => finiteHaltEvent I dest price N c E ρ) Filter.atTop
      (nhds (haltEventLimit I dest price c E ρ)) := by
  have h := MixedClockSeries.cpSeriesLimit_tendsto (fun n => exactEventLayer I dest price n c E)
    (fun n => exactEventLayer_cp I dest price n c E) (exactEventLayer_bound I dest price c E) ρ
  simpa only [← LinearMap.sum_apply,exactEventLayer_sum] using! h

theorem haltEventLimit_tni (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) : TraceNonIncreasing (haltEventLimit I dest price c E) := by
  intro ρ hρ
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_matrix_trace (haltEventLimit_tendsto I dest price c E ρ))
  apply le_of_tendsto h
  exact Filter.Eventually.of_forall fun N => finite_event_tni I dest price N c (haltPredicate E) hρ

theorem haltEventLimit_reference_tendsto (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (R : ℕ) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) :
    Filter.Tendsto (fun N => tensorLeft (finiteHaltEvent I dest price N c E) X) Filter.atTop
      (nhds (tensorLeft (haltEventLimit I dest price c E) X)) := by
  rw [tendsto_matrix_iff_entrywise]
  intro x y
  exact (tendsto_matrix_iff_entrywise.mp
    (haltEventLimit_tendsto I dest price c E (fun i j => X (i,x.2) (j,y.2)))) x.1 y.1

end
end Qatlib.Concepts.MbqcFlow.FlowDecision
