/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainderDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMixedState
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabularyDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace CoinCode
variable {α : Type}

def paths : CoinCode α → List (α × List Bool)
  | .ret a => [(a, [])]
  | .bit p q => (p.paths.map (fun z => (z.1, false :: z.2))) ++
      (q.paths.map (fun z => (z.1, true :: z.2)))

noncomputable def wordWeight (w : List Bool) : ℝ := (1 / 2 : ℝ) ^ w.length
end CoinCode

structure FairFeedback (D : ℕ) (A : Type) where
  first : ObservedCircuit (Fin D)
  choose : Fin (observedLeafCount first) → CoinCode A
  next : (i : Fin (observedLeafCount first)) → A → ObservedCircuit (Fin D)

structure FairFeedbackRecord (A : Type) where
  value : A
  prefixAccepted : Bool
  accepted : Bool
  coinWord : List Bool
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  prefixBorn : List (ℕ × ℕ)
  suffixBorn : List (ℕ × ℕ)

namespace FairFeedback
variable {D : ℕ} {A : Type}

def path (M : FairFeedback D A) (i : Fin (observedLeafCount M.first))
    (c : Fin (M.choose i).paths.length) : A × List Bool :=
  (M.choose i).paths.get c

abbrev Outcome (M : FairFeedback D A) :=
  Σ i : Fin (observedLeafCount M.first), Σ c : Fin (M.choose i).paths.length,
    Fin (observedLeafCount (M.next i (M.path i c).1))

def codeWord (M : FairFeedback D A) (z : M.Outcome) : List Bool :=
  (M.path z.1 z.2.1).2

noncomputable def prefixLeaf (M : FairFeedback D A) (O : Operator D)
    (i : Fin (observedLeafCount M.first)) : ObservedKrausLeaf D := observedLeaf O M.first i

noncomputable def suffixLeaf (M : FairFeedback D A) (O : Operator D)
    (z : M.Outcome) : ObservedKrausLeaf D :=
  observedLeaf O (M.next z.1 (M.path z.1 z.2.1).1) z.2.2

noncomputable def record (M : FairFeedback D A) (O : Operator D) (z : M.Outcome) :
    FairFeedbackRecord A :=
  let p := M.prefixLeaf O z.1
  let s := M.suffixLeaf O z
  ⟨(M.path z.1 z.2.1).1, p.accepted, s.accepted, M.codeWord z,
    p.queries + s.queries, p.gates + s.gates, p.measurements + s.measurements,
    p.outcomes, s.outcomes⟩

noncomputable def kraus (M : FairFeedback D A) (O : Operator D) (z : M.Outcome) : Operator D :=
  ((Real.sqrt (CoinCode.wordWeight (M.codeWord z)) : ℝ) : ℂ) •
    ((M.suffixLeaf O z).operator * (M.prefixLeaf O z.1).operator)

def Legal (M : FairFeedback D A) : Prop :=
  observedWellFormed M.first ∧ ∀ i a, observedWellFormed (M.next i a)

end FairFeedback

def measuredFeedbackFirst : ObservedCircuit (Fin 2) :=
  .measure 2 (fun i => i) (fun o => .halt (o == 1))

def measuredFeedbackCoins (i : Fin 2) : CoinCode (Option (Fin 2) × ℕ) :=
  if i = 0 then weightedTrial (fun j : Fin 2 => if j = 0 then 1 else 0) 0
  else weightedTrial (fun _ : Fin 2 => 1) 1

noncomputable def measuredFeedbackFlip : Operator 2 :=
    Qatlib.Concepts.GateVocabulary.GateVocab.toFinGate PauliX

noncomputable def measuredFeedbackNext (i : Fin 2) (a : Option (Fin 2) × ℕ) :
    ObservedCircuit (Fin 2) :=
  if i = 0 then .step (.gate measuredFeedbackFlip) (.halt true)
  else if a.1 = some 0 then .step (.gate Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin) (.halt true)
  else if a.1 = some 1 then .step .query (.halt false)
  else .halt false

noncomputable def measuredFeedback : FairFeedback 2 (Option (Fin 2) × ℕ) where
  first := measuredFeedbackFirst
  choose i := measuredFeedbackCoins i
  next i a := measuredFeedbackNext i a

noncomputable def measuredFeedbackInput : Operator 2 := ((1 / 2 : ℝ) : ℂ) • (1 : Operator 2)

def measuredFeedbackZero : measuredFeedback.Outcome :=
  ⟨⟨0, by decide +kernel⟩, ⟨0, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩
def measuredFeedbackHadamard : measuredFeedback.Outcome :=
  ⟨⟨1, by decide +kernel⟩, ⟨0, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩
def measuredFeedbackQuery : measuredFeedback.Outcome :=
  ⟨⟨1, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩

inductive HybridProgram (D : ℕ) (A : Type) where
  | ret : A → HybridProgram D A
  | step : Step (Fin D) → HybridProgram D A → HybridProgram D A
  | bit : HybridProgram D A → HybridProgram D A → HybridProgram D A
  | measure (n : ℕ) (label : Fin D → Fin n) (next : Fin n → HybridProgram D A) : HybridProgram D A
  | project : Operator D → HybridProgram D A → HybridProgram D A → HybridProgram D A

inductive HybridEvent where
  | query
  | gate
  | bit : Bool → HybridEvent
  | born : ℕ → ℕ → HybridEvent
  deriving DecidableEq, Repr

structure HybridCounts where
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  reads : ℕ
  deriving DecidableEq, Repr

namespace HybridCounts
def zero : HybridCounts := ⟨0,0,0,0⟩
def plus (a b : HybridCounts) : HybridCounts :=
  ⟨a.queries + b.queries,a.gates + b.gates,a.measurements + b.measurements,a.reads + b.reads⟩
end HybridCounts

structure HybridLeaf (D : ℕ) (A : Type) where
  value : A
  operator : Operator D
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  coins : List Bool
  born : List (ℕ × ℕ)
  history : List HybridEvent

namespace HybridLeaf
variable {D : ℕ} {A : Type}

def counts (t : HybridLeaf D A) : HybridCounts :=
  ⟨t.queries,t.gates,t.measurements,t.coins.length⟩

noncomputable def quantum (U : Operator D) (q g m : ℕ) (out : List (ℕ × ℕ))
    (leaf : HybridLeaf D A) : HybridLeaf D A :=
  { leaf with
    operator := leaf.operator * U
    queries := leaf.queries + q
    gates := leaf.gates + g
    measurements := leaf.measurements + m
    born := out ++ leaf.born
    history := List.replicate q .query ++ List.replicate g .gate ++
      out.map (fun z => .born z.1 z.2) ++ leaf.history }

def coin (b : Bool) (leaf : HybridLeaf D A) : HybridLeaf D A :=
  { leaf with coins := b :: leaf.coins, history := .bit b :: leaf.history }

noncomputable def effect (leaf : HybridLeaf D A) : Operator D :=
  ((CoinCode.wordWeight leaf.coins : ℝ) : ℂ) • (leaf.operator.conjTranspose * leaf.operator)

noncomputable def kraus (leaf : HybridLeaf D A) : Operator D :=
  ((Real.sqrt (CoinCode.wordWeight leaf.coins) : ℝ) : ℂ) • leaf.operator

noncomputable def toObserved {D : ℕ} (t : HybridLeaf D Bool) : ObservedKrausLeaf D :=
  ⟨t.operator,t.value,t.queries,t.gates,t.measurements,t.born⟩

noncomputable def join {B : Type} (a : HybridLeaf D A) (b : HybridLeaf D B) : HybridLeaf D B :=
  ⟨b.value,b.operator * a.operator,b.queries + a.queries,b.gates + a.gates,
    b.measurements + a.measurements,a.coins ++ b.coins,a.born ++ b.born,a.history ++ b.history⟩

end HybridLeaf

namespace HybridProgram
variable {D : ℕ} {A B : Type}

def bind : HybridProgram D A → (A → HybridProgram D B) → HybridProgram D B
  | .ret a, k => k a
  | .step s p, k => .step s (p.bind k)
  | .bit p q, k => .bit (p.bind k) (q.bind k)
  | .measure n label next, k => .measure n label (fun i => (next i).bind k)
  | .project P p q, k => .project P (p.bind k) (q.bind k)

def ofCoins (p : CoinCode B) (k : B → HybridProgram D A) : HybridProgram D A :=
  match p with
  | .ret a => k a
  | .bit p q => .bit (ofCoins p k) (ofCoins q k)

def Frontier : HybridProgram D A → Prop
  | .bit _ _ => False
  | _ => True

def runCoins : List Bool → HybridProgram D A → HybridProgram D A × ℕ
  | [], p => (p,0)
  | b :: bs, .bit p q =>
      let z := runCoins bs (if b then q else p)
      (z.1, 1 + z.2)
  | _ :: _, p => (p,0)

def ofObserved : ObservedCircuit (Fin D) → HybridProgram D Bool
  | .halt b => .ret b
  | .step s p => .step s (ofObserved p)
  | .measure n label next => .measure n label (fun i => ofObserved (next i))
  | .project P p q => .project P (ofObserved p) (ofObserved q)

def prependCircuit : Circuit (Fin D) → HybridProgram D A → HybridProgram D A
  | [], p => p
  | s :: C, p => .step s (prependCircuit C p)

def cut : ℕ → HybridProgram D A → HybridProgram D (A ⊕ HybridProgram D A)
  | 0, .ret a => .ret (.inl a)
  | 0, p => .ret (.inr p)
  | _ + 1, .ret a => .ret (.inl a)
  | n + 1, .step s p => .step s (cut n p)
  | n + 1, .bit p q => .bit (cut n p) (cut n q)
  | n + 1, .measure m label next => .measure m label (fun i => cut n (next i))
  | n + 1, .project P p q => .project P (cut n p) (cut n q)

noncomputable def leaves (O : Operator D) : HybridProgram D A → List (HybridLeaf D A)
  | .ret a => [⟨a,1,0,0,0,[],[],[]⟩]
  | .step (.gate U) p => (p.leaves O).map (HybridLeaf.quantum U 0 1 0 [])
  | .step .query p => (p.leaves O).map (HybridLeaf.quantum O 1 0 0 [])
  | .bit p q => (p.leaves O).map (HybridLeaf.coin false) ++ (q.leaves O).map (HybridLeaf.coin true)
  | .measure n label next =>
      (List.ofFn (fun i : Fin n => ((next i).leaves O).map
        (HybridLeaf.quantum (Projector (Finset.univ.filter fun x => label x = i)) 0 0 1 [(n,i.val)]))).flatten
  | .project P p q => (p.leaves O).map (HybridLeaf.quantum (1 - P) 0 0 1 [(2,0)]) ++
      (q.leaves O).map (HybridLeaf.quantum P 0 0 1 [(2,1)])

def leafCount : HybridProgram D A → ℕ
  | .ret _ => 1
  | .step _ p => p.leafCount
  | .bit p q => p.leafCount + q.leafCount
  | .measure n _ next => ∑ i : Fin n, (next i).leafCount
  | .project _ p q => p.leafCount + q.leafCount

def Legal : HybridProgram D A → Prop
  | .ret _ => True
  | .step (.gate U) p => U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ p.Legal
  | .step .query p => p.Legal
  | .bit p q => p.Legal ∧ q.Legal
  | .measure _ _ next => ∀ i, (next i).Legal
  | .project P p q => IsOrthogonalProjector P ∧ p.Legal ∧ q.Legal

def cutQueries : ℕ → HybridProgram D A → HybridProgram D (A ⊕ HybridProgram D A)
  | _, .ret a => .ret (.inl a)
  | n, .step (.gate U) p => .step (.gate U) (cutQueries n p)
  | 0, .step .query p => .ret (.inr (.step .query p))
  | n + 1, .step .query p => .step .query (cutQueries n p)
  | n, .bit p q => .bit (cutQueries n p) (cutQueries n q)
  | n, .measure m label k => .measure m label (fun i => cutQueries n (k i))
  | n, .project P p q => .project P (cutQueries n p) (cutQueries n q)

noncomputable def eval (O : Operator D) : HybridProgram D A → QState (Fin D) →
    (A → QState (Fin D) → ℝ) → ℝ
  | .ret a, ψ, F => F a ψ
  | .step (.gate U) p, ψ, F => eval O p (ApplyGate U ψ) F
  | .step .query p, ψ, F => eval O p (ApplyGate O ψ) F
  | .bit p q, ψ, F => (1/2 : ℝ) * (eval O p ψ F + eval O q ψ F)
  | .measure n label k, ψ, F => ∑ i : Fin n, eval O (k i) (Collapse ψ (Finset.univ.filter fun x => label x = i)) F
  | .project P p q, ψ, F => eval O p (ApplyGate (1 - P) ψ) F + eval O q (ApplyGate P ψ) F

noncomputable def evalCounts (O : Operator D) : HybridProgram D A → QState (Fin D) → HybridCounts →
    (A → QState (Fin D) → HybridCounts → ℝ) → ℝ
  | .ret a,ψ,c,F => F a ψ c
  | .step (.gate U) p,ψ,c,F => evalCounts O p (ApplyGate U ψ) (c.plus ⟨0,1,0,0⟩) F
  | .step .query p,ψ,c,F => evalCounts O p (ApplyGate O ψ) (c.plus ⟨1,0,0,0⟩) F
  | .bit p q,ψ,c,F => (1/2 : ℝ) * (evalCounts O p ψ (c.plus ⟨0,0,0,1⟩) F +
      evalCounts O q ψ (c.plus ⟨0,0,0,1⟩) F)
  | .measure n label k,ψ,c,F => ∑ i : Fin n,
      evalCounts O (k i) (Collapse ψ (Finset.univ.filter fun x => label x = i)) (c.plus ⟨0,0,1,0⟩) F
  | .project P p q,ψ,c,F => evalCounts O p (ApplyGate (1-P) ψ) (c.plus ⟨0,0,1,0⟩) F +
      evalCounts O q (ApplyGate P ψ) (c.plus ⟨0,0,1,0⟩) F

inductive Path : HybridProgram D A → Type where
  | ret (a : A) : Path (.ret a)
  | step (s : Step (Fin D)) {p : HybridProgram D A} : Path p → Path (.step s p)
  | bitFalse {p q : HybridProgram D A} : Path p → Path (.bit p q)
  | bitTrue {p q : HybridProgram D A} : Path q → Path (.bit p q)
  | measure {n : ℕ} {label : Fin D → Fin n} {k : Fin n → HybridProgram D A}
      (i : Fin n) : Path (k i) → Path (.measure n label k)
  | projectFalse {P : Operator D} {p q : HybridProgram D A} : Path p → Path (.project P p q)
  | projectTrue {P : Operator D} {p q : HybridProgram D A} : Path q → Path (.project P p q)

namespace Path

def result {p : HybridProgram D A} : Path p → A
  | .ret a => a
  | .step _ h => h.result
  | .bitFalse h => h.result
  | .bitTrue h => h.result
  | .measure _ h => h.result
  | .projectFalse h => h.result
  | .projectTrue h => h.result

noncomputable def record (O : Operator D) {p : HybridProgram D A} : Path p → HybridLeaf D A
  | .ret a => ⟨a,1,0,0,0,[],[],[]⟩
  | .step (.gate U) h => (h.record O).quantum U 0 1 0 []
  | .step .query h => (h.record O).quantum O 1 0 0 []
  | .bitFalse h => (h.record O).coin false
  | .bitTrue h => (h.record O).coin true
  | @Path.measure _ _ n label k i h =>
      (h.record O).quantum (Projector (Finset.univ.filter fun x => label x = i)) 0 0 1 [(n,i.val)]
  | .projectFalse (P := P) h => (h.record O).quantum (1 - P) 0 0 1 [(2,0)]
  | .projectTrue (P := P) h => (h.record O).quantum P 0 0 1 [(2,1)]

def sequence {p : HybridProgram D A} (h : Path p) (k : A → HybridProgram D B)
    (next : Path (k h.result)) : Path (p.bind k) :=
  match h with
  | .ret _ => next
  | .step s h => .step s (h.sequence k next)
  | .bitFalse h => .bitFalse (h.sequence k next)
  | .bitTrue h => .bitTrue (h.sequence k next)
  | .measure i h => .measure i (h.sequence k next)
  | .projectFalse h => .projectFalse (h.sequence k next)
  | .projectTrue h => .projectTrue (h.sequence k next)

def prepend (C : Circuit (Fin D)) {p : HybridProgram D A} (h : Path p) : Path (prependCircuit C p) :=
  match C with
  | [] => h
  | s :: C => .step s (prepend C h)

end Path

end HybridProgram

namespace HybridCounts

def charge (q g m r : ℝ) (c : HybridCounts) : ℝ :=
  q*c.queries + g*c.gates + m*c.measurements + r*c.reads

end HybridCounts

namespace CoinCode
variable {A : Type}
noncomputable def readMean (p : CoinCode A) : ℝ :=
  (p.paths.map (fun z => wordWeight z.2 * (z.2.length : ℝ))).sum

end CoinCode

end Qatlib.Concepts.AdversaryBounds.AdvDuality
