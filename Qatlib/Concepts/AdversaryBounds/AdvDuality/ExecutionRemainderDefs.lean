/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainderDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMixedState
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabularyDefs

/-!
# Fair feedback and hybrid execution data

This module defines finite execution data for circuits controlled by fair coin programs and
measurement outcomes. `FairFeedback` selects a coin program after an observed prefix, while
`HybridProgram` permits gates, queries, coin choices, and measurements at arbitrary nodes. The
operator and measurement terminology follows [NielsenChuang2010].

`HybridLeaf` records branch operators, classical histories, and resource counts. The recursive
evaluators and the cuts `HybridProgram.cut` and `HybridProgram.cutQueries` provide execution
interfaces for later probability and composition laws.

## Main definitions

* `CoinCode.paths`: terminating values paired with their consumed coin words.
* `FairFeedback.kraus`: a branch operator scaled by the square root of its coin weight.
* `HybridProgram.leaves`: finite branch enumeration with execution records.
* `HybridProgram.evalCounts`: recursive evaluation carrying accumulated resource counts.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- Enumerate the terminating values and consumed coin words of a finite coin program. -/
def paths : CoinCode α → List (α × List Bool)
  | .ret a => [(a, [])]
  | .bit p q => (p.paths.map (fun z => (z.1, false :: z.2))) ++
      (q.paths.map (fun z => (z.1, true :: z.2)))

/-- The real fair coin weight `2⁻ˡ` of a Boolean word of length `l`. -/
noncomputable def wordWeight (w : List Bool) : ℝ := (1 / 2 : ℝ) ^ w.length
end CoinCode

/-- An observed prefix followed by a coin program chosen from its outcome and an observed
continuation chosen from the resulting value. -/
structure FairFeedback (D : ℕ) (A : Type) where
  first : ObservedCircuit (Fin D)
  choose : Fin (observedLeafCount first) → CoinCode A
  next : (i : Fin (observedLeafCount first)) → A → ObservedCircuit (Fin D)

/-- The returned classical value, acceptance flags, coin word, resource counts, and measurement
records of a feedback execution. -/
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

/-- The returned value and coin word at a selected path index of the chosen coin program. -/
def path (M : FairFeedback D A) (i : Fin (observedLeafCount M.first))
    (c : Fin (M.choose i).paths.length) : A × List Bool :=
  (M.choose i).paths.get c

/-- Feedback outcomes indexed by a prefix leaf, a coin path, and a leaf of the selected suffix
circuit. -/
abbrev Outcome (M : FairFeedback D A) :=
  Σ i : Fin (observedLeafCount M.first), Σ c : Fin (M.choose i).paths.length,
    Fin (observedLeafCount (M.next i (M.path i c).1))

/-- The coin word associated with a feedback outcome. -/
def codeWord (M : FairFeedback D A) (z : M.Outcome) : List Bool :=
  (M.path z.1 z.2.1).2

/-- The observed Kraus leaf of the feedback prefix at the chosen index. -/
noncomputable def prefixLeaf (M : FairFeedback D A) (O : Operator D)
    (i : Fin (observedLeafCount M.first)) : ObservedKrausLeaf D := observedLeaf O M.first i

/-- The observed Kraus leaf of the continuation selected by a feedback outcome. -/
noncomputable def suffixLeaf (M : FairFeedback D A) (O : Operator D)
    (z : M.Outcome) : ObservedKrausLeaf D :=
  observedLeaf O (M.next z.1 (M.path z.1 z.2.1).1) z.2.2

/-- Combine the prefix and suffix records with the chosen classical value and coin word. -/
noncomputable def record (M : FairFeedback D A) (O : Operator D) (z : M.Outcome) :
    FairFeedbackRecord A :=
  let p := M.prefixLeaf O z.1
  let s := M.suffixLeaf O z
  ⟨(M.path z.1 z.2.1).1, p.accepted, s.accepted, M.codeWord z,
    p.queries + s.queries, p.gates + s.gates, p.measurements + s.measurements,
    p.outcomes, s.outcomes⟩

/-- The suffix operator times the prefix operator, scaled by the square root of the coin word's
weight. -/
noncomputable def kraus (M : FairFeedback D A) (O : Operator D) (z : M.Outcome) : Operator D :=
  ((Real.sqrt (CoinCode.wordWeight (M.codeWord z)) : ℝ) : ℂ) •
    ((M.suffixLeaf O z).operator * (M.prefixLeaf O z.1).operator)

/-- Require the observed prefix and every possible observed continuation to be well formed. -/
def Legal (M : FairFeedback D A) : Prop :=
  observedWellFormed M.first ∧ ∀ i a, observedWellFormed (M.next i a)

end FairFeedback

/-- Measure a two dimensional computational basis label and accept exactly outcome one. -/
def measuredFeedbackFirst : ObservedCircuit (Fin 2) :=
  .measure 2 (fun i => i) (fun o => .halt (o == 1))

/-- The example coin choice, deterministic after prefix outcome zero and using one fair bit
after outcome one. -/
def measuredFeedbackCoins (i : Fin 2) : CoinCode (Option (Fin 2) × ℕ) :=
  if i = 0 then weightedTrial (fun j : Fin 2 => if j = 0 then 1 else 0) 0
  else weightedTrial (fun _ : Fin 2 => 1) 1

/-- The Pauli X operator on the two dimensional register used in the feedback example. -/
noncomputable def measuredFeedbackFlip : Operator 2 :=
    Qatlib.Concepts.GateVocabulary.GateVocab.toFinGate PauliX

/-- The example continuation selecting a bit flip, a Hadamard gate, or an oracle query from the
prefix and coin result. -/
noncomputable def measuredFeedbackNext (i : Fin 2) (a : Option (Fin 2) × ℕ) :
    ObservedCircuit (Fin 2) :=
  if i = 0 then .step (.gate measuredFeedbackFlip) (.halt true)
  else if a.1 = some 0 then .step (.gate Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin) (.halt true)
  else if a.1 = some 1 then .step .query (.halt false)
  else .halt false

/-- The two dimensional feedback example combining a basis measurement, a conditional coin
choice, and a selected continuation. -/
noncomputable def measuredFeedback : FairFeedback 2 (Option (Fin 2) × ℕ) where
  first := measuredFeedbackFirst
  choose i := measuredFeedbackCoins i
  next i a := measuredFeedbackNext i a

/-- The maximally mixed operator `1 / 2` times the identity on the two dimensional register. -/
noncomputable def measuredFeedbackInput : Operator 2 := ((1 / 2 : ℝ) : ℂ) • (1 : Operator 2)

/-- The example outcome with prefix measurement zero and its deterministic coin path. -/
def measuredFeedbackZero : measuredFeedback.Outcome :=
  ⟨⟨0, by decide +kernel⟩, ⟨0, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩
/-- The example outcome with prefix measurement one and the coin path selecting a Hadamard gate. -/
def measuredFeedbackHadamard : measuredFeedback.Outcome :=
  ⟨⟨1, by decide +kernel⟩, ⟨0, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩
/-- The example outcome with prefix measurement one and the coin path selecting an oracle query. -/
def measuredFeedbackQuery : measuredFeedback.Outcome :=
  ⟨⟨1, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩

/-- Finite programs with returned values, quantum steps, fair coin branches, labeled basis
measurements, and binary projection branches. -/
inductive HybridProgram (D : ℕ) (A : Type) where
  | ret : A → HybridProgram D A
  | step : Step (Fin D) → HybridProgram D A → HybridProgram D A
  | bit : HybridProgram D A → HybridProgram D A → HybridProgram D A
  | measure (n : ℕ) (label : Fin D → Fin n) (next : Fin n → HybridProgram D A) : HybridProgram D A
  | project : Operator D → HybridProgram D A → HybridProgram D A → HybridProgram D A

/-- A recorded query, gate, fair coin bit, or measurement outcome with its outcome count. -/
inductive HybridEvent where
  | query
  | gate
  | bit : Bool → HybridEvent
  | born : ℕ → ℕ → HybridEvent
  deriving DecidableEq, Repr

/-- Natural number counts of queries, gates, measurements, and coin reads. -/
structure HybridCounts where
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  reads : ℕ
  deriving DecidableEq, Repr

namespace HybridCounts
/-- The resource record with every count zero. -/
def zero : HybridCounts := ⟨0,0,0,0⟩
/-- Add two resource records componentwise. -/
def plus (a b : HybridCounts) : HybridCounts :=
  ⟨a.queries + b.queries,a.gates + b.gates,a.measurements + b.measurements,a.reads + b.reads⟩
end HybridCounts

/-- A terminal branch record containing its value, operator, resource counts, coin word,
measurement outcomes, and event history. -/
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

/-- Extract a leaf's resource counts, using the coin word length as its read count. -/
def counts (t : HybridLeaf D A) : HybridCounts :=
  ⟨t.queries,t.gates,t.measurements,t.coins.length⟩

/-- Prepend a quantum operation by multiplying the leaf operator on the right and updating its
counts, measurement record, and history. -/
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

/-- Prepend a coin bit to a leaf's coin word and event history. -/
def coin (b : Bool) (leaf : HybridLeaf D A) : HybridLeaf D A :=
  { leaf with coins := b :: leaf.coins, history := .bit b :: leaf.history }

/-- The adjoint product of a leaf's operator scaled by its fair coin word weight. -/
noncomputable def effect (leaf : HybridLeaf D A) : Operator D :=
  ((CoinCode.wordWeight leaf.coins : ℝ) : ℂ) • (leaf.operator.conjTranspose * leaf.operator)

/-- The leaf operator scaled by the square root of its fair coin word weight. -/
noncomputable def kraus (leaf : HybridLeaf D A) : Operator D :=
  ((Real.sqrt (CoinCode.wordWeight leaf.coins) : ℝ) : ℂ) • leaf.operator

/-- Convert a Boolean hybrid leaf to an observed Kraus leaf using its operator, value, quantum
counts, and measurement outcomes. -/
noncomputable def toObserved {D : ℕ} (t : HybridLeaf D Bool) : ObservedKrausLeaf D :=
  ⟨t.operator,t.value,t.queries,t.gates,t.measurements,t.born⟩

/-- Compose two branch records in execution order, retaining the second value and concatenating
their classical histories. -/
noncomputable def join {B : Type} (a : HybridLeaf D A) (b : HybridLeaf D B) : HybridLeaf D B :=
  ⟨b.value,b.operator * a.operator,b.queries + a.queries,b.gates + a.gates,
    b.measurements + a.measurements,a.coins ++ b.coins,a.born ++ b.born,a.history ++ b.history⟩

end HybridLeaf

namespace HybridProgram
variable {D : ℕ} {A B : Type}

/-- Replace every return in a hybrid program with its value dependent continuation. -/
def bind : HybridProgram D A → (A → HybridProgram D B) → HybridProgram D B
  | .ret a, k => k a
  | .step s p, k => .step s (p.bind k)
  | .bit p q, k => .bit (p.bind k) (q.bind k)
  | .measure n label next, k => .measure n label (fun i => (next i).bind k)
  | .project P p q, k => .project P (p.bind k) (q.bind k)

/-- Embed a finite coin program by replacing its returns with hybrid continuations. -/
def ofCoins (p : CoinCode B) (k : B → HybridProgram D A) : HybridProgram D A :=
  match p with
  | .ret a => k a
  | .bit p q => .bit (ofCoins p k) (ofCoins q k)

/-- The predicate that a program's outermost constructor is not a coin branch. -/
def Frontier : HybridProgram D A → Prop
  | .bit _ _ => False
  | _ => True

/-- Consume supplied bits through consecutive outer coin branches, returning the residual
program and number of bits used. -/
def runCoins : List Bool → HybridProgram D A → HybridProgram D A × ℕ
  | [], p => (p,0)
  | b :: bs, .bit p q =>
      let z := runCoins bs (if b then q else p)
      (z.1, 1 + z.2)
  | _ :: _, p => (p,0)

/-- Embed an observed circuit as a Boolean valued hybrid program. -/
def ofObserved : ObservedCircuit (Fin D) → HybridProgram D Bool
  | .halt b => .ret b
  | .step s p => .step s (ofObserved p)
  | .measure n label next => .measure n label (fun i => ofObserved (next i))
  | .project P p q => .project P (ofObserved p) (ofObserved q)

/-- Prepend the steps of a circuit to a hybrid program. -/
def prependCircuit : Circuit (Fin D) → HybridProgram D A → HybridProgram D A
  | [], p => p
  | s :: C, p => .step s (prependCircuit C p)

/-- Execute up to a given number of nonreturn constructors along each branch, returning either a
value or a residual program. -/
def cut : ℕ → HybridProgram D A → HybridProgram D (A ⊕ HybridProgram D A)
  | 0, .ret a => .ret (.inl a)
  | 0, p => .ret (.inr p)
  | _ + 1, .ret a => .ret (.inl a)
  | n + 1, .step s p => .step s (cut n p)
  | n + 1, .bit p q => .bit (cut n p) (cut n q)
  | n + 1, .measure m label next => .measure m label (fun i => cut n (next i))
  | n + 1, .project P p q => .project P (cut n p) (cut n q)

/-- Enumerate hybrid execution leaves, recording operators, coin words, measurements, and
resource histories for the supplied oracle. -/
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

/-- The syntactic number of terminal paths in a hybrid program. -/
def leafCount : HybridProgram D A → ℕ
  | .ret _ => 1
  | .step _ p => p.leafCount
  | .bit p q => p.leafCount + q.leafCount
  | .measure n _ next => ∑ i : Fin n, (next i).leafCount
  | .project _ p q => p.leafCount + q.leafCount

/-- Require gates to be unitary, binary projection operators to be orthogonal projectors, and
all subprograms to be legal. -/
def Legal : HybridProgram D A → Prop
  | .ret _ => True
  | .step (.gate U) p => U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ p.Legal
  | .step .query p => p.Legal
  | .bit p q => p.Legal ∧ q.Legal
  | .measure _ _ next => ∀ i, (next i).Legal
  | .project P p q => IsOrthogonalProjector P ∧ p.Legal ∧ q.Legal

/-- Stop before exceeding a query budget, retaining other operations and returning either a
completed value or a residual program. -/
def cutQueries : ℕ → HybridProgram D A → HybridProgram D (A ⊕ HybridProgram D A)
  | _, .ret a => .ret (.inl a)
  | n, .step (.gate U) p => .step (.gate U) (cutQueries n p)
  | 0, .step .query p => .ret (.inr (.step .query p))
  | n + 1, .step .query p => .step .query (cutQueries n p)
  | n, .bit p q => .bit (cutQueries n p) (cutQueries n q)
  | n, .measure m label k => .measure m label (fun i => cutQueries n (k i))
  | n, .project P p q => .project P (cutQueries n p) (cutQueries n q)

/-- Recursively evaluate a real terminal statistic on unnormalized branch states, averaging fair
coin choices and summing measurement branches. -/
noncomputable def eval (O : Operator D) : HybridProgram D A → QState (Fin D) →
    (A → QState (Fin D) → ℝ) → ℝ
  | .ret a, ψ, F => F a ψ
  | .step (.gate U) p, ψ, F => eval O p (ApplyGate U ψ) F
  | .step .query p, ψ, F => eval O p (ApplyGate O ψ) F
  | .bit p q, ψ, F => (1/2 : ℝ) * (eval O p ψ F + eval O q ψ F)
  | .measure n label k, ψ, F => ∑ i : Fin n, eval O (k i) (Collapse ψ (Finset.univ.filter fun x => label x = i)) F
  | .project P p q, ψ, F => eval O p (ApplyGate (1 - P) ψ) F + eval O q (ApplyGate P ψ) F

/-- Recursively evaluate a terminal statistic while carrying accumulated query, gate,
measurement, and coin read counts. -/
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

/-- A syntactic terminal path specifying every coin and measurement branch of a hybrid program. -/
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

/-- The value returned by a syntactic terminal path. -/
def result {p : HybridProgram D A} : Path p → A
  | .ret a => a
  | .step _ h => h.result
  | .bitFalse h => h.result
  | .bitTrue h => h.result
  | .measure _ h => h.result
  | .projectFalse h => h.result
  | .projectTrue h => h.result

/-- The operator and classical execution record of a syntactic path for a supplied oracle. -/
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

/-- Compose a path with a path through the continuation selected by its returned value. -/
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

/-- Extend a path by the steps of a circuit prepended to its program. -/
def prepend (C : Circuit (Fin D)) {p : HybridProgram D A} (h : Path p) : Path (prependCircuit C p) :=
  match C with
  | [] => h
  | s :: C => .step s (prepend C h)

end Path

end HybridProgram

namespace HybridCounts

/-- The real linear resource charge with the given query, gate, measurement, and coin read
prices. -/
def charge (q g m r : ℝ) (c : HybridCounts) : ℝ :=
  q*c.queries + g*c.gates + m*c.measurements + r*c.reads

end HybridCounts

namespace CoinCode
variable {A : Type}
/-- The weighted mean of the terminating coin word lengths of a finite coin program. -/
noncomputable def readMean (p : CoinCode A) : ℝ :=
  (p.paths.map (fun z => wordWeight z.2 * (z.2.length : ℝ))).sum

end CoinCode

end Qatlib.Concepts.AdversaryBounds.AdvDuality
