/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.XorOracle
public import Qatlib.Concepts.QPrograms.OracleBridge

@[expose] public section

/-!
# Theorem 3.6: standard-oracle query-cost bridge (first executable slice)

The first executable slice of the QWeakness97 line for Theorem 3.6 (Theorem 3.6 of
quant-ph/9701001v1, lines 459-547 of the fixed v1 text). A query-word execution against
the standard (non-phase) XOR oracle of `Qatlib.Concepts.CircuitLang.XorOracle` is
billed consistently on the program and circuit layers: the program-side history
ledger `progQCost` prices every intermediate history by the public `QueryCount` of the
circuit word implementing that step - this cost-model assumption is stated as an
explicit hypothesis (`hmodel`), never hidden in a definition - and the word-side
oracle-step count of the executed trajectory word agrees with the bill exactly
(`charge_agreeTrajWord`, `progBill_agreeTrajWord`). The main statement
`stdOracleCostBridge` additionally records that the counted trajectory word denotes a
unitary against `xorOracle f`, reusing the XOR word unitarity theorem `xorWord_uni`. `uniformStepBill`
is the n-step form of the single-step agreement `oneQueryAgree`, and the
`phaseBracket_*` lemmas show that the typed `PhaseOf` bracket adds two gate layers and
exactly one standard query, so a phase-form step still bills one query.

This is a finite counting/agreement theorem only. It is NOT Theorem 3.6 and no part of
it: no random permutation oracle, no hybrid or mixed-schedule argument, no
probability-one statement, no countable-QTM or all-lengths uniformity, no NP∩coNP
separation, no BQTime membership, and no asymptotic reading of the finite equality
(a finite equality is never an asymptotic statement, per the design document's
four-aspect conclusion-type criteria). The in-place permutation coupling of
`Qatlib.Papers.QWeakness97.MainResults.PermCoupling` is a different restricted model and is deliberately not
consumed here; nor is any bridge claimed from the source paper's QTM queries to the
three-block register `OReg`.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Concepts.QPrograms.QueryBilling
open Qatlib.Concepts.QPrograms.OracleBridge

namespace Qatlib.Papers.QWeakness97.OracleCostBridge

variable {O I : Type}

/-! ## The trajectory word and the generic counting core -/

/-- The trajectory word of a query-word execution: starting from history `h`, the step
word of `h` is executed first, then the step word of the history extended by the next
outcome, and so on. The word implementing the step at an intermediate history is part
of the execution description; no measurement or branching semantics is claimed. -/
def trajWord (word : List O → Circuit I) : List O → List O → Circuit I
  | _, [] => []
  | h, o :: os => word h ++ trajWord word (h ++ [o]) os

/-- The core agreement, history by history: if the ledger prices every history by the
public query count of its step word (the cost-model hypothesis `hmodel`, stated
explicitly), then the accumulated charge along a trajectory equals the public query
count of the trajectory word. Pure finite counting; gates never enter the bill. -/
theorem charge_agreeTrajWord (word : List O → Circuit I) (cost : List O → ℕ)
    (hmodel : ∀ h, cost h = QueryCount (word h)) (h os : List O) :
    charge cost h os = QueryCount (trajWord word h os) := by
  induction os generalizing h with
  | nil => rfl
  | cons o os ih =>
    show cost h + charge cost (h ++ [o]) os
        = QueryCount (word h ++ trajWord word (h ++ [o]) os)
    rw [hmodel h, queryCount_append, ih (h ++ [o])]

/-- The top-level bridge at the empty history: the program-side bill of a trajectory
equals the word-side public query count of the executed trajectory word, under the
explicit cost-model hypothesis that each step is priced by its implementing word's
`QueryCount`. A bookkeeping equality between the two layers, not an identification of
their semantics. -/
theorem progBill_agreeTrajWord (word : List O → Circuit I) (cost : List O → ℕ)
    (hmodel : ∀ h, cost h = QueryCount (word h)) (os : List O) :
    progQCost cost os = QueryCount (trajWord word [] os) :=
  charge_agreeTrajWord word cost hmodel [] os

/-- A history-independent step word turns the trajectory word into the public repeated
circuit: constant policies bill and count through the public repetition lemmas. -/
theorem trajWord_const (C : Circuit I) (h os : List O) :
    trajWord (fun _ => C) h os = RepeatCircuit C os.length := by
  induction os generalizing h with
  | nil => rfl
  | cons o os ih =>
    simp only [trajWord, RepeatCircuit, List.length_cons]
    rw [ih (h ++ [o])]

/-- If every step word is unitary, so is the whole trajectory word: the counted object
is a legal unitary execution, not an arbitrary list of instructions. -/
theorem trajWord_unitary [Fintype I] [DecidableEq I] (word : List O → Circuit I)
    (hstep : ∀ h, IsUnitaryCircuit (word h)) (h os : List O) :
    IsUnitaryCircuit (trajWord word h os) := by
  induction os generalizing h with
  | nil => exact isUnitaryCircuit_nil
  | cons o os ih =>
    simp only [trajWord]
    exact (isUnitaryCircuit_append _ _).mpr ⟨hstep h, ih (h ++ [o])⟩

/-- A trajectory of single-query steps bills exactly its length under the constant unit
cost - the n-step form of the single-step agreement `oneQueryAgree`. The equality
is finite data per trajectory; it implies no asymptotic statement. -/
theorem uniformStepBill [Fintype I] [DecidableEq I] (os : List O) :
    progQCost (fun _ => 1) os = os.length := by
  have key := progBill_agreeTrajWord (I := I) (word := fun _ => [Step.query])
    (cost := fun _ => 1) (fun _ => rfl) os
  have hq : QueryCount ([Step.query] : Circuit I) = 1 := rfl
  rw [key, trajWord_const, queryCount_repeatCircuit, hq, Nat.mul_one]

/-! ## The standard XOR oracle layer -/

variable {a w : ℕ}

/-- The standard-oracle cost bridge, main statement of this slice: for step words over
the standard XOR-oracle register `OReg a w`, billed under the explicit per-word cost
model, the program-side bill equals the word-side oracle-step count of the trajectory
word, and that trajectory word is a unitary execution against `xorOracle f` (via the
XOR word unitarity theorem `xorWord_uni`). Counting agreement only; see the module docstring for what
this does not claim. -/
theorem stdOracleCostBridge (f : Addr a → Bool) (word : List O → Circuit (OReg a w))
    (cost : List O → ℕ) (hmodel : ∀ h, cost h = QueryCount (word h))
    (hstep : ∀ h, IsUnitaryCircuit (word h)) (os : List O) :
    progQCost cost os = QueryCount (trajWord word [] os) ∧
      Denote (xorOracle f) (trajWord word [] os) ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  ⟨progBill_agreeTrajWord word cost hmodel os,
    xorWord_uni f (trajWord_unitary word hstep [] os)⟩

/-- The typed phase bracket of a `PhaseOf` interface as a concrete circuit word: one
standard query wrapped in two answer-block Hadamard layers. -/
def phaseBracket (P : PhaseOf (a := a) (w := w)) : Circuit (OReg a w) :=
  [Step.gate P.hLayer, Step.query, Step.gate P.hLayer]

/-- The phase bracket contains exactly one oracle-query instruction: phase-form
bracketing adds gates, never queries. -/
theorem phaseBracket_queryCount (P : PhaseOf (a := a) (w := w)) :
    QueryCount (phaseBracket P) = 1 := rfl

/-- The phase bracket contains exactly two explicit gate instructions, namely the two
Hadamard layers; they are macro gates and stay outside the query bill. -/
theorem phaseBracket_gateCount (P : PhaseOf (a := a) (w := w)) :
    GateCount (phaseBracket P) = 2 := rfl

/-- The phase bracket denotes exactly the typed phase form `hLayer * oracle * hLayer`
of `PhaseOf`, so the bracketed word is the standard-form witness of the phase
interface. -/
theorem phaseBracketDenote (P : PhaseOf (a := a) (w := w)) :
    Denote (xorOracle P.f) (phaseBracket P) = P.hLayer * xorOracle P.f * P.hLayer := by
  simp only [phaseBracket]
  rw [denote_gate, denote_query, denote_gate, denote_nil, Matrix.one_mul]

/-- The phase bracket is a unitary word execution against the standard oracle whenever
the `PhaseOf` Hadamard layer is unitary, reusing the phase-form unitarity. -/
theorem phaseBracket_uni (P : PhaseOf (a := a) (w := w)) :
    Denote (xorOracle P.f) (phaseBracket P) ∈ Matrix.unitaryGroup (OReg a w) ℂ := by
  rw [phaseBracketDenote]
  exact phaseOf_uni P

/-- A trajectory of phase-bracket steps bills exactly its length under the per-word
cost model: one standard query per step, the Hadamard layers never reaching the query
bill. Finite counting data, no asymptotic claim. -/
theorem phaseStepBill (P : PhaseOf (a := a) (w := w)) (os : List O) :
    progQCost (fun _ => QueryCount (phaseBracket P)) os = os.length := by
  have key := progBill_agreeTrajWord (I := OReg a w) (word := fun _ => phaseBracket P)
    (cost := fun _ => QueryCount (phaseBracket P)) (fun _ => rfl) os
  rw [key, trajWord_const, queryCount_repeatCircuit, phaseBracket_queryCount, Nat.mul_one]

end Qatlib.Papers.QWeakness97.OracleCostBridge
