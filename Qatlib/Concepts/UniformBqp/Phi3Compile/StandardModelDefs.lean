/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Uniform circuit and tape-machine specifications

This module defines local QTM well-formedness conditions, bounded halting and emission
predicates, and uniform simulation specifications. It also introduces circuit-based language
predicates, closure statements, communication decision lists, and Boolean formula lower-bound
statements.

The oracle definitions give finite-window transition matrices, acceptance probabilities, and
accumulated query mass. Each specification records its explicit quantifiers and resource bounds.

For background, see [BernsteinVazirani1997].

## Main statements

* `QTMToUniformCircuitSpec`: window simulation together with polynomial gate-count emission.
* `HeadStaySimulationSpec`: acceptance simulation with the stated circuit-size time bound.
* `OracleQTM`: a local machine with query states and an answer map.
* `oracleQueryMass`: total query-state mass over the execution steps.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

namespace Qatlib.Concepts.UniformBqp.Phi3Compile

open Matrix
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.UniformBqp.BvParityBound

/-- The conjunction of local transition normalization, orthogonality for distinct source pairs,
and the three specified cross-direction orthogonality conditions. -/
def LocalQTMFiveConditions {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) : Prop :=
  (∀ q a, ∑ q' : Q, ∑ b : A, ∑ d : QtmMove, ‖M.step q a d q' b‖ ^ 2 = 1) ∧
  (∀ q₁ a₁ q₂ a₂, (q₁, a₁) ≠ (q₂, a₂) →
      ∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
        star (M.step q₁ a₁ d q' b) * M.step q₂ a₂ d q' b = 0) ∧
  (∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ : A) (c d : A),
      ∑ q' : Q, M.step q₁ a₁ QtmMove.right q' c
        * star (M.step q₂ a₂ QtmMove.stay q' d) = 0) ∧
  (∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ : A) (c d : A),
      ∑ q' : Q, M.step q₁ a₁ QtmMove.stay q' c
        * star (M.step q₂ a₂ QtmMove.left q' d) = 0) ∧
  ∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ : A) (c d : A),
    ∑ q' : Q, M.step q₁ a₁ QtmMove.right q' c
      * star (M.step q₂ a₂ QtmMove.left q' d) = 0

/-- Runs a tape machine for at most the given step budget, returning its terminal configuration
if it halts within that budget. -/
def TM0HaltRun {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1))) :
    ℕ → Turing.TM0.Cfg (Option Bool) (Fin (q + 1)) →
      Option (Turing.TM0.Cfg (Option Bool) (Fin (q + 1)))
  | 0, cfg => if Turing.TM0.step M cfg = none then some cfg else none
  | t + 1, cfg =>
      match Turing.TM0.step M cfg with
      | none => some cfg
      | some cfg' => TM0HaltRun M t cfg'

/-- The predicate that a tape machine halts within the stated polynomial source-length bound
with the prescribed output on its right tape, padded by blanks. -/
def TM0EmitsPoly {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (c d : ℕ) (src out : List Bool) : Prop :=
  ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))),
    s ≤ c * (src.length + d) ^ d + c ∧
    TM0HaltRun M s (Turing.TM0.init (src.map some)) = some cfg ∧
    Turing.TM0.step M cfg = none ∧
    ∀ i : ℕ, cfg.Tape.right₀.nth i = (out.map some).getD i none

/-- The specification of exact unitary window circuits with zero queries and quadratic gate
bounds, together with polynomial tape emission of gate-count words from the stated binary
pair encoding. -/
def QTMToUniformCircuitSpec : Prop :=
  ∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (M : LocalQTM Q A), LocalQTMFiveConditions M →
    ∃ (build : (n t : ℕ) → Circuit (WReg t Q A))
      (q c d : ℕ) (emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
      (∀ (n t : ℕ), 0 < n → 0 < t → n ≤ t →
        IsUnitaryCircuit (build n t) ∧ QueryCount (build n t) = 0 ∧
        GateCount (build n t) ≤ 2 * t * t ∧
        (∀ x : Fin n → A, ∀ cfg : WindowCfg t Q A,
          Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (build n t)
              (Ket (windowEncode (initWindowCfg (t := t) M n x))) =
            windowEmbed ((windowStep (t := t) M) ^ t *ᵥ
              Ket (initWindowCfg (t := t) M n x)) ∧
          BornProb (Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (build n t)
              (Ket (windowEncode (initWindowCfg (t := t) M n x)))) (windowEncode cfg) =
            BornProb ((windowStep (t := t) M) ^ t *ᵥ
              Ket (initWindowCfg (t := t) M n x)) cfg)) ∧
      (∀ (n t : ℕ), 0 < n → 0 < t → n ≤ t →
        TM0EmitsPoly emitter c d (n.bits ++ [false] ++ t.bits)
          ((GateCount (build n t)).bits ++ [false]))

/-- The predicate that every Boolean input yields a terminal configuration within the bound `c *
length^k + c`. -/
def HaltsWithinPolyTime {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (c k : ℕ) : Prop :=
  ∀ x : List Bool, ∃ (t : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))),
    t ≤ c * x.length ^ k + c ∧
    TM0HaltRun M t (Turing.TM0.init (x.map some)) = some cfg ∧
    Turing.TM0.step M cfg = none

/-- The predicate that language membership is equivalent to reaching a designated accepting
terminal label within a fixed polynomial bound. -/
def InPolyTime (L : List Bool → Prop) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (qacc : Fin (q + 1)) (c k : ℕ),
    ∀ x : List Bool,
      (L x ↔ ∃ (t : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))),
         t ≤ c * x.length ^ k + c ∧
         TM0HaltRun M t (Turing.TM0.init (x.map some)) = some cfg ∧
         Turing.TM0.step M cfg = none ∧ cfg.q = qacc)

/-- The uniform probability distribution on Boolean registers of width `m`, assigning mass `1 /
2^m` to each register. -/
noncomputable def uniformRegDist (m : ℕ) : FinDist (Reg m) where
  prob _ := 1 / (2 ^ m : ℝ)
  nonneg _ := by positivity
  sum_one := by
    have h2 : ((2 : ℝ) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_reg, Nat.cast_pow]
    field_simp
    push_cast
    rfl

/-- Forms a register by placing the coin bits first and the Boolean input bits afterward. -/
def regCoinInput {m : ℕ} (r : Reg m) (x : List Bool) : Reg (m + x.length) :=
  fun i => if h : i.val < m then r ⟨i.val, h⟩ else x.getD (i.val - m) false

/-- The expected circuit acceptance probability over uniformly chosen coin registers prepended
to the input. -/
noncomputable def RandomAcceptProb (F : CircuitFamily) (coin : ℕ → ℕ) (x : List Bool)
    (hpos : 0 < coin x.length) : ℝ :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect (uniformRegDist (coin x.length)) (fun r =>
    AcceptProb (Run (1 : Matrix (Reg (coin x.length + x.length))
      (Reg (coin x.length + x.length)) ℂ) (F.build (coin x.length + x.length))
      (Ket (regCoinInput r x)))
      (Nat.lt_of_lt_of_le hpos (Nat.le_add_right (coin x.length) x.length)))

/-- The circuit-family language predicate requiring polynomial emission of size words and
acceptance probability at least two thirds on members and at most one third on nonmembers. -/
def InBPP (L : List Bool → Prop) : Prop :=
  ∃ (F : CircuitFamily) (coin : ℕ → ℕ) (hcoin : ∀ m, 0 < coin m)
    (q c d : ℕ) (emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
    (∀ m : ℕ,
      TM0EmitsPoly emitter c d m.bits ((Size (F.build (coin m + m))).bits ++ [false])) ∧
    ∀ x : List Bool,
      (L x → (2 / 3 : ℝ) ≤ RandomAcceptProb F coin x (hcoin x.length)) ∧
      (¬ L x → RandomAcceptProb F coin x (hcoin x.length) ≤ 1 / 3)

/-- The conjunction of complement and binary intersection closure statements for `InPolyTime`. -/
def PPClosureSpec : Prop :=
  (∀ L : List Bool → Prop, InPolyTime L → InPolyTime (fun x => ¬ L x)) ∧
  (∀ (L₁ L₂ : List Bool → Prop), InPolyTime L₁ → InPolyTime L₂ →
    InPolyTime (fun x => L₁ x ∧ L₂ x))

/-- The conjunction of error reduction with the stated circuit-size bound and binary
intersection closure for `InBPP`. -/
def BPPClosureSpec : Prop :=
  (∀ (L : List Bool → Prop), InBPP L → ∀ ε : ℝ, 0 < ε →
    ∃ (F : CircuitFamily) (coin : ℕ → ℕ) (hcoin : ∀ m, 0 < coin m) (c k : ℕ),
      (∀ m : ℕ, Size (F.build (coin m + m)) ≤
        c * m ^ k * (Nat.log 2 (Nat.ceil (1 / ε)) + 1) ^ k + c) ∧
      (∀ x : List Bool, L x → 1 - ε ≤ RandomAcceptProb F coin x (hcoin x.length)) ∧
      (∀ x : List Bool, ¬ L x → RandomAcceptProb F coin x (hcoin x.length) ≤ ε)) ∧
  (∀ (L₁ L₂ : List Bool → Prop), InBPP L₁ → InBPP L₂ →
    InBPP (fun x => L₁ x ∧ L₂ x))

/-- The three gate labels H, T, and CNOT. -/
inductive DLambdaGate where
  | H : DLambdaGate
  | T : DLambdaGate
  | CNOT : DLambdaGate

/-- The specification that every unitary circuit has an acceptance-preserving local QTM
simulation satisfying the five conditions, with positive window and time parameters and time
at most `(Size C + 2)^6`. -/
def HeadStaySimulationSpec : Prop :=
  ∀ (n : ℕ) (C : Circuit (Reg n)) (hn : 0 < n), IsUnitaryCircuit C →
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (qacc : Q) (M : LocalQTM Q Bool)
      (w t : ℕ), 0 < w ∧ 0 < t ∧ n ≤ w ∧ t ≤ (Size C + 2) ^ 6 ∧
      LocalQTMFiveConditions M ∧
      ∀ x : Reg n,
        (∑ c ∈ Finset.univ.filter (fun c => c.state = qacc),
          BornProb ((windowStep (t := w) M) ^ t *ᵥ
            Ket (initWindowCfg (t := w) M n x)) c) =
        AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) C (Ket x)) hn

/-- A fixed list of queries selecting bits from two input registers, together with a Boolean
verdict function on the answers. -/
structure CommDecisionList (m : ℕ) where

  queries : List (Bool × Fin m)

  verdict : List Bool → Bool

/-- Evaluates a communication decision list by collecting the selected input bits and applying
its verdict function. -/
def commListOutput {m : ℕ} (P : CommDecisionList m) (a b : Reg m) : Bool :=
  P.verdict (P.queries.map (fun q => if q.1 then a q.2 else b q.2))

/-- The number of bit queries in a communication decision list. -/
def commListCost {m : ℕ} (P : CommDecisionList m) : ℕ := P.queries.length

/-- The statement that every fixed-query decision list deciding equality satisfies the given
positive-constant lower bound involving two base-two logarithms. -/
def CommunicationOmegaLogLogSpec : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ (m : ℕ), 2 ≤ m →
    ∀ P : CommDecisionList m,
      (∀ a b : Reg m, commListOutput P a b = decide (a = b)) →
        c * Nat.log 2 (Nat.log 2 (2 ^ m)) ≤ commListCost P

/-- Boolean formulas generated from variables, negation, conjunction, and disjunction. -/
inductive BoolFormula (V : Type) where
  | var : V → BoolFormula V
  | not : BoolFormula V → BoolFormula V
  | and : BoolFormula V → BoolFormula V → BoolFormula V
  | or : BoolFormula V → BoolFormula V → BoolFormula V

/-- Evaluates a Boolean formula under a Boolean assignment to its variables. -/
def BoolFormula.eval {V : Type} (a : V → Bool) : BoolFormula V → Bool
  | .var v => a v
  | .not f => !f.eval a
  | .and f g => f.eval a && g.eval a
  | .or f g => f.eval a || g.eval a

/-- Counts variable occurrences in a Boolean formula, adding at binary connectives and ignoring
negation nodes. -/
def BoolFormula.size {V : Type} : BoolFormula V → ℕ
  | .var _ => 1
  | .not f => f.size
  | .and f g => f.size + g.size
  | .or f g => f.size + g.size

/-- The number of true bits in a Boolean register. -/
def regWeight (n : ℕ) (x : Reg n) : ℕ := ∑ i, if x i then 1 else 0

/-- The strict-majority predicate, true when twice the register weight exceeds its width. -/
def regMajority (n : ℕ) (x : Reg n) : Bool := decide (n < 2 * regWeight n x)

/-- The statement that every formula computing strict majority on `n` input bits has at least
`n` variable occurrences. -/
def MajorityFormulaLowerBoundSpec : Prop :=
  ∀ (n : ℕ) (F : BoolFormula (Fin n)), (∀ x : Reg n, F.eval x = regMajority n x) →
    n ≤ F.size

/-- A local QTM equipped with a finite set of query states and a tape-symbol answer map. -/
structure OracleQTM (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    where

  machine : LocalQTM Q A

  queryStates : Finset Q

  oracleAnswer : A → A

/-- The finite-window transition matrix induced by a raw local transition-amplitude function. -/
noncomputable def rawWindowStep {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {t : ℕ} (δ : Q → A → QtmMove → Q → A → ℂ) :
    Matrix (WindowCfg t Q A) (WindowCfg t Q A) ℂ :=
  Matrix.of fun c' c =>
    ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
      if moveCell d c.head = some c'.head ∧ c'.state = q' ∧
          ∀ j : Fin (2 * t + 1), c'.tape j = if j = c.head then b else c.tape j
      then δ c.state (c.tape c.head) d q' b else 0

/-- Uses the underlying transition rule outside query states and, in query states, replaces the
scanned symbol by its oracle answer while keeping the state and head fixed. -/
noncomputable def oracleDelta {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (O : OracleQTM Q A) : Q → A → QtmMove → Q → A → ℂ :=
  fun q a d q' b =>
    if q ∈ O.queryStates then
      (if d = QtmMove.stay ∧ q' = q ∧ b = O.oracleAnswer a then 1 else 0)
    else O.machine.step q a d q' b

/-- The finite-window transition matrix determined by the oracle-modified local transition
function. -/
noncomputable def oracleWindowStep {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] {t : ℕ} (O : OracleQTM Q A) :
    Matrix (WindowCfg t Q A) (WindowCfg t Q A) ℂ :=
  rawWindowStep (oracleDelta O)

/-- The condition that ordinary states use the underlying rule and each query state has
normalized outgoing amplitudes with amplitude one for its prescribed oracle update. -/
def OracleExecutionCorrect {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (O : OracleQTM Q A) : Prop :=
  (∀ q a, q ∉ O.queryStates → ∀ d q' b,
      oracleDelta O q a d q' b = O.machine.step q a d q' b) ∧
  (∀ q a, q ∈ O.queryStates →
    (∑ d : QtmMove, ∑ q' : Q, ∑ b : A, ‖oracleDelta O q a d q' b‖ ^ 2 = 1) ∧
      oracleDelta O q a QtmMove.stay q (O.oracleAnswer a) = 1)

/-- The Born mass of configurations in the specified accepting state after the given number of
oracle-window steps. -/
noncomputable def oracleQtmAcceptProb {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {w : ℕ} (O : OracleQTM Q A) (qacc : Q)
    (m steps : ℕ) (x : Fin m → A) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => c.state = qacc),
    BornProb ((oracleWindowStep (t := w) O) ^ steps *ᵥ
      Ket (initWindowCfg (t := w) O.machine m x)) c

/-- The sum, over execution times before the step bound, of the Born mass in configurations
whose states are query states. -/
noncomputable def oracleQueryMass {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {w : ℕ} (O : OracleQTM Q A) (m steps : ℕ)
    (x : Fin m → A) : ℝ :=
  ∑ j ∈ Finset.range steps,
    ∑ c ∈ Finset.univ.filter (fun c => c.state ∈ O.queryStates),
      BornProb ((oracleWindowStep (t := w) O) ^ j *ᵥ
        Ket (initWindowCfg (t := w) O.machine m x)) c

/-- The integer-valued Boolean character given by the product of minus-one factors at
coordinates where both registers are true. -/
def phaseChar {n : ℕ} (s g : Reg n) : ℤ := ∏ i : Fin n, if s i ∧ g i then (-1 : ℤ) else 1

/-- The conjunction of the stated oracle separation, bit recovery, single-query-state
simulation, phase-character computation, amplification, query-mass, clocking, and
approximate halting specifications. It also includes complement and intersection closure for
`InBQP`. -/
def OracleTransportSpec : Prop :=
  ParityOracleSeparationRestricted ∧
  (∀ (n : ℕ), 0 < n → ∀ s : Reg n,
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (qacc : Fin n → Q)
      (O : OracleQTM Q (Reg n × Bool)) (w t : ℕ),
      0 < w ∧ n ≤ w ∧ O.queryStates.card = 1 ∧ t ≤ (n + 8) ^ 6 ∧
      OracleExecutionCorrect O ∧
      (∀ j : Fin n,
        (s j = true →
          (2 / 3 : ℝ) ≤ oracleQtmAcceptProb (w := w) O (qacc j) 0 t
            (fun _ => (ZeroStr n, false))) ∧
        (s j = false →
          oracleQtmAcceptProb (w := w) O (qacc j) 0 t
            (fun _ => (ZeroStr n, false)) ≤ 1 / 3))) ∧
  (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (O : OracleQTM Q A) (qacc : Q), OracleExecutionCorrect O →
    ∃ (Q' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (O' : OracleQTM Q' A)
      (qacc' : Q'),
      O'.queryStates.card = 1 ∧ OracleExecutionCorrect O' ∧
      ∀ (m steps w : ℕ) (x : Fin m → A), 0 < w → m ≤ w →
        ∃ t', t' ≤ (steps + 2) ^ 2 ∧
          oracleQtmAcceptProb (w := w) O' qacc' m t' x =
            oracleQtmAcceptProb (w := w) O qacc m steps x) ∧
  (∀ (n : ℕ), 0 < n → ∀ s : Reg n,
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (qacc : Q)
      (O : OracleQTM Q (Reg n × Bool)) (w t : ℕ),
      0 < w ∧ n ≤ w ∧ O.queryStates.card ≤ 1 ∧ t ≤ (n + 8) ^ 6 ∧
      OracleExecutionCorrect O ∧
      ∀ g : Reg n,
        oracleQtmAcceptProb (w := w) O qacc n t (fun _ => (g, false)) =
          (1 + (phaseChar s g : ℝ)) / 2) ∧
  (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (O : OracleQTM Q A) (qacc : Q) (m steps w : ℕ) (x : Fin m → A) (δ : ℝ),
    0 < δ → 0 < w → m ≤ w → OracleExecutionCorrect O →
    1 / 2 + δ ≤ oracleQtmAcceptProb (w := w) O qacc m steps x →
    ∃ (Q' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (O' : OracleQTM Q' A)
      (qacc' : Q') (t' : ℕ),
      t' ≤ (steps + Nat.ceil (1 / δ) + 8) ^ 6 ∧
      O'.queryStates.card ≤ O.queryStates.card * (Nat.ceil (1 / δ) + 1) ∧
      OracleExecutionCorrect O' ∧
      2 / 3 ≤ oracleQtmAcceptProb (w := w) O' qacc' m t' x) ∧
  (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (O : OracleQTM Q A) (m w : ℕ) (x : Fin m → A), 0 < w → m ≤ w →
    ∀ steps : ℕ, oracleQueryMass (w := w) O m steps x ≤ steps) ∧
  (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (O : OracleQTM Q A) (m t w : ℕ) (x : Fin m → A), 0 < t → 0 < w → m ≤ w →
    ∃ (Q' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (qck : Q')
      (O' : OracleQTM Q' (A × Bool)) (t' : ℕ),
      t' ≤ (t + 2) ^ 2 ∧ O'.queryStates.card ≤ O.queryStates.card + 1 ∧
      OracleExecutionCorrect O' ∧
      (∑ c ∈ Finset.univ.filter (fun c => c.state = qck),
        BornProb ((oracleWindowStep (t := w) O') ^ t' *ᵥ
          Ket (initWindowCfg (t := w) O'.machine m (fun i => (x i, false)))) c) = 1) ∧
  (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (_O : OracleQTM Q A) (m t w : ℕ) (x : Fin m → A) (ε : ℝ),
    0 < ε → 0 < w → m ≤ w →
    ∃ (Q' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (qhalt : Q')
      (O' : OracleQTM Q' A) (t' : ℕ),
      t' ≤ (t + Nat.log 2 (Nat.ceil (1 / ε)) + 8) ^ 6 ∧
      (∑ c ∈ Finset.univ.filter (fun c => c.state = qhalt),
        BornProb ((oracleWindowStep (t := w) O') ^ t' *ᵥ
          Ket (initWindowCfg (t := w) O'.machine m x)) c) ≥ 1 - ε) ∧
  (∀ L : (n : ℕ) → Reg n → Prop, InBQP L → InBQP (fun n x => ¬ L n x)) ∧
  (∀ (L₁ L₂ : (n : ℕ) → Reg n → Prop), InBQP L₁ → InBQP L₂ →
    InBQP (fun n x => L₁ n x ∧ L₂ n x))

end Qatlib.Concepts.UniformBqp.Phi3Compile
