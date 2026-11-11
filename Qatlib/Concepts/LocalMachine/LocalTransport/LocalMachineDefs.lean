/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log

/-!
# Local machine and recursive Fourier sampling definitions

`QtmRule` records finite quantum Turing transition data, with `QtmRule.LocalWellformed`
expressing the local normalization and orthogonality conditions. Finite-window evolution,
entrywise gate approximations, and a concrete Fourier transition rule provide the underlying
machine data for the complexity setting of [BernsteinVazirani1997].

The recursive Fourier sampling definitions encode queries, character promises, counted
evaluations, finite restrictions, and query transcripts. `rfsHitProb` and `rfsHitProbAbove` are
finite counting ratios over legal restrictions consistent with a transcript.

## Main statements

* `QtmRule.LocalWellformed`: specify local normalization and transition orthogonality.
* `PrecisionGateApprox`: record entrywise approximations to a finite gate word.
* `RfsRestr`: represent a finite recursive Fourier sampling subtree.
* `rfsHitProb`: count consistent legal restrictions whose selected child was queried.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
open Qatlib.Foundations.StandardDefs.WindowSim
open scoped Classical BigOperators

/-- Finite quantum Turing transition data consisting of a blank symbol, a start state, and
complex transition amplitudes. -/
structure QtmRule (Q A : Type*) [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] where

  blank : A

  start : Q

  step : Q → A → QtmMove → Q → A → ℂ

/-- Local normalization and orthogonality conditions for transitions, including the right-stay,
stay-left, and right-left overlap conditions. -/
def QtmRule.LocalWellformed {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (R : QtmRule Q A) : Prop :=
  (∀ q a, ∑ q' : Q, ∑ b : A, ∑ d : QtmMove, ‖R.step q a d q' b‖ ^ 2 = 1) ∧
    (∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ : A), (q₁, a₁) ≠ (q₂, a₂) →
      ∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
        star (R.step q₁ a₁ d q' b) * R.step q₂ a₂ d q' b = 0) ∧
    (∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ c d : A),
      ∑ q' : Q, R.step q₁ a₁ QtmMove.right q' c *
        star (R.step q₂ a₂ QtmMove.stay q' d) = 0) ∧
    (∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ c d : A),
      ∑ q' : Q, R.step q₁ a₁ QtmMove.stay q' c *
        star (R.step q₂ a₂ QtmMove.left q' d) = 0) ∧
    (∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ c d : A),
      ∑ q' : Q, R.step q₁ a₁ QtmMove.right q' c *
        star (R.step q₂ a₂ QtmMove.left q' d) = 0)

/-- Package a locally well-formed transition rule as a `LocalQTM` with the same blank, start
state, and amplitudes. -/
def QtmRule.toLocal {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (R : QtmRule Q A) (h : R.LocalWellformed) :
    LocalQTM Q A where
  blank := R.blank
  start := R.start
  step := R.step
  wf_norm := h.1
  wf_sameCell := h.2.1
  wf_rightStay := h.2.2.1
  wf_stayLeft := h.2.2.2.1
  wf_rightLeft := h.2.2.2.2

/-- Extract the blank symbol, start state, and transition amplitudes from a `LocalQTM`. -/
def QtmRule.ofLocal {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) : QtmRule Q A where
  blank := M.blank
  start := M.start
  step := M.step

/-- Move a head position within a finite window, returning `none` when the move crosses a
boundary. -/
def moveCell {w : ℕ} (i : Fin w) : QtmMove → Option (Fin w)
  | QtmMove.left => if _h : 0 < i.val then some ⟨i.val - 1, by omega⟩ else none
  | QtmMove.stay => some i
  | QtmMove.right =>
      if _h : i.val + 1 < w then some ⟨i.val + 1, by omega⟩ else none

/-- A finite-window configuration consisting of a machine state, head position, and tape
contents. -/
abbrev QtmCfg (Q A : Type*) (w : ℕ) := Q × Fin w × (Fin w → A)

/-- Write `b` at the current head cell, change the state to `q'`, and move the head, failing at
a window boundary. -/
def QtmRule.stepTarget {Q A : Type*} {w : ℕ}
    (c : QtmCfg Q A w) (d : QtmMove) (q' : Q) (b : A) :
    Option (QtmCfg Q A w) :=
  (moveCell c.2.1 d).map fun j => (q', j, Function.update c.2.2 c.2.1 b)

/-- The total transition amplitude between two finite-window configurations, summed over moves,
target states, and written symbols. -/
noncomputable def QtmRule.stepAmplitude {Q A : Type*} [Fintype Q]
    [DecidableEq Q] [Fintype A] [DecidableEq A] (R : QtmRule Q A) (w : ℕ)
    (c c' : QtmCfg Q A w) : ℂ :=
  ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
    if QtmRule.stepTarget c d q' b = some c' then
      R.step c.1 (c.2.2 c.2.1) d q' b
    else 0

/-- The linear evolution of configuration amplitudes induced by the finite-window transition
amplitudes. -/
noncomputable def QtmRule.evolve {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (R : QtmRule Q A) (w : ℕ) :
    QState (QtmCfg Q A w) → QState (QtmCfg Q A w) :=
  fun ψ c' => ∑ c : QtmCfg Q A w, ψ c * R.stepAmplitude w c c'

/-- Iterate the finite-window evolution map `t` times. -/
noncomputable def QtmRule.runSteps {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (R : QtmRule Q A) (w : ℕ) (t : ℕ) :
    QState (QtmCfg Q A w) → QState (QtmCfg Q A w) :=
  (R.evolve w)^[t]

/-- Gate matrix approximations whose entries differ from the exact matrices by at most
`2^(-lam)` for gates occurring in the word. -/
structure PrecisionGateApprox (q : ℕ) (gs : List FiniteGateCode) where

  lam : ℕ

  approx : FiniteGateCode → Matrix (Reg q) (Reg q) ℂ

  entryClose : ∀ g ∈ gs, ∀ i j : Reg q,
    ‖approx g i j - finiteCodeMatrix q g i j‖ ≤ (2 : ℝ) ^ (-(lam : ℤ))

/-- Apply the reverse product of the approximate gate matrices to the computational basis input. -/
noncomputable def PrecisionGateApprox.run {q : ℕ} {gs : List FiniteGateCode}
    (P : PrecisionGateApprox q gs) (x : Reg q) : QState (Reg q) :=
  Matrix.mulVec ((gs.map P.approx).reverse.prod) (Ket x)

/-- The measurement weight of the output event after running the approximate gate word. -/
noncomputable def PrecisionGateApprox.acceptProb {q : ℕ}
    {gs : List FiniteGateCode} (P : PrecisionGateApprox q gs) (x : Reg q) :
    ℝ :=
  MeasureProb (P.run x) (uniformBqpOutputEvent q)

/-- The explicit acceptance-error bound `2 * length * 2^q * 2^(-lam) * (1 + 2^q * 2^(-lam))^(2 *
length)`. -/
noncomputable def acceptProbPrecisionBound (q lam : ℕ)
    (gs : List FiniteGateCode) : ℝ :=
  2 * gs.length * ((2 ^ q : ℕ) : ℝ) * (2 : ℝ) ^ (-(lam : ℤ)) *
    (1 + ((2 ^ q : ℕ) : ℝ) * (2 : ℝ) ^ (-(lam : ℤ))) ^ (2 * gs.length)

/-- The five control states used by the concrete Fourier transition rule. -/
inductive FourierState where
  | q0 | qa | qb | qc | qf
  deriving DecidableEq, Fintype, Repr

/-- The tape alphabet consisting of a blank symbol and two bit symbols. -/
inductive FourierSymbol where
  | blank | bit0 | bit1
  deriving DecidableEq, Fintype, Repr

/-- Hadamard amplitudes on the two bit symbols, extended by zero whenever either symbol is
blank. -/
noncomputable def fourierH (b' b : FourierSymbol) : ℂ :=
  if b' = FourierSymbol.blank ∨ b = FourierSymbol.blank then 0
  else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
    (if b' = FourierSymbol.bit1 ∧ b = FourierSymbol.bit1 then -1 else 1)

/-- The concrete five-state transition rule that scans, applies Hadamard amplitudes, returns,
and resets from `qf` to `q0`. -/
noncomputable def fourierRule : QtmRule FourierState FourierSymbol where
  blank := FourierSymbol.blank
  start := FourierState.q0
  step := fun q a d q' b =>
    match q with
    | FourierState.q0 =>
        if d = QtmMove.right ∧ q' = FourierState.qa ∧ b = a then 1 else 0
    | FourierState.qa =>
        if d = QtmMove.left ∧ q' = FourierState.qb ∧ b = a then 1 else 0
    | FourierState.qb =>
        if a = FourierSymbol.blank then
          (if d = QtmMove.left ∧ q' = FourierState.qc ∧
              b = FourierSymbol.blank then 1 else 0)
        else if d = QtmMove.right ∧ q' = FourierState.qb then fourierH b a
        else 0
    | FourierState.qc =>
        if a = FourierSymbol.blank then
          (if d = QtmMove.right ∧ q' = FourierState.qf ∧
              b = FourierSymbol.blank then 1 else 0)
        else if d = QtmMove.left ∧ q' = FourierState.qc ∧ b = a then 1 else 0
    | FourierState.qf =>
        if d = QtmMove.right ∧ q' = FourierState.q0 ∧ b = a then 1 else 0

/-- The designated Fourier computation time `2 * n + 4`. -/
def bvFourierTime (n : ℕ) : ℕ := 2 * n + 4

/-- Place the `n` input bits in tape cells `1` through `n` and fill the other cells with blanks. -/
def fourierTape (n : ℕ) (s : Reg n) : Fin (n + 3) → FourierSymbol :=
  fun i =>
    if h : 0 < i.val ∧ i.val ≤ n then
      (if s ⟨i.val - 1, by omega⟩ then FourierSymbol.bit1
       else FourierSymbol.bit0)
    else FourierSymbol.blank

/-- The sign determined by the parity of the coordinatewise Boolean inner product of `s` and
`t`. -/
def hadamardSign {n : ℕ} (s t : Reg n) : ℂ :=
  if (Finset.univ.filter fun i : Fin n => s i && t i).card % 2 = 1 then -1
  else 1

/-- The normalized Boolean Fourier transform of an `n`-qubit amplitude vector. -/
noncomputable def hadamardN {n : ℕ} (φ : QState (Reg n)) : QState (Reg n) :=
  fun s => (((Real.sqrt 2) ^ n : ℝ)⁻¹ : ℂ) *
    ∑ t : Reg n, hadamardSign s t * φ t

/-- Embed the input amplitudes into configurations with control state `q0`, head at cell `1`,
and the corresponding Fourier tape. -/
noncomputable def fourierInit (n : ℕ) (φ : QState (Reg n)) :
    QState (QtmCfg FourierState FourierSymbol (n + 3)) :=
  fun c => ∑ s : Reg n,
    if c = (FourierState.q0, ⟨1, by omega⟩, fourierTape n s) then φ s else 0

/-- Embed the Boolean Fourier-transformed amplitudes into configurations with control state `qf`
and head at cell `1`. -/
noncomputable def fourierFinal (n : ℕ) (φ : QState (Reg n)) :
    QState (QtmCfg FourierState FourierSymbol (n + 3)) :=
  fun c => ∑ s : Reg n,
    if c = (FourierState.qf, ⟨1, by omega⟩, fourierTape n s) then
      hadamardN φ s
    else 0

/-- The property that a configuration has the specified halting control state. -/
def IsFinalCfg {Q : Type*} {A : Type*} (halt : Q) {w : ℕ}
    (c : QtmCfg Q A w) : Prop :=
  c.1 = halt

/-- A recursive Fourier sampling query symbol, either a Boolean bit or a separator. -/
inductive RfsSymbol where
  | bit : Bool → RfsSymbol
  | sep : RfsSymbol
  deriving DecidableEq, Fintype, Repr

/-- A recursive Fourier sampling query encoded as a list of query symbols. -/
abbrev RfsQuery := List RfsSymbol

/-- A Boolean-valued oracle on recursive Fourier sampling queries. -/
abbrev RfsOracle := RfsQuery → Bool

/-- The key length `2^l` at level `l`. -/
def rfsKeyLen (l : ℕ) : ℕ := 2 ^ l

/-- Append a separator and the bits of a child index to a query prefix. -/
def rfsChild (x : RfsQuery) {k : ℕ} (y : Reg k) : RfsQuery :=
  x ++ RfsSymbol.sep :: (List.ofFn fun i : Fin k => RfsSymbol.bit (y i))

/-- The Boolean parity character given by the coordinatewise inner product of an index and a
key. -/
def rfsChar {k : ℕ} (y key : Reg k) : Bool :=
  (Finset.univ.filter fun i : Fin k => y i && key i).card % 2 = 1

/-- Recursively evaluate a Fourier sampling node using a key representing the child values, with
the zero key as fallback when no such key exists. -/
noncomputable def rfsValueOf (f : RfsQuery → Bool) :
    (l : ℕ) → RfsQuery → Bool
  | 0, x => f x
  | l + 1, x =>
      f (rfsChild x
        (if h : ∃ k : Reg (rfsKeyLen (l + 1)),
            ∀ y : Reg (rfsKeyLen (l + 1)),
              rfsValueOf f l (rfsChild x y) = rfsChar y k
         then Classical.choose h
         else fun _ => false))

/-- Choose a key whose parity character matches all child values, or return the zero key when
the character condition fails. -/
noncomputable def rfsKeyOf (f : RfsQuery → Bool) (l : ℕ) (x : RfsQuery) :
    Reg (rfsKeyLen (l + 1)) :=
  if h : ∃ k : Reg (rfsKeyLen (l + 1)),
      ∀ y : Reg (rfsKeyLen (l + 1)),
        rfsValueOf f l (rfsChild x y) = rfsChar y k
  then Classical.choose h
  else fun _ => false

/-- The promise that every node at every positive level has child values given by a Boolean
parity character. -/
def RfsLegal (f : RfsQuery → Bool) : Prop :=
  ∀ (l : ℕ) (x : RfsQuery), ∃ k : Reg (rfsKeyLen (l + 1)),
    ∀ y : Reg (rfsKeyLen (l + 1)),
      rfsValueOf f l (rfsChild x y) = rfsChar y k

/-- The Boolean acceptance value given by recursive Fourier sampling evaluation. -/
noncomputable def rfsAccepts (f : RfsQuery → Bool) (l : ℕ)
    (x : RfsQuery) : Bool :=
  rfsValueOf f l x

/-- The product of `n / 2^i` over indices from zero through `Nat.log 2 n`, with value `1` at
zero. -/
def rfsGamma (n : ℕ) : ℕ :=
  if n = 0 then 1
  else ((List.range (Nat.log 2 n + 1)).foldl
    (fun acc i => acc * (n / 2 ^ i)) 1)

/-- The recursive count starting at `1` and adding one to the number of children times the count
at the preceding level. -/
def rfsNodeCount : ℕ → ℕ
  | 0 => 1
  | l + 1 => 1 + 2 ^ rfsKeyLen (l + 1) * rfsNodeCount l

/-- Pair the recursive Fourier sampling value with a count obtained by summing the child counts
and adding one. -/
noncomputable def rfsRecoverCounted (f : RfsQuery → Bool) :
    (l : ℕ) → RfsQuery → Bool × ℕ
  | 0, x => (f x, 1)
  | l + 1, x =>
      (rfsValueOf f (l + 1) x,
        1 + ∑ y : Reg (rfsKeyLen (l + 1)),
          (rfsRecoverCounted f l (rfsChild x y)).2)

/-- The recursive schedule with initial value `1` and update `c * (l + 2)^d + 4 * previous`. -/
def rfsTimeSchedule (c d : ℕ) : ℕ → ℕ
  | 0 => 1
  | l + 1 => c * (l + 2) ^ d + 4 * rfsTimeSchedule c d l

/-- A finite query set and answer function consistent with some legal recursive Fourier sampling
oracle. -/
structure RfsRun where

  queries : Finset RfsQuery

  answers : RfsQuery → Bool

  consistent : ∃ f : RfsQuery → Bool,
    RfsLegal f ∧ ∀ q ∈ queries, f q = answers q

/-- The predicate identifying a query at the root for level zero, or among the children and
recursively bounded descendants at positive levels. -/
def rfsQueryBelow : (l : ℕ) → (y : RfsQuery) → RfsQuery → Prop
  | 0, y, q => q = y
  | l + 1, y, q =>
      (∃ k : Reg (rfsKeyLen (l + 1)), q = rfsChild y k) ∨
        (∃ k : Reg (rfsKeyLen (l + 1)), rfsQueryBelow l (rfsChild y k) q)

/-- The number of queries in a transcript satisfying `rfsQueryBelow` for the given root and
level. -/
noncomputable def rfsRunQueriesBelow (r : RfsRun) (l : ℕ) (y : RfsQuery) :
    ℕ :=
  (r.queries.filter fun q => rfsQueryBelow l y q).card

/-- Finite recursive oracle data consisting of a Boolean leaf value or child answers together
with restrictions for all child subtrees. -/
def RfsRestr (x : RfsQuery) : (l : ℕ) → Type
  | 0 => Bool
  | l + 1 =>
      (Reg (rfsKeyLen (l + 1)) → Bool) ×
        ((y : Reg (rfsKeyLen (l + 1))) → RfsRestr (rfsChild x y) l)

/-- Construct the finite enumeration of recursive Fourier sampling restrictions at a given root
and depth. -/
def rfsRestrFintype (x : RfsQuery) : (l : ℕ) → Fintype (RfsRestr x l)
  | 0 => show Fintype Bool from inferInstance
  | l + 1 =>
      show Fintype ((Reg (rfsKeyLen (l + 1)) → Bool) ×
        ((y : Reg (rfsKeyLen (l + 1))) → RfsRestr (rfsChild x y) l)) from
      let sub : (y : Reg (rfsKeyLen (l + 1))) →
          Fintype (RfsRestr (rfsChild x y) l) :=
        fun y => rfsRestrFintype (rfsChild x y) l
      letI := sub
      letI : Fintype (Reg (rfsKeyLen (l + 1)) → Bool) := inferInstance
      inferInstance

instance (x : RfsQuery) (l : ℕ) : Fintype (RfsRestr x l) :=
  rfsRestrFintype x l

/-- Evaluate a restriction at its selected parity key, using the zero key when no matching key
exists. -/
noncomputable def RfsRestr.value {x : RfsQuery} :
    {l : ℕ} → RfsRestr x l → Bool
  | 0, ω => ω
  | l + 1, ω =>
      ω.1 (if h : ∃ k : Reg (rfsKeyLen (l + 1)),
          ∀ y : Reg (rfsKeyLen (l + 1)),
            RfsRestr.value (ω.2 y) = rfsChar y k
        then Classical.choose h
        else fun _ => false)

/-- Choose a parity key representing the child restriction values, with a zero-key fallback. -/
noncomputable def RfsRestr.key {x : RfsQuery} {l : ℕ}
    (ω : RfsRestr x (l + 1)) : Reg (rfsKeyLen (l + 1)) :=
  if h : ∃ k : Reg (rfsKeyLen (l + 1)),
      ∀ y : Reg (rfsKeyLen (l + 1)), RfsRestr.value (ω.2 y) = rfsChar y k
  then Classical.choose h
  else fun _ => false

/-- The recursive character promise on child values, together with legality of every child
restriction. -/
def RfsRestr.Legal {x : RfsQuery} :
    {l : ℕ} → RfsRestr x l → Prop
  | 0, _ => True
  | l + 1, ω =>
      (∃ k : Reg (rfsKeyLen (l + 1)),
        ∀ y : Reg (rfsKeyLen (l + 1)),
          RfsRestr.value (ω.2 y) = rfsChar y k) ∧
        ∀ y : Reg (rfsKeyLen (l + 1)), RfsRestr.Legal (ω.2 y)

/-- The property that a restriction's stored answers agree with every corresponding query answer
in a transcript. -/
def RfsRestr.Agree {x : RfsQuery} :
    {l : ℕ} → RfsRestr x l → RfsRun → Prop
  | 0, ω, r => ∀ q ∈ r.queries, q = x → r.answers q = ω
  | l + 1, ω, r =>
      (∀ k : Reg (rfsKeyLen (l + 1)),
        ∀ q ∈ r.queries, q = rfsChild x k → r.answers q = ω.1 k) ∧
        ∀ y : Reg (rfsKeyLen (l + 1)), RfsRestr.Agree (ω.2 y) r

/-- At positive depth, the property that the transcript queried the child selected by the
restriction's key; it is false at depth zero. -/
def RfsRestr.Hit {x : RfsQuery} :
    {l : ℕ} → RfsRestr x l → RfsRun → Prop
  | 0, _, _ => False
  | _ + 1, ω, r => rfsChild x (RfsRestr.key ω) ∈ r.queries

/-- Parse an exact child query of prefix `x` with `k` encoded bits, returning `none` for a
malformed query. -/
def rfsParseChild (x : RfsQuery) (k : ℕ) (q : RfsQuery) : Option (Reg k) :=
  if q.length = x.length + 1 + k ∧ q.take x.length = x ∧
      (q.drop x.length).head? = some RfsSymbol.sep then
    let bits := q.drop (x.length + 1)
    if bits.length = k ∧ ∀ b ∈ bits, b ≠ RfsSymbol.sep then
      some fun i : Fin k =>
        match (bits.drop i).head? with
        | some (RfsSymbol.bit b) => b
        | _ => false
    else none
  else none

/-- Parse the first child index of a query strictly longer than the corresponding child prefix. -/
def rfsParseDescendant (x : RfsQuery) (k : ℕ) (q : RfsQuery) : Option (Reg k) :=
  if x.length + 1 + k < q.length then
    rfsParseChild x k (q.take (x.length + 1 + k))
  else none

/-- Look up a query in a finite restriction by parsing its child prefixes, returning false
outside the represented data. -/
noncomputable def RfsRestr.lookup {x : RfsQuery} :
    {l : ℕ} → RfsRestr x l → RfsQuery → Bool
  | 0, ω, q => if q = x then ω else false
  | l + 1, ω, q =>
      match rfsParseChild x (rfsKeyLen (l + 1)) q with
      | some k => ω.1 k
      | none =>
          match rfsParseDescendant x (rfsKeyLen (l + 1)) q with
          | some y => RfsRestr.lookup (ω.2 y) q
          | none => false

/-- The fraction of legal restrictions consistent with a transcript whose selected child was
queried, defined as zero when there are no consistent legal restrictions. -/
noncomputable def rfsHitProb (l : ℕ) (x : RfsQuery) (r : RfsRun) : ℝ :=
  let all := (Finset.univ : Finset (RfsRestr x l)).filter
    fun ω => ω.Legal ∧ ω.Agree r
  if all.card = 0 then 0
  else ((all.filter fun ω => ω.Hit r).card : ℝ) / all.card

/-- A path step recording a level and a child index of the corresponding key length. -/
structure RfsStep where

  level : ℕ

  index : Reg (rfsKeyLen level)

/-- A list of level-index steps describing a path through recursive Fourier sampling queries. -/
abbrev RfsPath := List RfsStep

/-- The property that successive path steps have levels starting at `L` and decreasing by one
with natural-number subtraction. -/
def RfsPath.WF (L : ℕ) : RfsPath → Prop
  | [] => True
  | s :: rest => s.level = L ∧ RfsPath.WF (L - 1) rest

/-- Follow a list of child indices from the given query prefix. -/
def rfsPathNode (x : RfsQuery) : RfsPath → RfsQuery
  | [] => x
  | s :: rest => rfsPathNode (rfsChild x s.index) rest

/-- Return the selected key at the end of a compatible path through a restriction, with a
level-zero fallback for invalid traversal. -/
noncomputable def RfsRestr.chainKey {x : RfsQuery} :
    {L : ℕ} → RfsRestr x L → RfsPath → Σ l, Reg (rfsKeyLen l)
  | 0, _, [] => ⟨0, fun _ => false⟩
  | _ + 1, ω, [] => ⟨_, RfsRestr.key ω⟩
  | 0, _, _ :: _ => ⟨0, fun _ => false⟩
  | L + 1, ω, s :: rest =>
      if h : s.level = L + 1 then
        RfsRestr.chainKey (ω.2 (cast (congrArg (fun m => Reg (rfsKeyLen m))
          h) s.index)) rest
      else ⟨0, fun _ => false⟩

/-- The property that the transcript queried the child determined by the restriction's key at
the given path node. -/
def RfsRestr.HitAlong {x : RfsQuery} {L : ℕ} (ω : RfsRestr x L)
    (p : RfsPath) (r : RfsRun) : Prop :=
  rfsChild (rfsPathNode x p) (ω.chainKey p).2 ∈ r.queries

/-- The fraction of legal restrictions consistent with a transcript that satisfy `HitAlong` for
a given path, with value zero when the conditioning set is empty. -/
noncomputable def rfsHitProbAbove (L : ℕ) (x : RfsQuery) (p : RfsPath)
    (r : RfsRun) : ℝ :=
  let all := (Finset.univ : Finset (RfsRestr x L)).filter
    fun ω => ω.Legal ∧ ω.Agree r
  if all.card = 0 then 0
  else ((all.filter fun ω => ω.HitAlong p r).card : ℝ) / all.card

end Qatlib.Concepts.LocalMachine.LocalTransport
