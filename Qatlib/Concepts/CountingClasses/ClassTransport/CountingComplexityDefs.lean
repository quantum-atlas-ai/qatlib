/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic

/-!
# Bit machines and counting complexity

This module defines a finite control bit machine with coin flips and charged oracle calls.
`CcProgram`, `CcConfig`, and `ccRun` specify execution, while acceptance and witness counts
define complexity predicates within this model.

It also supplies affine Boolean hashes and query encodings for approximate counting. For
background on machine models and computational complexity, see [BernsteinVazirani1997].

## Main statements

* `ccStep`: one machine transition with resource counters.
* `InBPP`: bounded error decision in the bit machine model.
* `InSharpP`: counting polynomial length verified witnesses.
* `InFBPPNP`: bounded error function computation with an NP oracle.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

namespace Qatlib.Concepts.CountingClasses.ClassTransport

open scoped BigOperators Classical

/-- The instructions of a bit machine, including tape operations, random branching, oracle
queries, and halting outcomes. -/
inductive CcAct (q : ℕ) where

  | moveL (q' : Fin q)

  | moveR (q' : Fin q)

  | write (b : Bool) (q' : Fin q)

  | branch (qt qf : Fin q)

  | coinFlip (qt qf : Fin q)

  | queryPush (q' : Fin q)

  | oracleCall (qt qf : Fin q)

  | accept

  | reject

/-- A transition table with `q + 1` control states for the bit machine. -/
structure CcProgram (q : ℕ) where

  states : Fin (q + 1) → CcAct (q + 1)

/-- A bit machine configuration containing its control state, tape, head, query buffer, coin
position, and resource counters. -/
structure CcConfig (q : ℕ) where

  state : Fin (q + 1)

  tape : ℕ → Bool

  head : ℕ

  query : List Bool

  coinIdx : ℕ

  time : ℕ

  queries : ℕ

  queryBits : ℕ

  coins : ℕ

/-- The Boolean oracle that returns `false` on every query. -/
def ccZeroOracle : List Bool → Bool := fun _ => false

/-- The infinite coin sequence whose entries are all `false`. -/
def ccDefaultCoin : ℕ → Bool := fun _ => false

/-- The initial configuration with input `x` on a tape padded by `false`, control state zero,
and all counters zero. -/
def ccInit (q : ℕ) (x : List Bool) : CcConfig q where
  state := ⟨0, Nat.succ_pos q⟩
  tape := fun i => x.getD i false
  head := 0
  query := []
  coinIdx := 0
  time := 0
  queries := 0
  queryBits := 0
  coins := 0

/-- Execute one instruction using oracle `A` and coin sequence `ρ`, updating the resource
counters. Halting configurations remain fixed. -/
def ccStep {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (c : CcConfig q) : CcConfig q :=
  match P.states c.state with
  | CcAct.accept => c
  | CcAct.reject => c
  | CcAct.moveL q' => { c with state := q', head := c.head - 1, time := c.time + 1 }
  | CcAct.moveR q' => { c with state := q', head := c.head + 1, time := c.time + 1 }
  | CcAct.write b q' =>
      { c with
        state := q'
        tape := fun i => if i = c.head then b else c.tape i
        time := c.time + 1 }
  | CcAct.branch qt qf =>
      { c with
        state := if c.tape c.head then qt else qf
        time := c.time + 1 }
  | CcAct.coinFlip qt qf =>
      { c with
        state := if ρ c.coinIdx then qt else qf
        coinIdx := c.coinIdx + 1
        coins := c.coins + 1
        time := c.time + 1 }
  | CcAct.queryPush q' =>
      { c with
        state := q'
        query := c.query ++ [c.tape c.head]
        head := c.head + 1
        time := c.time + 1 }
  | CcAct.oracleCall qt qf =>
      { c with
        state := if A c.query then qt else qf
        tape := fun i => if i = c.head then A c.query else c.tape i
        query := []
        queries := c.queries + 1
        queryBits := c.queryBits + c.query.length
        time := c.time + c.query.length + 2 }

/-- The configuration obtained after `t` iterations of `ccStep` from the initial input
configuration. -/
def ccRun {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) : ℕ → CcConfig q
  | 0 => ccInit q x
  | t + 1 => ccStep P A ρ (ccRun P A ρ x t)

/-- The charged time recorded after `t` machine transitions. -/
def ccTime {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ := (ccRun P A ρ x t).time

/-- The number of oracle calls recorded after `t` machine transitions. -/
def ccQueries {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ := (ccRun P A ρ x t).queries

/-- The total length of oracle queries recorded after `t` machine transitions. -/
def ccQueryBits {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ := (ccRun P A ρ x t).queryBits

/-- The number of coin bits consumed after `t` machine transitions. -/
def ccCoinsRead {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ := (ccRun P A ρ x t).coins

/-- The tape prefix strictly before the head after `t` machine transitions. -/
def ccOutput {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : List Bool :=
  let c := ccRun P A ρ x t
  (List.range c.head).map c.tape

/-- The halting outcome after `t` transitions, or `none` when the current instruction is not a
halting instruction. -/
def ccResult {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : Option Bool :=
  match P.states (ccRun P A ρ x t).state with
  | CcAct.accept => some true
  | CcAct.reject => some false
  | _ => none

/-- A machine that pushes `ℓ` input bits into its query buffer, calls the oracle once, and then
accepts. -/
def ccCallMachine (ℓ : ℕ) : CcProgram (ℓ + 1) where
  states := fun i =>
    if h : (i : ℕ) < ℓ then CcAct.queryPush ⟨(i : ℕ) + 1, by omega⟩
    else if (i : ℕ) = ℓ then CcAct.oracleCall ⟨ℓ + 1, by omega⟩ ⟨ℓ + 1, by omega⟩
    else CcAct.accept

/-- Every oracle and coin sequence yields a halting result within `c * x.length ^ k + c`
transitions and charged time. -/
def CcPolyTime {q : ℕ} (P : CcProgram q) (c k : ℕ) : Prop :=
  ∀ (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool),
    ccResult P A ρ x (c * x.length ^ k + c) ≠ none ∧
      ccTime P A ρ x (c * x.length ^ k + c) ≤ c * x.length ^ k + c

/-- Extend a finite coin string to an infinite sequence by padding with `false`. -/
def ccCoinString {t : ℕ} (ω : Fin t → Bool) : ℕ → Bool :=
  fun i => if h : i < t then ω ⟨i, h⟩ else false

/-- The number of length `t` coin strings for which the machine accepts after `t` transitions. -/
def ccAcceptCount {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (x : List Bool)
    (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun ω : Fin t → Bool =>
    ccResult P A (ccCoinString ω) x t = some true)).card

/-- Test whether the machine accepts `z` with oracle `A` and the default coins at the prescribed
polynomial cutoff. -/
def ccOracleAccepts {q : ℕ} (V : CcProgram q) (A : List Bool → Bool) (c k : ℕ)
    (z : List Bool) : Bool :=
  decide (ccResult V A ccDefaultCoin z (c * z.length ^ k + c) = some true)

/-- Acceptance at the prescribed polynomial cutoff with the zero oracle and default coins. -/
def ccAccepts {q : ℕ} (V : CcProgram q) (c k : ℕ) (z : List Bool) : Bool :=
  ccOracleAccepts V ccZeroOracle c k z

/-- Run the default acceptance test on the concatenation of input `x` and witness `w`. -/
def ccVerifies {q : ℕ} (V : CcProgram q) (c k : ℕ) (x w : List Bool) : Bool :=
  ccAccepts V c k (x ++ w)

/-- Run the oracle acceptance test on the concatenation of input `x` and witness `w`. -/
def ccOracleVerifies {q : ℕ} (V : CcProgram q) (A : List Bool → Bool) (c k : ℕ)
    (x w : List Bool) : Bool :=
  ccOracleAccepts V A c k (x ++ w)

/-- Count accepted witnesses of length `p * x.length ^ p + p` for the verifier. -/
def ccRelCount {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) : ℕ :=
  (Finset.univ.filter (fun w : Fin (p * x.length ^ p + p) → Bool =>
    ccVerifies V c k x (List.ofFn w) = true)).card

/-- Count witnesses of length `p * x.length ^ p + p` whose concatenation with `x` is accepted
directly by oracle `A`. -/
def ccOracleRelCount (A : List Bool → Bool) (p : ℕ) (x : List Bool) : ℕ :=
  (Finset.univ.filter (fun w : Fin (p * x.length ^ p + p) → Bool =>
    A (x ++ List.ofFn w) = true)).card

/-- The language is decided by a polynomial time bit machine using the zero oracle and default
coins. -/
def InP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      ccResult M ccZeroOracle ccDefaultCoin x (c * x.length ^ k + c)
        = some (if L x then true else false)

/-- The language has a polynomial time verifier with existentially quantified witnesses of the
prescribed polynomial length. -/
def InNP (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ∃ w : Fin (p * x.length ^ p + p) → Bool,
        ccVerifies V c k x (List.ofFn w) = true)

/-- The predicate `InNP` on a set of Boolean strings. -/
def CcInNPSet (B : List Bool → Prop) : Prop := InNP B

/-- The language is decided by a polynomial time bit machine with acceptance probability at
least two thirds on members and at most one third on nonmembers. -/
def InBPP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x → 3 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
          ≥ 2 * 2 ^ (c * x.length ^ k + c))
        ∧ (¬L x → 3 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
            ≤ 2 ^ (c * x.length ^ k + c))

/-- The language consists exactly of inputs accepted on strictly more than half of the finite
coin strings by a polynomial time bit machine. -/
def InPP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x ↔ 2 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
          > 2 ^ (c * x.length ^ k + c))

/-- The function counts polynomial length witnesses accepted by a polynomial time bit machine
verifier. -/
def InSharpP (f : List Bool → ℕ) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool, f x = ccRelCount V c k p x

/-- The Boolean characteristic oracle of the predicate `B`. -/
noncomputable def ccOracleOf (B : List Bool → Prop) : List Bool → Bool :=
  fun z => decide (B z)

/-- Count length `t` coin strings yielding exactly the output tape prefix `y` after `t`
transitions. -/
def ccExactOutputCount {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (x : List Bool) (t : ℕ) (y : List Bool) : ℕ :=
  (Finset.univ.filter (fun ω : Fin t → Bool =>
    ccOutput M A (ccCoinString ω) x t = y)).card

/-- The function is computed with probability at least two thirds by a polynomial time bit
machine with an oracle for a language satisfying `InNP`. -/
def InFBPPNP (F : List Bool → List Bool) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q) (B : List Bool → Prop),
    CcInNPSet B ∧ CcPolyTime M c k ∧
      ∀ x : List Bool,
        3 * ccExactOutputCount M (ccOracleOf B) x (c * x.length ^ k + c) (F x)
          ≥ 2 * 2 ^ (c * x.length ^ k + c)

/-- Alternate existential and universal quantification over Boolean blocks of length `plen`,
starting with the quantifier selected by `ex`. -/
def ccAlt (ex : Bool) (plen : ℕ) (D : List Bool → Prop) : ℕ → List Bool → Prop
  | 0, z => D z
  | lev + 1, z =>
      if ex then ∃ w : Fin plen → Bool, ccAlt false plen D lev (z ++ List.ofFn w)
      else ∀ w : Fin plen → Bool, ccAlt true plen D lev (z ++ List.ofFn w)

/-- The language is expressed by `lev` alternating polynomial length witness blocks over a
polynomial time verifier, starting existentially. -/
def InPHLevel (lev : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ccAlt true (p * x.length ^ p + p)
        (fun z => ccAccepts V c k z = true) lev x)

/-- Strict majority acceptance by a polynomial time bit machine relative to oracle `A`. -/
def InOraclePP (A : List Bool → Bool) (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x ↔ 2 * ccAcceptCount M A x (c * x.length ^ k + c)
          > 2 ^ (c * x.length ^ k + c))

/-- Alternating polynomial length witness blocks over a polynomial time verifier relative to
oracle `A`, starting existentially. -/
def InOracleSigma (A : List Bool → Bool) (lev : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ccAlt true (p * x.length ^ p + p)
        (fun z => ccOracleAccepts V A c k z = true) lev x)

/-- The function counts polynomial length witnesses accepted directly by oracle `A` on the
concatenated input and witness. -/
def InSharpPOracle (A : List Bool → Bool) (f : List Bool → ℕ) : Prop :=
  ∃ p : ℕ, ∀ x : List Bool, f x = ccOracleRelCount A p x

/-- The set has an existential polynomial length witness characterization using a polynomial
time verifier relative to oracle `A`. -/
def CcInNPOracleSet (A : List Bool → Bool) (B : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ z : List Bool,
      (B z ↔ ∃ w : Fin (p * z.length ^ p + p) → Bool,
        ccOracleVerifies V A c k z (List.ofFn w) = true)

/-- The affine Boolean hash with linear part `Mat` and offset `b`, using parity for the row
sums. -/
def ccHash {ℓ m : ℕ} (Mat : Matrix (Fin ℓ) (Fin m) Bool) (b : Fin ℓ → Bool)
    (w : Fin m → Bool) : Fin ℓ → Bool :=
  fun i => Bool.xor (∑ j, (Mat i j && w j)) (b i)

/-- Encode a natural number as that many `true` bits followed by a `false` terminator. -/
def ccUnary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Read leading `true` bits into an accumulator, returning the count and the suffix after the
first `false` or the end of the list. -/
def ccReadUnaryAux : List Bool → ℕ → ℕ × List Bool
  | [], acc => (acc, [])
  | true :: rest, acc => ccReadUnaryAux rest (acc + 1)
  | false :: rest, acc => (acc, rest)

/-- Read a unary prefix with initial accumulator zero and return the remaining suffix. -/
def ccReadUnary (z : List Bool) : ℕ × List Bool := ccReadUnaryAux z 0

/-- Concatenate unary encodings of the hash dimension, input length, and matrix data length with
the matrix data and input. -/
def ccEncodeHashQuery (ℓ n : ℕ) (M x : List Bool) : List Bool :=
  ccUnary ℓ ++ ccUnary n ++ ccUnary M.length ++ M ++ x

/-- Parse the three unary headers and split the hash data from the input, returning `none` if
the remaining input length is incorrect. -/
def ccDecodeHashQuery (z : List Bool) : Option (ℕ × ℕ × List Bool × List Bool) :=
  let p₁ := ccReadUnary z
  let p₂ := ccReadUnary p₁.2
  let p₃ := ccReadUnary p₂.2
  if (p₃.2.drop p₃.1).length = p₂.1 then
    some (p₁.1, p₂.1, p₃.2.take p₃.1, p₃.2.drop p₃.1)
  else none

/-- Read an `ℓ` by `m` Boolean matrix in row order from a list, padding missing entries with
`false`. -/
def ccMatrixFromList (ℓ m : ℕ) (M : List Bool) : Matrix (Fin ℓ) (Fin m) Bool :=
  fun i j => M.getD ((i : ℕ) * m + j) false

/-- Read the affine offset vector after the first `ℓ * m` bits, padding missing entries with
`false`. -/
def ccVectorFromList (ℓ m : ℕ) (M : List Bool) : Fin ℓ → Bool :=
  fun i => M.getD (ℓ * m + i) false

/-- The encoded query has the required hash data length and possesses a verified witness that
hashes to the zero vector. -/
def ccHashWitnessSet {q : ℕ} (V : CcProgram q) (c k p : ℕ) :
    List Bool → Prop := fun z =>
  match ccDecodeHashQuery z with
  | none => False
  | some (ℓ, n, M, x) =>
      M.length = ℓ * (p * n ^ p + p) + ℓ ∧ ∃ w : Fin (p * n ^ p + p) → Bool,
        ccVerifies V c k x (List.ofFn w) = true ∧
          ∀ i : Fin ℓ, ccHash (ccMatrixFromList ℓ (p * n ^ p + p) M)
              (ccVectorFromList ℓ (p * n ^ p + p) M) w i = false

/-- The encoded query has the required hash data length and possesses a witness accepted by
oracle `A` that hashes to zero. -/
def ccHashWitnessOracleSet (A : List Bool → Bool) (p : ℕ) :
    List Bool → Prop := fun z =>
  match ccDecodeHashQuery z with
  | none => False
  | some (ℓ, n, M, x) =>
      M.length = ℓ * (p * n ^ p + p) + ℓ ∧ ∃ w : Fin (p * n ^ p + p) → Bool,
        A (x ++ List.ofFn w) = true ∧
          ∀ i : Fin ℓ, ccHash (ccMatrixFromList ℓ (p * n ^ p + p) M)
              (ccVectorFromList ℓ (p * n ^ p + p) M) w i = false

/-- Interpret a Boolean list as a binary natural number with the least significant bit first. -/
def ccBitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * ccBitsToNat bs

/-- Test relative counting error at most `1 / (d + 1)`, requiring an estimate of zero when the
true count is zero. -/
def ccApproxOK (d ŷ N : ℕ) : Bool :=
  if N = 0 then decide (ŷ = 0)
  else decide ((d + 1) * ((ŷ : ℤ) - (N : ℤ)).natAbs ≤ N)

/-- Count finite coin strings for which the binary output of the estimator satisfies
`ccApproxOK` for the target count `N`. -/
def ccEstGoodCount {q : ℕ} (E : CcProgram q) (A : List Bool → Bool) (x : List Bool)
    (t d N : ℕ) : ℕ :=
  (Finset.univ.filter (fun ω : Fin t → Bool =>
    ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString ω) x t)) N = true)).card

end Qatlib.Concepts.CountingClasses.ClassTransport
