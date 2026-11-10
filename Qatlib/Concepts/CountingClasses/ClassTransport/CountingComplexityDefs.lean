/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic

namespace Qatlib.Concepts.CountingClasses.ClassTransport

open scoped BigOperators Classical

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

structure CcProgram (q : ℕ) where

  states : Fin (q + 1) → CcAct (q + 1)

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

def ccZeroOracle : List Bool → Bool := fun _ => false

def ccDefaultCoin : ℕ → Bool := fun _ => false

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

def ccRun {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) : ℕ → CcConfig q
  | 0 => ccInit q x
  | t + 1 => ccStep P A ρ (ccRun P A ρ x t)

def ccTime {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ := (ccRun P A ρ x t).time

def ccQueries {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ := (ccRun P A ρ x t).queries

def ccQueryBits {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ := (ccRun P A ρ x t).queryBits

def ccCoinsRead {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ := (ccRun P A ρ x t).coins

def ccOutput {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : List Bool :=
  let c := ccRun P A ρ x t
  (List.range c.head).map c.tape

def ccResult {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : Option Bool :=
  match P.states (ccRun P A ρ x t).state with
  | CcAct.accept => some true
  | CcAct.reject => some false
  | _ => none

def ccCallMachine (ℓ : ℕ) : CcProgram (ℓ + 1) where
  states := fun i =>
    if h : (i : ℕ) < ℓ then CcAct.queryPush ⟨(i : ℕ) + 1, by omega⟩
    else if (i : ℕ) = ℓ then CcAct.oracleCall ⟨ℓ + 1, by omega⟩ ⟨ℓ + 1, by omega⟩
    else CcAct.accept

def CcPolyTime {q : ℕ} (P : CcProgram q) (c k : ℕ) : Prop :=
  ∀ (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool),
    ccResult P A ρ x (c * x.length ^ k + c) ≠ none ∧
      ccTime P A ρ x (c * x.length ^ k + c) ≤ c * x.length ^ k + c

def ccCoinString {t : ℕ} (ω : Fin t → Bool) : ℕ → Bool :=
  fun i => if h : i < t then ω ⟨i, h⟩ else false

def ccAcceptCount {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (x : List Bool)
    (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun ω : Fin t → Bool =>
    ccResult P A (ccCoinString ω) x t = some true)).card

def ccOracleAccepts {q : ℕ} (V : CcProgram q) (A : List Bool → Bool) (c k : ℕ)
    (z : List Bool) : Bool :=
  decide (ccResult V A ccDefaultCoin z (c * z.length ^ k + c) = some true)

def ccAccepts {q : ℕ} (V : CcProgram q) (c k : ℕ) (z : List Bool) : Bool :=
  ccOracleAccepts V ccZeroOracle c k z

def ccVerifies {q : ℕ} (V : CcProgram q) (c k : ℕ) (x w : List Bool) : Bool :=
  ccAccepts V c k (x ++ w)

def ccOracleVerifies {q : ℕ} (V : CcProgram q) (A : List Bool → Bool) (c k : ℕ)
    (x w : List Bool) : Bool :=
  ccOracleAccepts V A c k (x ++ w)

def ccRelCount {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) : ℕ :=
  (Finset.univ.filter (fun w : Fin (p * x.length ^ p + p) → Bool =>
    ccVerifies V c k x (List.ofFn w) = true)).card

def ccOracleRelCount (A : List Bool → Bool) (p : ℕ) (x : List Bool) : ℕ :=
  (Finset.univ.filter (fun w : Fin (p * x.length ^ p + p) → Bool =>
    A (x ++ List.ofFn w) = true)).card

def InP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      ccResult M ccZeroOracle ccDefaultCoin x (c * x.length ^ k + c)
        = some (if L x then true else false)

def InNP (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ∃ w : Fin (p * x.length ^ p + p) → Bool,
        ccVerifies V c k x (List.ofFn w) = true)

def CcInNPSet (B : List Bool → Prop) : Prop := InNP B

def InBPP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x → 3 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
          ≥ 2 * 2 ^ (c * x.length ^ k + c))
        ∧ (¬L x → 3 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
            ≤ 2 ^ (c * x.length ^ k + c))

def InPP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x ↔ 2 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
          > 2 ^ (c * x.length ^ k + c))

def InSharpP (f : List Bool → ℕ) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool, f x = ccRelCount V c k p x

noncomputable def ccOracleOf (B : List Bool → Prop) : List Bool → Bool :=
  fun z => decide (B z)

def ccExactOutputCount {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (x : List Bool) (t : ℕ) (y : List Bool) : ℕ :=
  (Finset.univ.filter (fun ω : Fin t → Bool =>
    ccOutput M A (ccCoinString ω) x t = y)).card

def InFBPPNP (F : List Bool → List Bool) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q) (B : List Bool → Prop),
    CcInNPSet B ∧ CcPolyTime M c k ∧
      ∀ x : List Bool,
        3 * ccExactOutputCount M (ccOracleOf B) x (c * x.length ^ k + c) (F x)
          ≥ 2 * 2 ^ (c * x.length ^ k + c)

def ccAlt (ex : Bool) (plen : ℕ) (D : List Bool → Prop) : ℕ → List Bool → Prop
  | 0, z => D z
  | lev + 1, z =>
      if ex then ∃ w : Fin plen → Bool, ccAlt false plen D lev (z ++ List.ofFn w)
      else ∀ w : Fin plen → Bool, ccAlt true plen D lev (z ++ List.ofFn w)

def InPHLevel (lev : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ccAlt true (p * x.length ^ p + p)
        (fun z => ccAccepts V c k z = true) lev x)

def InOraclePP (A : List Bool → Bool) (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x ↔ 2 * ccAcceptCount M A x (c * x.length ^ k + c)
          > 2 ^ (c * x.length ^ k + c))

def InOracleSigma (A : List Bool → Bool) (lev : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ccAlt true (p * x.length ^ p + p)
        (fun z => ccOracleAccepts V A c k z = true) lev x)

def InSharpPOracle (A : List Bool → Bool) (f : List Bool → ℕ) : Prop :=
  ∃ p : ℕ, ∀ x : List Bool, f x = ccOracleRelCount A p x

def CcInNPOracleSet (A : List Bool → Bool) (B : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ z : List Bool,
      (B z ↔ ∃ w : Fin (p * z.length ^ p + p) → Bool,
        ccOracleVerifies V A c k z (List.ofFn w) = true)

def ccHash {ℓ m : ℕ} (Mat : Matrix (Fin ℓ) (Fin m) Bool) (b : Fin ℓ → Bool)
    (w : Fin m → Bool) : Fin ℓ → Bool :=
  fun i => Bool.xor (∑ j, (Mat i j && w j)) (b i)

def ccUnary (n : ℕ) : List Bool := List.replicate n true ++ [false]

def ccReadUnaryAux : List Bool → ℕ → ℕ × List Bool
  | [], acc => (acc, [])
  | true :: rest, acc => ccReadUnaryAux rest (acc + 1)
  | false :: rest, acc => (acc, rest)

def ccReadUnary (z : List Bool) : ℕ × List Bool := ccReadUnaryAux z 0

def ccEncodeHashQuery (ℓ n : ℕ) (M x : List Bool) : List Bool :=
  ccUnary ℓ ++ ccUnary n ++ ccUnary M.length ++ M ++ x

def ccDecodeHashQuery (z : List Bool) : Option (ℕ × ℕ × List Bool × List Bool) :=
  let p₁ := ccReadUnary z
  let p₂ := ccReadUnary p₁.2
  let p₃ := ccReadUnary p₂.2
  if (p₃.2.drop p₃.1).length = p₂.1 then
    some (p₁.1, p₂.1, p₃.2.take p₃.1, p₃.2.drop p₃.1)
  else none

def ccMatrixFromList (ℓ m : ℕ) (M : List Bool) : Matrix (Fin ℓ) (Fin m) Bool :=
  fun i j => M.getD ((i : ℕ) * m + j) false

def ccVectorFromList (ℓ m : ℕ) (M : List Bool) : Fin ℓ → Bool :=
  fun i => M.getD (ℓ * m + i) false

def ccHashWitnessSet {q : ℕ} (V : CcProgram q) (c k p : ℕ) :
    List Bool → Prop := fun z =>
  match ccDecodeHashQuery z with
  | none => False
  | some (ℓ, n, M, x) =>
      M.length = ℓ * (p * n ^ p + p) + ℓ ∧ ∃ w : Fin (p * n ^ p + p) → Bool,
        ccVerifies V c k x (List.ofFn w) = true ∧
          ∀ i : Fin ℓ, ccHash (ccMatrixFromList ℓ (p * n ^ p + p) M)
              (ccVectorFromList ℓ (p * n ^ p + p) M) w i = false

def ccHashWitnessOracleSet (A : List Bool → Bool) (p : ℕ) :
    List Bool → Prop := fun z =>
  match ccDecodeHashQuery z with
  | none => False
  | some (ℓ, n, M, x) =>
      M.length = ℓ * (p * n ^ p + p) + ℓ ∧ ∃ w : Fin (p * n ^ p + p) → Bool,
        A (x ++ List.ofFn w) = true ∧
          ∀ i : Fin ℓ, ccHash (ccMatrixFromList ℓ (p * n ^ p + p) M)
              (ccVectorFromList ℓ (p * n ^ p + p) M) w i = false

def ccBitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * ccBitsToNat bs

def ccApproxOK (d ŷ N : ℕ) : Bool :=
  if N = 0 then decide (ŷ = 0)
  else decide ((d + 1) * ((ŷ : ℤ) - (N : ℤ)).natAbs ≤ N)

def ccEstGoodCount {q : ℕ} (E : CcProgram q) (A : List Bool → Bool) (x : List Bool)
    (t d N : ℕ) : ℕ :=
  (Finset.univ.filter (fun ω : Fin t → Bool =>
    ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString ω) x t)) N = true)).card

end Qatlib.Concepts.CountingClasses.ClassTransport
