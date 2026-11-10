/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Qatlib.Concepts.WalkSearch.Primitives

structure UGraph (n : ℕ) where

  edges : Finset (Fin n × Fin n)

  symm : ∀ a b : Fin n, (a, b) ∈ edges → (b, a) ∈ edges

  loopless : ∀ a : Fin n, (a, a) ∉ edges

variable {n : ℕ}

def nbrOf (S : Finset (Fin n × Fin n)) (v : Fin n) : Finset (Fin n) :=
  (S.filter fun p => p.1 = v).image Prod.snd ∪
    (S.filter fun p => p.2 = v).image Prod.fst

def degOf (S : Finset (Fin n × Fin n)) (v : Fin n) : ℕ := (nbrOf S v).card

def tOf (S : Finset (Fin n × Fin n)) (a b : Fin n) : ℕ :=
  (nbrOf S a ∩ nbrOf S b).card

def thinPairs (S : Finset (Fin n × Fin n)) (k : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => tOf S p.1 p.2 ≤ k

def tri3B (S : Finset (Fin n × Fin n)) (a b c : Fin n) : Bool :=
  a != b && b != c && a != c &&
    (decide ((a, b) ∈ S) || decide ((b, a) ∈ S)) &&
    (decide ((b, c) ∈ S) || decide ((c, b) ∈ S)) &&
    (decide ((a, c) ∈ S) || decide ((c, a) ∈ S))

def tri3 (S : Finset (Fin n × Fin n)) (a b c : Fin n) : Prop :=
  tri3B S a b c = true

def trianglesOf (S : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun x : Fin n × Fin n × Fin n =>
    x.1 < x.2.1 ∧ x.2.1 < x.2.2 ∧ tri3B S x.1 x.2.1 x.2.2

def triCount (S : Finset (Fin n × Fin n)) : ℕ := (trianglesOf S).card

def verticesOf (S : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  S.image Prod.fst ∪ S.image Prod.snd

structure SafeGrover where

  seed : Type

  [seedFin : Fintype seed]

  [seedNe : Nonempty seed]

  cExp : ℕ

  κ : ℕ

  run : {N : ℕ} → (marked : Fin N → Bool) → (check floor : ℕ) → seed → Option (Fin N)

  cost : {N : ℕ} → (marked : Fin N → Bool) → (check floor : ℕ) → seed → ℕ

  sound : ∀ {N} (marked : Fin N → Bool) (check floor : ℕ) (ρ : seed) {x : Fin N},
    run marked check floor ρ = some x → marked x = true

  reject : ∀ {N} (marked : Fin N → Bool) (check floor : ℕ) (ρ : seed),
    (∀ x, marked x = false) → run marked check floor ρ = none

  finds : ∀ {N} (marked : Fin N → Bool) (check floor : ℕ),
    (∃ x, marked x = true) →
    ((Finset.univ.filter fun ρ : seed => run marked check floor ρ = none).card : ℕ) *
      (max N floor + 1) ^ cExp ≤ Fintype.card seed

  charges : ∀ {N} (marked : Fin N → Bool) (check floor : ℕ) (ρ : seed),
    cost marked check floor ρ ≤
      κ * (Nat.log 2 (max N floor + 1) + 2) * (check + 1) * (Nat.sqrt (max N floor + 1) + 1)

structure EdgeTriSearch where

  seed : Type

  [seedFin : Fintype seed]

  [seedNe : Nonempty seed]

  cExp : ℕ

  κ : ℕ

  run : {n : ℕ} → (G : UGraph n) → (E : Finset (Fin n × Fin n)) → (floor : ℕ) →
    seed → Option (Fin n × Fin n × Fin n)

  cost : {n : ℕ} → (G : UGraph n) → (E : Finset (Fin n × Fin n)) → (floor : ℕ) → seed → ℕ

  sound : ∀ {n} (G : UGraph n) (E : Finset (Fin n × Fin n)) (floor : ℕ) (ρ : seed)
    {a b c : Fin n},
    run G E floor ρ = some (a, b, c) →
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (a, b) ∈ E ∧ (a, b) ∈ G.edges ∧ (a, c) ∈ G.edges ∧ (b, c) ∈ G.edges

  reject : ∀ {n} (G : UGraph n) (E : Finset (Fin n × Fin n)) (floor : ℕ) (ρ : seed),
    (∀ a b c : Fin n, ¬(a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (a, b) ∈ E ∧ (a, b) ∈ G.edges ∧ (a, c) ∈ G.edges ∧ (b, c) ∈ G.edges)) →
    run G E floor ρ = none

  finds : ∀ {n} (G : UGraph n) (E : Finset (Fin n × Fin n)) (floor : ℕ),
    (∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (a, b) ∈ E ∧ (a, b) ∈ G.edges ∧ (a, c) ∈ G.edges ∧ (b, c) ∈ G.edges) →
    ((Finset.univ.filter fun ρ : seed => run G E floor ρ = none).card : ℕ) *
      (floor + 1) ^ cExp ≤ Fintype.card seed

  charges : ∀ {n} (G : UGraph n) (E : Finset (Fin n × Fin n)) (floor : ℕ) (ρ : seed),
    cost G E floor ρ ≤
      κ * (Nat.log 2 (E.card + n * (E ∩ G.edges).card + 1) + 2) *
        (Nat.sqrt E.card + Nat.sqrt (n * (E ∩ G.edges).card) + 1)

def fact5 : Prop :=
  ∀ (n τ : ℕ) (T : Finset (Fin n × Fin n)) (l : List (Fin n × Fin n)),
    (∀ p, p ∈ T ↔ p ∈ l) →
    l.Nodup →
    (∀ i, (h : i < l.length) →
      tOf (l.take i).toFinset l[i].1 l[i].2 ≤ τ) →
    triCount T ≤ n.choose 2 * τ

def lemma3Sampling : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < n → 0 < ε → ε < 1 →
    let k : ℕ := Nat.ceil (4 * (n : ℝ) ^ ε * (Nat.log 2 n + 1))
    0 < k →
    ∀ (G : UGraph n),
      ((Finset.univ.filter (fun s : Fin k → Fin n =>
          ¬ (let S : Finset (Fin n) := Finset.univ.image s
             let G' : Finset (Fin n × Fin n) :=
               Finset.univ.filter fun p => ∀ v ∈ S, (p.1, v) ∉ G.edges ∨ (p.2, v) ∉ G.edges
             G' ⊆ thinPairs G.edges (Nat.floor ((n : ℝ) ^ (1 - ε)))))).card : ℕ) *
        n < Fintype.card (Fin k → Fin n)

def hitRounds (G : UGraph n) (v : Fin n) (K c : ℕ) (tape : Fin K → Fin c → Fin n) : ℕ :=
  (Finset.univ.filter fun i =>
    (Finset.univ.filter fun j => (v, tape i j) ∈ G.edges).card != 0).card

def degreeTestLow (G : UGraph n) (v : Fin n) (K c : ℕ) (tape : Fin K → Fin c → Fin n) : Bool :=
  decide (¬ (2 * hitRounds G v K c tape + 1 ≤ K))

def testCorrect (G : UGraph n) (v : Fin n) (dHi dLo K c : ℕ)
    (tape : Fin K → Fin c → Fin n) : Prop :=
  (dHi < degOf G.edges v → degreeTestLow G v K c tape = false) ∧
    (degOf G.edges v < dLo → degreeTestLow G v K c tape = true)

def fact2DegreeTest : Prop :=
  ∀ (n : ℕ) (δ : ℝ), 64 ≤ n → 0 < δ → δ < 1 →
    let K : ℕ := 64 * (Nat.log 2 n + 2)
    let c : ℕ := Nat.ceil ((n : ℝ) ^ δ)
    0 < c →
    ∀ (G : UGraph n) (v : Fin n),
      ((Finset.univ.filter fun tape : Fin K → Fin c → Fin n =>
          10 * Nat.ceil ((n : ℝ) ^ (1 - δ)) < degOf G.edges v ∧
            degreeTestLow G v K c tape).card : ℕ) * n ^ 3
        ≤ Fintype.card (Fin K → Fin c → Fin n) ∧
      ((Finset.univ.filter fun tape : Fin K → Fin c → Fin n =>
          degOf G.edges v < Nat.floor ((n : ℝ) ^ (1 - δ) / 10) ∧
            ¬ degreeTestLow G v K c tape).card : ℕ) * n ^ 3
        ≤ Fintype.card (Fin K → Fin c → Fin n)

def pairsAt (S : Finset (Fin n × Fin n)) (v : Fin n) : Finset (Fin n × Fin n) :=
  S.filter fun p => p.1 = v ∨ p.2 = v

def presentDeg (G : UGraph n) (S : Finset (Fin n × Fin n)) (v : Fin n) : ℕ :=
  (G.edges ∩ pairsAt S v).card

noncomputable def drainLow (S T : Finset (Fin n × Fin n)) (τ : ℕ) :
    ℕ → Finset (Fin n × Fin n) × Finset (Fin n × Fin n)
  | 0 => (S, T)
  | fuel + 1 =>
    match (Finset.univ.filter
      (fun p : Fin n × Fin n => p ∈ S ∧ tOf S p.1 p.2 < τ)).toList.head? with
    | some p => drainLow (S.erase p) (insert p T) τ fuel
    | none => (S, T)

noncomputable def pickOf {n : ℕ} (hn : 0 < n) (S : Finset (Fin n × Fin n)) : Fin n :=
  (verticesOf S).toList.head?.getD ⟨0, hn⟩

inductive ClassifyOut (n : ℕ) : Type

  | tri (v w w' : Fin n) (q : ℕ) : ClassifyOut n

  | part (T E : Finset (Fin n × Fin n)) (q : ℕ) : ClassifyOut n

noncomputable def sgsFind (sgs : SafeGrover) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) : Option α :=
  (sgs.run (fun i => marked ((Fintype.equivFin α).symm i)) check floor ρ).map
    fun i => (Fintype.equivFin α).symm i

noncomputable def sgsFindCost (sgs : SafeGrover) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) : ℕ :=
  sgs.cost (fun i => marked ((Fintype.equivFin α).symm i)) check floor ρ

noncomputable def extendSeed {B : ℕ} {seed : Type} [Nonempty seed] (τ : Fin B → seed)
    (i : ℕ) : seed :=
  if h : i < B then τ ⟨i, h⟩ else Classical.arbitrary seed

noncomputable def classify {n : ℕ} (hn : 0 < n) (G : UGraph n) (sgs : SafeGrover)
    (τ dHi dLo K c : ℕ) (ttape : Fin n → Fin K → Fin c → Fin n)
    (stape : ℕ → sgs.seed) :
    (G' T E : Finset (Fin n × Fin n)) → (q fuel : ℕ) → ClassifyOut n
  | _G', T, E, q, 0 => .part T E q
  | G', T, E, q, fuel + 1 =>
    if G' = ∅ then .part T E q
    else
      let ⟨G'd, Td⟩ := drainLow G' T τ fuel
      if G'd = ∅ then .part Td E q
      else
        let v := pickOf hn G'd
        let A' := nbrOf G'd v
        if ¬ degreeTestLow G v K c (ttape v) ∧ dLo ≤ presentDeg G G'd v then

          let A := nbrOf G.edges v
          let marked : Fin n × Fin n → Bool :=
            fun p => decide (p.1 ∈ A ∧ p.2 ∈ A ∧ p ∈ G.edges)
          let ρ := stape (2 * n * n + fuel)
          match sgsFind sgs marked 2 (n * n) ρ with
          | some (w, w') =>
              .tri v w w' (q + K * c + n + sgsFindCost sgs marked 2 (n * n) ρ)
          | none =>
              let Eadd :=
                G'd.filter fun p => p.1 = v ∨ p.2 = v ∨ (p.1 ∈ A ∧ p.2 ∈ A')
              classify hn G sgs τ dHi dLo K c ttape stape (G'd \ Eadd) Td (E ∪ Eadd)
                (q + K * c + n + sgsFindCost sgs marked 2 (n * n) ρ) fuel
        else

          let Ev := pairsAt G'd v
          classify hn G sgs τ dHi dLo K c ttape stape (G'd \ Ev) Td (E ∪ Ev)
            (q + K * c) fuel

def classifyBudget (n dLo τ K c : ℕ) (sgs : SafeGrover) : ℕ :=
  (n * n / (dLo * τ) + n + 1) *
    (K * c + n + sgs.κ * (Nat.log 2 (n * n + 1) + 2) * 3 * (n + 1))

def classifySpec : Prop :=
  ∀ (n : ℕ) (G : UGraph n) (sgs : SafeGrover) (τ dHi dLo K c tThin : ℕ),
    (hn : 0 < n) → 1 ≤ dLo → dLo ≤ dHi → 1 ≤ τ →
    ∀ (ttape : Fin n → Fin K → Fin c → Fin n),
      (∀ v : Fin n, testCorrect G v dHi dLo K c (ttape v)) →
      ∀ (stape : Fin (3 * n * n + 2) → sgs.seed) (G' : Finset (Fin n × Fin n)),
        G.edges ⊆ G' → G' ⊆ thinPairs G.edges tThin →
        (match classify hn G sgs τ dHi dLo K c ttape (@extendSeed (3 * n * n + 2) sgs.seed sgs.seedNe stape)
              G' ∅ ∅ 0 (G'.card + 1) with
        | .tri v w w' q =>
            (v, w) ∈ G.edges ∧ (v, w') ∈ G.edges ∧ (w, w') ∈ G.edges ∧
              v ≠ w ∧ w ≠ w' ∧ v ≠ w' ∧ q ≤ classifyBudget n dLo τ K c sgs
        | .part T E q =>
            T ∪ E = G' ∧ T ∩ E = ∅ ∧
              triCount T ≤ n.choose 2 * τ ∧
              (E ∩ G.edges).card ≤
                2 * n * dHi +
                  (n * n / (dLo * τ) + n + 1) * (dHi + n * (tThin + 1)) ∧
              q ≤ classifyBudget n dLo τ K c sgs)

inductive CombOut (n : ℕ) : Type

  | tri (a b c : Fin n) (q : ℕ) : CombOut n

  | reject (q : ℕ) : CombOut n

noncomputable def stepFour {n : ℕ} (hn : 0 < n) (G : UGraph n) (sgs : SafeGrover)
    (stape : ℕ → sgs.seed) :
    List (Fin n) → (i q : ℕ) → Option (Fin n × Fin n × Fin n) × ℕ
  | [], _i, q => (none, q)
  | v :: rest, i, q =>
      let A := nbrOf G.edges v
      let marked : Fin n × Fin n → Bool :=
        fun p => decide (p.1 ∈ A ∧ p.2 ∈ A ∧ p ∈ G.edges)
      let ρ := stape i
      match sgsFind sgs marked 2 (n * n) ρ with
      | some (w, w') => (some (v, w, w'), q + sgsFindCost sgs marked 2 (n * n) ρ)
      | none =>
        stepFour hn G sgs stape rest (i + 1)
          (q + sgsFindCost sgs marked 2 (n * n) ρ)

noncomputable def combAlg {n : ℕ} (hn : 0 < n) (G : UGraph n) (sgs : SafeGrover)
    (ets : EdgeTriSearch) (k K c dHi dLo τ _tThin : ℕ)
    (vtape : Fin k → Fin n) (ttape : Fin n → Fin K → Fin c → Fin n)
    (stape : ℕ → sgs.seed) (etstape : ℕ → ets.seed) : CombOut n :=
  let S : Finset (Fin n) := Finset.univ.image vtape
  let q₀ := k * n
  match stepFour hn G sgs stape S.toList 0 q₀ with
  | (some (a, b, cc), q₁) => .tri a b cc q₁
  | (none, q₁) =>
      let G' : Finset (Fin n × Fin n) :=
        Finset.univ.filter fun p => ∀ v ∈ S, (p.1, v) ∉ G.edges ∨ (p.2, v) ∉ G.edges
      match classify hn G sgs τ dHi dLo K c ttape (fun i => stape (k + i)) G' ∅ ∅ q₁
          (G'.card + 1) with
      | .tri v w w' q₂ => .tri v w w' q₂
      | .part T E q₂ =>
          let marked : {x // x ∈ trianglesOf T} → Bool :=
            fun t => match t with
              | ⟨(a, b, cc), _⟩ =>
                decide ((a, b) ∈ G.edges ∧ (a, cc) ∈ G.edges ∧ (b, cc) ∈ G.edges)
          let ρ := stape (k + 3 * n * n + 2)
          match sgsFind sgs (α := {x // x ∈ trianglesOf T}) marked 2 (n * n) ρ with
          | some t =>
            match t with
            | ⟨(a, b, cc), _⟩ =>
              .tri a b cc
                (q₂ + sgsFindCost sgs (α := {x // x ∈ trianglesOf T}) marked 2 (n * n) ρ)
          | none =>
              match ets.run G E (n * n) (etstape 0) with
              | some (a, b, cc) => .tri a b cc (q₂ + ets.cost G E (n * n) (etstape 0))
              | none => .reject (q₂ + ets.cost G E (n * n) (etstape 0))

@[reducible]
def combTape (n k K c : ℕ) (sgs : SafeGrover) (ets : EdgeTriSearch) (B : ℕ) : Type :=
  (Fin k → Fin n) × (Fin n → Fin K → Fin c → Fin n) ×
    (Fin B → sgs.seed) × (Fin B → ets.seed)

def combSound {n : ℕ} (hn : 0 < n) (G : UGraph n) (sgs : SafeGrover)
    (ets : EdgeTriSearch) (k K c dHi dLo τ _tThin B : ℕ) : Prop :=
  ∀ t : combTape n k K c sgs ets B,
    (match combAlg hn G sgs ets k K c dHi dLo τ _tThin
        t.1 t.2.1 (@extendSeed B sgs.seed sgs.seedNe t.2.2.1)
          (@extendSeed B ets.seed ets.seedNe t.2.2.2) with
    | .tri a b cc _ => tri3 G.edges a b cc ∧ (a, b) ∈ G.edges ∧
        (a, cc) ∈ G.edges ∧ (b, cc) ∈ G.edges
    | .reject _ => True)

def combComplete {n : ℕ} (hn : 0 < n) (G : UGraph n) (sgs : SafeGrover)
    (ets : EdgeTriSearch) (k K c dHi dLo τ tThin B : ℕ) : Prop :=
  1 ≤ triCount G.edges →
    haveI := sgs.seedFin
    haveI := ets.seedFin
    ((Finset.univ.filter fun t : combTape n k K c sgs ets B =>
        (match combAlg hn G sgs ets k K c dHi dLo τ tThin
            t.1 t.2.1 (@extendSeed B sgs.seed sgs.seedNe t.2.2.1)
              (@extendSeed B ets.seed ets.seedNe t.2.2.2) with
        | .tri _ _ _ _ => false
        | .reject _ => true) = true).card : ℕ) * n ≤
      2 * Fintype.card (combTape n k K c sgs ets B)

def combCost {n : ℕ} (hn : 0 < n) (G : UGraph n) (sgs : SafeGrover)
    (ets : EdgeTriSearch) (k K c dHi dLo τ tThin B : ℕ) (C : ℝ) : Prop :=
  ∀ t : combTape n k K c sgs ets B,
    (match combAlg hn G sgs ets k K c dHi dLo τ tThin
        t.1 t.2.1 (@extendSeed B sgs.seed sgs.seedNe t.2.2.1)
          (@extendSeed B ets.seed ets.seedNe t.2.2.2) with
    | .tri _ _ _ q => q
    | .reject q => q) ≤
      (2 ^ 24 : ℕ) * ((Nat.log 2 n + 2 : ℕ) ^ 4) * C

def theorem1 : Prop :=
  ∀ (n : ℕ) (ε δ ε' : ℝ), (hn : 0 < n) → 0 < ε → ε < 1 → 0 < δ → 0 < ε' → δ + ε' ≤ ε →
    ∀ (G : UGraph n) (sgs : SafeGrover) (ets : EdgeTriSearch),
    let k : ℕ := Nat.ceil (4 * (n : ℝ) ^ ε * (Nat.log 2 n + 1))
    let K : ℕ := 64 * (Nat.log 2 n + 2)
    let c : ℕ := Nat.ceil ((n : ℝ) ^ δ)
    let dHi : ℕ := 10 * Nat.ceil ((n : ℝ) ^ (1 - δ))
    let dLo : ℕ := Nat.floor ((n : ℝ) ^ (1 - δ) / 10)
    let τ : ℕ := Nat.ceil ((n : ℝ) ^ (1 - ε'))
    let tThin : ℕ := Nat.floor ((n : ℝ) ^ (1 - ε))
    let B : ℕ := k + 3 * n * n + 3
    0 < k → 0 < c → 1 ≤ dLo →
    combSound hn G sgs ets k K c dHi dLo τ tThin B ∧
    combComplete hn G sgs ets k K c dHi dLo τ tThin B ∧
    combCost hn G sgs ets k K c dHi dLo τ tThin B
      ((n : ℝ) ^ (1 + ε) + (n : ℝ) ^ (1 + δ + ε') +
        (n : ℝ) ^ ((3 - ε') / 2) +
        (n : ℝ) ^ ((3 - min δ (ε - δ - ε')) / 2))

def theorem1Dense : Prop :=
  ∀ (n : ℕ), (hn : 0 < n) →
    ∀ (G : UGraph n) (sgs : SafeGrover) (ets : EdgeTriSearch),
    let k : ℕ := Nat.ceil (4 * (n : ℝ) ^ (3 / 7 : ℝ) * (Nat.log 2 n + 1))
    let K : ℕ := 64 * (Nat.log 2 n + 2)
    let c : ℕ := Nat.ceil ((n : ℝ) ^ (1 / 7 : ℝ))
    let dHi : ℕ := 10 * Nat.ceil ((n : ℝ) ^ (6 / 7 : ℝ))
    let dLo : ℕ := Nat.floor ((n : ℝ) ^ (6 / 7 : ℝ) / 10)
    let τ : ℕ := Nat.ceil ((n : ℝ) ^ (6 / 7 : ℝ))
    let tThin : ℕ := Nat.floor ((n : ℝ) ^ (4 / 7 : ℝ))
    let B : ℕ := k + 3 * n * n + 3
    0 < k → 0 < c → 1 ≤ dLo →
    combSound hn G sgs ets k K c dHi dLo τ tThin B ∧
    combComplete hn G sgs ets k K c dHi dLo τ tThin B ∧
    combCost hn G sgs ets k K c dHi dLo τ tThin B
      (4 * (n : ℝ) ^ (10 / 7 : ℝ) + 2 * (n : ℝ) ^ (3 / 2 : ℝ) +
        (n : ℝ) ^ (10 / 7 : ℝ))

end Qatlib.Concepts.WalkSearch.Primitives
