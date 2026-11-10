/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

structure OGraph (n : ℕ) where

  edges : Finset (Fin n × Fin n)

  symm : ∀ a b : Fin n, (a, b) ∈ edges → (b, a) ∈ edges

  loopless : ∀ a : Fin n, (a, a) ∉ edges

variable {n : ℕ}

def adjB (G : OGraph n) (a b : Fin n) : Bool := decide ((a, b) ∈ G.edges)

structure KCollisionSolver where

  seed : Type

  [seedFin : Fintype seed]

  [seedNe : Nonempty seed]

  cExp : ℕ

  κ : ℕ

  run : {n k : ℕ} → (r : ℕ) → (R : (Fin k → Fin n) → Bool) → (s u c : ℕ) → seed →
    Option (Fin k → Fin n)

  cost : {n k : ℕ} → (r : ℕ) → (R : (Fin k → Fin n) → Bool) → (s u c : ℕ) → seed → ℕ

  sound : ∀ {n k} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ) (ρ : seed)
    {t : Fin k → Fin n},
    run r R s u c ρ = some t → R t = true

  reject : ∀ {n k} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ) (ρ : seed),
    (∀ t, R t = false) → run r R s u c ρ = none

  finds : ∀ {n k} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ),
    (∃ t, R t = true) →
    ((Finset.univ.filter fun ρ : seed => run r R s u c ρ = none).card : ℕ) *
      (n + 1) ^ cExp ≤ Fintype.card seed

  charges : ∀ {n k} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ) (ρ : seed),
    cost r R s u c ρ ≤
      κ * (Nat.log 2 (n + 1) + 2) * (s + (n / r) ^ (k / 2) * (c + Nat.sqrt r * u))

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

structure NoisySearch where

  seed : Type

  [seedFin : Fintype seed]

  [seedNe : Nonempty seed]

  cExp : ℕ

  κ : ℕ

  run : {N : ℕ} → (marked : Fin N → Bool) → (test : Fin N → Bool) →
    (tcost floor : ℕ) → seed → Option (Fin N)

  cost : {N : ℕ} → (marked : Fin N → Bool) → (test : Fin N → Bool) →
    (tcost floor : ℕ) → seed → ℕ

  sound : ∀ {N} (marked : Fin N → Bool) (test : Fin N → Bool)
    (tcost floor : ℕ) (ρ : seed) {v : Fin N},
    run marked test tcost floor ρ = some v → marked v = true

  reject : ∀ {N} (marked : Fin N → Bool) (test : Fin N → Bool)
    (tcost floor : ℕ) (ρ : seed),
    (∀ v, marked v = false) → run marked test tcost floor ρ = none

  finds : ∀ {N} (marked : Fin N → Bool) (test : Fin N → Bool) (tcost floor : ℕ),
    (∃ v, marked v = true) →
    (∀ v, test v = true → marked v = true) →
    ((Finset.univ.filter fun ρ : seed => run marked test tcost floor ρ = none).card : ℕ) *
      (floor + 1) ^ cExp ≤ Fintype.card seed

  charges : ∀ {N} (marked : Fin N → Bool) (test : Fin N → Bool) (tcost floor : ℕ)
    (ρ : seed),
    cost marked test tcost floor ρ ≤
      κ * (Nat.log 2 (floor + 1) + 2) * (tcost + 1) * (Nat.sqrt (floor + 1) + 1)

noncomputable def extSeed {B : ℕ} {seed : Type} [Nonempty seed] (τ : Fin B → seed)
    (i : ℕ) : seed :=
  if h : i < B then τ ⟨i, h⟩ else Classical.arbitrary seed

def gcRel (G : OGraph n) (f : Fin n → Bool) (t : Fin 2 → Fin n) : Bool :=
  f (t 0) && f (t 1) && adjB G (t 0) (t 1)

noncomputable def gcAlg {n : ℕ} (G : OGraph n) (f : Fin n → Bool) (kcs : KCollisionSolver)
    (r : ℕ) (ρ : kcs.seed) : Option (Fin n × Fin n) × ℕ :=
  match kcs.run r (gcRel G f) r 1 0 ρ with
  | some t =>
      let u₀ := t 0
      let u₁ := t 1
      if f u₀ && f u₁ && adjB G u₀ u₁ then (some (u₀, u₁), kcs.cost r (gcRel G f) r 1 0 ρ + 2)
      else (none, kcs.cost r (gcRel G f) r 1 0 ρ + 2)
  | none => (none, kcs.cost r (gcRel G f) r 1 0 ρ)

def cCOf (kcs : KCollisionSolver) (ncs : NoisySearch) (n r r' c₀ : ℕ) : ℕ :=
  ncs.κ * (Nat.log 2 (n + 1) + 2) *
    (c₀ * (kcs.κ * (Nat.log 2 (r + 1) + 2) * (r' + (r / r') * Nat.sqrt r')) + 3) *
    (Nat.sqrt (n + 1) + 1)

def triRel {n : ℕ} (adj : Fin n → Fin n → Bool) (t : Fin 2 → Fin n) : Bool :=
  decide (t 0 ≠ t 1 ∧ adj (t 0) (t 1) ∧ ∃ w : Fin n, adj (t 0) w ∧ adj (t 1) w)

noncomputable def th4Alg {n : ℕ} (adj : Fin n → Fin n → Bool)
    (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover) (r r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (gtape : ℕ → sgs.seed) :
    Option (Fin n × Fin n × Fin n) × ℕ :=
  let cC := cCOf kcs ncs n r r' c₀
  match kcs.run (n := n) (k := 2) r (triRel adj) (r * r) r cC (stape 0) with
  | some t =>
      let u₁ := t 0
      let u₂ := t 1
      let marked : Fin n → Bool :=
        fun w => decide (w ≠ u₁ ∧ w ≠ u₂ ∧ adj u₁ w ∧ adj u₂ w)
      match sgs.run marked 3 n (gtape 0) with
      | some w =>
          if adj u₁ u₂ && adj u₁ w && adj u₂ w then
            (some (u₁, u₂, w),
              kcs.cost (n := n) (k := 2) r (triRel adj) (r * r) r cC (stape 0) +
                sgs.cost marked 3 n (gtape 0) + 3)
          else
            (none, kcs.cost (n := n) (k := 2) r (triRel adj) (r * r) r cC (stape 0) +
              sgs.cost marked 3 n (gtape 0) + 3)
      | none =>
          (none, kcs.cost (n := n) (k := 2) r (triRel adj) (r * r) r cC (stape 0) +
            sgs.cost marked 3 n (gtape 0))
  | none => (none, kcs.cost (n := n) (k := 2) r (triRel adj) (r * r) r cC (stape 0))

def hCandRel {n k : ℕ} (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (K : Fin (k - 1) → Fin n) : Bool :=
  decide (
    (∀ i j : Fin (k - 1), i ≠ j → K i ≠ K j) ∧
    ∃ v : Fin n, ∃ σ : Fin k → Fin n,
      (∀ i j : Fin k, i ≠ j → σ i ≠ σ j) ∧
      σ hv = v ∧
      (∀ i : Fin k, i ≠ hv → ∃ j : Fin (k - 1), σ i = K j) ∧
      (∀ a b : Fin k, (a, b) ∈ H.edges → adj (σ a) (σ b) = true))

noncomputable def hAlg {n k : ℕ} (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (kcs : KCollisionSolver) (r qH : ℕ) (stape : ℕ → kcs.seed) :
    Option (Fin (k - 1) → Fin n) × ℕ :=
  match kcs.run (k := k - 1) r (hCandRel adj H hv) (r * r) r qH (stape 0) with
  | some K =>
      if hCandRel adj H hv K then
        (some K, kcs.cost (k := k - 1) r (hCandRel adj H hv) (r * r) r qH (stape 0))
      else
        (none, kcs.cost (k := k - 1) r (hCandRel adj H hv) (r * r) r qH (stape 0))
  | none => (none, kcs.cost (k := k - 1) r (hCandRel adj H hv) (r * r) r qH (stape 0))

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
