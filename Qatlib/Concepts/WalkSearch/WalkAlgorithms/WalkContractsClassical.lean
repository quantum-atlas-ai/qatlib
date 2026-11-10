/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

def theorem3 : Prop :=
  ∀ (n : ℕ), (hn : 0 < n) →
    ∀ (G : OGraph n) (f : Fin n → Bool) (kcs : KCollisionSolver),
    ∃ r : ℕ,
      1 ≤ r ∧ n * n ≤ r * r * r ∧ r * r * r ≤ n * n * (n + 1) ∧
      (∀ ρ : kcs.seed,
        (match gcAlg G f kcs r ρ with
        | (some (u₀, u₁), _) => f u₀ = true ∧ f u₁ = true ∧ (u₀, u₁) ∈ G.edges ∧ u₀ ≠ u₁
        | (none, _) => True)) ∧
      ((∃ t, gcRel G f t = true) →
        ((@Finset.univ kcs.seed kcs.seedFin).filter fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 = none).card *
          (n + 1) ^ kcs.cExp ≤ @Fintype.card kcs.seed kcs.seedFin) ∧
      (∀ ρ : kcs.seed,
        ((gcAlg G f kcs r ρ).2 : ℝ) ≤
          (2 * kcs.κ : ℕ) * ((Nat.log 2 n + 2 : ℕ) ^ 2) * ((n : ℝ) ^ (2 / 3 : ℝ)))

noncomputable def triCheck {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (ntape : ncs.seed) :
    Option (Fin n × Fin n) × ℕ :=
  let e : Fin (Fintype.card ↥U) → Fin n := fun i => ((Fintype.equivFin ↥U).symm i : Fin n)
  let m : ℕ := Fintype.card ↥U
  let marked : Fin n → Bool :=
    fun v => decide (∃ u₁ ∈ U, ∃ u₂ ∈ U, u₁ ≠ u₂ ∧ adj v u₁ ∧ adj v u₂ ∧ adj u₁ u₂)
  let subR : Fin n → (Fin 2 → Fin m) → Bool :=
    fun v t => decide (t 0 ≠ t 1 ∧ adj v (e (t 0)) ∧ adj v (e (t 1)) ∧ adj (e (t 0)) (e (t 1)))
  let test : Fin n → Bool :=
    fun v =>
      ((List.range c₀).any fun i =>
        match kcs.run (n := m) (k := 2) r' (subR v) r' 1 0 (stape (v.val * c₀ + i)) with
        | some t => adj v (e (t 0)) && adj v (e (t 1))
        | none => false)
  let tcost :=
    c₀ * (kcs.κ * (Nat.log 2 (m + 1) + 2) * (r' + (m / r') * Nat.sqrt r')) + 2
  match ncs.run marked test tcost n ntape with
  | some v =>
      match kcs.run (n := m) (k := 2) r' (subR v) r' 1 0 (stape (v.val * c₀)) with
      | some t =>
          (some (e (t 0), e (t 1)),
            tcost * (Nat.log 2 (n + 1) + 2) * (Nat.sqrt (n + 1) + 1) +
              kcs.cost (n := m) (k := 2) r' (subR v) r' 1 0 (stape (v.val * c₀)) + 2)
      | none =>
          (none, tcost * (Nat.log 2 (n + 1) + 2) * (Nat.sqrt (n + 1) + 1) + 2)
  | none => (none, ncs.cost marked test tcost n ntape)

def triCheckSpec {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ) : Prop :=
  (∀ stape : ℕ → kcs.seed, ∀ ntape : ncs.seed,
    (match triCheck adj U kcs ncs r' c₀ stape ntape with
    | (some (u₁, u₂), _) => u₁ ∈ U ∧ u₂ ∈ U ∧ u₁ ≠ u₂ ∧
        ∃ v : Fin n, adj v u₁ = true ∧ adj v u₂ = true ∧ adj u₁ u₂ = true
    | (none, _) => True)) ∧
  ((∃ v : Fin n, ∃ u₁ ∈ U, ∃ u₂ ∈ U, u₁ ≠ u₂ ∧ adj v u₁ = true ∧ adj v u₂ = true ∧
      adj u₁ u₂ = true) →
    haveI := ncs.seedFin
    haveI := kcs.seedFin
    ((Finset.univ.filter fun ρ : ncs.seed × (Fin (n * c₀ + 1) → kcs.seed) =>
        (triCheck adj U kcs ncs r' c₀ (@extSeed (n * c₀ + 1) kcs.seed kcs.seedNe ρ.2) ρ.1).1 = none).card *
      (n + 1) ^ (min ncs.cExp (c₀ * kcs.cExp)) ≤
      2 * (Fintype.card ncs.seed * Fintype.card (Fin (n * c₀ + 1) → kcs.seed)))) ∧
  (∀ stape : ℕ → kcs.seed, ∀ ntape : ncs.seed,
    (triCheck adj U kcs ncs r' c₀ stape ntape).2 ≤
      (2 * cCOf kcs ncs n U.card r' c₀ : ℕ))

def theorem4 : Prop :=
  ∀ (n : ℕ), (hn : 0 < n) →
    ∀ (adj : Fin n → Fin n → Bool) (kcs : KCollisionSolver) (ncs : NoisySearch)
      (sgs : SafeGrover),
    ∃ r r' : ℕ,
      1 ≤ r ∧ n * n * n ≤ r * r * r * r * r ∧ r * r * r * r * r ≤ n * n * n * (n + 1) ∧
      1 ≤ r' ∧ r' * r' * r' ≤ r * r ∧ r * r ≤ r' * r' * r' * (r + 1) ∧
      triCheckSpec adj Finset.univ kcs ncs r' 4 ∧
      (∀ stape : ℕ → kcs.seed, ∀ gtape : ℕ → sgs.seed,
        (match th4Alg adj kcs ncs sgs r r' 4 stape gtape with
        | (some (a, b, c), _) =>
            a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
            adj a b = true ∧ adj a c = true ∧ adj b c = true
        | (none, _) => True)) ∧
      ((∃ t : Fin 2 → Fin n, triRel adj t = true) →
        haveI := kcs.seedFin
        haveI := sgs.seedFin
        ((Finset.univ.filter fun ρ : kcs.seed × sgs.seed =>
            (th4Alg adj kcs ncs sgs r r' 4 (fun _ => ρ.1) (fun _ => ρ.2)).1 = none).card *
          (n + 1) ^ (min kcs.cExp sgs.cExp) ≤
          2 * Fintype.card (kcs.seed × sgs.seed))) ∧
      (∀ stape : ℕ → kcs.seed, ∀ gtape : ℕ → sgs.seed,
        ((th4Alg adj kcs ncs sgs r r' 4 stape gtape).2 : ℝ) ≤
          (2 ^ 16 : ℕ) * ((Nat.log 2 n + 2 : ℕ) ^ 3) * ((n : ℝ) ^ (13 / 10 : ℝ)))

def theorem5 : Prop :=
  ∀ (n k : ℕ), 4 ≤ k → (hn : 0 < n) →
    ∀ (H : OGraph k) (hv : Fin k),
    ∀ (adj : Fin n → Fin n → Bool) (kcs : KCollisionSolver) (qH : ℕ),
    ∃ r : ℕ,
      1 ≤ r ∧ n ^ (k - 1) ≤ r ^ k ∧ r ^ k ≤ n ^ (k - 1) * (n + 1) ∧
      (∀ stape : ℕ → kcs.seed,
        (match hAlg adj H hv kcs r qH stape with
        | (some K, _) => hCandRel adj H hv K = true
        | (none, _) => True)) ∧
      ((∃ K : Fin (k - 1) → Fin n, hCandRel adj H hv K = true) →
        haveI := kcs.seedFin
        ((Finset.univ.filter fun ρ : kcs.seed =>
            (hAlg adj H hv kcs r qH (fun _ => ρ)).1 = none).card *
          (n + 1) ^ kcs.cExp ≤ 2 * Fintype.card kcs.seed)) ∧
      (∀ stape : ℕ → kcs.seed,
        ((hAlg adj H hv kcs r qH stape).2 : ℝ) ≤
          (2 ^ 16 : ℕ) * ((Nat.log 2 n + 2 : ℕ) ^ 3) *
            ((r : ℝ) ^ 2 +
              ((n : ℝ) / r) ^ ((k - 1) / 2) * ((qH : ℝ) + (Nat.sqrt r : ℝ) * r) +
              (qH : ℝ) + (n : ℝ)))

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
