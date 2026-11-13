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

/-!
# Corrected graph-search contracts

This module defines `triCheckAmpExtract` and `triCheckAmp`, which use repeated collision-search
calls to extract a validated candidate while accumulating charges. The proposition
`triCheckSpecCorrected` records the corresponding soundness, failure, and cost requirements.

The contracts `theorem3WalkCorrected`, `theorem4WalkCorrected`, and `theorem5WalkCorrected`
track positive solver constants; the latter two use least-power subset windows. These
formulations support the quantum search bounds discussed in [Ambainis2005].

## References

* [Ambainis, 2005][Ambainis2005]
-/

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- Tries up to `c₀` collision-search seeds for a fixed vertex, retains the first candidate
passing the two incident-edge checks, and accumulates the charges of attempted calls. -/
noncomputable def triCheckAmpExtract {n : ℕ} (adj : Fin n → Fin n → Bool) {m : ℕ}
    (e : Fin m → Fin n) (kcs : KCollisionSolver) (r' : ℕ)
    (subR : (Fin 2 → Fin m) → Bool) (v : Fin n) (c₀ : ℕ) (stape : ℕ → kcs.seed) :
    Option (Fin 2 → Fin m) × ℕ :=
  (List.range c₀).foldl (fun acc i =>
    match acc with
    | (some t, q) => (some t, q)
    | (none, q) =>
        let qᵢ := kcs.cost (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i))
        match kcs.run (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) with
        | some t =>
            if adj v (e (t 0)) && adj v (e (t 1)) then (some t, q + qᵢ) else (none, q + qᵢ)
        | none => (none, q + qᵢ)) (none, 0)

/-- Uses noisy search with repeated collision tests and then `triCheckAmpExtract` on the same
seed tape to return a pair inside `U` together with its accumulated charge. -/
noncomputable def triCheckAmp {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
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
  | none => (none, ncs.cost marked test tcost n ntape)
  | some v =>
      let ex := triCheckAmpExtract adj e kcs r' (subR v) v c₀ stape
      match ex.1 with
      | some t =>
          (some (e (t 0), e (t 1)), ncs.cost marked test tcost n ntape + ex.2 + 2)
      | none =>
          (none, ncs.cost marked test tcost n ntape + ex.2 + 2)

/-- The specification of `triCheckAmp` under positive solver constants, requiring sound output,
a failure-count bound scaled by `U.card + 1`, and a cost bound by twice `cCOf`. -/
def triCheckSpecCorrected {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ) : Prop :=
  1 ≤ kcs.κ → 1 ≤ ncs.κ →
  (∀ stape : ℕ → kcs.seed, ∀ ntape : ncs.seed,
    (match triCheckAmp adj U kcs ncs r' c₀ stape ntape with
    | (some (u₁, u₂), _) => u₁ ∈ U ∧ u₂ ∈ U ∧ u₁ ≠ u₂ ∧
        ∃ v : Fin n, adj v u₁ = true ∧ adj v u₂ = true ∧ adj u₁ u₂ = true
    | (none, _) => True)) ∧
  ((∃ v : Fin n, ∃ u₁ ∈ U, ∃ u₂ ∈ U, u₁ ≠ u₂ ∧ adj v u₁ = true ∧ adj v u₂ = true ∧
      adj u₁ u₂ = true) →
    haveI := ncs.seedFin
    haveI := kcs.seedFin
    ((Finset.univ.filter fun ρ : ncs.seed × (Fin (n * c₀ + 1) → kcs.seed) =>
        (triCheckAmp adj U kcs ncs r' c₀ (@extSeed (n * c₀ + 1) kcs.seed kcs.seedNe ρ.2) ρ.1).1 = none).card *
      (U.card + 1) ^ (min ncs.cExp (c₀ * kcs.cExp)) ≤
      2 * (Fintype.card ncs.seed * Fintype.card (Fin (n * c₀ + 1) → kcs.seed)))) ∧
  (∀ stape : ℕ → kcs.seed, ∀ ntape : ncs.seed,
    (triCheckAmp adj U kcs ncs r' c₀ stape ntape).2 ≤
      (2 * cCOf kcs ncs n U.card r' c₀ : ℕ))

/-- The graph-collision contract with a positive collision-solver constant, soundness, a
finite-seed failure bound, and an explicit n^(2/3) cost estimate with a squared logarithmic
factor. -/
def theorem3WalkCorrected : Prop :=
  ∀ (n : ℕ), (hn : 0 < n) →
    ∀ (G : OGraph n) (f : Fin n → Bool) (kcs : KCollisionSolver), 1 ≤ kcs.κ →
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

/-- The maximum of the collision, noisy-search, and safe Grover-search charge constants. -/
def walkKappa (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover) : ℕ :=
  max kcs.κ (max ncs.κ sgs.κ)

/-- The triangle-search contract for symmetric loopless adjacency with positive solver
constants, least-power subset parameters, and `triCheckSpecCorrected`. It requires
soundness, a finite-seed failure bound, and an n^(13/10) cost estimate including the cube of
`walkKappa`. -/
def theorem4WalkCorrected : Prop :=
  ∀ (n : ℕ), (hn : 0 < n) →
    ∀ (adj : Fin n → Fin n → Bool),
    (∀ a b : Fin n, adj a b = adj b a) → (∀ a : Fin n, adj a a = false) →
    ∀ (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover),
    1 ≤ kcs.κ → 1 ≤ ncs.κ → 1 ≤ sgs.κ →
    ∃ r r' : ℕ,
      1 ≤ r ∧ n * n * n ≤ r ^ 5 ∧ (r - 1) ^ 5 < n * n * n ∧
      1 ≤ r' ∧ r * r ≤ r' ^ 3 ∧ (r' - 1) ^ 3 < r * r ∧
      triCheckSpecCorrected adj Finset.univ kcs ncs r' 4 ∧
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
          (2 ^ 16 : ℕ) * (walkKappa kcs ncs sgs) ^ 3 * ((Nat.log 2 n + 2 : ℕ) ^ 3) *
            ((n : ℝ) ^ (13 / 10 : ℝ)))

/-- The subgraph candidate-search contract for `k ≥ 4`, using a least-power subset size and a
positive collision-solver constant. It requires soundness, a finite-seed failure bound, and
a cost estimate retaining that constant. -/
def theorem5WalkCorrected : Prop :=
  ∀ (n k : ℕ), 4 ≤ k → (hn : 0 < n) →
    ∀ (H : OGraph k) (hv : Fin k),
    ∀ (adj : Fin n → Fin n → Bool) (kcs : KCollisionSolver) (qH : ℕ), 1 ≤ kcs.κ →
    ∃ r : ℕ,
      1 ≤ r ∧ n ^ (k - 1) ≤ r ^ k ∧ (r - 1) ^ k < n ^ (k - 1) ∧
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
          (2 ^ 16 : ℕ) * kcs.κ * ((Nat.log 2 n + 2 : ℕ) ^ 3) *
            ((r : ℝ) ^ 2 +
              ((n : ℝ) / r) ^ ((k - 1) / 2) * ((qH : ℝ) + (Nat.sqrt r : ℝ) * r) +
              (qH : ℝ) + (n : ℝ)))

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
