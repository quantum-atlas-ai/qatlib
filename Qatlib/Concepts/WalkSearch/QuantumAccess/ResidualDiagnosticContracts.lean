/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.NativeCapabilityVocabulary
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkCorrectedContracts
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts

/-!
# Residual native and walk-search contracts

This module states native-realization existence requirements for search and collision interfaces
and defines residual specifications for stored subgraphs, checker substitution, and
subgraph-search numerical charges. These propositions separate the remaining requirements in a
quantum-walk search development [MagniezNayakRolandSantha2011].

## Main statements

* `SafeGroverNative`, `NoisySearchNative`, and `KCollisionNative`: realization existence at each
  exponent at least three.
* `StoredSubgraphSUC`: stored-edge and cost requirements.
* `CheckerSubstitution` and `Th5Numeric`: combined checker and numerical charge specifications.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- For every failure exponent at least three, requires a `SafeGrover` capability with that
exponent, positive fee constant, and native realization. -/
def SafeGroverNative : Prop :=
  ∀ (cExp : ℕ), 3 ≤ cExp →
  ∃ (sgs : Qatlib.Concepts.WalkSearch.Primitives.SafeGrover),
    sgs.cExp = cExp ∧ 1 ≤ sgs.κ ∧ SafeGrover.NativeRealized sgs

/-- For every failure exponent at least three, requires a noisy-search capability with that
exponent, positive fee constant, and native realization. -/
def NoisySearchNative : Prop :=
  ∀ (cExp : ℕ), 3 ≤ cExp →
  ∃ (ncs : NoisySearch),
    ncs.cExp = cExp ∧ 1 ≤ ncs.κ ∧ NoisySearch.NativeRealized ncs

/-- For every failure exponent at least three, requires a collision solver with that exponent,
positive fee constant, and native realization. -/
def KCollisionNative : Prop :=
  ∀ (cExp : ℕ), 3 ≤ cExp →
  ∃ (kcs : KCollisionSolver),
    kcs.cExp = cExp ∧ 1 ≤ kcs.κ ∧ KCollisionSolver.NativeRealized kcs

end Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.WalkSearch.QuantumAccess.Walk

open Qatlib.Concepts.WalkSearch.WalkAlgorithms
open Qatlib.Concepts.WalkSearch.Primitives

/-- Requires a symmetric loopless stored edge set for every adjacency input and subset, with
setup cost `U.card * U.card`, update cost `U.card`, zero check cost, and positive setup and
update costs. -/
def StoredSubgraphSUC : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (U : Finset (Fin n)),
    ∃ (D : Finset (Fin n × Fin n)),
      (∀ a b : Fin n, (a, b) ∈ D ↔ a ∈ U ∧ b ∈ U ∧ adj a b = true) ∧
      (∀ a b : Fin n, (a, b) ∈ D → (b, a) ∈ D) ∧
      (∀ a : Fin n, (a, a) ∉ D) ∧

      (∃ s u c : ℕ, s = (U.card * U.card) ∧ u = U.card ∧ c = 0 ∧
        1 ≤ s ∧ 1 ≤ u)

/-- The specification that suitable subset windows yield corrected checker behavior and the
combined triangle algorithm's soundness, failure-count, and `n ^ (13 / 10)` charge bounds. -/
def CheckerSubstitution : Prop :=
  ∀ (n : ℕ) (_hn : 0 < n) (adj : Fin n → Fin n → Bool),
    (∀ a b : Fin n, adj a b = adj b a) → (∀ a : Fin n, adj a a = false) →
    ∀ (kcs : Qatlib.Concepts.WalkSearch.WalkAlgorithms.KCollisionSolver)
      (ncs : Qatlib.Concepts.WalkSearch.WalkAlgorithms.NoisySearch)
      (sgs : Qatlib.Concepts.WalkSearch.WalkAlgorithms.SafeGrover),
    1 ≤ kcs.κ → 1 ≤ ncs.κ → 1 ≤ sgs.κ →
    ∃ (r r' : ℕ),
      1 ≤ r ∧ n * n * n ≤ r ^ 5 ∧ (r - 1) ^ 5 < n * n * n ∧
      1 ≤ r' ∧ r * r ≤ r' ^ 3 ∧ (r' - 1) ^ 3 < r * r ∧
      triCheckSpecCorrected adj Finset.univ kcs ncs r' 4 ∧

      (∀ (stape : ℕ → kcs.seed) (gtape : ℕ → sgs.seed),
        (match th4Alg adj kcs ncs sgs r r' 4 stape gtape with
        | (some (a, b, c), _) =>
            a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
            adj a b = true ∧ adj a c = true ∧ adj b c = true
        | (none, _) => True)) ∧

      ((∃ t : Fin 2 → Fin n, triRel adj t = true) →
        haveI := kcs.seedFin
        haveI := sgs.seedFin
        ((Finset.univ.filter (fun ρ : kcs.seed × sgs.seed =>
            (th4Alg adj kcs ncs sgs r r' 4 (fun _ => ρ.1) (fun _ => ρ.2)).1 = none)).card *
          (n + 1) ^ (min kcs.cExp sgs.cExp) ≤
          2 * Fintype.card (kcs.seed × sgs.seed))) ∧

      (∀ (stape : ℕ → kcs.seed) (gtape : ℕ → sgs.seed),
        ((th4Alg adj kcs ncs sgs r r' 4 stape gtape).2 : ℝ) ≤
          (2 ^ 16 : ℕ) * (walkKappa kcs ncs sgs) ^ 3 *
            ((Nat.log 2 n + 2 : ℕ) ^ 3) * ((n : ℝ) ^ (13 / 10 : ℝ)))

/-- Requires a positive constant bounding the subgraph algorithm's charge by `C * n ^ (2 - 2 /
k)` at a least-power subset window whenever `qH ≤ C`. -/
def Th5Numeric : Prop :=
  ∀ (k : ℕ) (_hk : 4 ≤ k) (kcs : KCollisionSolver), 1 ≤ kcs.κ →
  ∃ (C : ℝ), 0 < C ∧
    ∀ (n : ℕ) (_hn : 0 < n) (H : OGraph k) (hv : Fin k)
      (adj : Fin n → Fin n → Bool) (qH : ℕ),
      (qH : ℝ) ≤ C →
      ∃ r : ℕ, 1 ≤ r ∧ n ^ (k - 1) ≤ r ^ k ∧ (r - 1) ^ k < n ^ (k - 1) ∧
        (∀ stape : ℕ → kcs.seed,
          ((hAlg adj H hv kcs r qH stape).2 : ℝ) ≤
            C * ((n : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ))))

end Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
