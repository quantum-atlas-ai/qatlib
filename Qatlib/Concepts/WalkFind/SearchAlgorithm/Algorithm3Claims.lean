/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3IsolationQuan
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3SuccessQuan
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3Native
import Qatlib.Concepts.WalkFind.SearchAlgorithm.EfficientBinaryHashFamily
import Qatlib.Concepts.WalkFind.SearchAlgorithm.EfficientPermutationFamily

/-!
# Named statements for collision search

This module packages query bounds, success and isolation contracts, hash families, and
permutation families into named propositions. The proved interfaces include the full-memory
search tree, the restricted binary hash construction, and the collision-support counting bounds.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `algorithm3`: constructs the stated full-memory search tree.
* `theorem1_restricted`: provides binary hashes with the specified seed count.
* `claim7`: compares approximately independent permutation events with independent samples.
* `claim8`: bounds collision support in the absence of a large disjoint packing.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm

open Qatlib
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The proposition that, for each `k ≥ 2`, a uniform positive constant bounds the query cost of
valid initial-frame search trees by `queryScale k N r` for all stated parameters. -/
def Theorem9AStatement : Prop :=
  ∀ (k : ℕ), 2 ≤ k →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M r : ℕ) [NeZero M], 0 < M → k ≤ r → r ≤ N →
        ∃ P : Algorithm3Tree N M k,
          treeFrame P = initialFrame N ∧ algorithm3Valid r C P ∧
            (treeQueries P : ℝ) ≤ C * queryScale k N r

/-- The Algorithm 3 success proposition `Algorithm3SuccessContract`. -/
def Theorem9BStatement : Prop :=
  Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3SuccessContract

/-- The conjunction of the Algorithm 3 query-bound and success statements. -/
def Theorem9Statement : Prop := Theorem9AStatement ∧ Theorem9BStatement

/-- The Algorithm 3 success statement holds [Ambainis2007ElementDistinctness]. -/
theorem theorem9b : Theorem9BStatement :=
  Qatlib.Concepts.WalkFind.SearchAlgorithm.algorithm3Success_answer

/-- The collision-isolation proposition `Algorithm3Isolation`. -/
def Lemma4Statement : Prop :=
  Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3Isolation

/-- The collision-isolation statement holds [Ambainis2007ElementDistinctness]. -/
theorem lemma4 : Lemma4Statement :=
  Qatlib.Concepts.WalkFind.SearchAlgorithm.algorithm3Isolation_answer

/-- The proposition that a full-memory initial-frame search tree exists with validity constant
two, unit unique-call guarantee, and the stated query and qubit bounds. -/
def Algorithm3Statement : Prop :=
  ∀ (k N M : ℕ) [NeZero M], 0 < N → k ≤ N →
    ∃ P : Algorithm3Tree N M k,
      treeFrame P = initialFrame N ∧ algorithm3Valid N 2 P ∧
        uniqueCallProbability 1 P ∧
        (treeQueries P : ℝ) ≤ 2 * queryScale k N N ∧
        (treeQubits P : ℝ) ≤ 2 * N * dataBits N M

/-- A full-memory Algorithm 3 tree satisfies the specified validity, unique-call, query, and
qubit guarantees [Ambainis2007ElementDistinctness]. -/
theorem algorithm3 : Algorithm3Statement :=
  fun k N M inst hN hkN =>
    Qatlib.Concepts.WalkFind.SearchAlgorithm.algorithm3Native_full_memory
      k N M hN hkN

/-- The proposition that binary `d`-wise independent hash families exist with positive seed
count and the stated power bound on family size. -/
def Theorem1Statement : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 2 ≤ N →
    ∃ (R : ℕ) (hash : Fin R → Fin N → Bool), 0 < R ∧
      (R : ℝ) ≤ ((N : ℝ) + 1) ^ ((d + 1) / 2) ∧
      ∀ (m : ℕ), m ≤ d → ∀ i : Fin m → Fin N, Function.Injective i →
        ∀ values : Fin m → Bool,
          eventProbability (fun s => ∀ j, hash s (i j) = values j) = 1 / (2 ^ m : ℝ)

/-- The proposition that binary `d`-wise independent hashes on `Fin N` exist with `2^(d *
Nat.clog 2 (N + 1))` seeds for `N ≥ 2`. -/
def Theorem1RestrictedStatement : Prop :=
  ∀ (N d : ℕ), 2 ≤ N →
    ∃ hash : Fin (2 ^ (d * Nat.clog 2 (N + 1))) → Fin N → Bool,
      ∀ (m : ℕ), m ≤ d → ∀ i : Fin m → Fin N, Function.Injective i →
        ∀ values : Fin m → Bool,
          eventProbability (fun s => ∀ j, hash s (i j) = values j) = 1 / (2 ^ m : ℝ)

/-- The restricted binary hash-family statement follows from the polynomial construction
[Ambainis2007ElementDistinctness]. -/
theorem theorem1_restricted : Theorem1RestrictedStatement :=
  fun N d hN => Qatlib.Concepts.WalkFind.SearchAlgorithm.logarithmicSeedBinaryHash_exists N d hN

/-- The proposition that approximately fully independent permutation families possess the stated
seed, register-width, and finite-gate bounds for forward and inverse evaluation. -/
def Theorem2Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ q t : ℕ, 2 ≤ q → 1 ≤ t →
      ∃ (R b : ℕ) (π : Fin R → Equiv.Perm (Fin q))
        (encode : Fin q → Reg b) (forward backward : Fin R → List FiniteGateCode),
        0 < R ∧ Function.Injective encode ∧
        (∃ hb : q ≤ 2 ^ b, ∀ i, encode i = (bitVecEquiv b).symm (Fin.castLE hb i)) ∧
        ApproxIndependent q (1 / (t : ℝ)) π ∧
        (Nat.clog 2 (R + 1) : ℝ) ≤ C * ((q : ℝ) ^ 2 * Nat.clog 2 (q + 1) + q * Nat.clog 2 (t + 1) + 1) ∧
        (b : ℝ) ≤ C * (q + Nat.clog 2 (q + 1) + Nat.clog 2 (t + 1) + 1) ^ 4 ∧
        (∀ s, finiteWordLegal b (forward s) = true ∧ finiteWordLegal b (backward s) = true ∧
          ((forward s).length + (backward s).length : ℝ) ≤
            C * (q + Nat.clog 2 (q + 1) + Nat.clog 2 (t + 1) + 1) ^ 8 ∧
          (∀ i, Run 1 (finiteCodeCircuit b (forward s)) (Ket (encode i)) = Ket (encode (π s i))) ∧
          (∀ i, Run 1 (finiteCodeCircuit b (backward s)) (Ket (encode i)) = Ket (encode ((π s).symm i))))

/-- The permutation-family statement holds with the specified finite-gate implementations and
resource bounds [Ambainis2007ElementDistinctness]. -/
theorem theorem2 : Theorem2Statement :=
  Qatlib.Concepts.WalkFind.SearchAlgorithm.efficientPermutationFamily_fullIndependence_endpoint

/-- The proposition that events on `m` distinct inputs under an approximately independent
permutation differ from independent uniform sampling by at most `η + m^2 / q` under the
stated bounds. -/
def Claim7Statement : Prop :=
  ∀ {q R d m : ℕ} {η : ℝ} {π : Fin R → Equiv.Perm (Fin q)},
    0 < q → 0 ≤ η → ApproxIndependent d η π → m ≤ d → m ≤ q →
      ∀ (i : Fin m → Fin q), Function.Injective i → ∀ V : (Fin m → Fin q) → Prop,
        |eventProbability (fun s => V (fun z => π s (i z))) -
            (((Finset.univ : Finset (Fin m → Fin q)).filter V).card : ℝ) / (q : ℝ) ^ m| ≤
          η + (m : ℝ) ^ 2 / q

/-- Approximately independent permutation events satisfy the stated independent-sampling error
bound [Ambainis2007ElementDistinctness]. -/
theorem claim7 : Claim7Statement :=
  fun {q R d m η π} hq hη hπ hmd hmq i hi V =>
    Qatlib.Concepts.WalkFind.SearchAlgorithm.approxIndependent_iid_event
      (q := q) (R := R) (d := d) (m := m) (η := η) (π := π) hq hη hπ hmd hmq i hi V

/-- The proposition that, for positive `k`, the absence of `t` disjoint `k`-collisions bounds
the collision support by `2 * k * (t - 1)`. -/
def Claim8Statement : Prop :=
  ∀ (q M k : ℕ), 0 < k → ∀ (x : Fin q → ZMod M) (T : Finset (Fin q)) (t : ℕ),
    (¬∃ i : Fin t → Fin k → Fin q,
      Function.Injective (fun z : Fin t × Fin k => i z.1 z.2) ∧
        ∀ a, CollisionIn k x T (Finset.univ.image (i a))) →
      (collisionSupport k x T).card ≤ 2 * k * (t - 1)

/-- The absence of `t` disjoint `k`-collisions gives the stated collision-support bound
[Ambainis2007ElementDistinctness]. -/
theorem claim8 : Claim8Statement := by
  intro q M k hk x T t hno
  rcases Qatlib.Concepts.WalkFind.SearchAlgorithm.collision_packing_dichotomy
    k hk x T t with hsmall | ⟨i, hinj, hall⟩
  · exact hsmall
  · exact absurd ⟨i, hinj, hall⟩ hno

end Qatlib.Concepts.WalkFind.SearchAlgorithm
