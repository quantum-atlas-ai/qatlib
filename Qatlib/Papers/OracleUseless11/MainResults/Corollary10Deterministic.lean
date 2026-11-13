/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OracleUseless11.MainResults.OracleProblem

set_option backward.isDefEq.respectTransparency false

/-!
# Deterministic Oracle Uselessness: Quantum `k` Queries vs Classical `2k` Queries

This module proves Corollary 10: for a deterministic oracle problem (one whose target
permutation is independent of the internal random seed), pairwise classical uselessness
of `k` queries is equivalent to weak classical uselessness of `2k` queries, so `k`
quantum queries are useless if and only if `2k` classical queries are useless.

## Main statements

* `Deterministic`: seed-independence predicate on an `OracleProblem`.
* `deterministic_pairwise_iff_weak`: `P.PairwiseUseless k ↔ P.WeakUseless (2 * k)` for deterministic `P`.
* `corollary10_deterministic`: `P.QuantumUseless k ↔ P.WeakUseless (2 * k)` for deterministic `P`.

## References

* [Harrow and Rosenbaum, 2011][HarrowRosenbaum2011], Corollary 10, Section 3, p. 6.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OracleUseless11.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A deterministic oracle problem: the internal seed does not affect the permutation. -/
def Deterministic (P : OracleProblem X Y) : Prop :=
  ∀ (c : P.C) (x : X) (r r' : P.R), P.perm c x r = P.perm c x r'

open scoped Classical in
private theorem probOfPred_seed_independent (P : OracleProblem X Y) (m : ℕ)
    (E : P.C × (Fin m → P.R) → Prop) (Q : P.C → Prop)
    (hE : ∀ c r, E (c, r) ↔ Q c) :
    P.probOfPred m E = ∑ c : P.C, if Q c then P.prior.prob c else 0 := by
  classical
  unfold OracleProblem.probOfPred
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [OracleProblem.joint, hE]
  by_cases hc : Q c
  · simp only [hc, ite_true]
    rw [← Finset.mul_sum, P.seedLaw.sum_probOf m, mul_one]
  · simp [hc]

open scoped Classical in
private theorem classEventProb_seed_independent (P : OracleProblem X Y) (m : ℕ)
    (j : P.J) (E : P.C × (Fin m → P.R) → Prop) (Q : P.C → Prop)
    (hE : ∀ c r, E (c, r) ↔ Q c) :
    P.classEventProb m j E =
      ∑ c : P.C, if P.classOf c = j ∧ Q c then P.prior.prob c else 0 := by
  classical
  unfold OracleProblem.classEventProb
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [OracleProblem.joint, hE]
  by_cases hc : P.classOf c = j ∧ Q c
  · simp only [hc.1, hc.2, and_self, ite_true]
    rw [← Finset.mul_sum, P.seedLaw.sum_probOf m, mul_one]
  · simp [hc]

/-- In a deterministic oracle problem, pairwise classical uselessness of `k` queries is
equivalent to weak classical uselessness of `2 * k` queries. -/
theorem deterministic_pairwise_iff_weak (P : OracleProblem X Y) (hdet : Deterministic P)
    (k : ℕ) : P.PairwiseUseless k ↔ P.WeakUseless (2 * k) := by
  classical
  let r₀ : P.R := Classical.choice inferInstance
  have hperm : ∀ c x r, P.perm c x r = P.perm c x r₀ :=
    fun c x r => hdet c x r r₀
  have hprobs (x : Fin (k + k) → X) (y z : Fin (k + k) → Y) (j : P.J) :
      P.classEventProb (k + k) j (P.answerEvent (k + k) x y z) =
        P.classEventProb k j (P.pairAnswerEvent k
          (fun i => x (Fin.castAdd k i)) (fun i => x (Fin.natAdd k i))
          (fun i => y (Fin.castAdd k i)) (fun i => y (Fin.natAdd k i))
          (fun i => z (Fin.castAdd k i)) (fun i => z (Fin.natAdd k i))) ∧
      P.probOfPred (k + k) (P.answerEvent (k + k) x y z) =
        P.probOfPred k (P.pairAnswerEvent k
          (fun i => x (Fin.castAdd k i)) (fun i => x (Fin.natAdd k i))
          (fun i => y (Fin.castAdd k i)) (fun i => y (Fin.natAdd k i))
          (fun i => z (Fin.castAdd k i)) (fun i => z (Fin.natAdd k i))) := by
    let Q : P.C → Prop := fun c => ∀ i, P.perm c (x i) r₀ (y i) = z i
    have hanswer : ∀ c r, P.answerEvent (k + k) x y z (c, r) ↔ Q c := by
      intro c r
      simp only [OracleProblem.answerEvent, Q, hperm]
    have hpair : ∀ c r, P.pairAnswerEvent k
        (fun i => x (Fin.castAdd k i)) (fun i => x (Fin.natAdd k i))
        (fun i => y (Fin.castAdd k i)) (fun i => y (Fin.natAdd k i))
        (fun i => z (Fin.castAdd k i)) (fun i => z (Fin.natAdd k i)) (c, r) ↔ Q c := by
      intro c r
      simp only [OracleProblem.pairAnswerEvent, Q, hperm, forall_and, Fin.forall_fin_add]
    constructor
    · rw [classEventProb_seed_independent P (k + k) j _ Q hanswer,
        classEventProb_seed_independent P k j _ Q hpair]
    · rw [probOfPred_seed_independent P (k + k) _ Q hanswer,
        probOfPred_seed_independent P k _ Q hpair]
  rw [two_mul]
  constructor
  · intro h x y z j
    obtain ⟨hclass, hprob⟩ := hprobs x y z j
    rw [hclass, hprob]
    exact h _ _ _ _ _ _ j
  · intro h x x' y y' z z' j
    have hweak := h (Fin.append x x') (Fin.append y y') (Fin.append z z') j
    obtain ⟨hclass, hprob⟩ :=
      hprobs (Fin.append x x') (Fin.append y y') (Fin.append z z') j
    rw [hclass, hprob] at hweak
    simpa only [Fin.append_left, Fin.append_right] using hweak

/-- **Corollary 10**: for any deterministic oracle problem, `k` quantum queries are
useless if and only if `2 * k` classical queries are useless. -/
theorem corollary10_deterministic (P : OracleProblem X Y) (hdet : Deterministic P) (k : ℕ) :
    P.QuantumUseless k ↔ P.WeakUseless (2 * k) := by
  rw [P.quantumUseless_iff_pairwiseUseless]
  exact deterministic_pairwise_iff_weak P hdet k

end Qatlib.Papers.OracleUseless11.MainResults
