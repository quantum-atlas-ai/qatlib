/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.Theorem4Quan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

namespace Qatlib.Papers.QSearchSurvey05.MainResults

theorem theorem44_triangle_finding
    (n : ℕ) (hn : 0 < n)
    (adj : Fin n → Fin n → Bool)
    (hsym : ∀ a b : Fin n, adj a b = adj b a)
    (hloop : ∀ a : Fin n, adj a a = false)
    (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover)
    (hκ1 : 1 ≤ kcs.κ) (hκ2 : 1 ≤ ncs.κ) (hκ3 : 1 ≤ sgs.κ) :
    ∃ r r' : ℕ,
      1 ≤ r ∧ n * n * n ≤ r ^ 5 ∧ (r - 1) ^ 5 < n * n * n ∧
      1 ≤ r' ∧ r * r ≤ r' ^ 3 ∧ (r' - 1) ^ 3 < r * r ∧
      triCheckSpecFreshValidation adj Finset.univ kcs ncs r' 4 ∧
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
          (2 ^ 16 : ℕ) * (walkKappa kcs ncs sgs) ^ 3 *
            ((Nat.log 2 n + 2 : ℕ) ^ 3) * ((n : ℝ) ^ (13 / 10 : ℝ))) := by
  have h := theorem4_answer
  unfold Theorem4 theorem4WalkFreshValidation at h
  exact h n hn adj hsym hloop kcs ncs sgs hκ1 hκ2 hκ3

end Qatlib.Papers.QSearchSurvey05.MainResults
