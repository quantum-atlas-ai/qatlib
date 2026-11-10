/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkCorrectedContracts
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms
open scoped Classical

noncomputable def triCheckFresh {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
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
      let ex := triCheckAmpExtract adj e kcs r' (subR v) v c₀ (fun i => stape (n * c₀ + i))
      match ex.1 with
      | some t =>
          (some (e (t 0), e (t 1)), ncs.cost marked test tcost n ntape + ex.2 + 2)
      | none =>
          (none, ncs.cost marked test tcost n ntape + ex.2 + 2)

def triCheckSpecFreshValidation {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ) : Prop :=
  1 ≤ kcs.κ → 1 ≤ ncs.κ →
  (∀ stape : ℕ → kcs.seed, ∀ ntape : ncs.seed,
    (match triCheckFresh adj U kcs ncs r' c₀ stape ntape with
    | (some (u₁, u₂), _) => u₁ ∈ U ∧ u₂ ∈ U ∧ u₁ ≠ u₂ ∧
        ∃ v : Fin n, adj v u₁ = true ∧ adj v u₂ = true ∧ adj u₁ u₂ = true
    | (none, _) => True)) ∧
  ((∃ v : Fin n, ∃ u₁ ∈ U, ∃ u₂ ∈ U, u₁ ≠ u₂ ∧ adj v u₁ = true ∧ adj v u₂ = true ∧
      adj u₁ u₂ = true) →
    haveI := ncs.seedFin
    haveI := kcs.seedFin
    ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        (triCheckFresh adj U kcs ncs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2) ρ.1).1 = none).card *
      (U.card + 1) ^ (min ncs.cExp (c₀ * kcs.cExp)) ≤
      2 * (Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed)))) ∧
  (∀ stape : ℕ → kcs.seed, ∀ ntape : ncs.seed,
    (triCheckFresh adj U kcs ncs r' c₀ stape ntape).2 ≤
      (2 * cCOf kcs ncs n U.card r' c₀ : ℕ))

def theorem4WalkFreshValidation : Prop :=
  ∀ (n : ℕ), (hn : 0 < n) →
    ∀ (adj : Fin n → Fin n → Bool),
    (∀ a b : Fin n, adj a b = adj b a) → (∀ a : Fin n, adj a a = false) →
    ∀ (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover),
    1 ≤ kcs.κ → 1 ≤ ncs.κ → 1 ≤ sgs.κ →
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
          (2 ^ 16 : ℕ) * (walkKappa kcs ncs sgs) ^ 3 * ((Nat.log 2 n + 2 : ℕ) ^ 3) *
            ((n : ℝ) ^ (13 / 10 : ℝ)))

theorem triCheckFresh_validation_slots_disjoint (n c₀ : ℕ) (v w : Fin n) (i j : Fin c₀) :
    v.val * c₀ + i.val ≠ n * c₀ + (w.val * c₀ + j.val) := by
  have hpre : v.val * c₀ + i.val < n * c₀ := by nlinarith [v.isLt, i.isLt]
  omega

theorem triCheckFresh_validation_slot_lt (n c₀ : ℕ) (v : Fin n) (i : Fin c₀) :
    n * c₀ + (v.val * c₀ + i.val) < 2 * n * c₀ + 1 := by
  have hpre : v.val * c₀ + i.val < n * c₀ := by nlinarith [v.isLt, i.isLt]
  rw [show 2 * n * c₀ = n * c₀ + n * c₀ by ring]
  omega

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
