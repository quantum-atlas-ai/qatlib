/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.Theorem5Quan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.CollisionSearch
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

theorem gcAlg_cost_le {n : ℕ} (G : OGraph n) (f : Fin n → Bool)
    (kcs : KCollisionSolver) (r : ℕ) (ρ : kcs.seed) :
    (gcAlg G f kcs r ρ).2≤
      kcs.κ*(Nat.log 2 (n+1)+2)*(r+(n/r)*Nat.sqrt r)+2 := by
  have hc := kcs.charges r (gcRel G f) r 1 0 ρ
  norm_num only [Nat.reduceDiv,pow_one,zero_add,mul_one] at hc
  cases hr : kcs.run r (gcRel G f) r 1 0 ρ with
  | none => simpa only [gcAlg,hr] using hc.trans (Nat.le_add_right _ 2)
  | some t =>
    rw [gcAlg_some_cost G f kcs r ρ t hr]
    exact Nat.add_le_add_right hc 2

theorem gcAlg_complete {n : ℕ} (G : OGraph n) (f : Fin n → Bool)
    (kcs : KCollisionSolver) (r : ℕ) (hex : ∃ t,gcRel G f t=true) :
    haveI := kcs.seedFin
    (Finset.univ.filter fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1=none).card*
      (n+1)^kcs.cExp≤Fintype.card kcs.seed := by
  haveI := kcs.seedFin
  simpa only [gcAlg_none_iff] using kcs.finds r (gcRel G f) r 1 0 hex

theorem hAlg_none_iff {n k : ℕ} (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (kcs : KCollisionSolver) (r qH : ℕ) (stape : ℕ → kcs.seed) :
    (hAlg adj H hv kcs r qH stape).1=none ↔
      kcs.run r (hCandRel adj H hv) (r*r) r qH (stape 0)=none := by
  cases hr : kcs.run r (hCandRel adj H hv) (r*r) r qH (stape 0) with
  | none => simp [hAlg,hr]
  | some K =>
    have ht := kcs.sound r (hCandRel adj H hv) (r*r) r qH (stape 0) hr
    simp [hAlg,hr,ht]

theorem hAlg_cost_le {n k : ℕ} (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (kcs : KCollisionSolver) (r qH : ℕ) (stape : ℕ → kcs.seed) :
    (hAlg adj H hv kcs r qH stape).2≤
      kcs.κ*(Nat.log 2 (n+1)+2)*
        (r*r+(n/r)^((k-1)/2)*(qH+Nat.sqrt r*r)) := by
  have hc := kcs.charges r (hCandRel adj H hv) (r*r) r qH (stape 0)
  cases hr : kcs.run r (hCandRel adj H hv) (r*r) r qH (stape 0) with
  | none => simpa only [hAlg,hr] using hc
  | some K =>
    simp only [hAlg,hr]
    split_ifs <;> exact hc

theorem hAlg_complete {n k : ℕ} (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (kcs : KCollisionSolver) (r qH : ℕ)
    (hex : ∃ K : Fin (k-1) → Fin n,hCandRel adj H hv K=true) :
    haveI := kcs.seedFin
    (Finset.univ.filter fun ρ : kcs.seed => (hAlg adj H hv kcs r qH (fun _ => ρ)).1=none).card*
      (n+1)^kcs.cExp≤Fintype.card kcs.seed := by
  haveI := kcs.seedFin
  simpa only [hAlg_none_iff] using kcs.finds r (hCandRel adj H hv) (r*r) r qH hex

theorem hAlg_has_embedding {n k : ℕ} (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (kcs : KCollisionSolver) (r qH : ℕ) (stape : ℕ → kcs.seed)
    (K : Fin (k-1) → Fin n) (hK : (hAlg adj H hv kcs r qH stape).1=some K) :
    ∃ σ : Fin k → Fin n,Function.Injective σ ∧
      ∀ a b : Fin k,(a,b)∈H.edges → adj (σ a) (σ b)=true := by
  have h := hAlg_sound adj H hv kcs r qH stape
  have ht : hCandRel adj H hv K=true := by
    cases he : hAlg adj H hv kcs r qH stape with
    | mk result cost =>
      cases result with
      | none => simp [he] at hK
      | some K' =>
        have hEq : K'=K := by simpa only [he,Option.some.injEq] using hK
        simpa only [he,hEq] using h
  obtain ⟨_,v,σ,hσ,hvσ,hrange,hedges⟩ := of_decide_eq_true ht
  refine ⟨σ,?_,hedges⟩
  intro a b hab
  by_contra hne
  exact hσ a b hne hab

theorem exists_least_subset_power (N k : ℕ) (hN : 0<N) (hk : 0<k) :
    ∃ r : ℕ,1≤r ∧ N≤r^k ∧ (r-1)^k<N := by
  have hex : ∃ r : ℕ,N≤r^k := ⟨N,Nat.le_self_pow hk.ne' N⟩
  let r := Nat.find hex
  have hp : N≤r^k := Nat.find_spec hex
  have hr : 0<r := by
    by_contra h
    have hz : r=0 := by omega
    rw [hz,zero_pow hk.ne'] at hp
    omega
  refine ⟨r,hr,hp,?_⟩
  exact Nat.lt_of_not_ge (Nat.find_min hex (show r-1<r by omega))
end Qatlib.Concepts.WalkSearch.Primitives
