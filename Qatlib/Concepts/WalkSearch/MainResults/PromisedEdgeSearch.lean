/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.GraphVocabulary
set_option warningAsError false
open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical

structure PromisedEdgeSearchFamily where
  cExp : ℕ
  κ : ℕ
  seed : ℕ → Type
  seedFin : ∀ n,Fintype (seed n)
  seedNe : ∀ n,Nonempty (seed n)
  run : {n : ℕ} → (G : UGraph n) → (E : Finset (Fin n×Fin n)) → (mBound : ℕ) → seed n → Option (Fin n×Fin n×Fin n)
  cost : {n : ℕ} → (G : UGraph n) → (E : Finset (Fin n×Fin n)) → (mBound : ℕ) → seed n → ℕ
  sound : ∀ {n} (G : UGraph n) (E : Finset (Fin n×Fin n)) (mBound : ℕ) (ρ : seed n) {a b c : Fin n},
    run G E mBound ρ=some (a,b,c) →
      a≠b ∧ b≠c ∧ a≠c ∧ (a,b)∈E ∧ (a,b)∈G.edges ∧ (a,c)∈G.edges ∧ (b,c)∈G.edges
  reject : ∀ {n} (G : UGraph n) (E : Finset (Fin n×Fin n)) (mBound : ℕ) (ρ : seed n),
    (∀ a b c : Fin n,¬(a≠b ∧ b≠c ∧ a≠c ∧ (a,b)∈E ∧ (a,b)∈G.edges ∧ (a,c)∈G.edges ∧ (b,c)∈G.edges)) →
      run G E mBound ρ=none
  finds : ∀ {n} (G : UGraph n) (E : Finset (Fin n×Fin n)) (mBound : ℕ),
    (E∩G.edges).card≤ mBound →
    (∃ a b c : Fin n,a≠b ∧ b≠c ∧ a≠c ∧ (a,b)∈E ∧ (a,b)∈G.edges ∧ (a,c)∈G.edges ∧ (b,c)∈G.edges) →
    letI:=seedFin n
    (Finset.univ.filter (fun ρ : seed n=>run G E mBound ρ=none)).card*(n*n+1)^cExp≤ Fintype.card (seed n)
  charges : ∀ {n} (G : UGraph n) (E : Finset (Fin n×Fin n)) (mBound : ℕ) (ρ : seed n),
    cost G E mBound ρ≤ κ*(Nat.log 2 (E.card+n*mBound+1)+2)*(Nat.sqrt E.card+Nat.sqrt (n*mBound)+1)

def promisedEdgeReservation (ets : PromisedEdgeSearchFamily) (n eBound mBound : ℕ) : ℕ :=
  ets.κ*(Nat.log 2 (eBound+n*mBound+1)+2)*(Nat.sqrt eBound+Nat.sqrt (n*mBound)+1)

theorem promisedEdge_cost_le_reservation (ets : PromisedEdgeSearchFamily) {n : ℕ} (G : UGraph n)
    (E : Finset (Fin n×Fin n)) (mBound : ℕ) (ρ : ets.seed n) (eBound : ℕ) (he : E.card≤ eBound) :
    ets.cost G E mBound ρ≤ promisedEdgeReservation ets n eBound mBound := by
  apply (ets.charges G E mBound ρ).trans
  unfold promisedEdgeReservation
  gcongr
end Qatlib.Concepts.WalkSearch.MainResults
