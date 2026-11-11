/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.DatabaseQuery

/-!
# Algorithm words with recording databases

This module lifts algorithm isometries to the joint register and database space and defines the
successive recording query states `checkpoint`. These states preserve the initial norm and are
supported on databases with at most as many occupied cells as the number of queries.

The mathematical context is discussed in [MagniezZur2026].

## Main statements

* `algorithmGate`: The lifted algorithm action on each fixed database.
* `checkpoint_norm`: Every checkpoint has the norm of the initial state.
* `checkpoint_supported`: After `t` queries, at most `t` cells can be occupied.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {W X P L : Type*} [Fintype W] [Fintype X] [Fintype P] [Fintype L] [Nonempty L]

/-- The basis equivalence that groups register and database pairs by their database value. -/
def algorithmSplit : DatabaseBasis W X P L ≃ Σ _db : X → Option L, Registers W X P where
  toFun b := ⟨b.2,b.1⟩
  invFun b := (b.2,b.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Euclidean isometry grouping a joint state into register vectors indexed by databases. -/
def algorithmGrouping : EuclideanSpace ℂ (DatabaseBasis W X P L) ≃ₗᵢ[ℂ]
    PiLp 2 (fun _db : X → Option L => EuclideanSpace ℂ (Registers W X P)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ algorithmSplit).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _db : X → Option L => fun _η : Registers W X P => ℂ))
omit [Nonempty L] in

/-- The database-indexed register vector evaluates to the original amplitude at the
corresponding register and database pair. -/
theorem algorithmGrouping_apply (ψ : EuclideanSpace ℂ (DatabaseBasis W X P L))
    (db : X → Option L) (η : Registers W X P) : algorithmGrouping ψ db η=ψ (η,db) := rfl
omit [Nonempty L] in

/-- Ungrouping a family of database-indexed register vectors evaluates the vector indexed by the
given database. -/
theorem algorithmGrouping_symm_apply
    (ψ : PiLp 2 (fun _db : X → Option L => EuclideanSpace ℂ (Registers W X P)))
    (η : Registers W X P) (db : X → Option L) : algorithmGrouping.symm ψ (η,db)=ψ db η := rfl

/-- Lift a register linear isometry equivalence by applying it independently within each fixed
database. -/
def algorithmGate (U : EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P)) :
    EuclideanSpace ℂ (DatabaseBasis W X P L) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (DatabaseBasis W X P L) :=
  (algorithmGrouping.trans (LinearIsometryEquiv.piLpCongrRight 2
    (fun _db : X → Option L => U))).trans algorithmGrouping.symm
omit [Nonempty L] in

/-- The lifted algorithm gate acts on the register vector belonging to the fixed database. -/
theorem algorithmGate_apply
    (U : EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (ψ : EuclideanSpace ℂ (DatabaseBasis W X P L)) (η : Registers W X P) (db : X → Option L) :
    algorithmGate U ψ (η,db)=U (algorithmGrouping ψ db) η := rfl

/-- The joint state supported on the all-empty database with register amplitudes given by
`initial`. -/
def initialDatabaseState (initial : EuclideanSpace ℂ (Registers W X P)) :
    EuclideanSpace ℂ (DatabaseBasis W X P L) :=
  algorithmGrouping.symm (PiLp.single 2 (fun _ : X => (none : Option L)) initial)
omit [Nonempty L] in

/-- Attaching the empty recording database preserves the norm of the initial register state. -/
theorem initialDatabaseState_norm (initial : EuclideanSpace ℂ (Registers W X P)) :
    ‖initialDatabaseState (L := L) initial‖=‖initial‖ := by
  simp [initialDatabaseState]
omit [Nonempty L] in

/-- The initial joint amplitude equals the register amplitude on the all-empty database and is
zero on every other database. -/
theorem initialDatabaseState_apply (initial : EuclideanSpace ℂ (Registers W X P))
    (η : Registers W X P) (db : X → Option L) :
    initialDatabaseState initial (η,db)=if db=(fun _ => none) then initial η else 0 := by
  unfold initialDatabaseState
  rw [algorithmGrouping_symm_apply]
  by_cases h : db=(fun _ => none)
  · subst db
    simp
  · rw [PiLp.single_eq_of_ne (β := fun _db : X → Option L => EuclideanSpace ℂ (Registers W X P)) 2 h initial]
    simp [h]

/-- The state after the initial algorithm gate and then `t` recording queries, each followed by
its next algorithm gate. -/
def checkpoint (phase : P → L → ℂ) (hp : ∀ p y, star (phase p y)*phase p y=1)
    (gates : ℕ → EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (initial : EuclideanSpace ℂ (Registers W X P)) : ℕ → EuclideanSpace ℂ (DatabaseBasis W X P L)
  | 0 => algorithmGate (gates 0) (initialDatabaseState initial)
  | t+1 => algorithmGate (gates (t+1)) (databaseQuery phase hp (checkpoint phase hp gates initial t))

/-- Every checkpoint has the same norm as the initial register state. -/
theorem checkpoint_norm (phase : P → L → ℂ) (hp : ∀ p y, star (phase p y)*phase p y=1)
    (gates : ℕ → EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (initial : EuclideanSpace ℂ (Registers W X P)) (t : ℕ) :
    ‖checkpoint phase hp gates initial t‖=‖initial‖ := by
  induction t with
  | zero => simp only [checkpoint,LinearIsometryEquiv.norm_map,initialDatabaseState_norm]
  | succ t ih => simpa only [checkpoint,LinearIsometryEquiv.norm_map] using ih

/-- The finite set of addresses whose database cell is different from `none`. -/
def occupied (db : X → Option L) : Finset X := Finset.univ.filter (fun x => db x ≠ none)
omit [Fintype L] [Nonempty L] in

/-- Updating a database cell can add an occupied address only at the updated position. -/
theorem occupied_update_subset (db : X → Option L) (x : X) (value : Option L) :
    occupied (Function.update db x value) ⊆ insert x (occupied db) := by
  intro j hj
  by_cases h : j=x
  · exact Finset.mem_insert.mpr (Or.inl h)
  · apply Finset.mem_insert.mpr
    right
    simpa [occupied,Function.update_of_ne h] using hj
omit [Fintype L] [Nonempty L] in

/-- Updating one database cell increases the number of occupied addresses by at most one. -/
theorem occupied_update_card (db : X → Option L) (x : X) (value : Option L) :
    (occupied (Function.update db x value)).card ≤ (occupied db).card+1 :=
  (Finset.card_le_card (occupied_update_subset db x value)).trans (Finset.card_insert_le x (occupied db))

/-- The joint state has zero amplitude on every database with more than `t` occupied cells. -/
def SupportedAtMost (t : ℕ) (ψ : EuclideanSpace ℂ (DatabaseBasis W X P L)) : Prop :=
  ∀ η db, t < (occupied db).card → ψ (η,db)=0
omit [Nonempty L] in

/-- The initial joint state is supported on databases with zero occupied cells. -/
theorem initial_supported (initial : EuclideanSpace ℂ (Registers W X P)) :
    SupportedAtMost 0 (initialDatabaseState (L := L) initial) := by
  intro η db hdb
  have h : db ≠ (fun _ => none) := by
    intro he
    simp [he,occupied] at hdb
  rw [initialDatabaseState_apply,if_neg h]
omit [Nonempty L] in

/-- An algorithm gate acting only on registers preserves a bound on the number of occupied
database cells in the state support. -/
theorem algorithmGate_supported (t : ℕ)
    (U : EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (ψ : EuclideanSpace ℂ (DatabaseBasis W X P L)) (hψ : SupportedAtMost t ψ) :
    SupportedAtMost t (algorithmGate U ψ) := by
  intro η db hdb
  rw [algorithmGate_apply]
  have hz : algorithmGrouping ψ db=0 := by
    ext η'
    exact hψ η' db hdb
  rw [hz,map_zero]
  rfl

/-- A recording database query increases the support bound on occupied cells by at most one. -/
theorem databaseQuery_supported (t : ℕ) (phase : P → L → ℂ)
    (hp : ∀ p y, star (phase p y)*phase p y=1)
    (ψ : EuclideanSpace ℂ (DatabaseBasis W X P L)) (hψ : SupportedAtMost t ψ) :
    SupportedAtMost (t+1) (databaseQuery phase hp ψ) := by
  intro η db hdb
  rw [databaseQuery_apply]
  apply Finset.sum_eq_zero
  intro value hvalue
  have hs := occupied_update_card (Function.update db η.2.1 value) η.2.1 (db η.2.1)
  have he : Function.update (Function.update db η.2.1 value) η.2.1 (db η.2.1)=db := by
    rw [Function.update_idem,Function.update_eq_self]
  rw [he] at hs
  have hl : t < (occupied (Function.update db η.2.1 value)).card := by omega
  rw [hψ η _ hl,mul_zero]

/-- The state at checkpoint `t` is supported on databases with at most `t` occupied cells. -/
theorem checkpoint_supported (phase : P → L → ℂ) (hp : ∀ p y, star (phase p y)*phase p y=1)
    (gates : ℕ → EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (initial : EuclideanSpace ℂ (Registers W X P)) (t : ℕ) :
    SupportedAtMost t (checkpoint phase hp gates initial t) := by
  induction t with
  | zero => exact algorithmGate_supported 0 _ _ (initial_supported initial)
  | succ t ih => exact algorithmGate_supported (t+1) _ _ (databaseQuery_supported t phase hp _ ih)
end Qatlib.Concepts.CompressedQuery.CyclicRecord
