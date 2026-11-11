/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.Action
import Mathlib.Logic.Equiv.Prod

/-!
# Recording queries on a full database

This module groups a joint state by its registers and all database cells except the queried one.
The linear isometry `databaseQuery` applies the local recording action on the remaining cell,
and `databaseQuery_apply` expresses its amplitudes as a sum over literal cell updates.

The mathematical context is discussed in [MagniezZur2026].

## Main statements

* `queryGrouping`: The isometric decomposition into queried-cell fibres.
* `databaseQuery`: The unitary recording query on the full database.
* `databaseQuery_apply`: The matrix entry formula using a single database cell update.

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

/-- The joint register basis consisting of workspace, query address and phase label. -/
abbrev Registers (W X P : Type*) := W × X × P

/-- The register basis paired with a database whose cells contain optional labels. -/
abbrev DatabaseBasis (W X P L : Type*) := Registers W X P × (X → Option L)

/-- The registers together with the database values away from the current query address. -/
abbrev QueryFibre (W X P L : Type*) := Σ η : Registers W X P, ({j : X // j ≠ η.2.1} → Option L)

/-- The basis equivalence separating the queried database cell from the registers and all other
cells. -/
def querySplit : DatabaseBasis W X P L ≃ Σ _f : QueryFibre W X P L, Option L where
  toFun b := ⟨⟨b.1,fun j => b.2 j⟩,b.2 b.1.2.1⟩
  invFun b := (b.1.1,(Equiv.piSplitAt b.1.1.2.1 (fun _ : X => Option L)).symm (b.2,b.1.2))
  left_inv b := by
    rcases b with ⟨η,db⟩
    have h := (Equiv.piSplitAt η.2.1 (fun _ : X => Option L)).symm_apply_apply db
    exact congrArg (fun d => (η,d)) h
  right_inv b := by
    rcases b with ⟨⟨η,z⟩,value⟩
    have h := (Equiv.piSplitAt η.2.1 (fun _ : X => Option L)).apply_symm_apply (value,z)
    have hhead : (⟨η,fun j => (Equiv.piSplitAt η.2.1 (fun _ : X => Option L)).symm (value,z) j⟩ :
        QueryFibre W X P L)=⟨η,z⟩ := by
      exact congrArg (fun zz => (⟨η,zz⟩ : QueryFibre W X P L)) (congrArg Prod.snd h)
    exact congrArg₂ (fun (f : QueryFibre W X P L) (v : Option L) =>
      (⟨f,v⟩ : Σ _f : QueryFibre W X P L, Option L)) hhead (congrArg Prod.fst h)

/-- The Euclidean isometry grouping states into queried-cell vectors indexed by the
complementary query fibres. -/
def queryGrouping : EuclideanSpace ℂ (DatabaseBasis W X P L) ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : QueryFibre W X P L => EuclideanSpace ℂ (Option L)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ querySplit).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ : QueryFibre W X P L => fun _ : Option L => ℂ))
omit [Nonempty L] in

/-- The grouped amplitude is the original amplitude at the database reconstructed from the
selected cell value and the residual database. -/
theorem queryGrouping_apply (ψ : EuclideanSpace ℂ (DatabaseBasis W X P L))
    (f : QueryFibre W X P L) (value : Option L) :
    queryGrouping ψ f value=ψ (f.1,(Equiv.piSplitAt f.1.2.1 (fun _ : X => Option L)).symm (value,f.2)) := rfl
omit [Nonempty L] in

/-- Ungrouping evaluates the query fibre determined by the registers and residual database at
the actual queried cell value. -/
theorem queryGrouping_symm_apply
    (ψ : PiLp 2 (fun _ : QueryFibre W X P L => EuclideanSpace ℂ (Option L)))
    (η : Registers W X P) (db : X → Option L) :
    queryGrouping.symm ψ (η,db)=ψ ⟨η,fun j => db j⟩ (db η.2.1) := by
  have h :=
      queryGrouping_apply (queryGrouping.symm ψ) (⟨η,fun j => db j⟩ : QueryFibre W X P L) (db η.2.1)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  have he := (Equiv.piSplitAt η.2.1 (fun _ : X => Option L)).symm_apply_apply db
  change (Equiv.piSplitAt η.2.1 (fun _ : X => Option L)).symm (db η.2.1,fun j => db j)=db at he
  rw [he] at h
  exact h.symm

/-- The linear isometry equivalence applying the recording action to the addressed cell with
phases selected by the phase register. -/
def databaseQuery (phase : P → L → ℂ) (hp : ∀ p y, star (phase p y)*phase p y=1) :
    EuclideanSpace ℂ (DatabaseBasis W X P L) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (DatabaseBasis W X P L) :=
  (queryGrouping.trans (LinearIsometryEquiv.piLpCongrRight 2
    (fun f : QueryFibre W X P L => recordingAction (phase f.1.2.2) (hp f.1.2.2)))).trans queryGrouping.symm

/-- Reconstruct the database with a specified value at `x` and the original values at every
other address. -/
def replaceCell (db : X → Option L) (x : X) (value : Option L) : X → Option L :=
  (Equiv.piSplitAt x (fun _ : X => Option L)).symm (value,fun j => db j)
omit [Fintype X] [Fintype L] [Nonempty L] in

/-- Replacing a database cell through the splitting equivalence equals `Function.update`. -/
theorem replaceCell_eq_update (db : X → Option L) (x : X) (value : Option L) :
    replaceCell db x value=Function.update db x value := by
  funext j
  by_cases hj : j=x
  · subst j
    simp [replaceCell,Equiv.piSplitAt]
  · simp [replaceCell,Equiv.piSplitAt,hj]

/-- A database query amplitude is the sum over possible values of the addressed cell, weighted
by the recording matrix and evaluated at the correspondingly updated database. -/
theorem databaseQuery_apply (phase : P → L → ℂ) (hp : ∀ p y, star (phase p y)*phase p y=1)
    (ψ : EuclideanSpace ℂ (DatabaseBasis W X P L)) (η : Registers W X P) (db : X → Option L) :
    databaseQuery phase hp ψ (η,db)=
      ∑ value : Option L,recording (phase η.2.2) (db η.2.1) value*ψ (η,Function.update db η.2.1 value) := by
  change queryGrouping.symm (LinearIsometryEquiv.piLpCongrRight 2
    (fun f : QueryFibre W X P L => recordingAction (phase f.1.2.2) (hp f.1.2.2)) (queryGrouping ψ)) (η,db)=_
  rw [queryGrouping_symm_apply]
  change recordingAction (phase η.2.2) (hp η.2.2) (queryGrouping ψ ⟨η,fun j => db j⟩) (db η.2.1)=_
  rw [recordingAction,matrixAction_apply]
  change (∑ value : Option L,recording (phase η.2.2) (db η.2.1) value*
    queryGrouping ψ ⟨η,fun j => db j⟩ value)=_
  apply Finset.sum_congr rfl
  intro value hvalue
  rw [queryGrouping_apply]
  have he := replaceCell_eq_update db η.2.1 value
  change _*((ψ (η,replaceCell db η.2.1 value)))=_
  rw [he]
end Qatlib.Concepts.CompressedQuery.CyclicRecord
