/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.Preparation
public import Qatlib.Concepts.QRAM.WordAccess.Lookup
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-!
# Geometry, variables, and residuals in finite-volume QRAM

[ChenXueChenEtAl2022], Section 3.1 and Figure 1, store the static geometry,
physical variables and a squared residual sum tree in separate memory areas.
The geometry contains a forward stencil and its reverse incidence lists. A
variable write recomputes only residuals that depend on that variable. A signed
right-hand-side callback expresses the chosen residual convention in the
linearization.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QFVMChen22.QramStorage

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Matrix

/-- The neighbor indices of each residual entry and their reverse incidence lists. -/
structure Geometry (depth : ℕ) where
  /-- The number of neighbor slots, including any padding. -/
  stencilSize : ℕ
  /-- The physical variable read at each neighbor slot. -/
  neighbor : Address depth → Fin stencilSize → Address depth
  /-- The list of residuals to refresh after changing one physical variable. -/
  affected : Address depth → List (Address depth)
  /-- The reverse incidence list contains precisely the rows that read the variable. -/
  mem_affected : ∀ variableIndex row, row ∈ affected variableIndex ↔ ∃ slot, neighbor row slot = variableIndex

/-- The physical variable region and its cached right-hand side region. -/
structure Snapshot (depth : ℕ) where
  /-- Current physical variables, addressed by encoded cell and component. -/
  physical : Address depth → ℝ
  /-- The squared norm tree containing the signed right-hand side entries. -/
  residual : Tree ℝ depth

variable {depth : ℕ}

/-- Encode the paper's cell and component pair as one physical word address. -/
def physicalAddress {cells components : ℕ} (cell : Address cells) (component : Address components) :
    Address (components + cells) :=
  joinAddress cells cell component

/-- Evaluate a signed residual at one row from only the physical variables in its stencil. -/
def residualEntry (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (physical : Address depth → ℝ) (row : Address depth) : ℝ :=
  localRhs row (fun slot => physical (geometry.neighbor row slot))

/-- The residual cache is valid and every leaf agrees with its stencil evaluation. -/
def Consistent (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) : Prop :=
  Valid snapshot.residual ∧
    ∀ row, read snapshot.residual row = residualEntry geometry localRhs snapshot.physical row

/-- Load the physical region and initialize every residual entry. -/
def initializeSnapshot (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (physical : Address depth → ℝ) : Snapshot depth :=
  ⟨physical, ofFn depth (residualEntry geometry localRhs physical)⟩

/-- Dense initialization establishes the residual invariant. -/
theorem consistent_initialize (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (physical : Address depth → ℝ) :
    Consistent geometry localRhs (initializeSnapshot geometry localRhs physical) :=
  ⟨valid_ofFn _ _, read_ofFn _ _⟩

/-- Write a physical variable and refresh exactly its reverse stencil. -/
def writePhysical (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (address : Address depth) (value : ℝ) : Snapshot depth :=
  let physical := Qatlib.Concepts.QRAM.WordAccess.write snapshot.physical address value
  ⟨physical, refresh snapshot.residual (geometry.affected address)
    (residualEntry geometry localRhs physical)⟩

/-- A local write preserves the global invariant, including at untouched residuals. -/
theorem consistent_write (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (h : Consistent geometry localRhs snapshot)
    (address : Address depth) (value : ℝ) :
    Consistent geometry localRhs (writePhysical geometry localRhs snapshot address value) := by
  refine ⟨valid_refresh _ h.1 _ _, ?_⟩
  intro row
  simp only [writePhysical, read_refresh]
  split_ifs with hAffected
  · rfl
  rw [h.2 row]
  unfold residualEntry
  congr 1
  funext slot
  have hOther : geometry.neighbor row slot ≠ address :=
    fun hEq => hAffected ((geometry.mem_affected address row).2 ⟨slot, hEq⟩)
  simp [Qatlib.Concepts.QRAM.WordAccess.write, hOther]

/-- The number of residual cells written is the reverse-stencil size times the path length. -/
theorem residual_cells_written (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (address : Address depth) (value : ℝ) :
    (refreshWithCount snapshot.residual (geometry.affected address)
      (residualEntry geometry localRhs
        (Qatlib.Concepts.QRAM.WordAccess.write snapshot.physical address value))).2 =
      (geometry.affected address).length * (depth + 1) :=
  refresh_cell_count _ _ _

/-- The residual preparation loads the normalized signed right-hand side of the current step. -/
theorem residual_preparation (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (snapshot : Snapshot depth) (h : Consistent geometry localRhs snapshot) (row : Address depth) :
    pathAmplitude snapshot.residual row =
      residualEntry geometry localRhs snapshot.physical row /
        Real.sqrt (∑ i, residualEntry geometry localRhs snapshot.physical i ^ 2) := by
  rw [path_amplitude_eq _ h.1, mass_eq_sum _ h.1]
  simp only [h.2]

/-- Coherent word access to the physical-variable region for a fixed encoding. -/
noncomputable def physicalQuery {width : ℕ} (encode : ℝ → BitVec width) (snapshot : Snapshot depth) :
    Matrix (Address depth × BitVec width) (Address depth × BitVec width) ℂ :=
  Qatlib.Concepts.QRAM.WordAccess.query (encode ∘ snapshot.physical)

/-- Coherently load the neighbor index into a separate target, preserving the row and slot. -/
noncomputable def geometryQuery {width : ℕ} (encode : Address depth → BitVec width)
    (geometry : Geometry depth) :
    Matrix ((Address depth × Fin geometry.stencilSize) × BitVec width)
      ((Address depth × Fin geometry.stencilSize) × BitVec width) ℂ :=
  Qatlib.Concepts.QRAM.WordAccess.query (fun address => encode (geometry.neighbor address.1 address.2))

/-- Coherent word access to all residual cache cells at the chosen tree level. -/
noncomputable def residualMassQuery {width remaining levels : ℕ} (encode : ℝ → BitVec width)
    (snapshot : Snapshot (remaining + levels)) :
    Matrix (Address levels × BitVec width) (Address levels × BitVec width) ℂ :=
  Qatlib.Concepts.QRAM.WordAccess.query
    (fun address => encode (mass (subtree levels snapshot.residual address)))

end Qatlib.Papers.QFVMChen22.QramStorage
