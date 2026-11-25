/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.QramStorage.ResidualMemory

@[expose] public section

/-!
# Sparse corrections in an implicit finite-volume step

[ChenXueChenEtAl2022], Sections 3.2–3.3, obtains a normalized classical
estimate of the linear-system solution by tomography and separately
estimates its scale. A sparse list of estimates is then rescaled and
written back into the physical state with local residual repairs. The
list and scale are inputs from the solver and readout phases.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Papers.QFVMChen22.QramStorage

variable {depth : ℕ}

/-- Apply the rescaled tomography output as sparse additions to the current variables. -/
noncomputable def applyCorrection (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (scale : ℝ) (updates : List (Address depth × ℝ)) (snapshot : Snapshot depth) :
    Snapshot depth :=
  updates.foldl (fun current correction =>
    writePhysical geometry localRhs current correction.1
      (current.physical correction.1 + scale * correction.2)) snapshot

/-- Each sparse addition repairs the incident residuals, preserving global consistency. -/
theorem consistent_apply_correction (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (scale : ℝ) (updates : List (Address depth × ℝ)) (snapshot : Snapshot depth)
    (h : Consistent geometry localRhs snapshot) :
    Consistent geometry localRhs (applyCorrection geometry localRhs scale updates snapshot) := by
  induction updates generalizing snapshot with
  | nil => exact h
  | cons correction updates ih =>
      exact ih _ (consistent_write geometry localRhs snapshot h _ _)

/-- Accumulate all normalized correction entries listed for one physical address. -/
def correctionAt (updates : List (Address depth × ℝ)) (address : Address depth) : ℝ :=
  (updates.map fun update => if update.1 = address then update.2 else 0).sum

/-- Sparse writeback adds the scaled correction at each address, even with repeated records. -/
theorem physical_eq_add_correction (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (scale : ℝ) (updates : List (Address depth × ℝ)) (snapshot : Snapshot depth)
    (address : Address depth) :
    (applyCorrection geometry localRhs scale updates snapshot).physical address =
      snapshot.physical address + scale * correctionAt updates address := by
  induction updates generalizing snapshot with
  | nil => simp [applyCorrection, correctionAt]
  | cons update pending ih =>
      change (applyCorrection geometry localRhs scale pending
        (writePhysical geometry localRhs snapshot update.1
          (snapshot.physical update.1 + scale * update.2))).physical address = _
      rw [ih]
      by_cases hAddress : address = update.1
      · simp [writePhysical, Qatlib.Concepts.QRAM.WordAccess.write, hAddress,
          correctionAt, mul_add, add_assoc]
      · simp [writePhysical, Qatlib.Concepts.QRAM.WordAccess.write, hAddress,
          Ne.symm hAddress, correctionAt]

/-- A physical variable absent from the tomography support is unchanged by the step. -/
theorem untouched_physical (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (scale : ℝ) (updates : List (Address depth × ℝ)) (snapshot : Snapshot depth)
    (address : Address depth) (h : address ∉ updates.map Prod.fst) :
    (applyCorrection geometry localRhs scale updates snapshot).physical address =
      snapshot.physical address := by
  induction updates generalizing snapshot with
  | nil => rfl
  | cons correction updates ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      change (applyCorrection geometry localRhs scale updates
        (writePhysical geometry localRhs snapshot correction.1
          (snapshot.physical correction.1 + scale * correction.2))).physical address = _
      rw [ih _ h.2]
      simp [writePhysical, Qatlib.Concepts.QRAM.WordAccess.write, h.1]

/-- Run the sparse corrections and charge one physical write, `rhsPrice` per refreshed
residual evaluation, and one squared-norm tree cell write at each level of its path. -/
noncomputable def applyCorrectionWithCost (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (scale : ℝ) (rhsPrice : ℕ) : List (Address depth × ℝ) → Snapshot depth → Snapshot depth × ℕ
  | [], snapshot => (snapshot, 0)
  | update :: rest, snapshot =>
      let next := writePhysical geometry localRhs snapshot update.1
        (snapshot.physical update.1 + scale * update.2)
      let result := applyCorrectionWithCost geometry localRhs scale rhsPrice rest next
      (result.1, 1 + (geometry.affected update.1).length * (rhsPrice + (depth + 1)) + result.2)

/-- The costed traversal writes exactly the same physical variables and residual tree
as the implicit step's sparse update. -/
theorem apply_correction_with_cost_snapshot (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (scale : ℝ) (rhsPrice : ℕ) (updates : List (Address depth × ℝ)) (snapshot : Snapshot depth) :
    (applyCorrectionWithCost geometry localRhs scale rhsPrice updates snapshot).1 =
      applyCorrection geometry localRhs scale updates snapshot := by
  induction updates generalizing snapshot with
  | nil => rfl
  | cons update rest ih => exact ih _

/-- The reverse-stencil bound gives the total maintenance charge for the sparse list,
including repeated addresses and padded stencil slots. -/
theorem apply_correction_cost_le (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (scale : ℝ) (rhsPrice degree : ℕ) (hDegree : ∀ address, (geometry.affected address).length ≤ degree)
    (updates : List (Address depth × ℝ)) (snapshot : Snapshot depth) :
    (applyCorrectionWithCost geometry localRhs scale rhsPrice updates snapshot).2 ≤
      updates.length * (1 + degree * (rhsPrice + (depth + 1))) := by
  induction updates generalizing snapshot with
  | nil => simp [applyCorrectionWithCost]
  | cons update rest ih =>
      let price := 1 + degree * (rhsPrice + (depth + 1))
      let next := writePhysical geometry localRhs snapshot update.1
        (snapshot.physical update.1 + scale * update.2)
      have hPrice : 1 + (geometry.affected update.1).length * (rhsPrice + (depth + 1)) ≤ price :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (hDegree update.1)) 1
      change _ + (applyCorrectionWithCost geometry localRhs scale rhsPrice rest next).2 ≤
        (rest.length + 1) * price
      calc
        _ ≤ price + rest.length * price := Nat.add_le_add hPrice (ih next)
        _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

end Qatlib.Papers.QFVMChen22.TimeStep
