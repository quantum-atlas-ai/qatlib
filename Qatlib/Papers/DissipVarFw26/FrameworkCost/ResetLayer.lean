/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Papers.DissipVarFw26.FrameworkCost.ResetLayers

noncomputable def slice {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (e : Fin A) : Operator D := fun i j => U (i,e) (j,seed)

noncomputable def resetInput {D A : ℕ} (seed : Fin A) (ρ : Operator D) :
    Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ :=
  fun x y => if x.2 = seed ∧ y.2 = seed then ρ x.1 y.1 else 0

noncomputable def discard {D A : ℕ}
    (ρ : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) : Operator D :=
  fun i j => ∑ e : Fin A, ρ (i,e) (j,e)

theorem discard_eq_partialTrace {D A : ℕ}
    (ρ : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) : discard ρ = PartialTrace ρ := rfl

theorem resetInput_tensor {D A : ℕ} (seed : Fin A) (ρ : Operator D) :
    resetInput seed ρ = Matrix.kronecker ρ (matrixUnit seed seed) := by
  ext x y
  simp [resetInput, matrixUnit_apply, eq_comm]

theorem slice_complete {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ) :
    KrausComplete (slice U seed) := by
  have hleft : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  ext i j
  have h := congrArg (fun M => M (i,seed) (j,seed)) hleft
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] at h
  rw [Finset.sum_comm] at h
  simpa [KrausComplete, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, slice, Matrix.one_apply, Prod.mk.injEq] using h

theorem actual_reset_unitary_discard {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A) (ρ : Operator D) :
    krausMap (slice U seed) ρ = discard (U * resetInput seed ρ * U.conjTranspose) := by
  ext i j
  simp only [krausMap, LinearMap.sum_apply, conjBranch_apply, Matrix.sum_apply,
    discard, kraus_mul_apply]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    resetInput, Finset.sum_mul, slice]
  simp only [ite_and]
  simp
  rw [Finset.sum_comm]

noncomputable def actualChannel {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ) : QuantumChannel D D where
  map := krausMap (slice U seed)
  completelyPositive := completelyPositive_of_krausForm (K := slice U seed) (by
    intro ρ
    simp only [krausMap, LinearMap.sum_apply, conjBranch_apply])
  tracePreserving := tracePreserving_of_krausComplete (K := slice U seed) (by
    intro ρ
    simp only [krausMap, LinearMap.sum_apply, conjBranch_apply]) (slice_complete U seed hU)

theorem actualChannel_map {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ) (ρ : Operator D) :
    (actualChannel U seed hU).map ρ = discard (U * resetInput seed ρ * U.conjTranspose) :=
  actual_reset_unitary_discard U seed ρ

theorem actualChannel_physical_map {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ) (ρ : Operator D) :
    (actualChannel U seed hU).map ρ =
      PartialTrace (U * Matrix.kronecker ρ (matrixUnit seed seed) * U.conjTranspose) := by
  rw [actualChannel_map, resetInput_tensor, discard_eq_partialTrace]

theorem composed_physical_map {D A B : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seedA : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ)
    (V : Matrix (Fin D × Fin B) (Fin D × Fin B) ℂ) (seedB : Fin B)
    (hV : V ∈ Matrix.unitaryGroup (Fin D × Fin B) ℂ) (ρ : Operator D) :
    ((actualChannel V seedB hV).comp (actualChannel U seedA hU)).map ρ =
      PartialTrace (V * Matrix.kronecker
        (PartialTrace (U * Matrix.kronecker ρ (matrixUnit seedA seedA) * U.conjTranspose))
        (matrixUnit seedB seedB) * V.conjTranspose) := by
  change (actualChannel V seedB hV).map ((actualChannel U seedA hU).map ρ) = _
  rw [actualChannel_physical_map, actualChannel_physical_map]

noncomputable def coherentChannel {D A : ℕ}
    (U V : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ) : QuantumChannel D D :=
  actualChannel (V * U) seed ((Matrix.unitaryGroup (Fin D × Fin A) ℂ).mul_mem hV hU)

end Qatlib.Papers.DissipVarFw26.FrameworkCost.ResetLayers
