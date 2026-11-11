/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring

/-!
# Reset channels from joint unitary evolution

A joint unitary with an ancilla initialized at `seed` defines Kraus operators `slice` and the
quantum channel `actualChannel`. The module identifies its map with ancilla preparation, joint
evolution, and partial trace, and records the physical expression for two successive reset
layers as well as coherent composition before discarding.

This development follows [YaoEtAl2026].

## Main statements

* `slice_complete`: the unitary slices satisfy Kraus completeness.
* `actualChannel_physical_map`: the channel equals joint unitary evolution followed by partial
  trace.
* `composed_physical_map`: two reset channels act by successive preparation, evolution, and
  partial trace.

## References

* [Yao et al., 2026][YaoEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Papers.DissipVarFw26.FrameworkCost.ResetLayers

/-- The system operator with entries `U (i, e) (j, seed)`, obtained by fixing the input and
output ancilla indices. -/
noncomputable def slice {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (e : Fin A) : Operator D := fun i j => U (i,e) (j,seed)

/-- The joint operator formed by placing the system operator in the ancilla block supported at
`seed`. -/
noncomputable def resetInput {D A : ℕ} (seed : Fin A) (ρ : Operator D) :
    Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ :=
  fun x y => if x.2 = seed ∧ y.2 = seed then ρ x.1 y.1 else 0

/-- The ancilla-discard map summing diagonal ancilla blocks. -/
noncomputable def discard {D A : ℕ}
    (ρ : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) : Operator D :=
  fun i j => ∑ e : Fin A, ρ (i,e) (j,e)

/-- The explicit discard map equals the standard partial trace. -/
theorem discard_eq_partialTrace {D A : ℕ}
    (ρ : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) : discard ρ = PartialTrace ρ := rfl

/-- Preparing the ancilla at `seed` gives the Kronecker product of the system operator with
`matrixUnit seed seed`. -/
theorem resetInput_tensor {D A : ℕ} (seed : Fin A) (ρ : Operator D) :
    resetInput seed ρ = Matrix.kronecker ρ (matrixUnit seed seed) := by
  ext x y
  simp [resetInput, matrixUnit_apply, eq_comm]

/-- For a unitary joint matrix, the system operators obtained by fixing the input ancilla at
`seed` satisfy Kraus completeness. -/
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

/-- The Kraus map of the slices equals preparing the ancilla, applying the joint matrix and its
conjugate transpose, and discarding the ancilla. -/
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

/-- The completely positive trace-preserving channel induced by a joint unitary and an ancilla
initialized at `seed`. See [YaoEtAl2026]. -/
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

/-- The reset-channel map equals the explicit prepare, joint-unitary, and discard expression. -/
theorem actualChannel_map {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ) (ρ : Operator D) :
    (actualChannel U seed hU).map ρ = discard (U * resetInput seed ρ * U.conjTranspose) :=
  actual_reset_unitary_discard U seed ρ

/-- The reset-channel map equals the partial trace of the joint unitary conjugation of `ρ ⊗
matrixUnit seed seed`. See [YaoEtAl2026]. -/
theorem actualChannel_physical_map {D A : ℕ}
    (U : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ) (ρ : Operator D) :
    (actualChannel U seed hU).map ρ =
      PartialTrace (U * Matrix.kronecker ρ (matrixUnit seed seed) * U.conjTranspose) := by
  rw [actualChannel_map, resetInput_tensor, discard_eq_partialTrace]

/-- Composing two reset channels equals applying their respective ancilla preparations, joint
unitary conjugations, and partial traces in sequence. See [YaoEtAl2026]. -/
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

/-- The reset channel obtained by applying the joint unitaries `U` and then `V` coherently
before discarding the single initialized ancilla. -/
noncomputable def coherentChannel {D A : ℕ}
    (U V : Matrix (Fin D × Fin A) (Fin D × Fin A) ℂ) (seed : Fin A)
    (hU : U ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D × Fin A) ℂ) : QuantumChannel D D :=
  actualChannel (V * U) seed ((Matrix.unitaryGroup (Fin D × Fin A) ℂ).mul_mem hV hU)

end Qatlib.Papers.DissipVarFw26.FrameworkCost.ResetLayers
