/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase

/-!
# Hermiticity of the graph Hamiltonians

This module proves that `pairPauli`, `qmcHamiltonian`, and `secondaryHamiltonian` equal their
conjugate transposes. These matrix identities justify the Hermitian Hamiltonian structure for
the finite weighted QMC and transverse-coupling models.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `pair_hermitian`: proves Hermiticity of the embedded pair operator.
* `qmc_hermitian` and `secondary_hermitian`: prove Hermiticity for real edge weights.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Hamiltonian
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase

/-- Every register pair Pauli operator equals its conjugate transpose. -/
theorem pair_hermitian {n : ℕ} (i j : Fin n) (a : Fin 3) : (pairPauli i j a)ᴴ=pairPauli i j a := by
  rw [pairPauli,qubitTensor_conjTranspose]
  congr 1
  funext h
  split <;> simp only [axis_adjoint,Matrix.conjTranspose_one]

/-- The QMC Hamiltonian with real edge weights equals its conjugate transpose. -/
theorem qmc_hermitian {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) : (qmcHamiltonian ends w)ᴴ=qmcHamiltonian ends w := by
  simp [qmcHamiltonian,edgeOperator,Matrix.conjTranspose_smul,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_sub,pair_hermitian]

/-- The secondary XX+YY Hamiltonian with real edge weights equals its conjugate transpose. -/
theorem secondary_hermitian {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) : (secondaryHamiltonian ends w)ᴴ=secondaryHamiltonian ends w := by
  simp [secondaryHamiltonian,Matrix.conjTranspose_smul,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_add,pair_hermitian]
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Hamiltonian
