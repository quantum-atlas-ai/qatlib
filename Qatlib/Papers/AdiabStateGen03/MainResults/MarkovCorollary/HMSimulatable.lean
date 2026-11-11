/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.MarkovCorollary.Basic

/-!
# Simulation of a reversible chain Hamiltonian

This module packages the sparse Hamiltonian simulation hypothesis in `SparseHamiltonianLemma`
and applies it to `HM` for a strongly samplable Markov chain. It also proves that the
square-root distribution state has zero Rayleigh value for this Hamiltonian through
`hm_rayleigh_sqrt`. The mathematical context is [AharonovTaShma2007].

## Main statements

* `hm_simulatable`: The chain Hamiltonian `HM M π` is simulatable under strong samplability, row
  computability, a polynomial norm bound, and `SparseHamiltonianLemma n`.
* `hm_rayleigh_sqrt`: The square-root distribution state has Rayleigh value zero for the
  Hamiltonian of a strongly samplable chain.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.MarkovCorollary

open Qatlib.Papers.AdiabStateGen03.MainResults
open WithLp

variable {n : ℕ}

/-- The proposition that row-sparse, row-computable Hamiltonians with polynomially bounded norm
are simulatable at size `n`. -/
def SparseHamiltonianLemma (n : ℕ) : Prop :=
  ∀ (H : Ham n) (D : ℕ), RowSparse H D → RowComputable H →
    PolyBoundedAt n ‖H‖ → Simulatable H

/-- The chain Hamiltonian `HM M π` is simulatable under strong samplability, row computability,
a polynomial norm bound, and `SparseHamiltonianLemma n`. -/
theorem hm_simulatable (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π)
    (hrow : RowComputable (HM M π)) (hnorm : PolyBoundedAt n ‖HM M π‖)
    (hlemma : SparseHamiltonianLemma n) : Simulatable (HM M π) :=
  hlemma (HM M π) (h.D + 1) (hm_rowSparse M π h) hrow hnorm

/-- The square-root distribution state has Rayleigh value zero for the Hamiltonian of a strongly
samplable chain [AharonovTaShma2007]. -/
theorem hm_rayleigh_sqrt (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π) :
    rayleigh (HM M π) (ketOfDist π) = 0 := by
  unfold rayleigh
  have hzero : toOp (HM M π) (ketOfDist π) = 0 := by
    have hk : ketOfDist π = toLp 2 (fun i : Dim n => (Real.sqrt (π i) : ℂ)) := rfl
    rw [hk]
    unfold toOp
    rw [Matrix.toEuclideanCLM_toLp]
    rw [show (HM M π) *ᵥ (fun i : Dim n => (Real.sqrt (π i) : ℂ)) = 0 from
      hm_mulVec_sqrt M π h]
    simp
  rw [hzero, inner_zero_right]
  simp

/-- The real part of the Hamiltonian expectation in the square-root distribution state is zero
for a strongly samplable chain. -/
theorem hm_ground_rayleigh (M : MC n) (π : Dim n → ℝ) (h : StronglySamplable M π) :
    (⟪ketOfDist π, toOp (HM M π) (ketOfDist π)⟫_ℂ).re = 0 :=
  hm_rayleigh_sqrt M π h

end Qatlib.Papers.AdiabStateGen03.MainResults.MarkovCorollary
