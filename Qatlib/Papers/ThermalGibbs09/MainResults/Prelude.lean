/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixExpTrace.ExpPerturbation

set_option backward.isDefEq.respectTransparency false

/-!
# ThermalGibbs09 — shared paper-layer vocabulary

Poulin--Wocjan, *Sampling from the thermal quantum Gibbs state and evaluating
partition functions with a quantum computer*, fixed arXiv:0905.2199.

This file supplies the partition function and the Gibbs state used by the
paper-layer contracts, together with the elementary positivity facts needed to
connect them to the matrix-exponential perturbation library
(`Qatlib.Concepts.MatrixExpTrace.ExpPerturbation`).

Boundary: these definitions only fix the paper's notation. They make no
complexity or algorithm statement; those live in the individual claim files.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ThermalGibbs09.MainResults

open Qatlib.Concepts.MatrixExpTrace.ExpPerturbation

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The partition function of a Hamiltonian `H` at inverse temperature `β`,
`Z(β) = Tr exp(-β H)`, taking the real part of the complex trace. This is the
quantity called `Z(β)` throughout arXiv:0905.2199 (eq. (3) and Appendix B). -/
noncomputable def partitionFunction (β : ℝ) (H : Matrix I I ℂ) : ℝ :=
  (Matrix.trace (NormedSpace.exp ((-β) • H))).re

/-- The (normalized) Gibbs state `ρ(β) = exp(-β H) / Z(β)` of
arXiv:0905.2199 (Appendix C). -/
noncomputable def gibbsState (β : ℝ) (H : Matrix I I ℂ) : Matrix I I ℂ :=
  (partitionFunction β H)⁻¹ • NormedSpace.exp ((-β) • H)

/-- The partition function is nonnegative for every Hermitian Hamiltonian. -/
theorem partitionFunction_nonneg (β : ℝ) (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    0 ≤ partitionFunction β H := by
  rw [partitionFunction, exp_trace_eq_sum _ (hH.smul (R := ℝ) (IsSelfAdjoint.all _))]
  exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

/-- The partition function is strictly positive on a nonempty space. -/
theorem partitionFunction_pos [Nonempty I] (β : ℝ) (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    0 < partitionFunction β H := by
  rw [partitionFunction, exp_trace_eq_sum _ (hH.smul (R := ℝ) (IsSelfAdjoint.all _))]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- The paper's `Z(β)` is the real trace of the matrix exponential at `-βH`. -/
theorem partitionFunction_eq_trace_exp (β : ℝ) (H : Matrix I I ℂ) :
    partitionFunction β H = (Matrix.trace (NormedSpace.exp ((-β) • H))).re :=
  rfl

/-- At zero inverse temperature the Gibbs weight is the identity, so the
partition function equals the Hilbert-space dimension, `Z(0) = D`.  This is the
initial value `Z(β_0) = D` of the paper's cooling schedule at `β_0 = 0`. -/
theorem partitionFunction_zero (H : Matrix I I ℂ) :
    partitionFunction 0 H = (Fintype.card I : ℝ) := by
  simp [partitionFunction]

end Qatlib.Papers.ThermalGibbs09.MainResults
