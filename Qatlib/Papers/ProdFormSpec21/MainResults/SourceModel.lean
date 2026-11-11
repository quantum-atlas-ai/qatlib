/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.Trace

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral analysis of product formulas — shared source model

Source: *Spectral Analysis of Product Formulas for Quantum Simulation*,
arXiv:2102.12655v2.  This module fixes the vocabulary shared by the paper-layer
statements of `ProdFormSpec21.MainResults`: pure states, the effective-Hamiltonian
picture `T(δt)^L = e^{-iH̃ (L δt)}` (paper Eq (30)), rank-one / spectral
projectors, the leakage functional, and the fidelity / phase defects.

The effective-Hamiltonian picture is exactly the paper's own definition
`H̃(s) ≡ i log(U^t(s))/δt` (Eq (30)), so replacing the raw product of single-step
unitaries by `HamiltonianEvolution H̃ t` is a change of notation, not of content.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The **rank-one (or spectral) projector** `|ψ⟩⟨ψ|` attached to a state `ψ`. -/
noncomputable def rankOne (ψ : QState I) : Matrix I I ℂ := fun i j => ψ i * star (ψ j)

/-- The expectation `⟨ψ| M |ψ⟩` of a matrix in a state. -/
noncomputable def expectOf (M : Matrix I I ℂ) (ψ : QState I) : ℂ := Inner ψ (ApplyGate M ψ)

/-- The **fidelity defect** `f = 1 − |⟨φ|ψ⟩|²` of two unit vectors, paper Eq (5). -/
noncomputable def fidelityDefect (φ ψ : QState I) : ℝ := 1 - ‖Inner φ ψ‖ ^ 2

/-- The **phase defect** `θ = Arg⟨φ|ψ⟩` of two unit vectors, paper Eq (6). -/
noncomputable def phaseDefect (φ ψ : QState I) : ℝ := Complex.arg (Inner φ ψ)

/-- The aggregate of a spectral subspace: the sum of rank-one projectors over an
index set `A`.  This is the paper's `P = Σ_{j∈A} Pj`. -/
noncomputable def spectralProjector (φ : I → QState I) (A : Finset I) : Matrix I I ℂ :=
  ∑ j ∈ A, rankOne (φ j)

/-! ## Bilinearity of the inner product (used by the Corollary 1 decomposition) -/

/-- `⟨u|v+w⟩ = ⟨u|v⟩ + ⟨u|w⟩`. -/
theorem Inner_add_right (u v w : QState I) : Inner u (v + w) = Inner u v + Inner u w := by
  simp only [inner_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- `⟨u|c•v⟩ = c·⟨u|v⟩` (linear in the second argument). -/
theorem Inner_smul_right (u v : QState I) (c : ℂ) : Inner u (c • v) = c * Inner u v := by
  simp only [inner_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Qatlib.Papers.ProdFormSpec21.MainResults
