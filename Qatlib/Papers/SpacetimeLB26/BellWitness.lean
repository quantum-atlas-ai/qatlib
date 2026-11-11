/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.Entanglement.BellWitness.Separable
import Qatlib.Concepts.Entanglement.Separability.EntanglementBoundaryConsumers

/-!
# A Bell-state witness for separable states

This module identifies the foundational Bell vector with the native state `bell (false, false)`.
It transfers the overlap and trace-norm separation estimates for separable two-qubit states to
this representation for the argument in [BhartiHaugTanggara2026].

## Main statements

* `foundation_phi_eq_native`: The foundational Bell vector equals the native Bell state `bell
  (false, false)`.
* `bell_state_witness`: A separable two-qubit state has overlap at most `1/2` with `bell (false,
  false)`, and its trace-norm distance from the corresponding pure-state matrix is at least one.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.SpacetimeLB26.BellWitness
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.FiniteLocc.LOCCProgram

/-- The foundational Bell vector equals the native Bell state `bell (false, false)`. -/
theorem foundation_phi_eq_native :
    Qatlib.Foundations.Entanglement.BellWitness.phi=bell (false,false) := by
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [Qatlib.Foundations.Entanglement.BellWitness.phi,bell,Qatlib.Foundations.PureStateMath.Ket]

/-- A separable two-qubit state has overlap at most `1/2` with `bell (false, false)`, and its
trace-norm distance from the corresponding pure-state matrix is at least one. See
[BhartiHaugTanggara2026]. -/
theorem bell_state_witness (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : IsSeparableState ρ) :
    (outerProduct (bell (false,false))*ρ).trace.re ≤ 1/2 ∧
      1 ≤ Matrix.traceNorm (outerProduct (bell (false,false))-ρ) := by
  have hs : Qatlib.Foundations.Entanglement.BellWitness.IsSeparableState ρ := hρ
  have ht := Qatlib.Foundations.Entanglement.BellWitness.bell_state_witness ρ hs
  have ho : Qatlib.Foundations.Entanglement.BellWitness.outerProduct
      Qatlib.Foundations.Entanglement.BellWitness.phi =
      outerProduct (bell (false,false)) := by
    rw [foundation_phi_eq_native]
    rfl
  simpa only [ho] using ht
end Qatlib.Papers.SpacetimeLB26.BellWitness
