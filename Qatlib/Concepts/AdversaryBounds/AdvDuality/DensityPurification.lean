/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped ComplexOrder MatrixOrder

private theorem purification_branchMass {d e : ℕ}
    (psi : QState (Fin d × Fin e)) :
    branchMass psi = (Matrix.trace (PartialTrace (outerProduct psi))).re := by
  rw [trace_partialTrace, trace_outerProduct]
  rfl

theorem density_purification_exists {d : ℕ} (rho : Operator d)
    (hrho : rho.PosSemidef) :
    ∃ psi : QState (Fin d × Fin d),
      PartialTrace (outerProduct psi) = rho ∧
        branchMass psi = (Matrix.trace rho).re := by
  let S : Operator d := CFC.sqrt rho
  have hS : S.conjTranspose = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg rho)).isHermitian
  let psi : QState (Fin d × Fin d) := fun p => S p.1 p.2
  have hmarginal : PartialTrace (outerProduct psi) = rho := by
    calc
      PartialTrace (outerProduct psi) = S * S.conjTranspose := by
        ext i j
        rfl
      _ = S * S := by rw [hS]
      _ = rho := CFC.sqrt_mul_sqrt_self rho hrho.nonneg
  refine ⟨psi, hmarginal, ?_⟩
  rw [purification_branchMass, hmarginal]

theorem density_purification_normalized {d : ℕ} (rho : Operator d)
    (hrho : IsDensityOperator rho) :
    ∃ psi : QState (Fin d × Fin d),
      Normalized psi ∧ PartialTrace (outerProduct psi) = rho := by
  obtain ⟨psi, hmarginal, hmass⟩ := density_purification_exists rho hrho.1
  refine ⟨psi, ?_, hmarginal⟩
  change branchMass psi = 1
  simpa only [hrho.2, Complex.one_re] using hmass

end Qatlib.Concepts.AdversaryBounds.AdvDuality
