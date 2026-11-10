/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.SdpRunMacros
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SdpMmwSolver.OracleError

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def sdpEventProbability {R : ℕ} (P : Fin R → Prop) : ℝ :=
  (Finset.univ.filter P).card / (R : ℝ)

def sdpSampledWidthBudget (α R κ ν : ℝ) : ℝ := α * (1 + 2 * R * (κ + ν))

def sdpSampledSeparationSlack (α κ ν : ℝ) : ℝ := 2 * α * (κ + ν)

def sdpSparsifiedPayoff (D m Q : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (α : ℝ) (idx : Fin Q → Fin m) : Operator D :=
  ((4 * α : ℝ))⁻¹ • (((Q : ℝ)⁻¹ • (∑ j : Fin Q, A (idx j))) - Cv + (2 * α) • (1 : Operator D))

def sdpScaledSparsifiedPayoff (D m Q : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (α mass : ℝ) (idx : Fin Q → Fin m) : Operator D :=
  ((4 * α : ℝ))⁻¹ •
    (mass • ((Q : ℝ)⁻¹ • (∑ j : Fin Q, A (idx j))) - Cv +
      (2 * α) • (1 : Operator D))

end Qatlib.Concepts.SdpMmwSolver.OracleError
