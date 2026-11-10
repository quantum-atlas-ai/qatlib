/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix

set_option autoImplicit false

def SelfTomographyOnGridOutput : Prop :=
  ∀ (D M : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ),
    0 < M → IsDensityOperator ρ → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
    ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ → (∀ i, 0 ≤ eig i) →
    (∀ i, ∃ z : Fin M, phaseDistance (-(eig i) / 2) ((z.val : ℝ) / M) = 0) →
    ∃ z : Fin D → Fin M,
      (∀ i, phaseDistance (-(eig i) / 2) ((z i).val / M) = 0) ∧
      copyQPEIdealOutput D M ρ =
        ∑ i, (eig i : ℂ) • outerProduct
          (fun p : Fin M × (Bool × Fin D) =>
            if p.2.1 then 0 else if p.1 = z i then V p.2.2 i else 0)

end Qatlib.Concepts.CopyEvolution.SelfTomography
