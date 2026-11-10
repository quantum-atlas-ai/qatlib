/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.CopyExponent

open Matrix

set_option autoImplicit false

def CommutingCopyExactTightness : Prop :=
  ∀ (t : ℝ) (n : ℕ) (s : ℝ), 0 ≤ t → 0 < n → t ^ 2 ≤ (n : ℝ) → 0 ≤ s → s ≤ 1 →
    (freshCopyReferenceRun (Matrix.diagonal (fun b : Fin 2 =>
          if b = 0 then (1 : ℂ) else 0)) (List.replicate n (t / (n : ℝ))) 1
        (TensorGate (Matrix.diagonal
            (fun b : Fin 2 => if b = 0 then ((1 - s : ℝ) : ℂ) else (s : ℝ)))
          (1 : Operator 1)) -
      TensorGate (Matrix.diagonal
          (fun b : Fin 2 => if b = 0 then ((1 - s : ℝ) : ℂ) else (s : ℝ)))
        (1 : Operator 1)) =
      ((1 : ℝ) - (Real.cos (t / (n : ℝ))) ^ (2 * n)) •
      (TensorGate (Matrix.diagonal (fun b : Fin 2 => if b = 0 then (1 : ℂ) else 0))
          (1 : Operator 1) -
        TensorGate (Matrix.diagonal
            (fun b : Fin 2 => if b = 0 then ((1 - s : ℝ) : ℂ) else (s : ℝ)))
          (1 : Operator 1)) ∧
    Matrix.traceNorm (freshCopyReferenceRun (Matrix.diagonal (fun b : Fin 2 =>
          if b = 0 then (1 : ℂ) else 0)) (List.replicate n (t / (n : ℝ))) 1
        (TensorGate (Matrix.diagonal
            (fun b : Fin 2 => if b = 0 then ((1 - s : ℝ) : ℂ) else (s : ℝ)))
          (1 : Operator 1)) -
      TensorGate (Matrix.diagonal
          (fun b : Fin 2 => if b = 0 then ((1 - s : ℝ) : ℂ) else (s : ℝ)))
        (1 : Operator 1)) = (1 - (Real.cos (t / (n : ℝ))) ^ (2 * n)) * 2 * s ∧
    t ^ 2 / (8 * (n : ℝ)) ≤ 1 - (Real.cos (t / (n : ℝ))) ^ (2 * n)

end Qatlib.Concepts.CopyEvolution.CopyExponent
