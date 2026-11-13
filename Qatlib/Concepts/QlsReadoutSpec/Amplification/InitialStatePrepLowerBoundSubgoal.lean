/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.InitialStatePreparationContracts

/-!
# Initial-state oracle obstruction

Exhibits a concrete obstruction for the proposed `bOracle` at index zero on `Fin 150` with unit
workspace. `initialStatePreparationOracleObstruction` shows that this matrix is not unitary and
fails the stated preparation identity even for normalized basis-state seeds. This records a
limitation of the oracle model used to formulate initial-state preparation bounds motivated by
[LowSu2026].

## Main statements

* `initialStatePreparationOracleObstruction`: proves nonunitarity and failure of the preparation
  identity for the specified oracle instance.

## References

* [Low and Su, 2026][LowSu2026]
-/

open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification
open Matrix

/-- For the zero-index `bOracle` on `Fin 150` with unit workspace, proves nonunitarity,
normalization of both chosen basis-state seeds, and failure to produce the stated `bState`
product vector from `solverStart`. -/
theorem initialStatePreparationOracleObstruction :
    bOracle (I := Fin 150) (W := Unit) 0 ∉
        Matrix.unitaryGroup (((Fin 150) × Bool) × Unit) ℂ ∧
      Normalized (Qatlib.Foundations.PureStateMath.Ket false) ∧ Normalized (Qatlib.Foundations.PureStateMath.Ket ()) ∧
      bOracle (I := Fin 150) (W := Unit) 0 *ᵥ
          solverStart (I := Fin 150) (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket ()) ≠
        (fun p : ((Fin 150) × Bool) × Unit =>
          bState 0 p.1.1 * Qatlib.Foundations.PureStateMath.Ket false p.1.2 * Qatlib.Foundations.PureStateMath.Ket () p.2) := by
  exact ⟨bOracle_not_unitary 0, normalized_ket false, normalized_ket (),
    bOracle_preparation_ne 0⟩

end Qatlib.Concepts.QlsReadoutSpec.Amplification
