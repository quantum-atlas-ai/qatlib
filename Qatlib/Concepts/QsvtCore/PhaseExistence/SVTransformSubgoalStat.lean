/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.SingularValueTransformation
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

/-!
# Specification of a cubic singular value transformation

`SVTransformSubgoal` states an explicit four-phase QSVT calculation for a projected unitary
encoding. The proposition records unitarity, compression to a polynomial in `A` and `A * Aᴴ`,
and evaluation of that polynomial along a normalized singular-vector pair. See
[GilyenSuLowWiebe2019].

## Main statements

* `SVTransformSubgoal`: the four-phase word and singular-vector specification.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Concepts.SignalPrimitive.LCUConsumers

open Matrix

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

/-- The assertion that a four-phase QSVT word for a projected unitary encoding is unitary, has
the displayed cubic compression, and acts on normalized singular-vector pairs by the
displayed scalar polynomial. -/
def SVTransformSubgoal : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ),
    IsProjectedEncoding U j₀ A 1 →
    ∀ c₀ c₁ c₂ c₃ : ℂ,
      c₀ * (starRingEnd ℂ) c₀ = 1 → c₁ * (starRingEnd ℂ) c₁ = 1 →
      c₂ * (starRingEnd ℂ) c₂ = 1 → c₃ * (starRingEnd ℂ) c₃ = 1 →
      QSVTWord U j₀ c₀ c₁ c₂ c₃ ∈ Matrix.unitaryGroup (J × I) ℂ ∧
      FiberProjector j₀ * (QSVTWord U j₀ c₀ c₁ c₂ c₃ * FiberProjector j₀)
        = FiberEmbed j₀ ((c₀ * c₂ * c₃) • A
            + (c₀ * (c₁ - 1) * c₃) • ((1 + (c₂ - 1) • (A * Aᴴ)) * A)) ∧
      ∀ (v w : QState I) (σ : ℝ),
        Normalized v → Normalized w →
        A *ᵥ v = ((σ : ℝ) : ℂ) • w → Aᴴ *ᵥ w = ((σ : ℝ) : ℂ) • v →
        ((c₀ * c₂ * c₃) • A
            + (c₀ * (c₁ - 1) * c₃) • ((1 + (c₂ - 1) • (A * Aᴴ)) * A)) *ᵥ v
          = ((c₀ * c₂ * c₃ * ((σ : ℝ) : ℂ)
              + c₀ * (c₁ - 1) * c₃ * ((1 : ℂ) + (c₂ - 1) * ((σ : ℝ) : ℂ) ^ 2)
                * ((σ : ℝ) : ℂ))) • w

end Qatlib.Concepts.QsvtCore.PhaseExistence
