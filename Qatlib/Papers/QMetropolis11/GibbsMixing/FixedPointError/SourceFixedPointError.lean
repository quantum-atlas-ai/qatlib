/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.Contraction.ContractionFixedPointErrorQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Fixed-point error bound (Temme et al. 2011, Sec. 4.3, Eq. (44))

Fixed source: arXiv:0911.3635v2, Section 4.3, printed page 16.

Error bound: the deviation between the exact fixed point `σ*` of `E` and the
Gibbs state `ρ_G = exp(-βH)/Z` obeys

`‖σ* - ρ_G‖₁ ≤ ε_sg / (1 - η₁)`,                                  (44)

where `η₁ < 1` is the ergodicity coefficient (Eq. (43) trace-norm
contraction) and `‖E[ρ_G] - ρ_G‖₁ ≤ ε_sg` is the single-application error.

Reused FQN:
`QuantumAlgorithm.Concepts.MixedInstrument.Contraction.contractionFixedPointError`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.FixedPointError

open Matrix
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedInstrument.Contraction

variable {D : ℕ}

/-- **c009, Eq. (44).**  Under trace-norm contraction with coefficient
`η₁ < 1`, a density fixed point `σ*`, and a single-step Gibbs error
`‖E[ρ_G] - ρ_G‖₁ ≤ ε`, the fixed-point error is at most `ε/(1-η₁)`.  Reused
FQN: `...Contraction.contractionFixedPointError`. -/
theorem source_fixedPointError (T : QuantumChannel D D) (σs ρG : Operator D)
    (hσ : IsDensityOperator σs) (hρ : IsDensityOperator ρG) (hfix : T.map σs = σs)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hcontr : ∀ X Y : Operator D, IsDensityOperator X → IsDensityOperator Y →
      SchattenOne (T.map X - T.map Y) ≤ η * SchattenOne (X - Y))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : SchattenOne (T.map ρG - ρG) ≤ ε) :
    SchattenOne (σs - ρG) ≤ ε / (1 - η) :=
  contractionFixedPointError D T σs ρG hσ hρ hfix η hη0 hη1 hcontr ε hε0 hε

/-- **c009, full contract.**  The frozen Eq. (44) statement in one line.
Reused FQN: `...Contraction.contractionFixedPointError`. -/
theorem source_contractionFixedPointError : ContractionFixedPointError :=
  contractionFixedPointError

end Qatlib.Papers.QMetropolis11.GibbsMixing.FixedPointError
