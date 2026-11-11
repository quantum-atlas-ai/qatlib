/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation

/-!
# Polynomial rotation and readout parameters

This module defines the exact arcsine target, its truncated odd polynomial, and the associated
tail constant. It also defines `riskPolyMeanLaw` and the combined amplitude, decoding, and
polynomial-bias window `riskPolyReadoutWindow`.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `riskSinTaylor`: The truncated odd payoff-angle polynomial with terms of degrees `2 * j + 1`
  for `j ≤ u`.
* `riskPolyReadoutWindow`: The readout error window combining amplitude and decoding errors
  divided by `c` with the polynomial bias `riskArcsinTail u * c ^ (2 * u + 2) / 2`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyReadout

/-- The scaled arcsine angle whose shifted squared sine targets the affine payoff `c * (y - 1 /
2) + 1 / 2`. -/
def riskArcsineTarget (c y : ℝ) : ℝ :=
  (Real.arcsin (Real.sqrt (c*(y-1/2)+1/2)) - Real.pi/4)/c

/-- The `j`th arcsine series coefficient, equal to `choose (2 * j) j / (4 ^ j * (2 * j + 1))`. -/
def riskArcsinCoeff (j : ℕ) : ℝ :=
  ((2*j).choose j : ℕ)/((4 : ℝ)^j*(2*j+1))

/-- The truncated odd payoff-angle polynomial with terms of degrees `2 * j + 1` for `j ≤ u`. -/
def riskSinTaylor (u : ℕ) (c y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (u+1), ((2*j).choose j : ℕ)/((2*j+1 : ℝ))*c^(2*j)*(y-1/2)^(2*j+1)

/-- The arcsine endpoint remainder after subtracting the first `u + 1` coefficients from `π /
2`. -/
def riskArcsinTail (u : ℕ) : ℝ :=
  Real.pi/2 - ∑ j ∈ Finset.range (u+1), riskArcsinCoeff j

/-- The amplitude-estimation law for the squared sine of the shifted polynomial payoff angle. -/
def riskPolyMeanLaw {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (A : Matrix I I ℂ)
    (j : I) (f : I → ℝ) (u : ℕ) (c : ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) :
    FinDist (Fin M) :=
  meanLaw M A j (fun i => Real.sin (c*riskSinTaylor u c (f i)+Real.pi/4)^2) hA
    (fun _ => ⟨sq_nonneg _, Real.sin_sq_le_one _⟩) hM

/-- The readout error window combining amplitude and decoding errors divided by `c` with the
polynomial bias `riskArcsinTail u * c ^ (2 * u + 2) / 2`. -/
def riskPolyReadoutWindow (u : ℕ) (c : ℝ) (M bits : ℕ) : ℝ :=
  (Real.pi/M + Real.pi^2/(M : ℝ)^2 + (1/2 : ℝ)^bits)/c + riskArcsinTail u*c^(2*u+2)/2

end Qatlib.Concepts.RiskEstimation.PolyReadout
