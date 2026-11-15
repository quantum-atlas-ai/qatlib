/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.ZeroMarginCanonicalComplementStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial

def BoundaryRootDeflation : Prop :=
  ∀ (P Q : Polynomial ℂ) (d : ℕ), BoundaryCanonical P Q d → Q ≠ 0 →
    let Q₀ := boundaryComplementFactor Q
    let R := boundaryComplementNormalizedQuotient Q
    let ζ := boundaryComplementQuotientPhase Q
    Q₀.Monic ∧ Q₀ ∣ Q ∧ Q = C ζ*Q₀*R ∧ ‖ζ‖ = 1 ∧
    Q₀.natDegree+R.natDegree = Q.natDegree ∧
    0 < (R.eval 0).re ∧ (R.eval 0).im = 0 ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → R.eval z ≠ 0) ∧
    (∀ z : ℂ, ‖z‖ = 1 → Q₀.rootMultiplicity z = Q.rootMultiplicity z) ∧
    (∀ z : ℂ, ‖z‖ = 1 → (Q₀.eval z = 0 ↔ ‖P.eval z‖ = 1)) ∧
    (∀ z : ℂ, ‖z‖ = 1 →
      ‖P.eval z‖^2 + ‖Q₀.eval z‖^2*boundaryComplementProfile Q z = 1) ∧
    (∀ z : ℂ, ‖z‖ = 1 → Q₀.eval z ≠ 0 →
      boundaryComplementProfile Q z = (1-‖P.eval z‖^2)/‖Q₀.eval z‖^2) ∧
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ z : ℂ, ‖z‖ = 1 → a ≤ boundaryComplementProfile Q z ∧ boundaryComplementProfile Q z ≤ b

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
