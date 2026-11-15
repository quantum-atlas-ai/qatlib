/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.BoundaryCanonicalComplement
public import Qatlib.Concepts.LaurentPolys.ProfileFftBound.CanonicalComplementFFTConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def Theorem4CorrectedComplementarity : Prop :=
  ∀ (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ),
    0 < d → P₀.natDegree ≤ d → 0 < ε → ε < 1 →
    (∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ ≤ 1) →
    let P := (1 - ε/4 : ℂ) • P₀
    let N := 2^m
    let δ := ε/4
    let η := ε/(16*(d+1))
    let ρ := (1/(1-δ))^(1/(d : ℝ) : ℝ)
    1 ≤ m → d+1 ≤ N →
    (Nat.ceil (2/Real.log ρ * Real.log (8*Real.log (1/δ)/(ρ-1)/η)) : ℕ) ≤ N →
    let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ) * Complex.I)
    let a := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
      ((Real.log (1 - ‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ) * ω^(-(n*j.val : ℤ))
    let q := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
      Complex.exp ((2 : ℂ)⁻¹ * a 0 +
        ∑ l ∈ Finset.range (N/2+1), if l = 0 then 0 else a l * ω^(l*j.val)) *
        ω^(-(n*j.val : ℤ))
    let Q := ∑ n ∈ Finset.range (d+1), Polynomial.monomial n (q n)
    Q.natDegree ≤ d ∧ (∀ z : ℂ, ‖z‖ = 1 → circleResidual P₀ Q z < ε)

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
