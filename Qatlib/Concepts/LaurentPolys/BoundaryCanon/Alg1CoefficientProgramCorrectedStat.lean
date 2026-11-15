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
open Qatlib.Concepts.LaurentPolys.ProfileFftBound Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def Algorithm1CoefficientProgramCorrected : Prop :=
  ∀ (P Q : Polynomial ℂ) (d m : ℕ) (δ ε : ℝ),
    0 < d → P.natDegree ≤ d → Q.natDegree ≤ d →
    0 < δ → δ < 1 → 0 < ε → ε < 1 →
    (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1 - δ) →
    0 < (Q.eval 0).re → (Q.eval 0).im = 0 →
    (∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) →
    (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2 + ‖Q.eval z‖^2 = 1) →
    let N := 2^m
    let ρ := (1/(1-δ))^(1/(d : ℝ) : ℝ)
    let r := min (2 : ℝ) ρ
    1 ≤ m → d+1 ≤ N →
    (Nat.ceil (2/Real.log r * Real.log (max (2 : ℝ) (8*Real.log (1/δ)/(r-1)/ε))) : ℕ) ≤ N →
    let run := canonicalComplementFourierRun P d m
    let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ) * Complex.I)
    let a := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
      ((Real.log (1 - ‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ) * ω^(-(n*j.val : ℤ))
    run.multiplications = 4*(m*2^m/2) + 2*2^m + 1 ∧
    run.additions = 4*m*2^m ∧
    run.logarithms = 2^m ∧
    run.exponentials = 2^m ∧
    (∀ n : Fin N, run.coefficients n =
      (N : ℂ)⁻¹ * ∑ j : Fin N,
        Complex.exp ((2 : ℂ)⁻¹ * a 0 +
          ∑ l ∈ Finset.range (N/2+1), if l = 0 then 0 else a l * ω^(l*j.val)) *
          ω^(-(n.val*j.val : ℤ)) ∧
      (n.val ≤ d → ‖Q.coeff n.val - run.coefficients n‖ < ε))

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
