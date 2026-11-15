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

def sourceCoeffAt (P : Polynomial ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then P.coeff n.toNat else 0

def sourceAutocorrDefect (P Q : Polynomial ℂ) (d : ℕ) (n : ℤ) : ℂ :=
  (Finset.sum (Finset.range (d+1)) (fun m : ℕ =>
    sourceCoeffAt P (n + (m : ℤ)) * star (sourceCoeffAt P (m : ℤ)) +
    sourceCoeffAt Q (n + (m : ℤ)) * star (sourceCoeffAt Q (m : ℤ)))) -
    (if n = 0 then (1 : ℂ) else 0)

def sourcePhiTilde (P Q : Polynomial ℂ) (d : ℕ) : ℝ :=
  Real.sqrt (Finset.sum (Finset.Icc (-(d : ℤ)) (d : ℤ))
    (fun n : ℤ => ‖sourceAutocorrDefect P Q d n‖^2))

def sourcePhiUniform (P Q : Polynomial ℂ) : ℝ :=
  sSup (circleResidual P Q '' {z : ℂ | ‖z‖ = 1})

def MetricLossEquivalence : Prop :=
  ∀ (P Q : Polynomial ℂ) (d : ℕ), P.natDegree ≤ d → Q.natDegree ≤ d →
    (1 / Real.sqrt ((2 : ℝ) * d + 1)) * sourcePhiUniform P Q ≤ sourcePhiTilde P Q d ∧
    sourcePhiTilde P Q d ≤ Real.sqrt ((2 : ℝ) * d + 1) * sourcePhiUniform P Q

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
