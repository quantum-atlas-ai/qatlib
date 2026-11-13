/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximationEntire
import Qatlib.Papers.Cbmd26.Algorithms.ApproximateQSVTBridge

/-!
# QSVT from bounded holomorphic approximation

`sharp_holomorphic_qsvt_exists` combines a bounded polynomial approximation with the normalized
QSVT bridge. For a function holomorphic on the radius-two closed disk, bounded by `M` on its
circle, and real and bounded by `1` on `[0, 1]`, it supplies four phase lists implementing its
Hermitian functional calculus on spectra in `[g, 1]`, with normalization `4`, error `ε`, and
explicit degree and query bounds.

This uniform construction supports the CBMD algorithms associated with [WangEtAl2026].

## Main statements

* `sharp_holomorphic_qsvt_exists` constructs uniform phases with explicit degree, query,
  normalization, and error bounds.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Matrix Polynomial Metric Set
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- For positive `g` and `ε`, a function complex differentiable on the radius-two closed disk,
bounded by `M ≥ 1` on its circle, and real with norm at most `1` on `[0, 1]` has a
polynomial and four uniform QSVT phase lists with the stated degree and query bounds. For
every projected unitary encoding of a Hermitian matrix with spectrum in `[g, 1]`, their LCU
block-encodes the functional calculus of `f` with normalization `4` and error `ε`. -/
theorem sharp_holomorphic_qsvt_exists
    (f : ℂ → ℂ) (g M ε : ℝ) (hg : 0 < g) (hM : 1 ≤ M) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 2))
    (hb : ∀ z ∈ sphere (0 : ℂ) 2, ‖f z‖ ≤ M)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, ‖f (x : ℂ)‖ ≤ 1)
    (hreal : ∀ x ∈ Icc (0 : ℝ) 1, ((f (x : ℂ)).re : ℂ) = f (x : ℂ)) :
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      P.natDegree ≤ dyadicOrder ((ε / 2) / (4 * M)) * (1 + 4 * ⌈512 / g⌉₊) ∧
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧
        (zs j).length = ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
        (hA : A.IsHermitian),
      ProjectedUnitaryEncoding A U F F →
      (∀ i, orderedHermitianValues hA i ∈ Icc g 1) →
      (∀ j, adjointQueryCount (hermitianResponseWord F
          (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j)
          (base j) (zs j)) ≤
        2 * (dyadicOrder ((ε / 2) / (4 * M)) * (1 + 4 * ⌈512 / g⌉₊)) + 1) ∧
      BlockEncoding (hermitianFunction A hA (fun x => f (x : ℂ)))
        (coefficientLCUUnitary fourBranchCoefficients
          (fun j => evaluate (parallelOracle U) (hermitianResponseWord F
            (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j)
            (base j) (zs j))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 ε := by
  obtain ⟨P, hd, hp, he⟩ := bounded_real_holomorphic_complex_polynomial_exists
    f g M (ε / 2) hg hM (by positivity) hf hb hpos hreal
  obtain ⟨base, zs, hphase, hactual⟩ := normalized_approximation_qsvt_uniform_phases
    P (fun x => f (x : ℂ)) (Icc g 1) (ε / 2) (by positivity) hp
    (fun x hx => hpos x ⟨hg.le.trans hx.1, hx.2⟩) he
  refine ⟨P, base, zs, hd, hphase, ?_⟩
  intro H I _ _ _ _ A U F hA hAU hs
  obtain ⟨hc, hblock⟩ := hactual H I A U F hA hAU hs
  refine ⟨fun j => (hc j).trans (by omega), ?_⟩
  convert hblock using 1
  ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
