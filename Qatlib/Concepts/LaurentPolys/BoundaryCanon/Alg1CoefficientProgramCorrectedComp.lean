/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Alg1CoefficientProgramCorrectedStat
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Algorithm1CoefficientProgramStat
public import Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT
public import Qatlib.Concepts.LaurentPolys.ProfileFftBound.CanonicalComplementFFTConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.ProfileFftBound Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial

/-- Under the corrected grid threshold, Algorithm 1 has the stated operation counts, Fourier
coefficient formula, and coefficient accuracy for the normalized complementary factor. -/
theorem algorithm1CoefficientProgramCorrected :
    Algorithm1CoefficientProgramCorrected := by
  intro P Q d m δ ε hd hPd hQd hδ hδ1 hε hε1 hP hQr hQi hQn hQc
  (try dsimp only)
  intro hm hgrid hthreshold
  have hcost := canonicalComplementFourierRun_cost P d m
  have hacc := canonical_complement_discrete_fourier_accuracy P Q d m δ ε
    hd hPd hQd hδ hδ1 hε hε1 hP hQr hQi hQn hQc hm hgrid hthreshold
  refine ⟨hcost.1, hcost.2.1, hcost.2.2.1, hcost.2.2.2, ?_⟩
  intro n
  refine ⟨canonicalComplementFourierRun_coefficients P d m n, ?_⟩
  intro hn
  rw [canonicalComplementFourierRun_coefficients P d m n]
  exact hacc n.val hn

/-- The corrected Algorithm 1 coefficient contract implies `Algorithm1CoefficientProgram`. -/
theorem algorithm1CoefficientProgramCorrected_implies_legacy :
    Algorithm1CoefficientProgramCorrected → Algorithm1CoefficientProgram := by
  intro hcorrect P Q d m δ ε hd hPd hQd hδ hδ1 hε hε1 hP hQr hQi hQn hQc
  (try dsimp only)
  intro hm hgrid hthreshold
  obtain ⟨hmul, hadd, hlog, hexp, hcoeff⟩ :=
    hcorrect P Q d m δ ε hd hPd hQd hδ hδ1 hε hε1
      hP hQr hQi hQn hQc hm hgrid hthreshold
  exact ⟨hmul, hadd, hlog, hexp, fun n h => (hcoeff n).2 h.2⟩

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
