/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Algorithm2TotalCostEndpointStat
public import Qatlib.Concepts.LaurentPolys.ProfileFftBound.CanonicalComplementFFTConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.ProfileFftBound Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial

/-- For a polynomial bounded by one on the unit circle, Algorithm 2 constructs a degree bounded
approximate complement with the stated residual, unitarity defect, grid size, and total
operation bounds. -/
theorem algorithm2TotalCostEndpoint : Algorithm2TotalCostEndpoint := by
  intro P₀ d ε hd hP₀d hε hε1 hP₀b
  obtain ⟨m, Q, hm1, hm2, hgrid, hQ, hdeg, hres, hcomp, hmul, hadd, hlog, hexp⟩ :=
    canonical_complement_algorithm_two_total_cost P₀ d ε hd hP₀d hε hε1 hP₀b
  refine ⟨m, Q, hm1, hm2, ?_, hQ, hdeg, hres, hcomp, hmul, hadd, hlog, hexp⟩
  rw [Nat.cast_pow]
  exact hgrid

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
