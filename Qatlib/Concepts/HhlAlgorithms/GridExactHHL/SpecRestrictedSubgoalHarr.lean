/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.SpecRestrictedSubgoalStat

/-!
# Exact phase readout and spectral inversion

This module proves `SpecRestrictedSubgoal` for a linear-system problem whose unitary eigenphases
lie exactly on the Fourier grid. It combines exact phase-estimation readout with an
inverse-eigenvalue solution expansion and a positive norm bound, following the spectral strategy
of [HarrowHassidimLloyd2009].

## Main statements

* `specRestrictedSubgoal`: exact grid readout and existence of the spectral linear-system
  solution.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL.LinearSystemProblem

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib
open Matrix

/-- Under the exact grid eigenphase hypotheses, phase estimation reads each eigenvector label
with probability one, and the inverse-eigenvalue expansion solves the system with positive
squared coefficient norm at least `1 / κ²`. -/
theorem specRestrictedSubgoal : SpecRestrictedSubgoal := by
  intro I _ _ p M hM U _hU g hUeig _hlink β hβ
  constructor
  · intro i
    exact qpe_exact_readout hM (p.eigvec_norm i) (g i) (hUeig i)
  · exact ⟨∑ i, (β i / ((p.eigval i : ℂ))) • p.eigvec i,
      ∑ i, ‖β i / ((p.eigval i : ℂ))‖ ^ 2,
      p.accept_mass_pos hβ, p.inverse_action hβ, p.accept_mass_lower_bound hβ, rfl, rfl⟩

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
