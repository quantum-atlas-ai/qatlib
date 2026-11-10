/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.SpecRestrictedSubgoalStat
set_option warningAsError false

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL.LinearSystemProblem

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib
open Matrix

theorem specRestrictedSubgoal : SpecRestrictedSubgoal := by
  intro I _ _ p M hM U _hU g hUeig _hlink β hβ
  constructor
  · intro i
    exact qpe_exact_readout hM (p.eigvec_norm i) (g i) (hUeig i)
  · exact ⟨∑ i, (β i / ((p.eigval i : ℂ))) • p.eigvec i,
      ∑ i, ‖β i / ((p.eigval i : ℂ))‖ ^ 2,
      p.accept_mass_pos hβ, p.inverse_action hβ, p.accept_mass_lower_bound hβ, rfl, rfl⟩

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
