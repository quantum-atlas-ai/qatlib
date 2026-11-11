/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality

/-!
# Real QSP polynomial completion

`corollary10RealQSP` proves that a real polynomial of positive degree, matching parity, and
magnitude at most one on `[-1, 1]` is the real part of a complex polynomial of the same degree
satisfying the complex QSP inequalities.

The result establishes the packaged `Corollary10RealQSP` formulation associated with Corollary
10 of [GilyenSuLowWiebe2019].

## Main statements

* `corollary10RealQSP`: constructs the complex polynomial with the prescribed real part and QSP
  inequalities.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-- Establishes `Corollary10RealQSP`: every bounded real polynomial of positive degree and
matching parity has a complex completion of the same degree and parity satisfying the real-
and imaginary-axis QSP conditions, with the prescribed real part [Gilyén et al., Corollary
10][GilyenSuLowWiebe2019]. -/
theorem corollary10RealQSP : Corollary10RealQSP := by
  intro Pt d _hd hdeg hpar hb
  obtain ⟨P, Q, hpair, hre, _⟩ := exists_completedPair_of_bounded
    (degree_le_of_natDegree_le hdeg.le) hpar hb
  have hl := natDegree_add_le P (conjugatePolynomial P)
  rw [hre, natDegree_C_mul (by norm_num : (2 : ℂ) ≠ 0),
    natDegree_map Complex.ofRealHom, hdeg] at hl
  have hc : (conjugatePolynomial P).natDegree ≤ P.natDegree := natDegree_map_le
  have hexact : P.natDegree = d := le_antisymm
    (natDegree_le_of_degree_le hpair.degreeP) (hl.trans (max_le le_rfl hc))
  exact ⟨P, hexact, hpair.parityP, fun _ hx => hpair.normSq_eval_le_one hx,
    fun _ hx => hpair.one_le_normSq_eval hx,
    fun he y => hpair.one_le_normSq_eval_imag he y, hre⟩

end Qatlib.Concepts.QsvtCore.PhaseExistence
