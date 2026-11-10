/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality
set_option warningAsError false

open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

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
