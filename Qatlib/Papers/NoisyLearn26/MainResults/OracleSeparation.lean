/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.OracleSeparation

open Qatlib.Papers.NoisyLearn26.MainResults

theorem nbqp_subset_bqp (O : Oracle) (yes no : Prop) : NBQP O yes no → BQP O yes no := by
  rintro ⟨A, ⟨_hpos, _hlt, hpoly⟩, hsolve⟩
  exact ⟨A, hpoly, hsolve⟩

theorem nisq_subset_nbqp (O : Oracle) (yes no : Prop) : NISQ O yes no → NBQP O yes no := by
  rintro ⟨A, ⟨hpos, hlt, hpoly, _hplog⟩, hsolve⟩
  exact ⟨A, ⟨hpos, hlt, hpoly⟩, hsolve⟩

theorem nbqp_bqp_separation_of_hard_promise (O : Oracle) {yes no : Prop}
    (h : BQP O yes no ∧ ¬ NBQP O yes no) : ClassStrict (NBQP O) (BQP O) :=
  ⟨fun y n hc => nbqp_subset_bqp O y n hc, ⟨yes, no, h.1, h.2⟩⟩

end Qatlib.Papers.NoisyLearn26.MainResults.OracleSeparation
