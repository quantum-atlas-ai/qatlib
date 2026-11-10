/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Lemma4

variable {α : Type*}

theorem InMA_mono (E : Encoding α) {L L' : PromiseProblem α}
    (hy : ∀ x, L'.yes x → L.yes x) (hn : ∀ x, L'.no x → L.no x) :
    InMA E L → InMA E L' := by
  rintro ⟨W, hW⟩
  refine ⟨W, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    exact (hW x).1 (hy x hx)
  · intro hx
    exact (hW x).2 (hn x hx)

theorem InAM_mono (E : Encoding α) {L L' : PromiseProblem α}
    (hy : ∀ x, L'.yes x → L.yes x) (hn : ∀ x, L'.no x → L.no x) :
    InAM E L → InAM E L' := by
  rintro ⟨A, hA⟩
  refine ⟨A, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    exact (hA x).1 (hy x hx)
  · intro hx
    exact (hA x).2 (hn x hx)

theorem InPostBPP_mono (E : Encoding α) {L L' : PromiseProblem α}
    (hy : ∀ x, L'.yes x → L.yes x) (hn : ∀ x, L'.no x → L.no x) :
    InPostBPP E L → InPostBPP E L' := by
  rintro ⟨M, hM⟩
  refine ⟨M, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    exact (hM x).1 (hy x hx)
  · intro hx
    exact (hM x).2 (hn x hx)

theorem InBPPpath_mono (E : Encoding α) {L L' : PromiseProblem α}
    (hy : ∀ x, L'.yes x → L.yes x) (hn : ∀ x, L'.no x → L.no x) :
    InBPPpath E L → InBPPpath E L' := by
  rintro ⟨P, hP⟩
  refine ⟨P, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    exact (hP x).1 (hy x hx)
  · intro hx
    exact (hP x).2 (hn x hx)

theorem InBPPNP_mono (E : Encoding α) {L L' : PromiseProblem α}
    (hy : ∀ x, L'.yes x → L.yes x) (hn : ∀ x, L'.no x → L.no x) :
    InBPPNP E L → InBPPNP E L' := by
  rintro ⟨B, hB, q, c, k, M, hM, hcond⟩
  refine ⟨B, hB, q, c, k, M, hM, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    exact (hcond x).1 (hy x hx)
  · intro hx
    exact (hcond x).2 (hn x hx)

end Qatlib.Papers.StoquasticHam06.MainResults.Lemma4
