/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ExactSimon97.MainResults

theorem exists_linIndep_generates {n : ℕ} (V : Submodule (ZMod 2) (BoolVec n)) :
    ∃ (k : ℕ) (v : Fin k → BoolVec n), LinIndep v ∧ Generates v V := by
  classical
  let b := Module.finBasis (ZMod 2) V
  refine ⟨Module.finrank (ZMod 2) V, fun i => ((b i : V) : BoolVec n), ?_, ?_⟩
  · exact b.linearIndependent.map' (Submodule.subtype V) (Submodule.ker_subtype V)
  · show Submodule.span (ZMod 2) (Set.range (fun i => ((b i : V) : BoolVec n))) = V
    rw [show (fun i => ((b i : V) : BoolVec n)) = (Submodule.subtype V) ∘ b from rfl]
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

theorem proposition1_span_generating_basis {n : ℕ} (X : Finset (BoolVec n)) :
    ∃ (k : ℕ) (v : Fin k → BoolVec n), LinIndep v ∧ Generates v (spanFinset X) :=
  exists_linIndep_generates (spanFinset X)

theorem proposition2_ortho_generating_basis {n k : ℕ} (X : Fin k → BoolVec n)
    (_hX : LinIndep X) :
    ∃ (l : ℕ) (v : Fin l → BoolVec n), LinIndep v ∧
      Generates v (ortho (Submodule.span (ZMod 2) (Set.range X))) :=
  exists_linIndep_generates (ortho (Submodule.span (ZMod 2) (Set.range X)))

end Qatlib.Papers.ExactSimon97.MainResults
