/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodeCert.DistCert.Tanner
public import QatlibTests.BinaryRank

@[expose] public section

/-! # Finite consumers of the Tanner girth certificate -/

namespace QatlibTests.TannerGirth

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodeCert.DistCert
open QatlibTests.BinaryRank

/-- A closed walk following the six nonzero incidences of the repetition checks. -/
def hexagon : (tanner repetitionChecks).Walk (.inl 0) (.inl 0) := by
  refine .cons (v := .inr 1) ?_ (.cons (v := .inl 1) ?_
    (.cons (v := .inr 2) ?_ (.cons (v := .inl 2) ?_
      (.cons (v := .inr 0) ?_ (.cons (v := .inl 0) ?_ .nil)))))
  all_goals
    simp only [tanner]
    decide +kernel

/-- The six-edge walk has distinct edges and distinct intermediate vertices. -/
theorem hexagon_cycle : hexagon.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    decide +kernel
  · simp [hexagon]
  · decide +kernel

/-- The same matrix used in the rank regression has Tanner girth six. -/
theorem repetitionGirth : (tanner repetitionChecks).egirth = 6 :=
  girth_six repetitionChecks ((checkRect_iff repetitionChecks).mp (by decide +kernel))
    hexagon_cycle rfl

/-- A full two-by-two incidence rectangle is rejected. -/
theorem rejectRectangle : checkRect (fun (_ _ : Fin 2) => (1 : ZMod 2)) = false := by
  decide +kernel

end QatlibTests.TannerGirth
