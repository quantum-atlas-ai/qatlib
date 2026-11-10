/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.RegularEncoding
import Qatlib.Papers.CollisionProb97.MainResults.CollisionExecution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.EncodedCollision
variable {X Y : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
local instance : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩

def run (F : X → Y) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    CostedLaw (Option (X × X)) :=
  CollisionExecution.run (Encoding.encoded F) r hr (Encoding.encoded_regular F r hF) K hK l hl hl4

theorem run_correct (F : X → Y) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (out : Option (X × X)) (c : ℕ) (hm : run F r hr hF K hK l hl hl4 (out,c) ≠ 0) :
    ∃ s t, out = some (s,t) ∧ s ≠ t ∧ F s = F t := by
  obtain ⟨s,t,ho,hne,he⟩ := CollisionExecution.run_correct (Encoding.encoded F) r hr
    (Encoding.encoded_regular F r hF) K hK l hl hl4 out c hm
  exact ⟨s,t,ho,hne,(Encoding.codomainEquiv Y).injective he⟩

theorem run_expected (F : X → Y) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectedCost (run F r hr hF K hK l hl hl4) ≤ (K.card:ℝ≥0∞)+
      ENNReal.ofReal ((1+4*SourcePhaseConstant l)*
        Real.sqrt ((Fintype.card X:ℝ)/(((r-1)*K.card:ℕ):ℝ))) :=
  CollisionExecution.run_expected (Encoding.encoded F) r hr (Encoding.encoded_regular F r hF) K hK l hl hl4

end Qatlib.Papers.CollisionProb97.MainResults.EncodedCollision
