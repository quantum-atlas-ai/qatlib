/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiscreteSim08.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.DiscreteSim08.MainResults

theorem sourceContinuousCoherentQL1_le_of_witness_time {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) {T ε : ℝ}
    {r : ℕ} (hr : 0 < r) (C : List (SourceContinuousStep (SourceSpace n q H r)))
    (hlegal : sourceContinuousLegal C) (hL1 : SourceDriverL1 C)
    (htime : sourceContinuousTime C ≤ T)
    (hfid : ∀ x, Real.sqrt (1 - ε) ≤
      (∑ p, star ((sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re) :
    sourceContinuousCoherentQL1 input ρ σ ε ≤ ENNReal.ofReal T := by
  unfold sourceContinuousCoherentQL1
  refine le_trans (sInf_le ?_) (ENNReal.ofReal_le_ofReal htime)
  exact ⟨r, hr, C, rfl, hlegal, hL1, hfid⟩

theorem sourceContinuousCoherentQ_le_coherentQL1' {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceContinuousCoherentQ input ρ σ ε ≤
      sourceContinuousCoherentQL1 input ρ σ ε :=
  sourceContinuousCoherentQ_le_coherentQL1 input ρ σ ε

end Qatlib.Papers.DiscreteSim08.MainResults
