/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.EffectiveSpectralGapContracts
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped BigOperators

theorem effectiveSpectralGap_contract_false : ¬ EffectiveSpectralGap := by
  classical
  intro h
  let V : Matrix (Empty ⊕ (Unit ⊕ Empty)) (Fin 1) ℂ := fun _ _ => 1
  have hVi : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V := by
    unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
    ext i j
    fin_cases i
    fin_cases j
    simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hVc : V*Vᴴ = 1 := by
    ext p q
    rcases p with p | p
    · exact p.elim
    rcases p with p | p
    · rcases q with q | q
      · exact q.elim
      rcases q with q | q
      · cases p
        cases q
        simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply]
      · exact q.elim
    · exact p.elim
  have hAdj : effectiveGapAdjacency (0 : Matrix Empty Empty ℂ) (0 : QState Empty) = 0 := by
    ext p q
    rcases p with p | p
    · exact p.elim
    rcases p with p | p
    · rcases q with q | q
      · exact q.elim
      rcases q with q | q
      · rfl
      · exact q.elim
    · exact p.elim
  have heig : effectiveGapAdjacency (0 : Matrix Empty Empty ℂ) (0 : QState Empty)*V =
      V*Matrix.diagonal (fun _ : Fin 1 => ((0 : ℝ) : ℂ)) := by simp [hAdj]
  have hb := h Empty Empty (0 : Matrix Empty Empty ℂ) (0 : QState Empty) (0 : QState Empty)
    1 (by norm_num) (by simp) (by simp [Qatlib.Foundations.PureStateMath.Inner]) 0 (by norm_num) 1 V (fun _ => 0) hVi hVc heig
  norm_num [V] at hb

end Qatlib.Concepts.QueryComplexity.Reflections
