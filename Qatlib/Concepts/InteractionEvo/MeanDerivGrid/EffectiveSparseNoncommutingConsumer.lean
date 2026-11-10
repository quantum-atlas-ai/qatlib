/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix
open scoped Matrix.Norms.L2Operator

theorem effectiveConsumer_noncommuting :
    let H : ℝ → Matrix (Reg 1) (Reg 1) ℂ := fun u =>
      (1/4 : ℂ) • (effectivePauliZ + (u : ℂ) • effectivePauliX)
    H 0 * H (1/2) ≠ H (1/2) * H 0 := by
  (try dsimp only)
  intro h
  let x : Reg 1 := fun _ => false
  let y : Reg 1 := fun _ => true
  have hx : effectivePauliX x y = 1 := by
    unfold effectivePauliX
    simp only [finiteCodeMatrix, show (0 : ℕ)<1 by decide, dite_true]
    rw [wireGate_apply, if_pos]
    · rfl
    · intro k hk
      exact (hk (Subsingleton.elim k _)).elim
  have he := congrArg (fun M : Matrix (Reg 1) (Reg 1) ℂ => M x y) h
  norm_num [Matrix.mul_add,Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.smul_apply,effectivePauliZ,Matrix.diagonal_mul,Matrix.mul_diagonal,x,y,hx] at he

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
