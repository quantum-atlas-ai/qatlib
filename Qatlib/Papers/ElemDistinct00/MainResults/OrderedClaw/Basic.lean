/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Qatlib.Papers.ElemDistinct00.MainResults.Claw.OrReduction
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw

open Qatlib.Papers.ElemDistinct00.MainResults.Defs
open Qatlib.Papers.ElemDistinct00.MainResults.Claw
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

section Guarantees

variable {X Y Z W : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype W] [DecidableEq W] [Preorder X] [Preorder Y] [LinearOrder Z]

theorem orderedClawBoundedError_of_clawBoundedError (A : ClawAlgorithm X Y Z W)
    (h : ClawBoundedError A) : OrderedClawBoundedError A :=
  fun f g _ hclaw => h f g hclaw

theorem orderedClawExact_of_clawExact (A : ClawAlgorithm X Y Z W)
    (h : ClawExact A) : OrderedClawExact A :=
  ⟨fun f g _ hclaw => h.1 f g hclaw, fun f g _ hnone => h.2 f g hnone⟩

theorem bothOrderedClawBoundedError_of_orderedClawBoundedError
    (A : ClawAlgorithm X Y Z W) (h : OrderedClawBoundedError A) :
    BothOrderedClawBoundedError A :=
  fun f g hf _ hclaw => h f g hf hclaw

theorem bothOrderedClawExact_of_orderedClawExact (A : ClawAlgorithm X Y Z W)
    (h : OrderedClawExact A) : BothOrderedClawExact A :=
  ⟨fun f g hf _ hclaw => h.1 f g hf hclaw,
    fun f g hf _ hnone => h.2 f g hf hnone⟩

end Guarantees

theorem monotone_fin_one (f : Fin 1 → ℤ) : Monotone f :=
  fun x y _ => le_of_eq (congrArg f (Subsingleton.elim x y))

theorem orderedclaw_qe_lower_at_one {M : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : ClawAlgorithm (Fin 1) (Fin M) ℤ W) (hE : OrderedClawExact A) (hM : 0 < M) :
    (M : ℝ) ≤ (QueryCount A.circuit : ℝ) :=
  claw_qe_lower_at_one A
    ⟨fun f g hh => hE.1 f g (monotone_fin_one f) hh,
      fun f g hh => hE.2 f g (monotone_fin_one f) hh⟩ hM

theorem orderedclaw_q2_lower_at_one {M : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : ClawAlgorithm (Fin 1) (Fin M) ℤ W) (hB : OrderedClawBoundedError A)
    (hM6 : 6 ≤ M) :
    Real.sqrt (M : ℝ) / 8 ≤ (QueryCount A.circuit : ℝ) :=
  claw_q2_lower_at_one A (fun f g hh => hB f g (monotone_fin_one f) hh) hM6

end Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw
