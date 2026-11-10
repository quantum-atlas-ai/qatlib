/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogTwoDimSamplingLawStat
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogOriginalContracts
import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogFourierLaw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.PeriodSampling.DlogGoodProb

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

theorem dlogTwoDimSamplingLaw_false : ¬ DlogTwoDimSamplingLawLegacy := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have ho : orderOf (2 : ZMod 3) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  have hh := (h 3 4 (2 : ZMod 3) (1 : ZMod 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ho 0 (by simp)).2.2 (0 : Fin 4) (0 : Fin 4) 0 (by norm_num)
  unfold BornProb dlogTwoDimState at hh
  rw [show (3 : ℕ)-1 = 2 by decide] at hh
  simp only [Fin.sum_univ_two] at hh
  have hn : (2 : ZMod 3) ≠ 1 := by decide
  norm_num [offGridPhase, hn] at hh

theorem dlogTwoDimSamplingLaw : DlogTwoDimSamplingLaw := by
  intro p q _ g x _hprime hp _hx0 hpq ho r hx
  refine ⟨dlog_state_normalized p q g x (by omega) hpq, ?_, ?_⟩
  · intro c d y
    rfl
  · intro c d k _hk
    rw [BornProb, dlog_single_fiber_amplitude p q g x (by omega) hpq ho r k hx c d]

end Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
