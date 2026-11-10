/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Matrix

namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin

noncomputable def coherentEnergySuperposition {D : ℕ} (i : Fin D) (x : Fin D → ℂ) :
    QState (Fin D × Fin D × Fin D × Fin 2) :=
  fun p => if p.2.2.2 = 0 ∧ p.2.1 = i ∧ p.1 = p.2.2.1 then x p.1 else 0

noncomputable def metropolisControlledCoin {D : ℕ} (E : Fin D → ℝ) (β : ℝ) :
    Matrix (Fin D × Fin D × Fin D × Fin 2) (Fin D × Fin D × Fin D × Fin 2) ℂ :=
  Matrix.of fun rq rp =>
    if rq.1 = rp.1 ∧ rq.2.1 = rp.2.1 ∧ rq.2.2.1 = rp.2.2.1 then
      MetropolisCoin (thermalAcceptance E β rq.2.1 rq.2.2.1) rq.2.2.2 rp.2.2.2
    else 0
end Qatlib.Papers.QMetropolis11.AcceptanceCoin
