/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Coherent Metropolis coin definitions

This module defines the input energy superposition and the energy-controlled acceptance coin for
Eqs. (2)-(3) of [TemmeEtAl2011]. The four registers hold a system label, the old energy label,
the proposed energy label, and a binary coin; the controlled operation preserves the first three
labels.

## Main statements

* `coherentEnergySuperposition` places amplitude `x k` at `(k, i, k, 0)`.
* `metropolisControlledCoin` applies the two-dimensional Metropolis coin with acceptance `min
  (1, exp (-β * (E k - E i)))` on each energy block.

## References

* [Temme et al., 2011][TemmeEtAl2011], *Quantum Metropolis Sampling*, Eqs. (2)-(3).
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Matrix

namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin

/-- The four-register amplitude function with amplitude `x k` at `(k, i, k, 0)` and zero
elsewhere. The proposal amplitudes need not be normalized in this definition. -/
noncomputable def coherentEnergySuperposition {D : ℕ} (i : Fin D) (x : Fin D → ℂ) :
    QState (Fin D × Fin D × Fin D × Fin 2) :=
  fun p => if p.2.2.2 = 0 ∧ p.2.1 = i ∧ p.1 = p.2.2.1 then x p.1 else 0

/-- The block-diagonal gate that preserves the system and energy labels and applies the
Metropolis coin controlled by the old and proposed energies. Its acceptance parameter is the
thermal acceptance of Eqs. (2)-(3) in [TemmeEtAl2011]. -/
noncomputable def metropolisControlledCoin {D : ℕ} (E : Fin D → ℝ) (β : ℝ) :
    Matrix (Fin D × Fin D × Fin D × Fin 2) (Fin D × Fin D × Fin D × Fin 2) ℂ :=
  Matrix.of fun rq rp =>
    if rq.1 = rp.1 ∧ rq.2.1 = rp.2.1 ∧ rq.2.2.1 = rp.2.2.1 then
      MetropolisCoin (thermalAcceptance E β rq.2.1 rq.2.2.1) rq.2.2.2 rp.2.2.2
    else 0
end Qatlib.Papers.QMetropolis11.AcceptanceCoin
