/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrumentSubgoalStat
import Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrumentSubgoalQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Coherent accept/reject coin (Temme et al. 2011, Eqs. (2)-(3))

Fixed source: arXiv:0911.3635v2, Section 3 Step 2, printed pages 5-6.  The
paper defines the energy-conditioned one-qubit unitary

`W(E_k, E_i) = [[√(1-f_ik), √f_ik], [√f_ik, -√(1-f_ik)]]`,   (2)
`f_ik = min(1, exp(-β(E_k - E_i)))`,                            (3)

and shows that `C`, the (ideal) phase-estimation step and `W` prepare
`Σ_k x_k √f_ik |ψ_k⟩|E_i⟩|E_k⟩|1⟩ + Σ_k x_k √(1-f_ik) |ψ_k⟩|E_i⟩|E_k⟩|0⟩`.
The established paper-layer statement `CoherentInstrumentSubgoal` and its three
clause theorems already formalise exactly this under ideal phase estimation;
this file only re-exports them through the paper's notation and records that
the block `MetropolisCoin (thermalAcceptance E β i k)` is literally the matrix
printed in (2)-(3).

Reused FQNs (namespace `Qatlib.Papers.QMetropolis11.AcceptanceCoin`):

* `coherentInstrumentSubgoal` (all three clauses);
* `metropolisControlledCoin_unitary`;
* `metropolisControlledCoin_coherent_state`;
* `metropolisControlledCoin_accept_mass`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrument

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Papers.QMetropolis11.AcceptanceCoin

variable {D : ℕ}

/-- **c004, Eq. (2) matrix form.**  The defined block `MetropolisCoin f` is
literally the paper's `W(E_k,E_i)` reflection: its entries are `√(1-f)`, `√f`,
`√f`, `-√(1-f)` in the computational coin basis. -/
theorem source_W_block_entries (f : ℝ) :
    MetropolisCoin f = !![((Real.sqrt (1 - f) : ℝ) : ℂ), ((Real.sqrt f : ℝ) : ℂ);
      ((Real.sqrt f : ℝ) : ℂ), (-(Real.sqrt (1 - f)) : ℂ)] := rfl

/-- **c004, Eq. (3).**  The paper's acceptance probability
`f_ik = min(1, exp(-β(E_k - E_i)))` is the `thermalAcceptance`. -/
theorem source_acceptance_eq (E : Fin D → ℝ) (β : ℝ) (i k : Fin D) :
    thermalAcceptance E β i k = min 1 (Real.exp (-β * (E k - E i))) := rfl

/-- **c004, clause 1 (Eq. (2)).**  The energy-conditioned coin
`W(E_k,E_i)` is unitary for every energy table, inverse temperature and ideal
phase-estimation outcome.  Reused FQN:
`...AcceptanceCoin.metropolisControlledCoin_unitary`. -/
theorem source_controlledCoin_unitary (E : Fin D → ℝ) (β : ℝ) :
    metropolisControlledCoin E β ∈ Matrix.unitaryGroup _ ℂ :=
  metropolisControlledCoin_unitary E β

/-- **c004, clause 2 (post-W state).**  Applied to the post-QPE state
`∑_k x_k |ψ_k⟩|E_i⟩|E_k⟩|0⟩`, the coin produces exactly the paper's
superposition: accept amplitude `x_k √f_ik` on coin `1`, reject amplitude
`x_k √(1-f_ik)` on coin `0`, zero elsewhere.  Reused FQN:
`...AcceptanceCoin.metropolisControlledCoin_coherent_state`. -/
theorem source_coherent_accept_reject_state (E : Fin D → ℝ) (β : ℝ) (i : Fin D) (x : Fin D → ℂ) :
    ApplyGate (metropolisControlledCoin E β) (coherentEnergySuperposition i x) =
      fun p : Fin D × Fin D × Fin D × Fin 2 =>
        if p.2.1 = i ∧ p.1 = p.2.2.1 then
          if p.2.2.2 = 1 then x p.1 * ((Real.sqrt (thermalAcceptance E β i p.1) : ℝ) : ℂ)
          else x p.1 * ((Real.sqrt (1 - thermalAcceptance E β i p.1) : ℝ) : ℂ)
        else 0 :=
  metropolisControlledCoin_coherent_state E β i x

/-- **c004, clause 3 (Born probability of acceptance).**  The accept outcome
(coin `= 1`) has Born probability `Σ_k ‖x_k‖² f_ik`, exactly the classical
Metropolis transition weights `|x_k^i|² f_k^i`.  Reused FQN:
`...AcceptanceCoin.metropolisControlledCoin_accept_mass`. -/
theorem source_accept_mass (E : Fin D → ℝ) (β : ℝ) (i : Fin D) (x : Fin D → ℂ) :
    MeasureProb (ApplyGate (metropolisControlledCoin E β) (coherentEnergySuperposition i x))
      (Finset.univ.filter (fun p : Fin D × Fin D × Fin D × Fin 2 => p.2.2.2 = 1)) =
      ∑ k, ‖x k‖ ^ 2 * thermalAcceptance E β i k :=
  metropolisControlledCoin_accept_mass E β i x

/-- **c004, full claim.**  The whole Eqs. (2)-(3) contract, including the
normalization hypothesis `∑_k ‖x_k‖² = 1` on the proposal amplitudes.  Reused
FQN: `...AcceptanceCoin.coherentInstrumentSubgoal`. -/
theorem source_coherentInstrumentSubgoal : CoherentInstrumentSubgoal :=
  coherentInstrumentSubgoal

end Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrument
