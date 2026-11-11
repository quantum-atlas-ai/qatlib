/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers

/-!
# Finite quantum search rounds and loops

This module defines a finite-horizon version of quantum search with unknown initial marked mass,
following [BrassardEtAl2002]. Each `qSearchRound` tries the prepared state, then a uniformly
chosen amplification depth from `qSearchWindow`; `qSearchLoop` stops on a marked output and
accumulates two cost counters.

## Main statements

* `BHMTQSearch.qSearchRound`: one randomized search round with two cost counters.
* `BHMTQSearch.qSearchLoop`: the search law for a finite number of rounds.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch

/-- The positive search-window size given by the integer ceiling of `(6/5)^l`, with a lower
bound of one. -/
def qSearchWindow (l : ℕ) : ℕ :=
  max 1 ((6^l + 5^l - 1) / 5^l)

/-- The law of one search round: test the prepared state, then on failure try a uniformly
selected amplification depth, returning an optional marked label and two costs. -/
noncomputable def qSearchRound {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (l : ℕ) : PMF (Option I × ℕ × ℕ) :=
  PMF.bind (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
    fun st =>
    if st.1.1 ∈ S then
      PMF.pure (some st.1.1, 1, 1)
    else
      PMF.bind
        (PMF.uniformOfFinset (Finset.univ : Finset (Fin (qSearchWindow l)))
          ⟨⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_one) (le_max_left 1
            ((6^l + 5^l - 1) / 5^l))⟩, Finset.mem_univ _⟩) fun j =>
        PMF.bind (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAATrial A hA j₀ S j) fun st2 =>
          PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
            2 + 2*j.val, 2 + j.val)

/-- The finite-horizon search law starting at a round offset, stopping on success and adding the
two cost counters on failure. -/
noncomputable def qSearchLoop {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    ℕ → ℕ → PMF (Option I × ℕ × ℕ)
  | 0, _ => PMF.pure (none, 0, 0)
  | T+1, off =>
      (qSearchRound A hA j₀ S (off+1)).bind fun out =>
        match out.1 with
        | some _ => PMF.pure out
        | none =>
            (qSearchLoop A hA j₀ S T (off+1)).map fun r =>
              (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2)
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
