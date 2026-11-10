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
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch

def qSearchWindow (l : ℕ) : ℕ :=
  max 1 ((6^l + 5^l - 1) / 5^l)

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
