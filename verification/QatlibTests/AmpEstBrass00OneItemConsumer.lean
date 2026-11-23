module

import Qatlib.Papers.AmpEstBrass00.OffGridQPE.Corollary14OneItem

/-!
# Consumer checks for the one-item counting endpoint

This module instantiates the endpoint theorem on the concrete nonempty domain `Fin 1`,
both for the empty marked set and for its unique marked item.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.AmpEstBrass00.OffGridQPE
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit

open scoped Matrix.Norms.L2Operator

namespace QatlibTests.AmpEstBrass00OneItemConsumer

/-- The concrete Euclidean state and one-point Fourier operator use the intended norms. -/
example : ‖oneItemEuclideanState‖ = 1 ∧ ‖QFTMatrix 1‖ = 1 :=
  oneItemEuclideanState_and_QFT_L2

/-- With no marked item, the circuit outputs zero and succeeds with certainty. -/
example :
    oneItemCor14Output (0 : Fin 1) = 0 ∧
      oneItemCountEventMass ∅ (fun z => |(oneItemCor14Output z : ℝ)| < 11) = 1 := by
  obtain ⟨_, hout, _, hmass, _⟩ := corollary14_one_item_endpoint ∅ (0 : Fin 1)
  exact ⟨hout, by simpa using hmass⟩

/-- With the unique item marked, the rounded error is one and lies in the
success window of the same one-query circuit. -/
example :
    |(oneItemCor14Output (0 : Fin 1) : ℝ) - 1| = 1 ∧
      oneItemCountEventMass Finset.univ
        (fun z => |(oneItemCor14Output z : ℝ) - 1| < 11) = 1 ∧
      QueryCount oneItemCountCircuit = 1 := by
  obtain ⟨_, hout, _, hmass, _, _, hquery⟩ :=
    corollary14_one_item_endpoint Finset.univ (0 : Fin 1)
  exact ⟨by rw [hout]; norm_num, by simpa using hmass, hquery⟩

end QatlibTests.AmpEstBrass00OneItemConsumer
