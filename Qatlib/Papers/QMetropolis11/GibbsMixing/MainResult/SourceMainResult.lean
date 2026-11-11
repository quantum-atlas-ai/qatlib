/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrumentSubgoalStat
import Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrumentSubgoalQuan
import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceFixedPointQuan
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Main result of the quantum Metropolis sampler (Temme et al. 2011, abstract + Secs. 3-4)

Fixed source: arXiv:0911.3635v2, abstract and Sections 3-4.

The abstract claims that the paper (i) implements a quantum version of the
Metropolis algorithm, (ii) samples directly from the eigenstates of the
Hamiltonian and therefore evades the sign problem, and (iii) is realisable at
small scale with present technology.  The two mathematically meaningful and
formalised components are:

* the coherent accept/reject coin of Eqs. (2)-(3), together with the ideal
  phase-estimation instrument that produces the energy-conditioned
  superposition (`CoherentInstrumentSubgoal`, Sec. 3);
* the detailed-balance fixed-point property of the constructed map
  (`QuantumDetailedBalanceFixedPoint`, Sec. 6), which makes the Gibbs state the
  steady state that is sampled;
* the exponentially decaying failure probability of the reject move
  (`RejectionFailureBound`, Sec. 3.1), which makes the construction
  implementable with finitely many measurements.

The "evades the sign problem" and "today's technology" sentences are
discursive, not propositions about a formal model; they are recorded here but
not asserted as Lean theorems.

Reused FQNs:
* `QuantumAlgorithm.Papers.QMetropolis11.AcceptanceCoin.coherentInstrumentSubgoal`;
* `QuantumAlgorithm.Concepts.QuantumGibbs.DetailedBalance.quantumDetailedBalanceFixedPoint`;
* `QuantumAlgorithm.Concepts.MixedInstrument.RewindAlgebra.rejectionFailureBound`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.MainResult

/-- **c018 (abstract / main result).**  The three formalised pillars of the
quantum Metropolis sampler: the coherent accept/reject instrument, the
detailed-balance fixed point (Gibbs state as steady state), and the
exponentially small reject-failure probability.  Assembled from the frozen
contracts; no new analytic content. -/
theorem source_mainResult :
    Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrumentSubgoal ∧
    Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceFixedPoint ∧
    Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBound :=
  ⟨Qatlib.Papers.QMetropolis11.AcceptanceCoin.coherentInstrumentSubgoal,
   Qatlib.Concepts.QuantumGibbs.DetailedBalance.quantumDetailedBalanceFixedPoint,
   Qatlib.Concepts.MixedInstrument.RewindAlgebra.rejectionFailureBound⟩

end Qatlib.Papers.QMetropolis11.GibbsMixing.MainResult
