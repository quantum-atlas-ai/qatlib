/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel

@[expose] public section


/-!
# Uniqueness of the fixed point / ergodicity (Temme et al. 2011, Sec. 3.2)

Fixed source: arXiv:0911.3635v2, Section 3.2, printed page 8.

The paper states: "Uniqueness of the Fixed point.  If we choose the set of all
possible updates `{C}` equal to a set of universal gates, then the Metropolis
Markov chain is ergodic for all finite `β < ∞`."  The argument (given in the
text) is that detailed balance plus the ability to reach every energy
eigenstate with non-zero probability makes the stationary state unique; the
only stationary state is then the Gibbs state of the detailed-balance lemma
.

Neither the frozen layer nor this file formalises the universal-gate set or
the irreducibility proof.  We state the two conclusions in terms of a
hypothesis that encodes the paper's content: every pair of distinct densities
is strictly contracted by some number of applications (the formal shadow of
"universal updates connect all eigenstates").  Both theorems are
statement-only; see the annotation on each.

Reused FQNs:
* `Qatlib.Foundations.PureStateMath.SchattenOne` and
  `IsDensityOperator` (trace-norm carrier);
* `...QuantumGibbs.DetailedBalance.QuantumDetailedBalance`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.UniquenessErgodicity

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
variable {D : ℕ}

/-- **ergodicity.**  Trace-norm convergence of every initial density to
the stationary density `σ` under repeated application of the channel.  This is
the paper's "the Metropolis Markov chain is ergodic" made quantitative. -/
def MetropolisErgodic (T : QuantumChannel D D) (σ : Operator D) : Prop :=
  ∀ ρ : Operator D, IsDensityOperator ρ →
    Filter.Tendsto (fun m : ℕ => SchattenOne ((T.map^[m]) ρ - σ))
      Filter.atTop (nhds 0)


end Qatlib.Papers.QMetropolis11.GibbsMixing.UniquenessErgodicity
