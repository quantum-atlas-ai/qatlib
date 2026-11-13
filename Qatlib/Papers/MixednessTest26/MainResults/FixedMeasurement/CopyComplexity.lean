/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Deterministic Pauli copy complexity (Theorem 1.5)

Paper: arXiv:2608.18839v3, Theorem 1.5 (page 3 of the PDF):

> The copy complexity of deterministic Pauli mixedness testing is
> `n = Ω(√(27^N)/ε²)` and `n = O(√(30^N)/ε²)`.

Deterministic Pauli testing is the `Ω = 1` special case of
`PauliBasisProtocol`: one fixed list of `n` Pauli bases, no private randomness.
Its copy complexity is `SourceModel.deterministicPauliComplexity N ε`, the
infimum of copy counts over correct deterministic protocols.

## Mathematical background and scope

* Fixed source: arXiv:2608.18839v3, Theorem 1.5, §4.1 (fixed-basis protocol)
  and §5.3 (fixed-measurement lower bound [LiuAcharya2024b]).
* Proof outline: the upper bound uses the fixed basis `X^{⊗N}` (or the
  variance-optimal choice among the three uniform bases) and the second moment
  of the collision statistic, whose covariance term is controlled by
  Lemma 4.1 (`FixedMeasurement/CovarianceCount.lean`); the variance scales like
  `√(30^N)/ε²`.  The lower bound instantiates the fixed-measurement framework
  of [LiuAcharya2024b] with `√(27^N)` scaling.
* Scope note: this module imports the deterministic protocol model and
  describes the copy-complexity bounds. The explicit `√(30^N)` variance
  computation, using the covariance count of Lemma 4.1 and the binomial sums
  `Σ_w 3^w C(N,w) = 4^N`, `Σ_w 10^w C(N,w) = 11^N`, and the
  [LiuAcharya2024b] fixed lower-bound framework are outside the scope of this
  file. Since `deterministicPauliComplexity` is an `sInf`, a bound from a
  feasible protocol also requires a copy-count estimate.
* Related definitions: `SourceModel.PauliBasisProtocol N n 1`,
  `IsPauliMixednessTester`, `deterministicPauliComplexity`,
  `SourceModel.pauliInfluence`, and `SourceModel.pauliNormSq`. The covariance
  quantities are defined in `FixedMeasurement/CovarianceCount.lean`.
* The upper-bound analysis applies Chebyshev's inequality
  (`FinDist.chebyshev_avg`) to the variance of the collision statistic. The
  lower-bound analysis uses the two-point method with the hard instance of
  Definition 5.2 projected onto a fixed basis, giving the `27^N` asymptotics.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.FixedMeasurement


end Qatlib.Papers.MixednessTest26.MainResults.FixedMeasurement
