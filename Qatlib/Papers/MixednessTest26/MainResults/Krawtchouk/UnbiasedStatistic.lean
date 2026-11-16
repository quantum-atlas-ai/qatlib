/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel
public import Qatlib.Papers.MixednessTest26.PauliShadow.KrawtchoukTester

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Unbiasedness of the Krawtchouk statistic `W_k` (Appendix A.2)

Paper: arXiv:2608.18839v3, Appendix A.2, the paragraph "We will show that `W_k`
is an unbiased statistic for `‖α^{=k}‖_2^2`" (page 23 of the PDF; the display
immediately after "Coupled with the fact that `d_H(x,y) = w_H(x ⊕ y)`").

With two independent `n`-tuples `X = (X_1,…,X_n)`, `Y = (Y_1,…,Y_n)` drawn from
`p^{⊗n}`, the two-sample collision statistic

`W_k = n^{-2} Σ_{i,j} K_k^{(N)}(d_H(X_i, Y_j))`

has expectation `‖α^{=k}‖_2^2 = Σ_{|S|=k} α_S^2 = cubeAlphaWeightMass p k`.

The frozen library proves the exact statement (for every `FinDist (Reg N)` and
every `n > 0`, with independent product sample mass `p.probOf`), so this file is
a verified bridge to that FQN.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.Krawtchouk
open Qatlib.Papers.MixednessTest26.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier
open Qatlib.Papers.MixednessTest26.PauliShadow
open scoped BigOperators

/-- Paper Appendix A.2: the Krawtchouk-based two-sample statistic `W_k` is an
unbiased estimator of the weight-`k` Pauli coefficient mass
`‖α^{=k}‖_2^2 = cubeAlphaWeightMass p k`.  Reuses the frozen FQN
`MixedStateCert.PauliShadow.krawtchoukStatistic_unbiased`. -/
theorem krawtchoukStatistic_expectation {N k : ℕ} (p : FinDist (Reg N)) {n : ℕ}
    (hn : 0 < n) :
    ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (p.probOf b.1 * p.probOf b.2) * krawtchoukStatistic k n b.1 b.2 =
      cubeAlphaWeightMass p k :=
  Qatlib.Papers.MixednessTest26.PauliShadow.krawtchoukStatistic_unbiased p hn

end Qatlib.Papers.MixednessTest26.MainResults.Krawtchouk
