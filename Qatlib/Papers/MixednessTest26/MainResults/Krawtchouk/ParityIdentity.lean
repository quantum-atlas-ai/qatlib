/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Krawtchouk parity identity (paper Eq. (2), §3.5)

Paper: arXiv:2608.18839v3, §3.5, Eq. (2) and the discussion after Theorem 2.4
(page 7 of the PDF).  For the Boolean cube `Reg N` with character
`χ_S(x) = ∏_{i∈S} x_i` (`true` encoded as `+1`), the level-`k` parity sum over
all weight-`k` sets is the degree-`k` Krawtchouk polynomial evaluated at the
Hamming weight of `x`:

`Σ_{|S|=k} χ_S(x) = K_k^{(N)}(w_H(x))`.

The frozen library already proves exactly this identity for every `N`, `k`
and `x` (including the boundary cases `N = 0`, `k = 0` and `k > N`), so the
paper-layer declaration is a verified bridge, not a new proof.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.Krawtchouk

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier
open scoped BigOperators

/-- Paper Eq. (2) (§3.5): the sum of characters over all weight-`k` subsets
equals the `k`-th Krawtchouk polynomial at the Hamming weight of `x`.
Reuses the frozen FQN
`MixedStateCert.PauliShadow.krawtchouk_char_sum`. -/
theorem krawtchouk_parity_sum_eq {N k : ℕ} (x : Reg N) :
    ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k), cubeChar S x =
      krawtchouk N k (cubeWeight x) :=
  Qatlib.Concepts.ShadowModels.BooleanCubeFourier.krawtchouk_char_sum x

end Qatlib.Papers.MixednessTest26.MainResults.Krawtchouk
