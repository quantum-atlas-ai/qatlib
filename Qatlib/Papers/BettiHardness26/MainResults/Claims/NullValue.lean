/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import Qatlib.Papers.BettiHardness26.MainResults.Topology.CliqueComplexHomology

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.1 (Null value)

Strelchuk, Subramanian, Wesołowski, "Average-case hardness of Betti number estimation",
fixed arXiv:2609.12777v1 (2026-09-11). Source: Lemma 4.1, §4, p.10.

`For k ≥ (2+ε) log₂ n, w.h.p. G₀ ∼ G(n, ½) has no (k−1)-clique, whence
β_{k−2}(skel_{k−2} X(G₀)) = 0.`

The deterministic core (`clique-free ⇒ β_{k−2}=0`) is fully proved here. The probabilistic half
(the Markov bound on the expected number of `(k−1)`-cliques, p.10) is not formalised: the
library has no Erdős–Rényi probability space; see `CliqueComplexHomology.lean`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Claims

open Qatlib.Papers.BettiHardness26.MainResults.Topology

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- **Lemma 4.1 (Null value), deterministic core** (§4, p.10): if `G₀` has no `(k−1)`-clique then
`β_{k−2}(skel_{k−2} X(G₀)) = 0`. -/
theorem lemma_4_1 (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k)
    (h : G.CliqueFree (k - 1)) : bettiNumber G (k - 2) = 0 :=
  lemma_4_1_core G hk h

end Qatlib.Papers.BettiHardness26.MainResults.Claims
