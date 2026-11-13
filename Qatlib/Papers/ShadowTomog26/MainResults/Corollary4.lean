/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowTomog26.MainResults.Theorem3

/-!
# Conditional exact value for block measurements

This module isolates the exact-value implication used in the block-measurement discussion of
[XuEtAl2026]. The wrapper `conditional_block_value` takes `IsHPerfect (toBodies F)` as an
explicit hypothesis and identifies the block minimax value with the reciprocal fractional
chromatic number of the union graph.

## Main statements

* `conditional_block_value` gives `deltaTauBlock F = 1 / fractionalChromatic F.Gunion` under the
  combined-body perfection hypothesis.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ShadowTomog26.MainResults

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {Blk : Type*} [Fintype Blk] [DecidableEq Blk]

omit [DecidableEq Blk] in

/-- If the combined graph-body system `toBodies F` is hbar-perfect, then `deltaTauBlock F`
equals the reciprocal fractional chromatic number of `F.Gunion`. -/
theorem conditional_block_value (F : BlockFamily V Blk)
    (hperf : IsHPerfect (toBodies F))
    :
    deltaTauBlock F = 1 / fractionalChromatic F.Gunion :=
  source_theorem3_tight_hperfect F hperf

end Qatlib.Papers.ShadowTomog26.MainResults
