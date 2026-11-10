/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowTomog26.MainResults.Theorem3
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ShadowTomog26.MainResults

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {Blk : Type*} [Fintype Blk] [DecidableEq Blk]

omit [DecidableEq Blk] in

theorem conditional_block_value (F : BlockFamily V Blk)
    (hperf : IsHPerfect (toBodies F))
    :
    deltaTauBlock F = 1 / fractionalChromatic F.Gunion :=
  source_theorem3_tight_hperfect F hperf

end Qatlib.Papers.ShadowTomog26.MainResults
