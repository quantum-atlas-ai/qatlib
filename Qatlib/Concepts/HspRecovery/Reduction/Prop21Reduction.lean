/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Prop21Reduction

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.OpenSieve

theorem prop21_reduction {N : ℕ} [NeZero N] {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (dec : DecidableEq S) (f : DihedralReg N → S)
    (H : DihedralSubgroupData N) (hf : DihedralSubgroupHides f H) :
    (∀ a b : ℕ, a < N → b < N →
        (f ((a : ℕ), false) = f ((b : ℕ), false) ↔
          ∃ k : ℕ, ((b : ℕ) : ZMod N) = ((a : ℕ) : ZMod N) +
            ((k * subgroupRotationPeriod H : ℕ) : ZMod N))) ∧
    (∀ a b : ℕ, a < N → b < N →
        (f ((a : ℕ), false) = f ((b : ℕ), true) ↔
          ∃ s : ZMod N, H.slope = some s ∧
            ∃ k : ℕ, ((b : ℕ) : ZMod N) = ((a : ℕ) : ZMod N) + s +
              ((k * subgroupRotationPeriod H : ℕ) : ZMod N))) ∧
    subgroupReductionAnswerWith dec f = reduceSubgroupData H :=
  walkGoal_prop21_reduction dec f H hf

theorem prop21_rotation_period {N : ℕ} [NeZero N] (H : DihedralSubgroupData N) :
    H.period * subgroupRotationPeriod H = N ∧ 0 < H.period :=
  walkGoal_prop21_rotation_part H

end Qatlib.Concepts.HspRecovery.ReductionCore.Prop21Reduction
