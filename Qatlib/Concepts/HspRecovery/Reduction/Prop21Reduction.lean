/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt

/-!
# Reduction of dihedral subgroup data

This module exposes the subgroup reduction associated with Proposition 2.1 of [Kuperberg2005].
For an oracle satisfying `DihedralSubgroupHides`, it characterizes collisions within the
rotation sector and between the two sectors in terms of the rotation period and optional
reflection slope.

## Main statements

* `prop21_reduction`: the collision characterizations and correctness of
  `subgroupReductionAnswerWith`.
* `prop21_rotation_period`: the rotation-period product identity and positivity of the subgroup
  period.

## References

* [Kuperberg, Proposition 2.1][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Prop21Reduction

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.OpenSieve

/-- Under the subgroup-hiding promise, rotation-sector and cross-sector collisions have the
stated period-and-slope descriptions, and the reduction answer equals the reduced subgroup
data. This supplies the formal reduction corresponding to [Kuperberg, Proposition
2.1][Kuperberg2005]. -/
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

/-- The subgroup period times its rotation period equals `N`, and the subgroup period is
positive, as used in [Kuperberg, Proposition 2.1][Kuperberg2005]. -/
theorem prop21_rotation_period {N : ℕ} [NeZero N] (H : DihedralSubgroupData N) :
    H.period * subgroupRotationPeriod H = N ∧ 0 < H.period :=
  walkGoal_prop21_rotation_part H

end Qatlib.Concepts.HspRecovery.ReductionCore.Prop21Reduction
