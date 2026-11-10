/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.Reductions
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

def SourceParityDescent : Prop := by
  classical
  exact
  (∀ (n : ℕ) (b : Bool), Function.Injective (paritySubgroupEmbedding n b)) ∧
  (∀ (n : ℕ) (S : Type) (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ (n + 1)) → S)
    (b : Bool) (t : ZMod (2 ^ n)),
    Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReflectionHides (2 ^ (n + 1)) f (parityLift n b t) →
      Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReflectionHides (2 ^ n) (parityRestrictedOracle n f b) t) ∧
  (∀ (n : ℕ) (s : ZMod (2 ^ (n + 1))),
    ∃! t : ZMod (2 ^ n), parityLift n (decide (s.val % 2 = 1)) t = s)

end Qatlib.Concepts.HspRecovery.ReductionCore
