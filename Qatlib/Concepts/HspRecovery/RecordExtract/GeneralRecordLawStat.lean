/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralCosetRecord
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.RecordExtract

def SourceGeneralRecordLaw : Prop := by
  classical
  exact
  ∀ (N : ℕ) [NeZero N] (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → S) (s : ZMod N),
    Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReflectionHides N f s →
      Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.HspRecovery.RecordExtract.dihedralRecordCircuit
        (N := N) (S := S)) = 1 ∧
      Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.HspRecovery.RecordExtract.dihedralRecordCircuit
        (N := N) (S := S)) = 1 ∧
      ∀ k : ZMod N, ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖ ^ 2) = 1 / (N : ℝ) ∧
        ∀ t z, Qatlib.Concepts.HspRecovery.RecordExtract.dihedralRecordJoint N f ((k, t), z) =
          γ z * Qatlib.Concepts.HspRecovery.RecordExtract.dihedralQubitState N s k t

end Qatlib.Concepts.HspRecovery.RecordExtract
