/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralCosetRecord
import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralSummandExtraction
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveBridge
import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentDihe
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm.Algorithm1

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

theorem algorithm1_record_law (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    QueryCount (dihedralRecordCircuit (N := 2 ^ n) (S := S)) = 1 ∧
    GateCount (dihedralRecordCircuit (N := 2 ^ n) (S := S)) = 1 ∧
    ∀ k : ZMod (2 ^ n), ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖ ^ 2) = 1 / (2 ^ n : ℝ) ∧
      ∀ t z, dihedralRecordJoint (2 ^ n) f ((k, t), z) =
        γ z * dihedralQubitState (2 ^ n) s k t :=
  dihedralRecordLaw n f s hf

theorem algorithm1_extraction_law (N : ℕ) [NeZero N] (s k ℓ : ZMod N) :
    ∃ xiPlus xiMinus : QState Bool, ∃ _hPlus : Normalized xiPlus,
      ∃ _hMinus : Normalized xiMinus, ∃ uPlus uMinus : ℂ,
      ‖uPlus‖ = 1 ∧ ‖uMinus‖ = 1 ∧
      xiPlus = uPlus • dihedralQubitState N s (k + ℓ) ∧
      xiMinus = uMinus • dihedralQubitState N s (k - ℓ) ∧
      ∀ (b : Bool) (ξ : QState Bool) (hξ : Normalized ξ),
        dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
          (normalized_dihedralQubitState N s k) (normalized_dihedralQubitState N s ℓ)
          (b, ⟨ξ, hξ⟩) =
          if (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus) then 1 / 2 else 0 :=
  dihedralExtractionLaw N s k ℓ

theorem algorithm1_sieve_bridge (n m : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    dihedralSieveActual n m f = (dihedralSieveRun n m s).1 :=
  dihedralSieveBridge n m S f s hf

theorem algorithm1_parity_readout (n : ℕ) (s : ZMod (2 ^ n)) :
    parityReadout (dihedralQubitState (2 ^ n) s ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))
        (normalized_dihedralQubitState (2 ^ n) s ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))) =
      PMF.pure (decide (s.val % 2 = 1)) :=
  dihedralParityReadoutPure n s

theorem algorithm1_step4_descent : SourceParityDescent :=
  sourceParityDescent

end Qatlib.Concepts.HspRecovery.SieveAlgorithm.Algorithm1
