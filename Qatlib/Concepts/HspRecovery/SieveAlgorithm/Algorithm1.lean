/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralCosetRecord
import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralSummandExtraction
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveBridge
import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentDihe

/-!
# Components of the dihedral sieve algorithm

This module collects the record-generation, extraction, readout, and descent results used in
Algorithm 1 of [Kuperberg2005]. The statements connect the oracle-driven sieve with its ideal
record process without asserting additional asymptotic bounds.

## Main statements

* `algorithm1_record_law`: the record amplitude factorization and circuit counts.
* `algorithm1_extraction_law`: the two equally weighted sum and difference branches.
* `algorithm1_sieve_bridge`: equality of actual and ideal output laws under the hiding promise.
* `algorithm1_parity_readout`: deterministic parity readout from the distinguished label.
* `algorithm1_step4_descent`: the parity descent specification.

## References

* [Kuperberg, Algorithm 1][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm.Algorithm1

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

/-- For an oracle hiding slope `s`, the record circuit uses one query and one gate, and each
label's joint amplitudes factor through the corresponding dihedral qubit with residual
squared norm `1 / 2 ^ n`. This is the record-generation law for [Kuperberg, Algorithm
1][Kuperberg2005]. -/
theorem algorithm1_record_law (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    QueryCount (dihedralRecordCircuit (N := 2 ^ n) (S := S)) = 1 ∧
    GateCount (dihedralRecordCircuit (N := 2 ^ n) (S := S)) = 1 ∧
    ∀ k : ZMod (2 ^ n), ∃ γ : S → ℂ, (∑ z : S, ‖γ z‖ ^ 2) = 1 / (2 ^ n : ℝ) ∧
      ∀ t z, dihedralRecordJoint (2 ^ n) f ((k, t), z) =
        γ z * dihedralQubitState (2 ^ n) s k t :=
  dihedralRecordLaw n f s hf

/-- Extracting two dihedral qubits gives exactly two normalized branch states, each with
probability one half, equal up to unit-modulus scalars to the qubits labeled `k + ℓ` and `k
- ℓ`. This is the combination step of [Kuperberg, Algorithm 1][Kuperberg2005]. -/
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

/-- Under the hidden-reflection promise, the actual sieve output law equals the ideal run's
output law for every `n` and `m`, connecting the two descriptions of [Kuperberg, Algorithm
1][Kuperberg2005]. -/
theorem algorithm1_sieve_bridge (n m : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ n) f s) :
    dihedralSieveActual n m f = (dihedralSieveRun n m s).1 :=
  dihedralSieveBridge n m S f s hf

/-- The dihedral qubit with label `2 ^ (n - 1)` yields the parity of the hidden slope with
probability one under `parityReadout`, as used in [Kuperberg, Algorithm 1][Kuperberg2005]. -/
theorem algorithm1_parity_readout (n : ℕ) (s : ZMod (2 ^ n)) :
    parityReadout (dihedralQubitState (2 ^ n) s ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))
        (normalized_dihedralQubitState (2 ^ n) s ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))) =
      PMF.pure (decide (s.val % 2 = 1)) :=
  dihedralParityReadoutPure n s

/-- The parity descent specification holds, providing the algebraic restriction and
reconstruction step of [Kuperberg, Algorithm 1][Kuperberg2005]. -/
theorem algorithm1_step4_descent : SourceParityDescent :=
  sourceParityDescent

end Qatlib.Concepts.HspRecovery.SieveAlgorithm.Algorithm1
