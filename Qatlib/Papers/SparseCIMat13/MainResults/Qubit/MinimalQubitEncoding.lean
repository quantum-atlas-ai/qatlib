/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright: paper-layer formalization for SparseCIMat13.
Source: B. Toloui and P. J. Love, "Quantum Algorithms for Quantum Chemistry based on the
sparsity of the CI-matrix", arXiv:1312.2579 (2013), Section II p.5-6, Eqs. (12)-(14) and
the conclusion (p.9 of the arXiv version).
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.BitVec
import Mathlib.Data.FinEnum
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Minimal-qubit CI representation (arXiv:1312.2579, Eqs. (12)-(14), main result)

The `ne`-electron sector of the Fock space has dimension `D(no,ne) = C(no,ne)`
(Eq. (14)).  The CI representation assigns the first `D` logical qubit states to the
configurations, which requires exactly `⌈log₂ D⌉ = Nat.clog 2 D` qubits (p.6).  This file
proves:

* the sector cardinality equals `C(no,ne)` (`card_configuration`);
* `⌈log₂ D⌉` qubits admit an injective encoding of all configurations
  (`exists_injective_encoding`);
* no smaller qubit count does (`ciQubitCount_minimal`), i.e. the encoding is optimal in
  qubit number, the "minimal number of qubits" statement of the conclusion;
* `⌈log₂ D⌉ ≤ no`, the reduction from the second-quantized `no` qubits.
-/

namespace Qatlib.Papers.SparseCIMat13.MainResults.Qubit

open Finset

/-- The `ne`-electron sector of the Fock space over `no` spin-orbitals: configurations
`orb(x)` are `ne`-element subsets of `Fin no` (paper Eqs. (14), (17)). -/
def configuration (no ne : ℕ) : Type :=
  {x : Finset (Fin no) // x.card = ne}

/-- Configurations with fixed occupation number form a finite type. -/
instance (no ne : ℕ) : Fintype (configuration no ne) := by
  unfold configuration
  infer_instance

/-- Equality of finite occupation configurations is decidable. -/
instance (no ne : ℕ) : DecidableEq (configuration no ne) := by
  unfold configuration
  infer_instance

/-- Paper Eq. (14): the dimension of the `ne`-particle sector is `C(no,ne)`. -/
theorem card_configuration (no ne : ℕ) :
    Fintype.card (configuration no ne) = Nat.choose no ne := by
  classical
  have h : Fintype.card (configuration no ne) = (Finset.univ.powersetCard ne).card :=
    Fintype.card_of_subtype (p := fun x : Finset (Fin no) => x.card = ne)
      (Finset.univ.powersetCard ne) (fun x => by simp)
  rw [h, Finset.card_powersetCard]
  simp

/-- Cardinality of the `b`-qubit state space: `2^b`. -/
theorem card_bitVec (b : ℕ) : Fintype.card (BitVec b) = 2 ^ b := by
  have e : BitVec b ≃ Fin (2 ^ b) := (BitVec.equivFin (m := b)).toEquiv
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- The number of qubits used by the CI encoding: `⌈log₂ C(no,ne)⌉`. -/
def ciQubitCount (no ne : ℕ) : ℕ :=
  Nat.clog 2 (Nat.choose no ne)

/-- The sector fits into `2 ^ ⌈log₂ D⌉` logical states (Eq. (14) and the mapping to
`n_Q = ⌈log₂ D⌉` qubits). -/
theorem ciQubitCount_spec (no ne : ℕ) :
    Nat.choose no ne ≤ 2 ^ ciQubitCount no ne := by
  exact Nat.le_pow_clog (by norm_num) _

/-- An explicit injective encoding of all configurations into
`⌈log₂ C(no,ne)⌉` qubits: enumerate the sector and pad to the next power of two. -/
noncomputable def ciEncoding (no ne : ℕ) :
    configuration no ne → BitVec (ciQubitCount no ne) :=
  fun c => BitVec.ofFin (Fin.castLE
    (by exact Nat.le_trans (le_of_eq (card_configuration no ne)) (ciQubitCount_spec no ne))
    ((Fintype.equivFin (configuration no ne)) c))

/-- Existence of an injective `⌈log₂ C(no,ne)⌉`-qubit encoding (paper p.6). -/
theorem exists_injective_encoding (no ne : ℕ) :
    ∃ enc : configuration no ne → BitVec (ciQubitCount no ne), Function.Injective enc := by
  refine ⟨ciEncoding no ne, ?_⟩
  intro a b hab
  have h1 : Fin.castLE
        (by exact Nat.le_trans (le_of_eq (card_configuration no ne)) (ciQubitCount_spec no ne))
        ((Fintype.equivFin (configuration no ne)) a) =
      Fin.castLE
        (by exact Nat.le_trans (le_of_eq (card_configuration no ne)) (ciQubitCount_spec no ne))
        ((Fintype.equivFin (configuration no ne)) b) := by
    simpa [ciEncoding] using congrArg BitVec.toFin hab
  exact (Fintype.equivFin (configuration no ne)).injective
    (Fin.castLE_injective _ h1)

/-- No `b`-qubit injective encoding exists for `b < ⌈log₂ C(no,ne)⌉`: the encoding is
optimal in the number of qubits (conclusion of the paper). -/
theorem ciQubitCount_minimal (no ne b : ℕ)
    (h : ∃ enc : configuration no ne → BitVec b, Function.Injective enc) :
    ciQubitCount no ne ≤ b := by
  obtain ⟨enc, henc⟩ := h
  have h1 : Fintype.card (configuration no ne) ≤ Fintype.card (BitVec b) :=
    Fintype.card_le_of_injective enc henc
  rw [card_configuration, card_bitVec] at h1
  exact Nat.clog_le_of_le_pow h1

/-- Bundled main result: `⌈log₂ C(no,ne)⌉` is exactly the minimal number of qubits for an
injective representation of the fixed-electron-number wavefunction. -/
theorem minimal_qubit_CI_representation (no ne : ℕ) :
    (∃ enc : configuration no ne → BitVec (ciQubitCount no ne), Function.Injective enc) ∧
      ∀ b, (∃ enc : configuration no ne → BitVec b, Function.Injective enc) →
        ciQubitCount no ne ≤ b :=
  ⟨exists_injective_encoding no ne, fun _ => ciQubitCount_minimal no ne _⟩

/-- `C(n,k) ≤ 2^n`, used to compare with the second-quantized `no` qubits. -/
theorem choose_le_two_pow (n k : ℕ) : Nat.choose n k ≤ 2 ^ n := by
  by_cases hk : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have h := Finset.single_le_sum (f := fun m => Nat.choose n m)
      (fun i _ => Nat.zero_le _) hmem
    simpa [Nat.sum_range_choose] using h
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

/-- The CI qubit count never exceeds the second-quantized `no` qubits (paper's claim that
the qubit requirement is reduced to `⌈log₂ C(no,ne)⌉ ≤ no`). -/
theorem ciQubitCount_le_no (no ne : ℕ) : ciQubitCount no ne ≤ no :=
  Nat.clog_le_of_le_pow (choose_le_two_pow no ne)

end Qatlib.Papers.SparseCIMat13.MainResults.Qubit
