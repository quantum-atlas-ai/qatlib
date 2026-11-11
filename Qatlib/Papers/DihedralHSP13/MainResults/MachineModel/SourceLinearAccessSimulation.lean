/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Data.List.Range

set_option backward.isDefEq.respectTransparency false

/-!
# Kuperberg 2013, Proposition 2.2: linear-access emulation of a quantum access memory

Source: Greg Kuperberg, *Another subexponential-time quantum algorithm for the dihedral
hidden subgroup problem*, arXiv:1112.3333v1 (TQC 2013), Proposition 2.2, Section 2.1,
page 2 (txt line 129, PDF p. 2).

The proposition states that in the RAM model a quantum access memory with `N` quantum or
classical cells can be simulated with a classical linear access memory, with the same
cells, at `Õ(N)` time overhead.

This file formalizes the constructive core of the paper's simulation: replace a
quantum random-access read `|a,b⟩ ↦ |a, b ⊕ mem a⟩` by a sequential scan over the `N`
addresses, each step applying the conditional flip
`|a,b⟩ ↦ |a, b ⊕ (if a = n then mem n else 0)⟩`.
The scan uses the *same* memory cells (`mem`), needs exactly one fixed gate per address
(hence `N` gates, which is stronger than `Õ(N)`), performs no oracle query, and
implements the random-access read exactly on every computational-basis state (and hence,
by linearity, on every superposition of the address register).  The computation is
carried out over `ZMod 2` bits; the corresponding Boolean-XOR statement is
`qramFlipBool_involutive` and `qramFlipBool_eq`.

The full machine-level statement — charging the scan against a RAM machine with a
classical linear tape and an auxiliary address tape, as described in the paper's proof
("step through the tape TC and add TC(n) to RQ on the quantum condition that n matches
TA") — is not part of the Foundations layer; the present theorem is the gate-level
resource accounting that proposition 2.2 invokes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.DihedralHSP13.MainResults.MachineModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## §1. Boolean and `ZMod 2` formulations of one memory cell -/

/-- The involutive permutation of a random-access read of a classical memory `mem`:
`|a, b⟩ ↦ |a, b ⊕ mem a⟩` (written additively over `ZMod 2`). -/
def qramFlip (mem : I → ZMod 2) : I × ZMod 2 → I × ZMod 2 :=
  fun p => (p.1, p.2 + mem p.1)

/-- A random-access read is an involution: adding the stored cell twice returns the
original bit.  This is the unitary that a quantum access memory performs in one step. -/
theorem qramFlip_involutive (mem : I → ZMod 2) : Function.Involutive (qramFlip mem) := by
  intro p
  rcases p with ⟨a, b⟩
  simp only [qramFlip, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- One step of the linear-access scan for address `n`: flip the data bit exactly when
the address register currently holds `n`, using the *same* memory cell `mem n`. -/
def scanFlip (mem : I → ZMod 2) (n : I) : I × ZMod 2 → I × ZMod 2 :=
  fun p => (p.1, p.2 + (if p.1 = n then mem n else 0))

/-- Each scan step is an involution (it is a conditional bit flip). -/
theorem scanFlip_involutive (mem : I → ZMod 2) (n : I) :
    Function.Involutive (scanFlip mem n) := by
  intro p
  rcases p with ⟨a, b⟩
  by_cases h : a = n
  · simp only [scanFlip, h, if_true, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · simp [scanFlip, h]

/-- A scan step only reads the cell `mem n` it is indexed by; this is the formal
"same cells" content of the scan. -/
theorem scanFlip_depends_only_on_cell (mem mem' : I → ZMod 2) (n : I)
    (h : mem n = mem' n) : scanFlip mem n = scanFlip mem' n := by
  funext p
  simp only [scanFlip, h]

/-- The Boolean-XOR form of a random-access read, for comparison with the paper's
`⊕` notation: reading the Boolean memory `f` flips the data bit by `f a`. -/
def qramFlipBool (f : I → Bool) : I × Bool → I × Bool :=
  fun p => (p.1, p.2 ^^ f p.1)

/-- The Boolean read is an involution (`xor` twice cancels). -/
theorem qramFlipBool_involutive (f : I → Bool) : Function.Involutive (qramFlipBool f) := by
  intro p
  rcases p with ⟨a, b⟩
  cases h : f a <;> simp [qramFlipBool, h]

/-- Applying the Boolean read twice is the identity, exactly matching the additive
`ZMod 2` involution `qramFlip_involutive`. -/
theorem qramFlipBool_eq (f : I → Bool) (p : I × Bool) :
    qramFlipBool f (qramFlipBool f p) = p :=
  qramFlipBool_involutive f p

/-! ## §2. The linear scan circuit -/

/-- The linear-access scan circuit on a list of addresses: one fixed gate per address,
executed in list order.  No oracle query occurs. -/
def scanCircuitOn (mem : I → ZMod 2) (L : List I) : Circuit (I × ZMod 2) :=
  L.map fun n => Step.gate (permMatrix (scanFlip mem n))

/-- The scan circuit over the full address set `I`. -/
noncomputable def scanCircuit (mem : I → ZMod 2) : Circuit (I × ZMod 2) :=
  scanCircuitOn mem (Finset.univ.toList)

/-- Every gate in the scan is a permutation gate, hence unitary. -/
theorem isUnitaryCircuit_scanCircuitOn (mem : I → ZMod 2) (L : List I) :
    IsUnitaryCircuit (scanCircuitOn mem L) := by
  intro U hU
  rw [scanCircuitOn, List.mem_map] at hU
  obtain ⟨n, _, hUn⟩ := hU
  rw [Step.gate.injEq] at hUn
  rw [← hUn]
  exact permMatrix_unitary (scanFlip_involutive mem n)

/-! ## §3. Gate and query accounting -/

/-- Counting gates through a `List.map` of gate steps. -/
theorem gateCount_map_gate {J K : Type*} (L : List J) (f : J → Matrix K K ℂ) :
    GateCount (L.map fun n => Step.gate (f n)) = L.length := by
  induction L with
  | nil => simp
  | cons n L ih => simp [ih]

/-- Counting queries through a `List.map` of gate steps: the scan performs none. -/
theorem queryCount_map_gate {J K : Type*} (L : List J) (f : J → Matrix K K ℂ) :
    QueryCount (L.map fun n => Step.gate (f n)) = 0 := by
  induction L with
  | nil => simp
  | cons n L ih => simp [ih]

/-- The scan circuit performs exactly one gate per address in `L`. -/
theorem gateCount_scanCircuitOn (mem : I → ZMod 2) (L : List I) :
    GateCount (scanCircuitOn mem L) = L.length := by
  simpa [scanCircuitOn] using gateCount_map_gate L (fun n => permMatrix (scanFlip mem n))

/-- The scan circuit performs no oracle query. -/
theorem queryCount_scanCircuitOn (mem : I → ZMod 2) (L : List I) :
    QueryCount (scanCircuitOn mem L) = 0 := by
  simpa [scanCircuitOn] using queryCount_map_gate L (fun n => permMatrix (scanFlip mem n))

/-! ## §4. Semantics of the scan -/

/-- **Running the scan on a basis state.**  After scanning the addresses in `L`, the
data bit has been flipped by the sum of the cells whose address occurred in `L` and
matched the address register. -/
theorem run_scanCircuitOn_ket (mem : I → ZMod 2) (L : List I) :
    ∀ (a : I) (b : ZMod 2),
      Run (1 : Matrix (I × ZMod 2) (I × ZMod 2) ℂ) (scanCircuitOn mem L) (Ket (a, b)) =
        Ket (a, b + (L.map fun n => if a = n then mem n else 0).sum) := by
  induction L with
  | nil =>
    intro a b
    simp [scanCircuitOn]
  | cons n L ih =>
    intro a b
    have hstep : scanCircuitOn mem (n :: L) =
        Step.gate (permMatrix (scanFlip mem n)) :: scanCircuitOn mem L := rfl
    rw [hstep, run_gate, applyGate_permMatrix_ket (scanFlip_involutive mem n)]
    simp only [scanFlip, List.map_cons, List.sum_cons]
    rw [ih]
    rw [add_assoc]

/-- Summing the conditional cell contributions over all addresses selects exactly the
cell at the current address. -/
theorem sum_ite_cell (mem : I → ZMod 2) (a : I) :
    (Finset.univ.sum fun n => if a = n then mem n else 0) = mem a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro n _ hn
    rw [if_neg (Ne.symm hn)]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- Bridge from the list sum produced by the circuit semantics to the finite-set sum
over all addresses. -/
theorem list_sum_map_univ (mem : I → ZMod 2) (a : I) :
    ((Finset.univ.toList).map fun n => if a = n then mem n else 0).sum =
      Finset.univ.sum fun n => if a = n then mem n else 0 := by
  rw [← List.sum_toFinset (fun n => if a = n then mem n else 0) (Finset.nodup_toList _),
    Finset.toList_toFinset]

/-- **Proposition 2.2 (constructive core).**  Scanning the `N = |I|` addresses of the
same classical memory implements the quantum random-access read exactly on every
computational basis state, with exactly `|I|` fixed gates and no oracle queries. -/
theorem prop22_scan_implements_qram (mem : I → ZMod 2) (a : I) (b : ZMod 2) :
    Run (1 : Matrix (I × ZMod 2) (I × ZMod 2) ℂ) (scanCircuit mem) (Ket (a, b)) =
        Ket (a, b + mem a) ∧
      GateCount (scanCircuit mem) = Fintype.card I ∧
      QueryCount (scanCircuit mem) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [scanCircuit, run_scanCircuitOn_ket, list_sum_map_univ, sum_ite_cell]
  · rw [scanCircuit, gateCount_scanCircuitOn, Finset.length_toList, Finset.card_univ]
  · rw [scanCircuit, queryCount_scanCircuitOn]

/-- The scan circuit over the full address set is unitary (every step is a permutation
gate), so it is a legitimate quantum circuit. -/
theorem isUnitaryCircuit_scanCircuit (mem : I → ZMod 2) :
    IsUnitaryCircuit (scanCircuit mem) :=
  isUnitaryCircuit_scanCircuitOn mem _

/-- The scan uses exactly one gate per memory cell, so its gate count is `N`, which is
bounded by the `Õ(N)` ledger `N · (log N + 1)` of Proposition 2.2. -/
theorem prop22_scan_gate_overhead (mem : I → ZMod 2) :
    GateCount (scanCircuit mem) = Fintype.card I ∧
      GateCount (scanCircuit mem) ≤ Fintype.card I * (Nat.log 2 (Fintype.card I) + 1) := by
  refine ⟨by rw [scanCircuit, gateCount_scanCircuitOn, Finset.length_toList, Finset.card_univ], ?_⟩
  rw [scanCircuit, gateCount_scanCircuitOn, Finset.length_toList, Finset.card_univ]
  simpa using Nat.mul_le_mul_left (Fintype.card I)
    (Nat.le_add_left 1 (Nat.log 2 (Fintype.card I)))

end Qatlib.Papers.DihedralHSP13.MainResults.MachineModel
