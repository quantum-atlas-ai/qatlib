/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.HiddenSubgroupRepetition
import Qatlib.Concepts.HspRecovery.BackendAudit.FiniteAbelianDuality
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Concepts.HspRecovery.Distinguisher

namespace Qatlib.Concepts.HspRecovery.BackendAudit

open Matrix
open scoped Classical

section TableScan

variable {G : Type} [Fintype G] [DecidableEq G]

def tableCandidateScan (tab : G → G → Bool) (x : G) : List G → Bool × ℕ
  | [] => (true, 0)
  | a :: xs =>
    let hit := tab a x
    let rest := tableCandidateScan tab x xs
    (hit && rest.1, rest.2 + 1)

private theorem tableCandidateScan_spec (tab : G → G → Bool) (x : G) (xs : List G) :
    (tableCandidateScan tab x xs).1 = true ↔ ∀ a ∈ xs, tab a x = true := by
  induction xs with
  | nil => simp [tableCandidateScan]
  | cons a xs ih => simp [tableCandidateScan, ih]

private theorem tableCandidateScan_reads (tab : G → G → Bool) (x : G) (xs : List G) :
    (tableCandidateScan tab x xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [tableCandidateScan] using congrArg Nat.succ ih

private def tableScanMerge (a b : Finset G × ℕ) : Finset G × ℕ :=
  (a.1 ∪ b.1, a.2 + b.2)

private instance : Std.Commutative (tableScanMerge (G := G)) :=
  ⟨fun a b => Prod.ext (Finset.union_comm a.1 b.1) (Nat.add_comm a.2 b.2)⟩

private instance : Std.Associative (tableScanMerge (G := G)) :=
  ⟨fun a b c => Prod.ext (Finset.union_assoc a.1 b.1 c.1) (Nat.add_assoc a.2 b.2 c.2)⟩

def tableEnumeratedScan (tab : G → G → Bool) (xs : List G) (candidates : Finset G) :
    Finset G × ℕ :=
  candidates.fold tableScanMerge (∅, 0) fun x =>
    let row := tableCandidateScan tab x xs
    (if row.1 then {x} else ∅, row.2)

private theorem tableEnumeratedScan_mem (tab : G → G → Bool) (xs : List G)
    (candidates : Finset G) (x : G) :
    x ∈ (tableEnumeratedScan tab xs candidates).1 ↔
      x ∈ candidates ∧ ∀ a ∈ xs, tab a x = true := by
  induction candidates using Finset.induction_on with
  | empty => simp [tableEnumeratedScan]
  | @insert y candidates hy ih =>
    simp only [tableEnumeratedScan] at ih ⊢
    rw [Finset.fold_insert hy]
    by_cases hrow : (tableCandidateScan tab y xs).1 = true
    · have hrows := (tableCandidateScan_spec tab y xs).mp hrow
      by_cases hxy : x = y <;> simp_all [tableScanMerge]
    · have hrows := (tableCandidateScan_spec tab y xs).not.mp hrow
      by_cases hxy : x = y <;> simp_all [tableScanMerge]

private theorem tableEnumeratedScan_reads (tab : G → G → Bool) (xs : List G)
    (candidates : Finset G) :
    (tableEnumeratedScan tab xs candidates).2 = candidates.card * xs.length := by
  induction candidates using Finset.induction_on with
  | empty => simp [tableEnumeratedScan]
  | @insert x candidates hx ih =>
    simp only [tableEnumeratedScan] at ih ⊢
    simp only [tableCandidateScan_reads] at ih
    rw [Finset.fold_insert hx]
    simp [tableScanMerge, tableCandidateScan_reads, ih, Finset.card_insert_of_notMem hx,
      Nat.add_mul, Nat.add_comm]

def tableKernelDecode (tab : G → G → Bool) (xs : List G) : Finset G × ℕ :=
  tableEnumeratedScan tab xs Finset.univ

theorem mem_tableKernelDecode (tab : G → G → Bool) (xs : List G) (x : G) :
    x ∈ (tableKernelDecode tab xs).1 ↔ ∀ a ∈ xs, tab a x = true := by
  simp [tableKernelDecode, tableEnumeratedScan_mem]

theorem tableKernelDecode_reads (tab : G → G → Bool) (xs : List G) :
    (tableKernelDecode tab xs).2 = Fintype.card G * xs.length := by
  simp [tableKernelDecode, tableEnumeratedScan_reads]

end TableScan

section ActualRecords

variable {G R : Type}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

noncomputable def tableGroupRecordDist (f : G → R) (e : G ≃ AddChar G ℂ) : FinDist G where
  prob a := (hiddenSubgroupSampleDist f e).prob (e a)
  nonneg a := (hiddenSubgroupSampleDist f e).nonneg (e a)
  sum_one := by
    show (∑ a : G, (hiddenSubgroupSampleDist f e).prob (e a)) = 1
    rw [e.sum_comp (fun χ => (hiddenSubgroupSampleDist f e).prob χ)]
    exact (hiddenSubgroupSampleDist f e).sum_one

noncomputable def tableSamplingCircuit (e : G ≃ AddChar G ℂ) (A : Matrix G G ℂ) :
    Circuit (G × R) :=
  Step.gate (TensorGate A 1) :: hiddenSubgroupSamplingCircuit (R := R) e

theorem tableSamplingCircuit_resources (e : G ≃ AddChar G ℂ) (A : Matrix G G ℂ) :
    QueryCount (tableSamplingCircuit (R := R) e A) = 1 ∧
      GateCount (tableSamplingCircuit (R := R) e A) = 2 := by
  exact ⟨rfl, rfl⟩

theorem tableSamplingCircuit_unitary (e : G ≃ AddChar G ℂ) (A : Matrix G G ℂ)
    (hA : A ∈ Matrix.unitaryGroup G ℂ) :
    IsUnitaryCircuit (tableSamplingCircuit (R := R) e A) := by
  rw [tableSamplingCircuit, isUnitaryCircuit_gate]
  exact ⟨tensorGate_unitary hA (Submonoid.one_mem _), hiddenSubgroupSamplingCircuit_unitary e⟩

theorem run_tableSamplingCircuit (e : G ≃ AddChar G ℂ) (A : Matrix G G ℂ) (f : G → R)
    (hprep : A *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : G) = Uniform G) :
    Run (AddOracle f) (tableSamplingCircuit (R := R) e A)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : G)) (Qatlib.Foundations.PureStateMath.Ket (0 : R))) =
      Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
        (TensorState (Uniform G) (Qatlib.Foundations.PureStateMath.Ket (0 : R))) := by
  rw [tableSamplingCircuit, run_gate, applyGate_tensorGate]
  have hone :
      ApplyGate (1 : Matrix R R ℂ)
      (Qatlib.Foundations.PureStateMath.Ket (0 : R)) = Qatlib.Foundations.PureStateMath.Ket (0 : R) := Matrix.one_mulVec _
  rw [hone]
  have hA : ApplyGate A (Qatlib.Foundations.PureStateMath.Ket (0 : G)) = Uniform G := by
    show A *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : G) = Uniform G
    exact hprep
  rw [hA]

end ActualRecords

end Qatlib.Concepts.HspRecovery.BackendAudit

namespace Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open Matrix
open scoped Classical

variable {G R : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

theorem character_table_actual_decoder_and_reads (tab : G → G → Bool) (xs : List G) :
    (∀ x : G, x ∈ (tableKernelDecode tab xs).1 ↔ ∀ a ∈ xs, tab a x = true) ∧
      (tableKernelDecode tab xs).2 = Fintype.card G * xs.length :=
  ⟨mem_tableKernelDecode tab xs, tableKernelDecode_reads tab xs⟩

theorem character_table_actual_fourier_record_relabel (f : G → R) (e : G ≃ AddChar G ℂ)
    (a : G) :
    (tableGroupRecordDist f e).prob a = (hiddenSubgroupSampleDist f e).prob (e a) :=
  rfl

theorem character_table_hiding_subgroup_never_removed (tab : G → G → Bool)
    (e : G ≃ AddChar G ℂ) (H : AddSubgroup G) (xs : List G)
    (htab : ∀ a x, tab a x = true ↔ e a x = 1)
    (hsupported : ∀ a ∈ xs, e a ∈ characterAnnihilator H) :
    ∀ x : G, x ∈ H → x ∈ (tableKernelDecode tab xs).1 := by
  intro x hx
  rw [mem_tableKernelDecode]
  intro a ha
  exact (htab a x).2 ((mem_characterAnnihilator H (e a)).1 (hsupported a ha) ⟨x, hx⟩)

theorem character_table_actual_preparation_and_resource_bridge (e : G ≃ AddChar G ℂ)
    (A : Matrix G G ℂ) (f : G → R) (hA : A ∈ Matrix.unitaryGroup G ℂ)
    (hprep : A *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : G) = Uniform G) :
    IsUnitaryCircuit (tableSamplingCircuit (R := R) e A) ∧
      QueryCount (tableSamplingCircuit (R := R) e A) = 1 ∧
      GateCount (tableSamplingCircuit (R := R) e A) = 2 ∧
      Run (AddOracle f) (tableSamplingCircuit (R := R) e A)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : G)) (Qatlib.Foundations.PureStateMath.Ket (0 : R))) =
        Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
          (TensorState (Uniform G) (Qatlib.Foundations.PureStateMath.Ket (0 : R))) :=
  ⟨tableSamplingCircuit_unitary (R := R) e A hA,
    (tableSamplingCircuit_resources (R := R) e A).1,
    (tableSamplingCircuit_resources (R := R) e A).2,
    run_tableSamplingCircuit (R := R) e A f hprep⟩

end Qatlib.Concepts.HspRecovery.BackendAudit
