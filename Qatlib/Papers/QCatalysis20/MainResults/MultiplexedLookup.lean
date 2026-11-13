/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCatalysis20.MainResults.Definitions
import Qatlib.Foundations.TableAccess.ReversibleTable

/-!
# Five-stage multiplexed XOR lookup

This module implements prefix computation, address addition, table query, subtraction, and
prefix erasure on finite bit-vector registers. It proves register restoration, involutivity, and
unitarity of the associated permutation matrix, including its action with an external reference
register. See [VonBurgEtAl2021].

## Main statements

* `actual_five_stage_lookup`: For a table agreeing with the desired data at flattened addresses,
  lookup from a zero workspace XORs the selected entry into the target and preserves all other
  registers.
* `lookupMatrix_unitary`: The permutation matrix of the five-stage lookup is unitary.
* `lookupWord_counts`: The lookup word contains one query, two prefix operations, and two
  arithmetic operations.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators
local instance (w : ℕ) : Fintype (BitVec w) :=
    Fintype.ofInjective BitVec.toFin BitVec.toFin_injective
open Qatlib.Foundations.TableAccess.ReversibleTable

namespace Qatlib.Papers.QCatalysis20.MainResults

/-- A valid ragged-table address together with address workspace, target, and dirty bit-vector
registers. -/
abbrev LookupState (J a b d : ℕ) (K : ℕ→ℕ) :=
  (Σ j : Fin J,Fin (K j)) × BitVec a × BitVec b × BitVec d

/-- The five stage labels for prefix computation, addition, query, subtraction, and prefix
erasure. -/
inductive LookupStage | prefix | add | query | subtract | unprefix
  deriving DecidableEq, Repr

/-- The ordered list of stages implementing the five-stage multiplexed lookup. -/
def lookupWord : List LookupStage := [.prefix,.add,.query,.subtract,.unprefix]

/-- Execute one lookup stage on the finite registers using the supplied bit-vector table. -/
def runLookupStage {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (g : LookupStage) (s : LookupState J a b d K) : LookupState J a b d K :=
  let ⟨jk,w,z,dirty⟩ := s
  let pre := BitVec.ofNat a (prefixOffset K jk.1.val)
  let k := BitVec.ofNat a jk.2.val
  match g with
  | .prefix => (jk,w ^^^ pre,z,dirty)
  | .add => (jk,w+k,z,dirty)
  | .query => (jk,w,z ^^^ table w,dirty)
  | .subtract => (jk,w-k,z,dirty)
  | .unprefix => (jk,w ^^^ pre,z,dirty)

/-- Execute the complete five-stage lookup by folding over `lookupWord`. -/
def runLookup {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (s : LookupState J a b d K) : LookupState J a b d K :=
  lookupWord.foldl (fun q g=>runLookupStage table g q) s

/-- The lookup restores the address workspace and dirty register and XORs the table value at the
computed temporary address into the target. See [VonBurgEtAl2021]. -/
theorem runLookup_registers {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (jk : Σ j : Fin J,Fin (K j)) (w : BitVec a) (z : BitVec b) (dirty : BitVec d) :
    runLookup table (jk,w,z,dirty)=
      (jk,w,z ^^^ table ((w ^^^ BitVec.ofNat a (prefixOffset K jk.1.val))+BitVec.ofNat a jk.2.val),dirty) := by
  simp [runLookup,lookupWord,runLookupStage,BitVec.xor_assoc]

/-- Executing the complete lookup twice returns every register to its original value. -/
theorem runLookup_involutive {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b) :
    Function.Involutive (runLookup (J:=J) (d:=d) (K:=K) table) := by
  rintro ⟨jk,w,z,dirty⟩
  simp only [runLookup_registers]
  simp [BitVec.xor_assoc]

/-- For a table agreeing with the desired data at flattened addresses, lookup from a zero
workspace XORs the selected entry into the target and preserves all other registers. -/
theorem actual_five_stage_lookup {J a b d : ℕ} {K : ℕ→ℕ}
    (table : BitVec a→BitVec b) (x : (j : Fin J)→Fin (K j)→BitVec b)
    (hdata : ∀(j : Fin J)(k : Fin (K j)),
      table (BitVec.ofNat a (multiplexedIndex K j.val k.val))=x j k)
    (j : Fin J) (k : Fin (K j)) (z : BitVec b) (dirty : BitVec d) :
    runLookup table (⟨j,k⟩,0#a,z,dirty)=(⟨j,k⟩,0#a,z ^^^ x j k,dirty) := by
  rw [runLookup_registers]
  simp only [BitVec.zero_xor]
  have hd : table (BitVec.ofNat a (prefixOffset K j.val+k.val))=x j k := hdata j k
  rw [← BitVec.ofNat_add,hd]

/-- The permutation matrix associated with the complete finite-register lookup. -/
def lookupMatrix {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b) :
    Matrix (LookupState J a b d K) (LookupState J a b d K) ℂ :=
  permMatrix (runLookup table)

/-- The permutation matrix of the five-stage lookup is unitary. See [VonBurgEtAl2021]. -/
theorem lookupMatrix_unitary {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b) :
    lookupMatrix (J:=J) (d:=d) (K:=K) table∈Matrix.unitaryGroup _ ℂ :=
  permMatrix_unitary (runLookup_involutive table)

/-- The lookup matrix sends the basis ket of a register state to the basis ket of its computed
output. -/
theorem lookupMatrix_basis {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (s : LookupState J a b d K) :
    lookupMatrix table *ᵥ Ket s=Ket (runLookup table s) :=
  applyGate_permMatrix_ket (runLookup_involutive table) s

/-- With an untouched finite reference register, the lookup permutation acts on amplitudes by
precomposition with the register lookup. See [VonBurgEtAl2021]. -/
theorem lookup_reference {R : Type*} [Fintype R] [DecidableEq R]
    {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (ψ : R×LookupState J a b d K→ℂ) :
    permMatrix (fun p:R×LookupState J a b d K=>(p.1,runLookup table p.2)) *ᵥ ψ=
      fun p=>ψ (p.1,runLookup table p.2) := by
  funext p
  exact applyGate_permMatrix (fun v=>by simp only [runLookup_involutive table v.2]) ψ p

/-- The lookup word contains one query, two prefix operations, and two arithmetic operations.
See [VonBurgEtAl2021]. -/
theorem lookupWord_counts :
    (lookupWord.count .query=1) ∧
    (lookupWord.count .prefix+lookupWord.count .unprefix=2) ∧
    (lookupWord.count .add+lookupWord.count .subtract=2) := by decide

/-- If the total entry count is zero, the type of valid ragged-table address pairs is empty. -/
theorem no_empty_address {J : ℕ} {K : ℕ→ℕ} (hQ : totalEntries J K=0) :
    IsEmpty (Σ j : Fin J,Fin (K j)) := by
  refine ⟨fun jk=>?_⟩
  have h:=multiplexedIndex_lt_total jk.1.isLt jk.2.isLt
  omega

end Qatlib.Papers.QCatalysis20.MainResults
