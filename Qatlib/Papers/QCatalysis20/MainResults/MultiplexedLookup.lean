/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCatalysis20.MainResults.Definitions
import Qatlib.Foundations.TableAccess.ReversibleTable
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators
local instance (w : ℕ) : Fintype (BitVec w) :=
    Fintype.ofInjective BitVec.toFin BitVec.toFin_injective
open Qatlib.Foundations.TableAccess.ReversibleTable

namespace Qatlib.Papers.QCatalysis20.MainResults

abbrev LookupState (J a b d : ℕ) (K : ℕ→ℕ) :=
  (Σ j : Fin J,Fin (K j)) × BitVec a × BitVec b × BitVec d

inductive LookupStage | prefix | add | query | subtract | unprefix
  deriving DecidableEq, Repr

def lookupWord : List LookupStage := [.prefix,.add,.query,.subtract,.unprefix]

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

def runLookup {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (s : LookupState J a b d K) : LookupState J a b d K :=
  lookupWord.foldl (fun q g=>runLookupStage table g q) s

theorem runLookup_registers {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (jk : Σ j : Fin J,Fin (K j)) (w : BitVec a) (z : BitVec b) (dirty : BitVec d) :
    runLookup table (jk,w,z,dirty)=
      (jk,w,z ^^^ table ((w ^^^ BitVec.ofNat a (prefixOffset K jk.1.val))+BitVec.ofNat a jk.2.val),dirty) := by
  simp [runLookup,lookupWord,runLookupStage,BitVec.xor_assoc]

theorem runLookup_involutive {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b) :
    Function.Involutive (runLookup (J:=J) (d:=d) (K:=K) table) := by
  rintro ⟨jk,w,z,dirty⟩
  simp only [runLookup_registers]
  simp [BitVec.xor_assoc]

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

def lookupMatrix {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b) :
    Matrix (LookupState J a b d K) (LookupState J a b d K) ℂ :=
  permMatrix (runLookup table)

theorem lookupMatrix_unitary {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b) :
    lookupMatrix (J:=J) (d:=d) (K:=K) table∈Matrix.unitaryGroup _ ℂ :=
  permMatrix_unitary (runLookup_involutive table)

theorem lookupMatrix_basis {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (s : LookupState J a b d K) :
    lookupMatrix table *ᵥ Ket s=Ket (runLookup table s) :=
  applyGate_permMatrix_ket (runLookup_involutive table) s

theorem lookup_reference {R : Type*} [Fintype R] [DecidableEq R]
    {J a b d : ℕ} {K : ℕ→ℕ} (table : BitVec a→BitVec b)
    (ψ : R×LookupState J a b d K→ℂ) :
    permMatrix (fun p:R×LookupState J a b d K=>(p.1,runLookup table p.2)) *ᵥ ψ=
      fun p=>ψ (p.1,runLookup table p.2) := by
  funext p
  exact applyGate_permMatrix (fun v=>by simp only [runLookup_involutive table v.2]) ψ p

theorem lookupWord_counts :
    (lookupWord.count .query=1) ∧
    (lookupWord.count .prefix+lookupWord.count .unprefix=2) ∧
    (lookupWord.count .add+lookupWord.count .subtract=2) := by decide

theorem no_empty_address {J : ℕ} {K : ℕ→ℕ} (hQ : totalEntries J K=0) :
    IsEmpty (Σ j : Fin J,Fin (K j)) := by
  refine ⟨fun jk=>?_⟩
  have h:=multiplexedIndex_lt_total jk.1.isLt jk.2.isLt
  omega

end Qatlib.Papers.QCatalysis20.MainResults
