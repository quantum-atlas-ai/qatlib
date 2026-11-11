/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.SequentialStore

/-!
# Sequential loops storing finite term codes

`loopCircuit` concatenates the reversible store circuit over a list of coordinates. `fill`
describes the resulting XOR updates to the stored code family while the address and PRN
workspace are restored after every step.

For `allTerms`, the circuit computes all finite term codes, with two queries and three known
gates per coordinate. This supplies a sequential term-evaluation component for the comparison
with the nested method of [KanekoEtAl2020].

## Main statements

* `loopCircuit_basis`: identifies loop execution with the recursive code update.
* `allTerms_basis`: fills an initially zero code family with every term code.
* `allTerms_counts`: counts the full coordinate loop.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.SequentialStore
open Qatlib.Papers.MonteCarloInt20.MainResults.TermCode
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit

namespace Qatlib.Papers.MonteCarloInt20.MainResults.SequentialLoop

noncomputable local instance workDecision (n s d p : ℕ) : DecidableEq (Work n s d p) :=
    instDecidableEqProd

/-- Concatenate the sample-specific term-store circuits over the supplied coordinate list. -/
def loopCircuit {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s)
    (is : List (Reg d)) : Circuit (Work n s d p) :=
  is.flatMap (storeCircuit (p:=p) a c seed j)

/-- A sequential store loop uses twice the list length in term queries and three times the list
length in known gates. -/
theorem loopCircuit_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (is : List (Reg d)) :
    QueryCount (loopCircuit (p:=p) a c seed j is)=2*is.length ∧
    GateCount (loopCircuit (p:=p) a c seed j is)=3*is.length := by
  induction is with
  | nil => exact ⟨rfl,rfl⟩
  | cons i is ih =>
    simp only [loopCircuit,List.flatMap_cons,queryCount_append,gateCount_append,List.length_cons]
    change 2+QueryCount (loopCircuit (p:=p) a c seed j is)=2*(is.length+1) ∧
      3+GateCount (loopCircuit (p:=p) a c seed j is)=3*(is.length+1)
    rw [ih.1,ih.2]
    constructor <;> omega

/-- Process a coordinate list by XORing the prescribed code into the stored word at each visited
coordinate. -/
def fill {d p : ℕ} (codes : Codes d p) : List (Reg d) → Codes d p → Codes d p
  | [],v => v
  | i::is,v => fill codes is (Function.update v i (fun b => v i b ^^ codes i b))

/-- For a list without repeated coordinates, `fill` XORs the prescribed code exactly at
coordinates in the list and leaves the others unchanged. -/
theorem fill_nodup {d p : ℕ} (codes : Codes d p) (is : List (Reg d)) (h : is.Nodup) (v : Codes d p) (q : Reg d) (b : Fin (p+1)) :
    fill codes is v q b=if q∈is then v q b ^^ codes q b else v q b := by
  induction is generalizing v with
  | nil => simp [fill]
  | cons i is ih =>
    rw [fill,ih h.tail]
    by_cases hq : q=i
    · subst q
      simp [(List.nodup_cons.mp h).1,Function.update]
    · by_cases hi : q∈is <;> simp [hq,hi]

/-- For positive coordinate width, the store loop restores its address and data seed and applies
`fill` with the PRN-based term codes to the stored code family. -/
theorem loopCircuit_basis {n s d p : ℕ} (hd : 0 < d) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (is : List (Reg d)) (v : Codes d p) :
    ApplyGate (runMatrix (oracle termCode j) (loopCircuit (p:=p) a c seed j is))
      (Ket ((ZeroStr d,dataSeed n s d p seed),v))=
      Ket ((ZeroStr d,dataSeed n s d p seed),
        fill (fun i => codeBits (termCode j i (residue a c seed j i))) is v) := by
  induction is generalizing v with
  | nil => rw [loopCircuit,List.flatMap_nil,runMatrix,applyGate_one]; rfl
  | cons i is ih =>
    rw [loopCircuit,List.flatMap_cons,runMatrix_append,applyGate_mul,storeCircuit_basis hd]
    exact ih _

/-- A list enumerating every `d`-bit coordinate. -/
def allTerms (d : ℕ) : List (Reg d) := Finset.univ.toList

/-- For positive coordinate width, the complete coordinate loop fills an initially zero code
family with the PRN-based term codes and restores the address and data seed
[KanekoEtAl2020]. -/
theorem allTerms_basis {n s d p : ℕ} (hd : 0 < d) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    ApplyGate (runMatrix (oracle termCode j) (loopCircuit (p:=p) a c seed j (allTerms d)))
      (Ket ((ZeroStr d,dataSeed n s d p seed),fun _ => ZeroStr (p+1)))=
      Ket ((ZeroStr d,dataSeed n s d p seed),fun i => codeBits (termCode j i (residue a c seed j i))) := by
  rw [loopCircuit_basis hd]
  congr 2
  funext q b
  unfold allTerms
  rw [fill_nodup _ _ (Finset.nodup_toList (Finset.univ : Finset (Reg d)))]
  simp [ZeroStr]

/-- The full coordinate store loop uses `2 * 2 ^ d` term queries and `3 * 2 ^ d` known gates. -/
theorem allTerms_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    QueryCount (loopCircuit (p:=p) a c seed j (allTerms d))=2*2^d ∧
    GateCount (loopCircuit (p:=p) a c seed j (allTerms d))=3*2^d := by
  have h : (allTerms d).length=2^d := by simp [allTerms,Reg]
  simpa only [h] using! loopCircuit_counts (p:=p) a c seed j (allTerms d)

/-- Every sequential store loop is a unitary circuit. -/
theorem loopCircuit_unitary {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (is : List (Reg d)) :
    IsUnitaryCircuit (loopCircuit (p:=p) a c seed j is) := by
  induction is with
  | nil => exact isUnitaryCircuit_nil
  | cons i is ih =>
    rw [loopCircuit,List.flatMap_cons,isUnitaryCircuit_append]
    exact ⟨storeCircuit_unitary (p:=p) a c seed j i,ih⟩

end Qatlib.Papers.MonteCarloInt20.MainResults.SequentialLoop
