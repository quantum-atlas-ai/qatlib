/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
import Qatlib.Papers.MonteCarloInt20.MainResults.CleanWorkspace
import Qatlib.Papers.MonteCarloInt20.MainResults.InnerValidity

/-!
# Reversible storage of coordinate term codes

`storeCircuit` prepares a sample-coordinate PRN address, queries its term code, XORs the code
into coordinate-indexed storage, and reverses the temporary computation. This gives a reversible
storage step for the sequential finite Monte Carlo construction associated with
[KanekoEtAl2020].

The basis-action theorem makes workspace restoration explicit. Each step uses two term queries
and three known gates at this circuit abstraction.

## Main statements

* `prepareAddress_basis`: computes the selected coordinate and PRN frame.
* `storeCircuit_basis`: stores one code and restores the temporary workspace.
* `storeCircuit_counts`: counts two queries and three known gates.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Papers.MonteCarloInt20.PrnJump.Stride
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
open Qatlib.Papers.MonteCarloInt20.MainResults.Cleanup
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Papers.MonteCarloInt20.MainResults.TermCode

namespace Qatlib.Papers.MonteCarloInt20.MainResults.SequentialStore

/-- A coordinate-indexed family of `p + 1`-bit term-code words. -/
abbrev Codes (d p : ℕ) := Reg d → Reg (p+1)

/-- The coordinate and native data workspace paired with the stored family of term codes. -/
abbrev Work (n s d p : ℕ) := (Reg d × Data n (s+d+1) p) × Codes d p
noncomputable local instance workDecision (n s d p : ℕ) : DecidableEq (Work n s d p) :=
    instDecidableEqProd
noncomputable local instance queryDecision (n s d p : ℕ) :
    DecidableEq (Reg d × Data n (s+d+1) p) := instDecidableEqProd

/-- The sample-specific finite term-query oracle extended by the identity on the stored code
family. -/
def oracle {n s d p : ℕ} (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    Matrix (Work n s d p) (Work n s d p) ℂ := TensorGate (queryOracle (k:=s+d+1) termCode j) 1

/-- The sequential storage oracle equals its conjugate transpose. -/
theorem oracle_selfadjoint {n s d p : ℕ} (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    (oracle termCode j).conjTranspose=oracle termCode j := by
  rw [oracle,tensorGate_conjTranspose,queryOracle_selfadjoint,Matrix.conjTranspose_one]

/-- XOR the requested coordinate into the coordinate register and perform its selected
stride-indexed PRN computation. -/
def prepareAddress {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    Matrix (Reg d × Data n (s+d+1) p) (Reg d × Data n (s+d+1) p) ℂ :=
  select (fun q : Reg d => TensorGate (strideCompute a c seed j q) (1:Matrix (Reg (p+1)) (Reg (p+1)) ℂ))*
    TensorGate (xorMatrix i) 1

/-- The coordinate and PRN address preparation matrix is unitary. -/
theorem prepareAddress_unitary {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    prepareAddress (p:=p) a c seed j i ∈ unitaryGroup (Reg d × Data n (s+d+1) p) ℂ :=
  (unitaryGroup _ ℂ).mul_mem
    (select_unitary _ (fun q => tensorGate_unitary (strideCompute_unitary a c seed j q) (unitaryGroup (Reg (p+1)) ℂ).one_mem))
    (tensorGate_unitary (xorMatrix_unitary i) (unitaryGroup (Data n (s+d+1) p) ℂ).one_mem)

/-- For positive coordinate width, address preparation maps the zero coordinate and data seed to
the requested coordinate and its computed PRN frame, leaving the code word zero. -/
theorem prepareAddress_basis {n s d p : ℕ} (hd : 0 < d) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    ApplyGate (prepareAddress (p:=p) a c seed j i) (Ket (ZeroStr d,dataSeed n s d p seed))=
      Ket (i,(frame (exponentBits j i) (residue a c seed j i),ZeroStr (p+1))) := by
  have hx : ApplyGate (xorMatrix i) (Ket (ZeroStr d))=Ket i := by
    simpa only [ZeroStr,Bool.xor_false] using! xorMatrix_frame (ZeroStr d) i
  rw [prepareAddress,applyGate_mul,← tensorState_ket_ket,applyGate_tensorGate,hx,applyGate_one,tensorState_ket_ket,
    select_basis]
  rw [dataSeed,← tensorState_ket_ket,applyGate_tensorGate,strideCompute_basis hd,applyGate_one,tensorState_ket_ket,tensorState_ket_ket]
  rfl

/-- Preserve the query workspace and XOR its current term-code word into storage at the current
coordinate. -/
def copyCode {n s d p : ℕ} (v : Work n s d p) : Work n s d p :=
  (v.1,Function.update v.2 v.1.1 (fun b => v.2 v.1.1 b ^^ v.1.2.2 b))

/-- Applying the code-storage XOR update twice restores the original workspace and stored codes. -/
theorem copyCode_involutive (n s d p : ℕ) : Function.Involutive (copyCode (n:=n) (s:=s) (d:=d) (p:=p)) := by
  intro v
  apply Prod.ext
  · rfl
  · funext q b
    by_cases h : q=v.1.1 <;> simp [copyCode,h]

/-- The permutation matrix implementing the coordinate-indexed code-storage XOR update. -/
def copyGate (n s d p : ℕ) : Matrix (Work n s d p) (Work n s d p) ℂ := permMatrix copyCode

/-- The circuit that prepares a PRN address, queries and copies a term code, and reverses the
query and address preparation. -/
def storeCircuit {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) : Circuit (Work n s d p) :=
  [.gate (TensorGate (prepareAddress (p:=p) a c seed j i) 1),.query,.gate (copyGate n s d p),.query,
    .gate (TensorGate (prepareAddress (p:=p) a c seed j i).conjTranspose 1)]

/-- A single coordinate-store circuit uses two term queries and three known gates. -/
theorem storeCircuit_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    QueryCount (storeCircuit (p:=p) a c seed j i)=2 ∧ GateCount (storeCircuit (p:=p) a c seed j i)=3 := by
  constructor <;> rfl

/-- For positive coordinate width, the store circuit XORs the selected PRN-based term code into
its coordinate's stored word and restores the zero coordinate and data seed. -/
theorem storeCircuit_basis {n s d p : ℕ} (hd : 0 < d) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) (v : Codes d p) :
    ApplyGate (runMatrix (oracle termCode j) (storeCircuit (p:=p) a c seed j i))
      (Ket ((ZeroStr d,dataSeed n s d p seed),v))=
      Ket ((ZeroStr d,dataSeed n s d p seed),Function.update v i
        (fun b => v i b ^^ codeBits (termCode j i (residue a c seed j i)) b)) := by
  let x := (ZeroStr d,dataSeed n s d p seed)
  let y := (i,(frame (exponentBits j i) (residue a c seed j i),ZeroStr (p+1)))
  let z :=
      (i,(frame (exponentBits j i) (residue a c seed j i),codeBits (termCode j i (residue a c seed j i))))
  let v' : Codes d p :=
      Function.update v i (fun b => v i b ^^ codeBits (termCode j i (residue a c seed j i)) b)
  have hk : ApplyGate (prepareAddress (p:=p) a c seed j i) (Ket x)=Ket y :=
      prepareAddress_basis hd a c seed j i
  have hq : ApplyGate (queryOracle (k:=s+d+1) termCode j) (Ket y)=Ket z :=
      queryOracle_clean termCode j i _ _
  have hqi : ApplyGate (queryOracle (k:=s+d+1) termCode j) (Ket z)=Ket y := by
    rw [← hq,← applyGate_mul]
    have hU := queryOracle_unitary (k:=s+d+1) termCode j
    have hInv : (queryOracle (k:=s+d+1) termCode j)*(queryOracle (k:=s+d+1) termCode j)=1 := by
      simpa only [Matrix.star_eq_conjTranspose,queryOracle_selfadjoint] using!
          Unitary.star_mul_self_of_mem hU
    rw [hInv,applyGate_one]
  have hki : ApplyGate (prepareAddress (p:=p) a c seed j i).conjTranspose (Ket y)=Ket x := by
    rw [← hk,← applyGate_mul]
    have hInv : (prepareAddress (p:=p) a c seed j i).conjTranspose*prepareAddress (p:=p) a c seed j i=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using!
          Unitary.star_mul_self_of_mem (prepareAddress_unitary (p:=p) a c seed j i)
    rw [hInv,applyGate_one]
  have hc : ApplyGate (copyGate n s d p) (Ket (z,v))=Ket (z,v') := by
    rw [copyGate,applyGate_permMatrix_ket (copyCode_involutive n s d p)]
    rfl
  change ApplyGate (runMatrix (oracle termCode j) (storeCircuit (p:=p) a c seed j i))
      (Ket (x,v))=Ket (x,v')
  simp only [storeCircuit,runMatrix,Matrix.one_mul,oracle,applyGate_mul]
  rw [← tensorState_ket_ket,applyGate_tensorGate,hk,applyGate_one,tensorState_ket_ket,
    ← tensorState_ket_ket,applyGate_tensorGate,hq,applyGate_one,tensorState_ket_ket,hc,
    ← tensorState_ket_ket,applyGate_tensorGate,hqi,applyGate_one,tensorState_ket_ket,
    ← tensorState_ket_ket,applyGate_tensorGate,hki,applyGate_one,tensorState_ket_ket]

/-- The coordinate-store circuit is a unitary circuit. -/
theorem storeCircuit_unitary {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) :
    IsUnitaryCircuit (storeCircuit (p:=p) a c seed j i) := by
  have hK := prepareAddress_unitary (p:=p) a c seed j i
  have hCopy : copyGate n s d p ∈ unitaryGroup (Work n s d p) ℂ :=
      permMatrix_unitary (copyCode_involutive n s d p)
  simp only [storeCircuit,isUnitaryCircuit_gate,isUnitaryCircuit_query,isUnitaryCircuit_nil,and_true]
  exact ⟨tensorGate_unitary hK (unitaryGroup (Codes d p) ℂ).one_mem,
    hCopy,tensorGate_unitary (conjTranspose_mem_unitaryGroup hK) (unitaryGroup (Codes d p) ℂ).one_mem⟩

/-- The sequential term-query oracle on the storage workspace is unitary. -/
theorem oracle_unitary {n s d p : ℕ} (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    oracle termCode j ∈ unitaryGroup (Work n s d p) ℂ :=
  tensorGate_unitary (queryOracle_unitary (k:=s+d+1) termCode j) (unitaryGroup (Codes d p) ℂ).one_mem

end Qatlib.Papers.MonteCarloInt20.MainResults.SequentialStore
