/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.Stride
import Qatlib.Papers.MonteCarloInt20.MainResults.FiniteTermCode
import Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation

/-!
# PRN-based finite inner oracles

This module assembles the data registers, reversible term queries, and stride-indexed PRN
computations used by the inner preparation for [KanekoEtAl2020]. `innerBody` prepares a uniform
coordinate superposition, rotates the flag by the decoded term value, and reverses the data
computation.

The matrix is unitary, and `innerBody_flag_born` identifies its true-flag probability with the
explicit finite average `termMean`.

## Main statements

* `dataCompute_basis`: identifies the computed PRN frame and term code.
* `innerBody_unitary`: establishes unitarity of the inner preparation.
* `innerBody_flag_born`: relates flag measurement to `termMean`.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Papers.MonteCarloInt20.PrnJump.Frame
open Qatlib.Papers.MonteCarloInt20.MainResults.TermCode Qatlib.Papers.MonteCarloInt20.PrnJump.Stride
open Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation

namespace Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle

/-- The native PRN workspace paired with a `p + 1`-bit term-code register. -/
abbrev Data (n k p : ℕ) := Reg (width n k) × Reg (p+1)

/-- Preserve the native workspace and XOR the sample- and coordinate-specific term code at its
decoded residue into the code register. -/
def dataQueryUpdate {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d)
    (v : Data n k p) : Data n k p :=
  (v.1,fun q => v.2 q ^^ codeBits (termCode j i (decodeNative n k v.1)) q)

/-- Applying the data term-query XOR update twice restores the original data registers. -/
theorem dataQueryUpdate_involutive {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) :
    Function.Involutive (dataQueryUpdate (k:=k) termCode j i) := by
  intro v
  apply Prod.ext
  · rfl
  · funext q
    simp [dataQueryUpdate]

/-- The permutation matrix implementing a term-code query on the data registers at fixed sample
and coordinate. -/
def dataQuery {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) :
    Matrix (Data n k p) (Data n k p) ℂ := permMatrix (dataQueryUpdate (k:=k) termCode j i)

/-- The data term-query matrix is unitary. -/
theorem dataQuery_unitary {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) :
    dataQuery (k:=k) termCode j i ∈ unitaryGroup (Data n k p) ℂ :=
  permMatrix_unitary (dataQueryUpdate_involutive termCode j i)

/-- On a framed residue with zero code register, the data query writes the corresponding term
code and preserves the frame. -/
theorem dataQuery_clean {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d)
    (bits : Reg k) (x : ZMod (2^n)) :
    ApplyGate (dataQuery termCode j i) (Ket (frame bits x,ZeroStr (p+1)))=
      Ket (frame bits x,codeBits (termCode j i x)) := by
  rw [dataQuery,applyGate_permMatrix_ket (dataQueryUpdate_involutive termCode j i)]
  simp only [dataQueryUpdate,decodeNative_frame,ZeroStr,Bool.false_xor]

/-- The term-query oracle is the coordinate-selected family of data-query matrices. -/
theorem queryOracle_eq_select {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    queryOracle (k:=k) termCode j=select (fun i => dataQuery (k:=k) termCode j i) := by
  ext ⟨i,r,q⟩ ⟨i',r',q'⟩
  by_cases hi : i=i'
  · subst i'
    simp [queryOracle,queryEquiv,queryUpdate,dataQuery,dataQueryUpdate,permMatrix,select]
  · simp [queryOracle,queryEquiv,queryUpdate,dataQuery,dataQueryUpdate,permMatrix,select,hi]

/-- The LCG residue reached from `seed` at the sample-coordinate position `position j i`. -/
def residue {n s d : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) (i : Reg d) : ZMod (2^n) :=
  lcg (a:ZMod (2^n)) c seed (position j i)

/-- The matrix that computes the stride-indexed PRN frame and then queries the corresponding
finite term code. -/
def dataCompute {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) :
    Matrix (Data n (s+d+1) p) (Data n (s+d+1) p) ℂ :=
  dataQuery termCode j i*TensorGate (strideCompute a c seed j i) 1

/-- The combined PRN and term-code data computation is unitary. -/
theorem dataCompute_unitary {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) :
    dataCompute a c seed termCode j i ∈ unitaryGroup (Data n (s+d+1) p) ℂ :=
  (unitaryGroup _ ℂ).mul_mem (dataQuery_unitary termCode j i)
    (tensorGate_unitary (strideCompute_unitary a c seed j i) (by simp))

/-- The initial data configuration with zero exponent bits, the given PRN seed, and a zero
term-code word. -/
def dataSeed (n s d p : ℕ) (seed : ZMod (2^n)) : Data n (s+d+1) p :=
  (frame (ZeroStr (s+d+1)) seed,ZeroStr (p+1))

/-- The computed data configuration containing the sample-coordinate exponent bits, the
corresponding LCG residue, and its term code. -/
def computedData {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) : Data n (s+d+1) p :=
  (frame (exponentBits j i) (residue a c seed j i),codeBits (termCode j i (residue a c seed j i)))

/-- For positive coordinate width, the data computation maps its initial seed basis state to
`computedData`. -/
theorem dataCompute_basis {n s d p : ℕ} (hd : 0 < d)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) :
    ApplyGate (dataCompute a c seed termCode j i) (Ket (dataSeed n s d p seed))=
      Ket (computedData a c seed termCode j i) := by
  rw [dataCompute,applyGate_mul,dataSeed,← tensorState_ket_ket,applyGate_tensorGate,
    strideCompute_basis hd,applyGate_one,tensorState_ket_ket,dataQuery_clean]
  rfl

/-- The coordinate and data registers paired with the Boolean output flag for the inner
preparation. -/
abbrev BodyReg (n s d p : ℕ) := (Reg d × Data n (s+d+1) p) × Bool

/-- The clean flag preparation controlled by the finite decoded term value after
coordinate-selected PRN and term computation. -/
def innerBody {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ :=
  cleanFlagPreparation d (dataCompute a c seed termCode j) (fun v => decodeCode p v.2.2)

/-- The PRN-based inner body matrix is unitary. -/
theorem innerBody_unitary {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    innerBody a c seed termCode j ∈ unitaryGroup (BodyReg n s d p) ℂ :=
  cleanFlagPreparation_unitary d _ (dataCompute_unitary a c seed termCode j) _
    (fun v => decodeCode_bounds p v.2.2)

/-- The initial inner body configuration with zero coordinate bits, the data seed, and a false
flag. -/
def bodySeed (n s d p : ℕ) (seed : ZMod (2^n)) : BodyReg n s d p :=
  ((ZeroStr d,dataSeed n s d p seed),false)

/-- The uniform coordinate average of the finite term codes evaluated at the sample-coordinate
LCG residues and scaled by `2 ^ p`. -/
def termMean {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) : ℝ :=
  (1/(2:ℝ)^d)*∑ i : Reg d,((termCode j i (residue a c seed j i)).val:ℝ)/(2:ℝ)^p

/-- For positive coordinate width, the true-flag probability of the inner preparation from
`bodySeed` equals `termMean`. -/
theorem innerBody_flag_born {n s d p : ℕ} (hd : 0 < d)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    MeasureProb (ApplyGate (innerBody a c seed termCode j) (Ket (bodySeed n s d p seed)))
      (Finset.univ.filter (fun v => v.2=true))=termMean a c seed termCode j := by
  have h := cleanFlagPreparation_born d (dataCompute a c seed termCode j)
    (dataCompute_unitary a c seed termCode j) (dataSeed n s d p seed)
    (computedData a c seed termCode j) (dataCompute_basis hd a c seed termCode j)
    (fun v => decodeCode p v.2.2) (fun v => decodeCode_bounds p v.2.2)
  simpa only [innerBody,bodySeed,computedData,decodeCode_codeBits,termMean] using! h

end Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
