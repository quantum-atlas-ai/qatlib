/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.FrameDecode
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Qatlib.Concepts.HspRecovery.RecordExtract
open scoped Classical
namespace Qatlib.Papers.MonteCarloInt20.MainResults.TermCode
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled Qatlib.Papers.MonteCarloInt20.PrnJump.Frame

def codeBits {p : ℕ} (v : Fin (2^p+1)) : Reg (p+1) :=
  Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits.ofNat (p+1) v.val

noncomputable def decodeCode (p : ℕ) (bits : Reg (p+1)) : ℝ :=
  min 1 ((booleanWordLSBValue (p+1) bits : ℝ)/(2^p : ℝ))

theorem decodeCode_bounds (p : ℕ) (bits : Reg (p+1)) :
    0 ≤ decodeCode p bits ∧ decodeCode p bits ≤ 1 := by
  constructor
  · exact le_min (by norm_num) (by positivity)
  · exact min_le_left _ _

theorem codeBits_value {p : ℕ} (v : Fin (2^p+1)) :
    booleanWordLSBValue (p+1) (codeBits v) = v.val := by
  rw [codeBits,Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits.ofNat_value]
  apply Nat.mod_eq_of_lt
  have hp : 0 < 2^p := by positivity
  rw [pow_succ]
  have hv := v.isLt
  omega

theorem decodeCode_codeBits {p : ℕ} (v : Fin (2^p+1)) :
    decodeCode p (codeBits v) = (v.val:ℝ)/(2^p:ℝ) := by
  rw [decodeCode,codeBits_value,min_eq_right]
  apply (div_le_one (by positivity : (0:ℝ)<2^p)).2
  exact_mod_cast (show v.val ≤ 2^p by have := v.isLt; omega)

abbrev QuerySpace (n k d p : ℕ) := Reg d × (Reg (width n k) × Reg (p+1))

def queryUpdate {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s)
    (v : QuerySpace n k d p) : QuerySpace n k d p :=
  (v.1,(v.2.1,fun q => v.2.2 q ^^ codeBits (termCode j v.1 (decodeNative n k v.2.1)) q))

theorem queryUpdate_involutive {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    Function.Involutive (queryUpdate (k := k) termCode j) := by
  intro v
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext q
      simp [queryUpdate]

def queryEquiv {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    Equiv.Perm (QuerySpace n k d p) where
  toFun := queryUpdate (k := k) termCode j
  invFun := queryUpdate (k := k) termCode j
  left_inv := queryUpdate_involutive (k := k) termCode j
  right_inv := queryUpdate_involutive (k := k) termCode j

noncomputable def queryOracle {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    Matrix (QuerySpace n k d p) (QuerySpace n k d p) ℂ := permMatrix (queryEquiv (k := k) termCode j)

theorem queryOracle_unitary {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    queryOracle (k := k) termCode j ∈ Matrix.unitaryGroup (QuerySpace n k d p) ℂ :=
  permMatrix_unitary_of_injective (queryEquiv (k := k) termCode j).injective

theorem queryOracle_selfadjoint {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    (queryOracle (k := k) termCode j)ᴴ = queryOracle (k := k) termCode j := by
  exact permMatrix_conjTranspose (queryUpdate_involutive (k := k) termCode j)

theorem queryOracle_basis {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s)
    (v : QuerySpace n k d p) :
    queryOracle (k := k) termCode j *ᵥ Ket v = Ket (queryUpdate (k := k) termCode j v) :=
by
  simpa only [queryOracle,queryEquiv] using!
    Qatlib.Papers.MonteCarloInt20.PrnJump.Affine.perm_basis (queryEquiv (k := k) termCode j) v

theorem queryOracle_clean {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s)
    (i : Reg d) (bits : Reg k) (x : ZMod (2^n)) :
    queryOracle (k := k) termCode j *ᵥ Ket (i,(frame bits x,(fun _ => false))) =
      Ket (i,(frame bits x,codeBits (termCode j i x))) := by
  rw [queryOracle_basis]
  simp only [queryUpdate,decodeNative_frame,Bool.false_xor]
end Qatlib.Papers.MonteCarloInt20.MainResults.TermCode
