/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.FrameDecode

/-!
# Finite term codes and reversible query oracles

`codeBits` represents integers from zero through `2 ^ p`, and `decodeCode` interprets arbitrary
words as clipped fixed-point values in `[0, 1]`. These codes support the finite separated-term
oracle for the Monte Carlo scheme of [KanekoEtAl2020].

`queryUpdate` XORs the selected term code into the output register. Its permutation matrix
`queryOracle` is unitary and self-adjoint, with an explicit action on clean framed inputs.

## Main statements

* `decodeCode_codeBits`: decodes valid codes exactly.
* `queryOracle_unitary`: establishes unitarity of the term oracle.
* `queryOracle_clean`: describes the oracle on a framed input and zero output word.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

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

/-- Encode an integer code from zero through `2 ^ p` in `p + 1` bits. -/
def codeBits {p : ℕ} (v : Fin (2^p+1)) : Reg (p+1) :=
  Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits.ofNat (p+1) v.val

/-- Decode a term word as its unsigned value divided by `2 ^ p`, clipped above at one. -/
noncomputable def decodeCode (p : ℕ) (bits : Reg (p+1)) : ℝ :=
  min 1 ((booleanWordLSBValue (p+1) bits : ℝ)/(2^p : ℝ))

/-- Every decoded term word lies between zero and one. -/
theorem decodeCode_bounds (p : ℕ) (bits : Reg (p+1)) :
    0 ≤ decodeCode p bits ∧ decodeCode p bits ≤ 1 := by
  constructor
  · exact le_min (by norm_num) (by positivity)
  · exact min_le_left _ _

/-- The unsigned value of the encoding of a valid term code equals the original integer code. -/
theorem codeBits_value {p : ℕ} (v : Fin (2^p+1)) :
    booleanWordLSBValue (p+1) (codeBits v) = v.val := by
  rw [codeBits,Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits.ofNat_value]
  apply Nat.mod_eq_of_lt
  have hp : 0 < 2^p := by positivity
  rw [pow_succ]
  have hv := v.isLt
  omega

/-- Encoding a valid term code and decoding it gives its integer value divided by `2 ^ p`. -/
theorem decodeCode_codeBits {p : ℕ} (v : Fin (2^p+1)) :
    decodeCode p (codeBits v) = (v.val:ℝ)/(2^p:ℝ) := by
  rw [decodeCode,codeBits_value,min_eq_right]
  apply (div_le_one (by positivity : (0:ℝ)<2^p)).2
  exact_mod_cast (show v.val ≤ 2^p by have := v.isLt; omega)

/-- The coordinate, native PRN workspace, and output-code register space for a term query. -/
abbrev QuerySpace (n k d p : ℕ) := Reg d × (Reg (width n k) × Reg (p+1))

/-- Preserve the coordinate and PRN workspace and XOR the sample-specific term code at the
decoded residue into the output word. -/
def queryUpdate {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s)
    (v : QuerySpace n k d p) : QuerySpace n k d p :=
  (v.1,(v.2.1,fun q => v.2.2 q ^^ codeBits (termCode j v.1 (decodeNative n k v.2.1)) q))

/-- Applying the term-query XOR update twice restores every register. -/
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

/-- The register permutation whose forward and inverse maps are both the term-query XOR update. -/
def queryEquiv {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    Equiv.Perm (QuerySpace n k d p) where
  toFun := queryUpdate (k := k) termCode j
  invFun := queryUpdate (k := k) termCode j
  left_inv := queryUpdate_involutive (k := k) termCode j
  right_inv := queryUpdate_involutive (k := k) termCode j

/-- The permutation matrix implementing the sample-specific finite term-code query. -/
noncomputable def queryOracle {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    Matrix (QuerySpace n k d p) (QuerySpace n k d p) ℂ := permMatrix (queryEquiv (k := k) termCode j)

/-- The finite term-code query oracle is unitary [KanekoEtAl2020]. -/
theorem queryOracle_unitary {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    queryOracle (k := k) termCode j ∈ Matrix.unitaryGroup (QuerySpace n k d p) ℂ :=
  permMatrix_unitary_of_injective (queryEquiv (k := k) termCode j).injective

/-- The finite term-code query oracle equals its conjugate transpose. -/
theorem queryOracle_selfadjoint {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    (queryOracle (k := k) termCode j)ᴴ = queryOracle (k := k) termCode j := by
  exact permMatrix_conjTranspose (queryUpdate_involutive (k := k) termCode j)

/-- The term-query oracle maps each basis vector to the basis vector specified by `queryUpdate`. -/
theorem queryOracle_basis {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s)
    (v : QuerySpace n k d p) :
    queryOracle (k := k) termCode j *ᵥ Ket v = Ket (queryUpdate (k := k) termCode j v) :=
by
  simpa only [queryOracle,queryEquiv] using!
    Qatlib.Papers.MonteCarloInt20.PrnJump.Affine.perm_basis (queryEquiv (k := k) termCode j) v

/-- On a framed residue and a zero output word, the term-query oracle writes the code for
`termCode j i x` and preserves the coordinate and frame. -/
theorem queryOracle_clean {n k s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s)
    (i : Reg d) (bits : Reg k) (x : ZMod (2^n)) :
    queryOracle (k := k) termCode j *ᵥ Ket (i,(frame bits x,(fun _ => false))) =
      Ket (i,(frame bits x,codeBits (termCode j i x))) := by
  rw [queryOracle_basis]
  simp only [queryUpdate,decodeNative_frame,Bool.false_xor]
end Qatlib.Papers.MonteCarloInt20.MainResults.TermCode
