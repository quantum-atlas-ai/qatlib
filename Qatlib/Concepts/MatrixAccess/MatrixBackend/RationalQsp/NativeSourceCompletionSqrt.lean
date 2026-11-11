/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceProducerGuards
import Mathlib.Data.Nat.Sqrt
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input spectral completion: CompletionSqrt.
This does not certify the full proposer, iterative deflation, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section SqrtLower

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- Construction for source Sqrt Lower in the native source completion sqrt model. -/
def sourceSqrtLower (x : ℚ) (bits : ℕ) : ℚ :=
  (Nat.sqrt (Int.toNat (⌊x*(2 : ℚ)^(2*bits)⌋ : ℤ)) : ℚ)/(2 : ℚ)^bits

/-- Construction for source Completion Sqrt Bits in the native source completion sqrt model. -/
def sourceCompletionSqrtBits (d : ℕ) (eta : ℚ) : ℕ :=
  sourceCeilLog2 (2*(3 : ℚ)^d/eta)

/-- The finite construction in `NativeSourceCompletionSqrt` satisfies `sourceSqrtLower_nonneg` under the displayed hypotheses. -/
theorem sourceSqrtLower_nonneg (x : ℚ) (bits : ℕ) : 0 ≤ sourceSqrtLower x bits := by
  unfold sourceSqrtLower
  positivity

/-- The finite construction in `NativeSourceCompletionSqrt` satisfies `sourceSqrtLower_squared` under the displayed hypotheses. -/
private theorem sourceSqrtLower_squared (x : ℚ) (hx : 0 ≤ x) (bits : ℕ) :
    (sourceSqrtLower x bits)^2 ≤ x ∧
      x < (sourceSqrtLower x bits+1/(2 : ℚ)^bits)^2 := by
  let B : ℚ := (2 : ℚ)^bits
  let v : ℚ := x*(2 : ℚ)^(2*bits)
  let n : ℕ := Int.toNat (⌊v⌋ : ℤ)
  have hB : 0<B := by dsimp [B]; positivity
  have hv : v=x*B^2 := by dsimp [v,B]; rw [Nat.mul_comm 2 bits,pow_mul]
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hn : n=⌊v⌋₊ := Int.floor_toNat v
  have hlo : (n : ℚ) ≤ v := by rw [hn]; exact Nat.floor_le hv0
  have hhi : v<(n : ℚ)+1 := by rw [hn]; exact Nat.lt_floor_add_one v
  have hkl : ((Nat.sqrt n : ℕ) : ℚ)^2 ≤ (n : ℚ) := by exact_mod_cast Nat.sqrt_le' n
  have hku : (n : ℚ)+1 ≤ ((Nat.sqrt n : ℚ)+1)^2 := by
    exact_mod_cast Nat.succ_le_succ_sqrt' n
  have he : sourceSqrtLower x bits=(Nat.sqrt n : ℚ)/B := rfl
  rw [he]
  constructor
  · rw [div_pow]
    apply (div_le_iff₀ (pow_pos hB 2)).mpr
    exact hkl.trans (by simpa only [hv] using hlo)
  · have heq : (Nat.sqrt n : ℚ)/B+1/(2 : ℚ)^bits=((Nat.sqrt n : ℚ)+1)/B := by
      change (Nat.sqrt n : ℚ)/B+1/B=((Nat.sqrt n : ℚ)+1)/B
      ring
    rw [heq,div_pow]
    apply (lt_div_iff₀ (pow_pos hB 2)).mpr
    exact (by simpa only [hv] using hhi.trans_le hku)

/-- The estimate `sourceSqrtLower_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceSqrtLower_error (x : ℚ) (hx : 0 ≤ x) (bits : ℕ) :
    (sourceSqrtLower x bits : ℝ) ≤ Real.sqrt (x : ℝ) ∧
      Real.sqrt (x : ℝ)-(sourceSqrtLower x bits : ℝ)<1/(2 : ℝ)^bits := by
  have hxR : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hn : (0 : ℝ) ≤ (sourceSqrtLower x bits : ℝ) := by
    exact_mod_cast sourceSqrtLower_nonneg x bits
  have hs := sourceSqrtLower_squared x hx bits
  have hl : (sourceSqrtLower x bits : ℝ)^2 ≤ (x : ℝ) := by exact_mod_cast hs.1
  have hu : (x : ℝ)<((sourceSqrtLower x bits : ℝ)+1/(2 : ℝ)^bits)^2 := by
    simpa only [Rat.cast_pow,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr hs.2
  have hsq := Real.sq_sqrt hxR
  have hpos := Real.sqrt_nonneg (x : ℝ)
  have hdelta : (0 : ℝ)<1/(2 : ℝ)^bits := by positivity
  constructor <;> nlinarith

/-- The finite construction in `NativeSourceCompletionSqrt` satisfies `sourceCompletionSqrtBits_envelope` under the displayed hypotheses. -/
theorem sourceCompletionSqrtBits_envelope (d : ℕ) (eta : ℚ) (heta : 0<eta) :
    1/(2 : ℚ)^sourceCompletionSqrtBits d eta ≤ eta/(2*(3 : ℚ)^d) := by
  have h := sourceCeilLog2_envelope (2*(3 : ℚ)^d/eta) (by positivity)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul,sourceCompletionSqrtBits,mul_comm] using (div_le_iff₀ heta).mp h

example : sourceSqrtLower (2 : ℚ) 4=11/8 := by decide +kernel
example : sourceSqrtLower (9/4 : ℚ) 4=3/2 := by decide +kernel
example : sourceSqrtLower 0 0=0 := by decide +kernel

end SqrtLower

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
