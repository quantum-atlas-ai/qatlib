/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeValueLabels

/-!
# Fourier-character laws for full-range phase kickback

The module evaluates and shifts the additive character used by the full-range value register.
`full_range_character_preparation` and `full_range_character_normalized` establish preparation
and normalization of the character state, while `full_range_query_kickback` proves its exact
response to the value oracle. See [Jordan2005Gradient] for background.

## Main statements

* `full_range_character_preparation`: Applying the inverse modular QFT to the character-index
  basis ket prepares the full-range kickback state.
* `full_range_query_kickback`: The value oracle multiplies the input state by the diagonal
  full-range phase while leaving the tensor-factor kickback state unchanged.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option warningAsError false

open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical BigOperators

/-- The additive character at the full-range character index equals the exponential phase
determined by the residue representative divided by `2 ^ k`. -/
theorem full_range_character_phase (K k : ℕ) (a : ZMod (2^(K+k))) :
    ZMod.stdAddChar (fullRangeCharacterIndex K k*a) =
      Complex.exp (2*Real.pi*Complex.I*(((a.val:ℝ)/(2:ℝ)^k):ℂ)) := by
  have he : fullRangeCharacterIndex K k*a = (((2^K*a.val:ℕ):ℤ):ZMod (2^(K+k))) := by
    simp [fullRangeCharacterIndex,Nat.cast_mul]
  rw [he,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add (2:ℂ)]
  field_simp

/-- Translating the conjugate additive character by `a` multiplies it by the character evaluated
at `j * a`. -/
theorem full_range_character_shift {N : ℕ} [NeZero N] (j y a : ZMod N) :
    star (ZMod.stdAddChar (j*(y-a))) = ZMod.stdAddChar (j*a)*star (ZMod.stdAddChar (j*y)) := by
  have hm : ZMod.stdAddChar (j*(y-a))*ZMod.stdAddChar (j*a) = ZMod.stdAddChar (j*y) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hu : ZMod.stdAddChar (j*a)*star (ZMod.stdAddChar (j*a))=1 := by
    change ZMod.stdAddChar (j*a)*(starRingEnd ℂ) (ZMod.stdAddChar (j*a))=1
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,ZMod.stdAddChar_apply,Circle.norm_coe]
    norm_num
  calc
    _ = 1*star (ZMod.stdAddChar (j*(y-a))) := (one_mul _).symm
    _ = (ZMod.stdAddChar (j*a)*star (ZMod.stdAddChar (j*a)))*star (ZMod.stdAddChar (j*(y-a))) := by rw [hu]
    _ = ZMod.stdAddChar (j*a)*star (ZMod.stdAddChar (j*(y-a))*ZMod.stdAddChar (j*a)) := by rw [star_mul];ring
    _ = _ := by rw [hm]

/-- Applying the inverse modular QFT to the character-index basis ket prepares the full-range
kickback state. -/
theorem full_range_character_preparation (K k : ℕ) :
    ApplyGate ((zmodQFTGate (N:=2^(K+k)))ᴴ) (Ket (fullRangeCharacterIndex K k)) = fullRangeKickState K k := by
  ext y
  simp only [ApplyGate,Matrix.mulVec,dotProduct,Ket,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,Matrix.conjTranspose_apply,zmodQFTGate_apply,
    fullRangeKickState,star_mul,Complex.star_def]
  simp [mul_comm]

/-- The full-range Fourier-character kickback state is normalized. -/
theorem full_range_character_normalized (K k : ℕ) : Normalized (fullRangeKickState K k) := by
  have hN : (0:ℝ)<(2^(K+k):ℕ) := by positivity
  have hn (y : ZMod (2^(K+k))) : ‖fullRangeKickState K k y‖^2=((2^(K+k):ℕ):ℝ)⁻¹ := by
    simp only [fullRangeKickState,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),norm_star,ZMod.stdAddChar_apply,Circle.norm_coe,mul_one]
    rw [inv_pow,Real.sq_sqrt hN.le]
  unfold Normalized
  simp [hn,ZMod.card]

/-- The value oracle multiplies the input state by the diagonal full-range phase while leaving
the tensor-factor kickback state unchanged. -/
theorem full_range_query_kickback {X : Type} [Fintype X] [DecidableEq X]
    (K k : ℕ) (v : X → ZMod (2^(K+k))) (ψ : QState X) :
    ApplyGate (gradientValueOracle (2^(K+k)) v) (TensorState ψ (fullRangeKickState K k)) =
      TensorState (ApplyGate (Matrix.diagonal (fun x => Complex.exp
        (2*Real.pi*Complex.I*(fullRangePhase K k v x:ℂ)))) ψ) (fullRangeKickState K k) := by
  rw [full_range_value_oracle_eq_addOracle]
  ext xy
  rcases xy with ⟨x,y⟩
  rw [applyGate_addOracle]
  simp only [TensorState,ApplyGate,Matrix.mulVec_diagonal,fullRangeKickState]
  rw [full_range_character_shift,full_range_character_phase]
  unfold fullRangePhase
  push_cast
  ring

end Qatlib.Concepts.GradientOracle.FullRange
