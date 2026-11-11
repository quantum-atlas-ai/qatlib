/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Kraus

/-!
# Correctness of the three-qubit cluster wire

The wire pattern uses the path with edges `(0, 1)` and `(1, 2)`, two zero-angle measurements,
and output Pauli corrections. Its corrected core is the identity matrix multiplied by a Boolean
sign and `1 / 2`.

For every two-bit measurement history, summing over the auxiliary readout yields the map sending
an operator to one quarter of itself. Summing the four histories therefore preserves trace,
giving an explicit cluster-wire calculation in the measurement-only setting of
[RaussendorfBriegel2000].

## Main statements

* `Clause18Wire.wire_ent_diag` and `Clause18Wire.wire_EL` compute the entangler and loaded
  amplitudes.
* `Clause18Wire1a.wire_core` identifies the corrected core as a scalar multiple of the identity.
* `clause7_clause1a` computes the corrected branch map as multiplication by `1 / 4`.
* `clause7_clause1c_wire` proves trace preservation after summing all measurement histories.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open scoped BigOperators Classical

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

/-- Both adaptive measurement angles of the wire pattern are zero for every measurement history. -/
theorem wire_angle (s : Fin 2 → Bool) (j : Fin 2) :
    mpAdaptiveAngle mpWirePattern s j = 0 := by
  simp only [mpAdaptiveAngle, mpWirePattern, mpParity_empty]
  norm_num

/-- A zero-angle measurement-vector coordinate is the complex embedding of a Boolean sign
divided by `Real.sqrt 2`. -/
theorem sv_zero (o b : Bool) :
    mpSVector 0 o b = (((if b then (if o then (-1 : ℝ) else 1) else 1) / Real.sqrt 2 : ℝ) : ℂ) := by
  simp only [mpSVector, Complex.ofReal_zero, Complex.exp_zero]
  rcases b with rfl | rfl <;> rcases o with rfl | rfl <;>
    simp [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg]

/-- Every zero-angle measurement-vector coordinate is unchanged by complex conjugation. -/
theorem sv_zero_real (o b : Bool) : star (mpSVector 0 o b) = mpSVector 0 o b := by
  rw [sv_zero]
  exact Complex.conj_ofReal _

/-- The product of a zero-angle measurement-vector coordinate and its conjugate is one half. -/
theorem sv_zero_sq (o b : Bool) :
    mpSVector 0 o b * star (mpSVector 0 o b) = (1 / 2 : ℂ) := by
  rw [sv_zero_real, sv_zero]
  have hsq : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv : (Real.sqrt 2 : ℝ)⁻¹ * (Real.sqrt 2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, hsq]
  have h : ((((if b then (if o then (-1 : ℝ) else 1) else 1) / Real.sqrt 2)
      * ((if b then (if o then (-1 : ℝ) else 1) else 1) / Real.sqrt 2)) : ℝ) = (1 / 2 : ℝ) := by
    cases b <;> cases o <;> simp [div_mul_div_comm, hsq, hinv]
  rw [← Complex.ofReal_mul, h, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

/-- A measurement-vector coordinate of the wire pattern is the corresponding zero-angle
coordinate. -/
theorem wire_sv (s : Fin 2 → Bool) (j : Fin 2) (b : Bool) :
    mpSVector (mpAdaptiveAngle mpWirePattern s j) (s j) b = mpSVector 0 (s j) b := by
  rw [wire_angle]
/-- Defines the three-vertex path with edges `(0, 1)` and `(1, 2)`. -/
def wireE : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 2)}

/-- The wire-pattern entangler equals the frame matrix multiplied by the controlled-Z matrix for
`wireE`. -/
theorem wire_entangler :
    mpWirePattern.entangler
      = Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix wireE * Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix wireE := by
  simp only [mpWirePattern]
  exact Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse_eq_frame_cz _

/-- The diagonal frame entry for the wire is the product of the Boolean signs on coordinates one
and two. -/
theorem wire_frame (x : Reg 3) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix wireE x x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply, if_pos (rfl : x = x),
    Fin.prod_univ_three]
  have h0 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd wireE 0 = false := by decide
  have h1 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd wireE 1 = true := by decide
  have h2 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd wireE 2 = true := by decide
  rw [h0, h1, h2]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The diagonal controlled-Z entry for the wire is the product of the Boolean signs of the two
adjacent-bit conjunctions. -/
theorem wire_cz (x : Reg 3) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix wireE x x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1 && x 2) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_pos (rfl : x = x)]
  rw [wireE, Finset.prod_pair (by decide : ((0, 1) : Fin 3 × Fin 3) ≠ (1, 2))]
  simp only [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- Every amplitude of the uniform two-qubit register state is one half. -/
theorem uniform2 (x : Reg 2) : Uniform (Reg 2) x = (1 / 2 : ℂ) := by
  show ((Real.sqrt (Fintype.card (Reg 2)) : ℝ) : ℂ)⁻¹ = 1 / 2
  have h4 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [card_reg]
  norm_num [h4]

/-- The wire load matrix has entry one half when the first register bit matches the input bit,
and zero otherwise. -/
theorem wire_load (d : Reg 3) (y : Reg 1) :
    mpLoadMatrix mpWirePattern (Uniform (Reg 2)) d y
      = if d 0 = y 0 then (1 / 2 : ℂ) else 0 := by
  simp only [mpLoadMatrix, mpWirePattern, Matrix.of_apply]
  by_cases h : ∀ i : Fin 1, d (Fin.castLE (by omega : (1:ℕ) ≤ 2 + 1) i) = y i
  · rw [if_pos h]
    have h0 : d 0 = y 0 := h ⟨0, by omega⟩
    rw [if_pos h0]
    have hres : Uniform (Reg 2)
        (fun k : Fin 2 => d (Fin.cast (by omega) (Fin.natAdd 1 k))) = (1 / 2 : ℂ) := uniform2 _
    rw [hres]
  · rw [if_neg h]
    have h0 : ¬ d 0 = y 0 := by
      intro hh
      apply h
      intro i
      fin_cases i
      exact hh
    rw [if_neg h0]

/-- The wire entangler is diagonal, with each diagonal entry equal to the product of its frame
signs and its two adjacent-bit controlled-Z signs. -/
theorem wire_ent_diag (x y : Reg 3) :
    mpWirePattern.entangler x y
      = if x = y then
          (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2)
            * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 1)
                * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1 && x 2)))
        else 0 := by
  rw [wire_entangler]
  by_cases h : x = y
  · subst h
    rw [if_pos rfl]
    rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · rw [wire_frame, wire_cz]
    · intro k _ hk
      rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply,
          if_neg (Ne.symm hk), zero_mul]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = x
    · subst hk
      rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_neg h, mul_zero]
    · rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply,
        if_neg (Ne.symm hk), zero_mul]

/-- The entangler-load product has the wire's diagonal phase multiplied by one half when the
input bit matches coordinate zero, and is zero otherwise. -/
theorem wire_EL (d : Reg 3) (y : Reg 1) :
    (mpWirePattern.entangler * mpLoadMatrix mpWirePattern (Uniform (Reg 2))) d y
      = if d 0 = y 0 then
          (1 / 2 : ℂ) * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (d 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (d 2)
            * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (d 0 && d 1)
                * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (d 1 && d 2)))
        else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single d]
  · rw [wire_ent_diag, if_pos rfl, wire_load]
    by_cases h : d 0 = y 0
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  · intro d' _ hdne
    rw [wire_ent_diag, if_neg (Ne.symm hdne), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire

/-- Constructs a three-bit register with coordinates `a0`, `a1`, and `a2`, in that order. -/
def pin3 (a0 a1 a2 : Bool) : Reg 3 := fun t =>
  if (t : ℕ) = 0 then a0 else if (t : ℕ) = 1 then a1 else a2

/-- Coordinate zero of `pin3 a0 a1 a2` is `a0`. -/
@[simp] theorem pin3_0 (a0 a1 a2 : Bool) : pin3 a0 a1 a2 0 = a0 := rfl

/-- Coordinate one of `pin3 a0 a1 a2` is `a1`. -/
@[simp] theorem pin3_1 (a0 a1 a2 : Bool) : pin3 a0 a1 a2 1 = a1 := rfl

/-- Coordinate two of `pin3 a0 a1 a2` is `a2`. -/
@[simp] theorem pin3_2 (a0 a1 a2 : Bool) : pin3 a0 a1 a2 2 = a2 := rfl

/-- Every three-bit register equals the register assembled by `pin3` from its three coordinates. -/
theorem reg3_eq_pin3 (x : Reg 3) : x = pin3 (x 0) (x 1) (x 2) := by
  funext t
  fin_cases t <;> rfl

/-- The Boolean sign of an XOR is the product of the signs of its two arguments. -/
theorem bitPhase_xor (a b : Bool) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (xor a b)
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase a * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase b := by
  cases a <;> cases b <;> simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase, Bool.xor]

/-- Negating a Boolean argument negates its complex Boolean sign. -/
theorem bitPhase_not (a : Bool) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!a) = -Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase a := by
  cases a <;> simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- A one-bit register encodes to `xp` exactly when its bit equals the bit decoded from `xp`. -/
theorem bitCond (xp : Fin 2) (y : Reg 1) :
    ((bitVecEquiv 1) y = xp) ↔ (y 0 = ((bitVecEquiv 1).symm xp) 0) := by
  constructor
  · intro h
    have hy : y = (bitVecEquiv 1).symm xp := by
      apply (Equiv.injective (bitVecEquiv 1))
      rw [h]
      exact (Equiv.apply_symm_apply (bitVecEquiv 1) xp).symm
    rw [hy]
  · intro h
    have hy : y = (bitVecEquiv 1).symm xp := by
      funext t
      fin_cases t
      exact h
    rw [hy]
    exact Equiv.apply_symm_apply (bitVecEquiv 1) xp

/-- The wire's output-bit constraint is equivalent to the equality between coordinate two and
its single corrected output bit. -/
theorem delta_iff (s : Fin 2 → Bool) (xp : Fin 2) (c : Reg 3) :
    (∀ v : Fin 1, c (Fin.natAdd 2 v) = mpOutBit mpWirePattern s xp v)
      ↔ (c 2 = mpOutBit mpWirePattern s xp 0) := by
  constructor
  · intro h
    have h0 := h ⟨0, by omega⟩
    simpa using h0
  · intro h v
    fin_cases v
    simpa using h

/-- Defines the wire core's summand as the product of conjugate measurement coordinates, the
corrected-output constraint, and the entangler-load entry. -/
noncomputable def wireSummand (s : Fin 2 → Bool) (xp : Fin 2) (y : Reg 1) : Reg 3 → ℂ := fun c =>
  (∏ j : Fin 2, star (mpSVector 0 (s j) (c (Fin.castLE (by omega : 2 ≤ 2 + 1) j))))
    * (if ∀ v : Fin 1, c (Fin.natAdd 2 v) = mpOutBit mpWirePattern s xp v then (1 : ℂ) else 0)
    * (mpWirePattern.entangler * mpLoadMatrix mpWirePattern (Uniform (Reg 2))) c y

/-- The wire core entry is its Z-correction sign multiplied by the sum of `wireSummand` over
three-bit registers. -/
theorem wire_corePre_eq (s : Fin 2 → Bool) (xp : Fin 2) (y : Reg 1) :
    corePre mpWirePattern (Uniform (Reg 2)) s xp y
      = (if mpWirePattern.zCorr 0 s && mpOutBit mpWirePattern s xp 0 then (-1 : ℂ) else 1)
          * ∑ c : Reg 3, wireSummand s xp y c := by
  simp only [corePre, Matrix.of_apply, wireSummand]
  rw [Fin.prod_univ_one]
  simp only [wire_sv]

/-- Expands the wire summand into zero-angle measurement coordinates, the fixed output-bit
constraint, and the explicit loaded entangler phase. -/
theorem wire_summand_eq (s : Fin 2 → Bool) (xp : Fin 2) (y : Reg 1) (c : Reg 3) :
    wireSummand s xp y c
      = (∏ j : Fin 2, star (mpSVector 0 (s j) (c (Fin.castLE (by omega : 2 ≤ 2 + 1) j))))
          * (if c 2 = mpOutBit mpWirePattern s xp 0 then (1 : ℂ) else 0)
          * (if c 0 = y 0 then
              (1 / 2 : ℂ) * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (c 1)
                * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (c 2)
                * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (c 0 && c 1)
                    * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (c 1 && c 2)))
            else 0) := by
  simp only [wireSummand]
  rw [wire_EL]
  simp only [delta_iff]

/-- The wire-summand sum reduces to the two registers with the prescribed input and corrected
output bits and either value of the middle bit. -/
theorem wire_sum_eq (s : Fin 2 → Bool) (xp : Fin 2) (y : Reg 1) :
    ∑ c : Reg 3, wireSummand s xp y c
      = wireSummand s xp y (pin3 (y 0) false (mpOutBit mpWirePattern s xp 0))
        + wireSummand s xp y (pin3 (y 0) true (mpOutBit mpWirePattern s xp 0)) := by
  set e : Bool := mpOutBit mpWirePattern s xp 0 with he
  apply Fintype.sum_eq_add
  · intro h
    have h1 := congrArg (fun z : Reg 3 => z 1) h
    simp at h1
  · intro x hx
    rw [wire_summand_eq]
    have key : x 0 = y 0 ∧ x 2 = e → x = pin3 (y 0) false e ∨ x = pin3 (y 0) true e := by
      intro ⟨h0, h2⟩
      by_cases h1 : x 1
      · right
        rw [reg3_eq_pin3 x]
        simp [h0, h1, h2]
      · left
        rw [reg3_eq_pin3 x]
        simp [h0, h1, h2]
    by_cases h0 : x 0 = y 0
    · by_cases h2 : x 2 = e
      · rcases key ⟨h0, h2⟩ with h | h
        · exact absurd h hx.1
        · exact absurd h hx.2
      · have hd : ¬ ∀ v : Fin 1, x (Fin.natAdd 2 v) = mpOutBit mpWirePattern s xp v := by
          intro hh
          apply h2
          simpa using (delta_iff s xp x).mp hh
        rw [if_neg h2, mul_zero, zero_mul]
    · rw [if_neg h0, mul_zero]

/-- The real square root of two multiplied by itself is two. -/
theorem hsq : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)

/-- The product of two inverse real square roots of two is the inverse of two. -/
theorem hinv : (Real.sqrt 2 : ℝ)⁻¹ * (Real.sqrt 2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by
  rw [← mul_inv, hsq]

/-- The product of two inverse complex embeddings of the real square root of two is the inverse
of two. -/
theorem hcinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, hsq, Complex.ofReal_ofNat]
  rw [← mul_inv, h]

/-- The product of the two conjugate zero-angle measurement coordinates equals the product of
the factors at coordinates zero and one. -/
theorem prod_star_sv (s : Fin 2 → Bool) (c : Reg 3) :
    (∏ j : Fin 2, star (mpSVector 0 (s j) (c (Fin.castLE (by omega : 2 ≤ 2 + 1) j))))
      = star (mpSVector 0 (s 0) (c 0)) * star (mpSVector 0 (s 1) (c 1)) := by
  rw [Fin.prod_univ_two]
  rfl

/-- Evaluates the wire summand with middle bit false as two conjugate measurement coordinates
multiplied by one half and the corrected output's Boolean sign. -/
theorem wire_summand_pin3_false (s : Fin 2 → Bool) (xp : Fin 2) (y : Reg 1) :
    wireSummand s xp y (pin3 (y 0) false (mpOutBit mpWirePattern s xp 0))
      = star (mpSVector 0 (s 0) (y 0)) * star (mpSVector 0 (s 1) false)
          * ((1 / 2 : ℂ) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (mpOutBit mpWirePattern s xp 0)) := by
  rw [wire_summand_eq, prod_star_sv]
  simp only [pin3_0, pin3_1, pin3_2, if_true, and_false, false_and]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- Evaluates the wire summand with middle bit true as two conjugate measurement coordinates
multiplied by one half and the frame and adjacent-bit Boolean signs. -/
theorem wire_summand_pin3_true (s : Fin 2 → Bool) (xp : Fin 2) (y : Reg 1) :
    wireSummand s xp y (pin3 (y 0) true (mpOutBit mpWirePattern s xp 0))
      = star (mpSVector 0 (s 0) (y 0)) * star (mpSVector 0 (s 1) true)
          * ((1 / 2 : ℂ) * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase true
              * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (mpOutBit mpWirePattern s xp 0)
              * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (y 0 && true)
                  * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase
                      (true && mpOutBit mpWirePattern s xp 0)))) := by
  rw [wire_summand_eq, prod_star_sv]
  simp only [pin3_0, pin3_1, pin3_2, if_true, and_true, true_and]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The wire core entry is the history-dependent Boolean sign divided by two when the input
register encodes to the output index, and is zero otherwise. -/
theorem wire_corePre (s : Fin 2 → Bool) (xp : Fin 2) (y : Reg 1) :
    corePre mpWirePattern (Uniform (Reg 2)) s xp y
      = if (bitVecEquiv 1) y = xp then
          (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (s 0 && !(s 1)) / 2 : ℂ)
        else 0 := by
  rw [wire_corePre_eq, wire_sum_eq, wire_summand_pin3_false, wire_summand_pin3_true]
  simp only [bitCond]
  have hout : mpOutBit mpWirePattern s xp 0 = xor (!(s 1)) ((bitVecEquiv 1).symm xp 0) := rfl
  have hz : mpWirePattern.zCorr 0 s = !s 0 := rfl
  rw [hout, hz]
  have hs0 : s 0 = true ∨ s 0 = false := Bool.eq_false_or_eq_true _
  have hs1 : s 1 = true ∨ s 1 = false := Bool.eq_false_or_eq_true _
  have hy0 : y 0 = true ∨ y 0 = false := Bool.eq_false_or_eq_true _
  have hbx : ((bitVecEquiv 1).symm xp) 0 = true ∨ ((bitVecEquiv 1).symm xp) 0 = false :=
    Bool.eq_false_or_eq_true _
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;>
    rcases hy0 with hy0 | hy0 <;> rcases hbx with hbx | hbx
  all_goals simp only [hs0, hs1, hy0, hbx]
  all_goals
    simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase, Bool.xor, Bool.not, sv_zero,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.conj_ofReal, div_eq_mul_inv, hcinv, mul_comm, mul_left_comm, mul_assoc,
      mul_neg, neg_mul, neg_neg, one_mul, mul_one]
  all_goals norm_num

/-- The corrected wire core is the identity matrix multiplied by `bitPhase (s 0 && !(s 1)) / 2`. -/
theorem wire_core (s : Fin 2 → Bool) :
    core mpWirePattern (Uniform (Reg 2)) s
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (s 0 && !(s 1)) / 2 : ℂ) • 1 := by
  ext xp yp
  simp only [core, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Equiv.refl_symm, Equiv.refl_apply]
  rw [wire_corePre, Equiv.apply_symm_apply]
  by_cases h : xp = yp
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_one]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/-- Conjugating any two-dimensional operator by the corrected wire core multiplies it by one
quarter. -/
theorem wire_core_conj (s : Fin 2 → Bool) (ρ : Operator 2) :
    core mpWirePattern (Uniform (Reg 2)) s * ρ
        * (core mpWirePattern (Uniform (Reg 2)) s).conjTranspose
      = (1 / 4 : ℂ) • ρ := by
  rw [wire_core]
  set c : ℂ := Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (s 0 && !(s 1)) / 2 with hc
  have h1 : ((c : ℂ) • (1 : Operator 2)) * ρ = c • ρ := by
    rw [smul_mul_assoc, Matrix.one_mul]
  rw [h1, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_smul, Matrix.mul_one]
  have h3 : c * star c = (1 / 4 : ℂ) := by
    rw [hc]
    have hst : star (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (s 0 && !(s 1)))
        = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (s 0 && !(s 1)) := by
      rcases Bool.eq_false_or_eq_true (s 0 && !(s 1)) with h | h <;> rw [h] <;>
        simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]
    rw [star_div₀, hst, star_ofNat]
    have hsqb : Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (s 0 && !(s 1))
        * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (s 0 && !(s 1)) = 1 :=
      Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase_sq _
    rw [div_mul_div_comm, hsqb]
    norm_num
  rw [h3]

/-- The sum over auxiliary readouts of the squared magnitudes of the wire's
measurement-coordinate products is one. -/
theorem sv_sum (s : Fin 2 → Bool) :
    ∑ z : Fin 2 → Bool,
      (∏ j : Fin 2, mpSVector (mpAdaptiveAngle mpWirePattern s j) (s j) (z j))
        * star (∏ j : Fin 2, mpSVector (mpAdaptiveAngle mpWirePattern s j) (s j) (z j)) = 1 := by
  simp only [wire_sv]
  have hz : ∀ z : Fin 2 → Bool,
      (∏ j : Fin 2, mpSVector 0 (s j) (z j))
          * star (∏ j : Fin 2, mpSVector 0 (s j) (z j)) = (1 / 4 : ℂ) := by
    intro z
    have hstar : star (∏ j : Fin 2, mpSVector 0 (s j) (z j))
        = ∏ j : Fin 2, star (mpSVector 0 (s j) (z j)) :=
      map_prod (starRingEnd ℂ) (fun j => mpSVector 0 (s j) (z j)) Finset.univ
    rw [hstar, Fin.prod_univ_two, Fin.prod_univ_two, mul_mul_mul_comm, sv_zero_sq, sv_zero_sq]
    norm_num
  simp_rw [hz]
  rw [Finset.sum_const, Finset.card_univ]
  rw [card_reg]
  norm_num

/-- For every wire measurement history, summing its Kraus conjugations over the auxiliary
readout multiplies any two-dimensional operator by one quarter. -/
theorem clause7_clause1a : ∀ (s : Fin 2 → Bool) (ρ : Operator 2),
    ∑ z : Fin 2 → Bool,
        (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z) * ρ
          * (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z).conjTranspose
      = (1 / 4 : ℂ) • ρ := by
  intro s ρ
  have hkey : ∀ z : Fin 2 → Bool,
      (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z) * ρ
          * (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z).conjTranspose
        = ((∏ j : Fin 2, mpSVector (mpAdaptiveAngle mpWirePattern s j) (s j) (z j))
            * star (∏ j : Fin 2, mpSVector (mpAdaptiveAngle mpWirePattern s j) (s j) (z j)))
            • (core mpWirePattern (Uniform (Reg 2)) s * ρ
                * (core mpWirePattern (Uniform (Reg 2)) s).conjTranspose) := by
    intro z
    rw [kraus_eq_smul_core, Matrix.conjTranspose_smul, smul_mul_assoc, smul_mul_smul]
  simp_rw [hkey]
  rw [← Finset.sum_smul, sv_sum, one_smul, wire_core_conj]
end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a
namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire

/-- For every wire measurement history, summing its Kraus conjugations over the auxiliary
readout multiplies any two-dimensional operator by one quarter. -/
theorem clause7_clause1a : ∀ (s : Fin 2 → Bool) (ρ : Operator 2),
    ∑ z : Fin 2 → Bool,
        (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z) * ρ
          * (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z).conjTranspose
      = (1 / 4 : ℂ) • ρ :=
  Clause18Wire1a.clause7_clause1a
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

/-- The sum of all wire-pattern branches preserves the trace of every two-dimensional operator. -/
theorem clause7_clause1c_wire (A : Operator 2) :
    Matrix.trace (∑ s : Fin 2 → Bool,
        mpPatternBranch mpWirePattern (Uniform (Reg 2)) s A) = Matrix.trace A := by
  have hbr : ∀ s : Fin 2 → Bool,
      mpPatternBranch mpWirePattern (Uniform (Reg 2)) s A
        = ∑ z : Fin 2 → Bool,
            (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z) * A
              * (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z).conjTranspose := by
    intro s
    show (∑ z : Fin 2 → Bool,
        conjBranch (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z)) A = _
    rfl
  simp_rw [hbr, clause7_clause1a]
  have hsum : (∑ _s : Fin 2 → Bool, (1 / 4 : ℂ) • A) = A := by
    have hcard : (Finset.univ : Finset (Fin 2 → Bool)).card = 4 := by decide
    rw [Finset.sum_const, hcard]
    have hcast : (4 : ℕ) • ((1 / 4 : ℂ) • A) = (4 : ℂ) • ((1 / 4 : ℂ) • A) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ 4 ((1 / 4 : ℂ) • A)]
      norm_num
    rw [hcast, smul_smul, show (4 : ℂ) * (1 / 4 : ℂ) = 1 by norm_num, one_smul]
  rw [hsum]
end Qatlib.Concepts.ClusterPatterns.CnotPatterns
