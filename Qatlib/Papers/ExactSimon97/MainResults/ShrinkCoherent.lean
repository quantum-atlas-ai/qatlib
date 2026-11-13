/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.FourierCoset

/-!
# Coherent shrinking of binary subspace states

The state operations `cnotBit`, `xorBit`, and `hadamardBit` coherently split a phased subspace
state using a vector with a nonzero pivot coordinate. The output is a state on the
coordinate-zero slice with the bit `dot g y` stored in an ancillary register. The development
follows [BrassardHoyer1997].

## Main statements

* `sliceEquiv`: decomposes the subspace as its coordinate-zero slice times one bit.
* `lemma6_coherent_word`: computes the complete coherent shrinking operation.
* `lemma6_linear_gates`: bounds the counted elementary operations by `n + 2`.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators Classical
open Finset

namespace Qatlib.Papers.ExactSimon97.MainResults

/-- The complex state space of a binary vector register paired with one binary ancillary
register. -/
abbrev QState1 (n : ℕ) : Type := BoolVec n × ZMod 2 → ℂ

/-- The complex normalization constant `1 / √2`. -/
def bitNorm : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The binary character pairing `ZMod.stdAddChar (b * b')`. -/
def bitChar (b b' : ZMod 2) : ℂ := ZMod.stdAddChar (b * b')

/-- The square of the complex coercion of `√2` equals two. -/
theorem sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [Real.mul_self_sqrt (by norm_num)]
  exact_mod_cast h

/-- The square of `bitNorm` equals `1 / 2`. -/
theorem bitNorm_sq : bitNorm * bitNorm = ((2 : ℂ))⁻¹ := by
  unfold bitNorm
  rw [← mul_inv, sqrt_two_mul_self]

/-- Apply a normalized binary Fourier transform to the ancillary register. -/
def hadamardBit {n : ℕ} (ψ : QState1 n) : QState1 n :=
  fun p => bitNorm * ∑ b', bitChar p.2 b' * ψ (p.1, b')

/-- Apply the controlled-NOT permutation with source coordinate `j` controlling the ancillary
bit. -/
def cnotBit {n : ℕ} (j : Fin n) (ψ : QState1 n) : QState1 n :=
  fun p => ψ (p.1, p.2 + p.1 j)

/-- Add `y` to the source vector when the ancillary bit is one. -/
def xorBit {n : ℕ} (y : BoolVec n) (ψ : QState1 n) : QState1 n :=
  fun p => ψ (p.1 + p.2 • y, p.2)

/-- The normalized character state on `H` with its ancillary bit fixed to zero. -/
def phiZero {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) (g : BoolVec n) : QState1 n :=
  fun p => if p.1 ∈ H ∧ p.2 = 0 then normFactor H * charFun g p.1 else 0

/-- The normalized character state on `K` with its ancillary bit fixed to `dot g y`. -/
def phiTag {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n)) (g y : BoolVec n) : QState1 n :=
  fun p => if p.2 = dot g y then
    (if p.1 ∈ K then normFactor K * charFun g p.1 else 0) else 0

/-- A sum indexed by `ZMod 2` is the sum of its values at zero and one. -/
theorem sum_zmod2 (f : ZMod 2 → ℂ) : (∑ i, f i) = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = ({0, 1} : Finset (ZMod 2)) by decide]
  simp

/-- The standard additive character of one in `ZMod 2` equals negative one. -/
theorem stdAddChar_one_zmod2 : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
  have h := ZMod.stdAddChar_coe (N := 2) (1 : ℤ)
  simp only [Int.cast_one] at h
  calc ZMod.stdAddChar (1 : ZMod 2)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * 1 / (2 : ℂ)) := by simpa using h
    _ = -1 := by
        have h2 : (2 * (Real.pi : ℂ) * Complex.I * 1 / (2 : ℂ)) =
            (Real.pi : ℂ) * Complex.I := by ring
        rw [h2, Complex.exp_mul_I]
        simp

/-- The expression `(1 + ZMod.stdAddChar z) / 2` is the indicator that `z = 0`. -/
theorem half_one_add_char (z : ZMod 2) :
    (1 + ZMod.stdAddChar z) / 2 = if z = 0 then 1 else 0 := by
  fin_cases z
  · change (1 + ZMod.stdAddChar (0 : ZMod 2)) / 2 = if (0 : ZMod 2) = 0 then 1 else 0
    rw [if_pos rfl, AddChar.map_zero_eq_one]
    norm_num
  · change (1 + ZMod.stdAddChar (1 : ZMod 2)) / 2 = if (1 : ZMod 2) = 0 then 1 else 0
    rw [stdAddChar_one_zmod2, if_neg (by norm_num : ¬((1 : ZMod 2) = 0))]
    norm_num

/-- The expression `(1 + bitChar b 1 * ZMod.stdAddChar t) / 2` is the indicator that `b = t`. -/
theorem half_one_add_bitChar (b t : ZMod 2) :
    (1 + bitChar b 1 * ZMod.stdAddChar t) / 2 = if b = t then 1 else 0 := by
  have hbt : bitChar b 1 * ZMod.stdAddChar t = ZMod.stdAddChar (b + t) := by
    unfold bitChar
    rw [mul_one, ← AddChar.map_add_eq_mul]
  rw [hbt, half_one_add_char]
  have hiff : b + t = 0 ↔ b = t := by
    constructor
    · intro h
      have ht : t + t = 0 := CharTwo.add_self_eq_zero t
      calc b = b + (t + t) := by rw [ht, add_zero]
        _ = (b + t) + t := by rw [add_assoc]
        _ = t := by rw [h, zero_add]
    · intro h
      rw [h]
      exact CharTwo.add_self_eq_zero t
  rw [if_congr hiff rfl rfl]

/-- If `y ∈ H` and `y j = 1`, the subspace `H` is equivalent to its coordinate-zero slice paired
with a binary coordinate. See [BrassardHoyer1997]. -/
def sliceEquiv {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) (y : BoolVec n)
    (hyH : y ∈ H) (j : Fin n) (hyj : y j = 1) :
    H ≃ sliceSub H j × ZMod 2 where
  toFun h :=
    (⟨h.1 - (h.1 j) • y, by
      refine mem_sliceSub.mpr ⟨H.sub_mem h.2 (H.smul_mem _ hyH), ?_⟩
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hyj, mul_one, sub_self]⟩, h.1 j)
  invFun p :=
    ⟨p.1.1 + p.2 • y, H.add_mem (mem_sliceSub.mp p.1.2).1 (H.smul_mem _ hyH)⟩
  left_inv h := by
    apply Subtype.ext
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      have hkj : p.1.1 j = 0 := (mem_sliceSub.mp p.1.2).2
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hkj, hyj,
        mul_one, zero_add]
      ring
    · have hkj : p.1.1 j = 0 := (mem_sliceSub.mp p.1.2).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hkj, hyj, mul_one, zero_add]

/-- If `y ∈ H` and `y j = 1`, the cardinality of `H` is twice the cardinality of its
coordinate-zero slice. -/
theorem natCard_sliceSub {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) (y : BoolVec n)
    (hyH : y ∈ H) (j : Fin n) (hyj : y j = 1) :
    Nat.card H = 2 * Nat.card (sliceSub H j) := by
  rw [Nat.card_congr (sliceEquiv H y hyH j hyj), Nat.card_prod, Nat.card_zmod,
    mul_comm]

/-- If `y ∈ H` and `y j = 1`, the normalization factor of `H` is `bitNorm` times that of its
coordinate-zero slice. -/
theorem normFactor_eq_bitNorm_mul {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n))
    (y : BoolVec n) (hyH : y ∈ H) (j : Fin n) (hyj : y j = 1) :
    normFactor H = bitNorm * normFactor (sliceSub H j) := by
  unfold normFactor bitNorm
  rw [natCard_sliceSub H y hyH j hyj, Nat.cast_mul, Nat.cast_ofNat,
    Real.sqrt_mul (by norm_num)]
  push_cast
  rw [← mul_inv]

/-- The controlled-NOT followed by the controlled vector addition restricts the source to the
coordinate-zero slice with the stated character amplitude. See [BrassardHoyer1997]. -/
theorem lemma6_xor_form {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) (y : BoolVec n)
    (hyH : y ∈ H) (j : Fin n) (hyj : y j = 1) (g : BoolVec n) :
    xorBit y (cnotBit j (phiZero H g)) =
      fun p => if p.1 ∈ sliceSub H j then normFactor H * charFun g (p.1 + p.2 • y) else 0 := by
  funext p
  obtain ⟨x, c⟩ := p
  have hcoord : (x + c • y) j = x j + c := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyj, mul_one]
  have hiff : (x + c • y ∈ H ∧ c + (x + c • y) j = 0) ↔ x ∈ sliceSub H j := by
    constructor
    · intro h
      obtain ⟨hxH, hc⟩ := h
      refine mem_sliceSub.mpr ⟨?_, ?_⟩
      · have hy : c • y ∈ H := H.smul_mem c hyH
        have hx : x = (x + c • y) + c • y := by
          funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        rw [hx]
        exact H.add_mem hxH hy
      · rw [hcoord] at hc
        have h2 : x j + (c + c) = 0 := by
          rw [show x j + (c + c) = c + (x j + c) by ring, hc]
        simpa [CharTwo.add_self_eq_zero c] using h2
    · intro hx
      obtain ⟨hxH, hxj⟩ := mem_sliceSub.mp hx
      refine ⟨H.add_mem hxH (H.smul_mem c hyH), ?_⟩
      rw [hcoord, hxj, zero_add]
      exact CharTwo.add_self_eq_zero c
  simp only [xorBit, cnotBit, phiZero]
  rw [if_congr hiff rfl rfl]

/-- The controlled-NOT, controlled vector addition, and ancillary Hadamard transform send
`phiZero H g` to the slice state tagged by `dot g y`. See [BrassardHoyer1997]. -/
theorem lemma6_coherent_word {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) (y : BoolVec n)
    (hyH : y ∈ H) (j : Fin n) (hyj : y j = 1) (g : BoolVec n) :
    hadamardBit (xorBit y (cnotBit j (phiZero H g))) = phiTag (sliceSub H j) g y := by
  rw [lemma6_xor_form H y hyH j hyj g]
  funext p
  obtain ⟨x, b⟩ := p
  by_cases hxK : x ∈ sliceSub H j
  · have hfac : (∑ b' : ZMod 2, bitChar b b' * charFun g (x + b' • y)) =
        charFun g x * (1 + bitChar b 1 * charFun g y) := by
      rw [sum_zmod2]
      have h0 : bitChar b 0 * charFun g (x + (0 : ZMod 2) • y) = charFun g x := by
        simp [bitChar]
      have h1 : bitChar b 1 * charFun g (x + (1 : ZMod 2) • y) =
          bitChar b 1 * (charFun g x * charFun g y) := by
        rw [one_smul, charFun_add_right]
      rw [h0, h1]
      ring
    have hsum2 : (∑ b' : ZMod 2, bitChar b b' *
          (normFactor H * charFun g (x + b' • y))) =
        normFactor H * (∑ b' : ZMod 2, bitChar b b' * charFun g (x + b' • y)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b' _ => by ring
    have hNH : bitNorm * normFactor H =
        normFactor (sliceSub H j) * (bitNorm * bitNorm) := by
      rw [normFactor_eq_bitNorm_mul H y hyH j hyj]
      ring
    have hbase : bitNorm * (normFactor H * (charFun g x *
          (1 + bitChar b 1 * charFun g y))) =
        normFactor (sliceSub H j) * charFun g x *
          ((1 + bitChar b 1 * charFun g y) / 2) := by
      calc bitNorm * (normFactor H * (charFun g x *
              (1 + bitChar b 1 * charFun g y)))
          = (bitNorm * normFactor H) * charFun g x *
              (1 + bitChar b 1 * charFun g y) := by ring
        _ = (normFactor (sliceSub H j) * (bitNorm * bitNorm)) * charFun g x *
              (1 + bitChar b 1 * charFun g y) := by rw [hNH]
        _ = normFactor (sliceSub H j) * charFun g x *
              ((1 + bitChar b 1 * charFun g y) / 2) := by
              rw [bitNorm_sq, div_eq_mul_inv]; ring
    have hstep : bitNorm * (∑ b' : ZMod 2, bitChar b b' *
          (if x ∈ sliceSub H j then normFactor H * charFun g (x + b' • y) else 0)) =
        phiTag (sliceSub H j) g y (x, b) := by
      simp only [if_pos hxK]
      rw [hsum2, hfac]
      simp only [phiTag]
      by_cases hb : b = dot g y
      · rw [if_pos hb, if_pos hxK]
        rw [hbase]
        rw [show charFun g y = ZMod.stdAddChar (dot g y) from rfl, ← hb,
          half_one_add_bitChar]
        simp
      · rw [if_neg hb]
        rw [hbase]
        rw [show charFun g y = ZMod.stdAddChar (dot g y) from rfl,
          half_one_add_bitChar, if_neg hb]
        simp
    simpa only [hadamardBit] using hstep
  · have hzero : (∑ b' : ZMod 2, bitChar b b' *
        (if x ∈ sliceSub H j then normFactor H * charFun g (x + b' • y) else 0)) = 0 := by
      simp [hxK]
    simp only [hadamardBit, hzero, mul_zero]
    simp [phiTag, hxK]

/-- The finite set of coordinates at which the binary vector `y` is nonzero. -/
def xorSupport {n : ℕ} (y : BoolVec n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => y i ≠ 0)

/-- The count consisting of one initial operation, one per nonzero coordinate of `y`, and one
final operation is at most `n + 2`. See [BrassardHoyer1997]. -/
theorem lemma6_linear_gates {n : ℕ} (y : BoolVec n) :
    1 + (xorSupport y).card + 1 ≤ n + 2 := by
  have h : (xorSupport y).card ≤ n := by
    rw [xorSupport]
    calc (Finset.univ.filter (fun i : Fin n => y i ≠ 0)).card ≤ Finset.univ.card :=
          Finset.card_filter_le _ _
      _ = n := by simp
  omega

end Qatlib.Papers.ExactSimon97.MainResults
