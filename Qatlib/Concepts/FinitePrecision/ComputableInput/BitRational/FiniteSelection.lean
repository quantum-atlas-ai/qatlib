/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Product
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.FiniteSelection

open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

def width (a : ℚ) : ℕ := (binomialRatHeight a).size

def product : List ℚ → ℚ × ℕ
  | [] => (1, 0)
  | a :: as =>
    let tail := product as
    let step := binomialRatMulBits a tail.1
    (step.1, step.2 + tail.2)

theorem product_value (as : List ℚ) : (product as).1 = as.prod := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (binomialRatMulBits a (product as).1).1 = a * as.prod
    rw [(binomial_rat_mul_bits a (product as).1).1, ih]

theorem product_cap_mono {a b : ℕ} (h : a ≤ b) :
    binomialRatOpGateCap a ≤ binomialRatOpGateCap b := by
  unfold binomialRatOpGateCap
  gcongr

theorem product_bounds (as : List ℚ) :
    width (product as).1 ≤ 1 + (as.map width).sum ∧
      (product as).2 ≤ as.length * binomialRatOpGateCap (1 + (as.map width).sum) := by
  induction as with
  | nil => norm_num [product, width, binomialRatHeight]
  | cons a as ih =>
    have h := binomial_rat_mul_bits a (product as).1
    change width (binomialRatMulBits a (product as).1).1 ≤ _ ∧
      (binomialRatMulBits a (product as).1).2 + (product as).2 ≤ _
    have hw : width a + width (product as).1 ≤ 1 + ((a :: as).map width).sum := by
      simp only [List.map_cons, List.sum_cons]
      omega
    have ht : 1 + (as.map width).sum ≤ 1 + ((a :: as).map width).sum := by
      simp only [List.map_cons, List.sum_cons]
      omega
    refine ⟨h.2.1.trans hw, ?_⟩
    have hs := h.2.2.trans (product_cap_mono hw)
    have hp := ih.2.trans (Nat.mul_le_mul_left as.length (product_cap_mono ht))
    simpa only [List.length_cons, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hs hp

def less (a b : ℚ) : Bool × ℕ :=
  let x := binomialBitMul a.num.natAbs.bits b.den.bits
  let y := binomialBitMul b.num.natAbs.bits a.den.bits
  let cmp := binomialBitCompare (max x.1.length y.1.length) x.1 y.1 false
  (cmp.1, x.2 + y.2 + cmp.2)

theorem less_correct (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (less a b).1 = true ↔ a < b := by
  let x := binomialBitMul a.num.natAbs.bits b.den.bits
  let y := binomialBitMul b.num.natAbs.bits a.den.bits
  have hc := (binomial_bit_compare (max x.1.length y.1.length) x.1 y.1 false
    (le_max_left _ _) (le_max_right _ _)).1
  have hx := (binomial_bit_mul a.num.natAbs.bits b.den.bits).1
  have hy := (binomial_bit_mul b.num.natAbs.bits a.den.bits).1
  simp only [binomial_bit_value_bits] at hx hy
  change (binomialBitCompare (max x.1.length y.1.length) x.1 y.1 false).1 = true ↔ _
  rw [hc, hx, hy]
  simp only [Bool.toNat_false, Nat.add_zero, Nat.add_one_le_iff]
  rw [Rat.lt_iff, ← Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha),
    ← Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hb)]
  norm_cast

theorem less_gates (a b : ℚ) :
    (less a b).2 ≤ 6 * (width a + width b) ^ 2 + 10 * (width a + width b) := by
  have hna : a.num.natAbs.bits.length ≤ width a := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size (le_max_left _ _)
  have hda : a.den.bits.length ≤ width a := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size (le_max_right _ _)
  have hnb : b.num.natAbs.bits.length ≤ width b := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size (le_max_left _ _)
  have hdb : b.den.bits.length ≤ width b := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size (le_max_right _ _)
  obtain ⟨_, hxl, hxg⟩ := binomial_bit_mul a.num.natAbs.bits b.den.bits
  obtain ⟨_, hyl, hyg⟩ := binomial_bit_mul b.num.natAbs.bits a.den.bits
  let x := binomialBitMul a.num.natAbs.bits b.den.bits
  let y := binomialBitMul b.num.natAbs.bits a.den.bits
  have hcl : max x.1.length y.1.length ≤ 2 * (width a + width b) := by
    apply max_le
    · dsimp only [x]
      omega
    · dsimp only [y]
      omega
  have hcg := (binomial_bit_compare (max x.1.length y.1.length) x.1 y.1 false
    (le_max_left _ _) (le_max_right _ _)).2
  have hxc : x.2 ≤ 5 * (width a) ^ 2 + 6 * width a * width b := by
    dsimp only [x]
    rw [hxg]
    gcongr
  have hyc : y.2 ≤ 5 * (width b) ^ 2 + 6 * width b * width a := by
    dsimp only [y]
    rw [hyg]
    gcongr
  change x.2 + y.2 + _ ≤ _
  rw [hcg]
  nlinarith [sq_nonneg (width a), sq_nonneg (width b)]

structure Selection (C : Type) where
  candidate : C
  gates : ℕ
  deriving Repr

def scan {C : Type} (score : C → ℚ × ℕ) : C → List C → Selection C
  | best, [] => ⟨best, 0⟩
  | best, c :: cs =>
    let a := score best
    let b := score c
    let cmp := less a.1 b.1
    let tail := scan score (if cmp.1 then c else best) cs
    ⟨tail.candidate, a.2 + b.2 + cmp.2 + tail.gates⟩

def rationalScan {C : Type} (score : C → ℚ) : C → List C → C
  | best, [] => best
  | best, c :: cs => rationalScan score (if score best < score c then c else best) cs

theorem scan_value {C : Type} (score : C → ℚ × ℕ) (hscore : ∀ c, 0 ≤ (score c).1)
    (best : C) (cs : List C) :
    (scan score best cs).candidate = rationalScan (fun c => (score c).1) best cs := by
  induction cs generalizing best with
  | nil => rfl
  | cons c cs ih =>
    simp only [scan, rationalScan, less_correct _ _ (hscore best) (hscore c)]
    exact ih _

theorem scan_gates {C : Type} (score : C → ℚ × ℕ) (S G : ℕ)
    (hwidth : ∀ c, width (score c).1 ≤ S) (hgate : ∀ c, (score c).2 ≤ G)
    (best : C) (cs : List C) :
    (scan score best cs).gates ≤ cs.length * (2 * G + 24 * S ^ 2 + 20 * S) := by
  induction cs generalizing best with
  | nil => simp [scan]
  | cons c cs ih =>
    have hc := less_gates (score best).1 (score c).1
    have hw : width (score best).1 + width (score c).1 ≤ 2 * S := by
      have := hwidth best
      have := hwidth c
      omega
    have hm : 6 * (width (score best).1 + width (score c).1) ^ 2 +
        10 * (width (score best).1 + width (score c).1) ≤ 24 * S ^ 2 + 20 * S := by
      calc
        _ ≤ 6 * (2 * S) ^ 2 + 10 * (2 * S) := by gcongr
        _ = _ := by ring
    change (score best).2 + (score c).2 + (less (score best).1 (score c).1).2 + _ ≤ _
    have ht := ih (if (less (score best).1 (score c).1).1 then c else best)
    have hcmp := hc.trans hm
    have ha := hgate best
    have hb := hgate c
    rw [List.length_cons, Nat.succ_mul]
    omega

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.FiniteSelection
