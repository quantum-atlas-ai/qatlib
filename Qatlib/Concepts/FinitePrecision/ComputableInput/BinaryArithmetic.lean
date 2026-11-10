/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.GaussianFFTDefs

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput
open scoped BigOperators

structure GaussianNaturalDivisionRun where
  quotient : ℕ
  remainder : ℕ
  rounds : ℕ
  deriving Repr, DecidableEq

def gaussianDivisionStep (D : ℕ) (bit : Bool) (r : GaussianNaturalDivisionRun) :
    GaussianNaturalDivisionRun :=
  let trial := Nat.bit bit r.remainder
  if D ≤ trial then ⟨Nat.bit true r.quotient, trial - D, r.rounds + 1⟩
  else ⟨Nat.bit false r.quotient, trial, r.rounds + 1⟩

def gaussianNaturalDivision (D n : ℕ) : GaussianNaturalDivisionRun :=
  Nat.binaryRec (motive := fun _ => GaussianNaturalDivisionRun) ⟨0, 0, 0⟩
    (fun bit _ r => gaussianDivisionStep D bit r) n

structure GaussianSignedDivisionRun where
  quotient : ℤ
  remainder : ℤ
  rounds : ℕ
  deriving Repr, DecidableEq

def gaussianSignedDivision (n : ℤ) (D : ℕ) : GaussianSignedDivisionRun :=
  if D = 0 then ⟨0, n, 0⟩ else
  let r := gaussianNaturalDivision D n.natAbs
  if 0 ≤ n then ⟨r.quotient, r.remainder, r.rounds⟩ else
  if r.remainder = 0 then ⟨-(r.quotient : ℤ), 0, r.rounds⟩ else
    ⟨-(r.quotient : ℤ) - 1, (D : ℤ) - r.remainder, r.rounds⟩

def gaussianDivisionStepCharge (D tailInput : ℕ) (bit : Bool) (r : GaussianNaturalDivisionRun) : ℕ :=
  let trial := Nat.bit bit r.remainder
  let width := max D.size trial.size + 1
  4 * (tailInput.size + 1) + 2 * (r.quotient.size + 1) + 2 * (r.remainder.size + 1) +
    2 * width + (if D ≤ trial then width else 0) + (r.rounds.size + 1) + 4

structure GaussianNaturalDivisionCharged where
  value : GaussianNaturalDivisionRun
  charge : ℕ
  deriving Repr, DecidableEq

def gaussianChargedNaturalDivision (D n : ℕ) : GaussianNaturalDivisionCharged :=
  Nat.binaryRec (motive := fun _ => GaussianNaturalDivisionCharged) ⟨⟨0, 0, 0⟩, D.size + 1⟩
    (fun bit tailInput r => ⟨gaussianDivisionStep D bit r.value,
      r.charge + gaussianDivisionStepCharge D tailInput bit r.value⟩) n

structure GaussianSignedDivisionCharged where
  value : GaussianSignedDivisionRun
  charge : ℕ
  deriving Repr, DecidableEq

def gaussianChargedSignedDivision (n : ℤ) (D : ℕ) : GaussianSignedDivisionCharged :=
  if D = 0 then ⟨⟨0, n, 0⟩, n.natAbs.size + 1⟩ else
  let r := gaussianChargedNaturalDivision D n.natAbs
  let value : GaussianSignedDivisionRun :=
    if 0 ≤ n then ⟨r.value.quotient, r.value.remainder, r.value.rounds⟩ else
    if r.value.remainder = 0 then ⟨-(r.value.quotient : ℤ), 0, r.value.rounds⟩ else
      ⟨-(r.value.quotient : ℤ) - 1, (D : ℤ) - r.value.remainder, r.value.rounds⟩
  ⟨value, r.charge + 6 * (n.natAbs.size + D.size + 2)⟩

structure GaussianNaturalMulRun where
  value : ℕ
  rounds : ℕ
  charge : ℕ
  deriving Repr, DecidableEq

def gaussianMulStepCharge (y tailInput : ℕ) (bit : Bool) (r : GaussianNaturalMulRun) : ℕ :=
  4 * (tailInput.size + 1) + 2 * (r.value.size + 1) +
    (if bit then max (r.value + r.value).size y.size + 1 else 0) +
    (r.rounds.size + 1) + 4

def gaussianNaturalMul (x y : ℕ) : GaussianNaturalMulRun :=
  Nat.binaryRec (motive := fun _ => GaussianNaturalMulRun) ⟨0, 0, y.size + 1⟩
    (fun bit tailInput r =>
      ⟨r.value + r.value + (if bit then y else 0), r.rounds + 1,
        r.charge + gaussianMulStepCharge y tailInput bit r⟩) x

structure GaussianBinaryMulRun where
  value : ℤ
  rounds : ℕ
  charge : ℕ
  deriving Repr, DecidableEq

def gaussianSignedMul (x y : ℤ) : GaussianBinaryMulRun :=
  let r := gaussianNaturalMul x.natAbs y.natAbs
  let value : ℤ := if x < 0 then (if y < 0 then r.value else -(r.value : ℤ))
    else (if y < 0 then -(r.value : ℤ) else r.value)
  ⟨value, r.rounds, r.charge + 6 * (x.natAbs.size + y.natAbs.size + 2)⟩

structure GaussianBinaryScalarRun where
  value : GaussianDyadicScalar
  charge : ℕ
  deriving Repr, DecidableEq

def gaussianBinaryComplexMul (D : ℕ) (x y : GaussianDyadicScalar) : GaussianBinaryScalarRun :=
  let ac := gaussianSignedMul x.1 y.1
  let bd := gaussianSignedMul x.2 y.2
  let ad := gaussianSignedMul x.1 y.2
  let bc := gaussianSignedMul x.2 y.1
  let re := gaussianChargedSignedDivision (ac.value - bd.value) D
  let im := gaussianChargedSignedDivision (ad.value + bc.value) D
  let adds := 2 * (max ac.value.natAbs.size bd.value.natAbs.size + 1) +
    2 * (max ad.value.natAbs.size bc.value.natAbs.size + 1)
  ⟨(re.value.quotient, im.value.quotient),
    ac.charge + bd.charge + ad.charge + bc.charge + adds + re.charge + im.charge⟩

theorem gaussian_integer_mul_bits (x y : ℤ) (a b : ℕ)
    (hx : x.natAbs.size ≤ a) (hy : y.natAbs.size ≤ b) : (x * y).natAbs.size ≤ a + b := by
  apply Nat.size_le.mpr
  rw [Int.natAbs_mul, pow_add]
  exact (Nat.mul_le_mul_right y.natAbs (Nat.size_le.mp hx).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.size_le.mp hy) (by positivity))

theorem gaussian_integer_add_bits (x y : ℤ) (a b : ℕ)
    (hx : x.natAbs.size ≤ a) (hy : y.natAbs.size ≤ b) :
    (x + y).natAbs.size ≤ max a b + 1 := by
  have hx' : x.natAbs < 2 ^ max a b :=
    (Nat.size_le.mp hx).trans_le (pow_le_pow_right₀ (by norm_num) (le_max_left _ _))
  have hy' : y.natAbs < 2 ^ max a b :=
    (Nat.size_le.mp hy).trans_le (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))
  apply Nat.size_le.mpr
  have h := Int.natAbs_add_le x y
  rw [pow_succ]
  omega

private theorem natural_division_bit (D n : ℕ) (bit : Bool) (h : n = 0 → bit = true) :
    gaussianNaturalDivision D (Nat.bit bit n) =
      gaussianDivisionStep D bit (gaussianNaturalDivision D n) := by
  unfold gaussianNaturalDivision
  rw [Nat.binaryRec_eq bit n (.inr h)]

theorem gaussian_natural_division_correct (D n : ℕ) (hD : 0 < D) :
    let r := gaussianNaturalDivision D n
    r.remainder + D * r.quotient = n ∧ r.remainder < D ∧ r.rounds = n.size := by
  induction n using Nat.binaryRec' with
  | zero => simpa [gaussianNaturalDivision] using hD
  | bit bit n hb ih =>
    have hne : Nat.bit bit n ≠ 0 := Nat.bit_ne_zero_iff.mpr hb
    obtain ⟨hi, hr, hs⟩ := ih
    dsimp only at hi hr hs ⊢
    rw [natural_division_bit D n bit hb]
    dsimp only [gaussianDivisionStep]
    split_ifs with h
    · refine ⟨?_, ?_, ?_⟩
      · have hsub := Nat.sub_add_cancel h
        cases bit <;> simp [Nat.bit] at hsub ⊢ <;> nlinarith only [hi, hsub]
      · have hsub := Nat.sub_add_cancel h
        cases bit <;> simp [Nat.bit] at hsub ⊢ <;> nlinarith only [hr, hsub]
      · rw [hs, Nat.size_bit hne]
    · refine ⟨?_, Nat.lt_of_not_ge h, ?_⟩
      · cases bit <;> simp [Nat.bit] at ⊢ <;> nlinarith only [hi]
      · rw [hs, Nat.size_bit hne]

theorem gaussian_signed_division_correct (n : ℤ) (D : ℕ) :
    let r := gaussianSignedDivision n D
    r.quotient = n / (D : ℤ) ∧ r.remainder = n % (D : ℤ) ∧
    r.rounds = if D = 0 then 0 else n.natAbs.size := by
  by_cases hD : D = 0
  · simp [gaussianSignedDivision, hD]
  have hd : 0 < D := Nat.pos_of_ne_zero hD
  have hdZ : (0 : ℤ) < D := by exact_mod_cast hd
  let r := gaussianNaturalDivision D n.natAbs
  have hc := gaussian_natural_division_correct D n.natAbs hd
  have he : (r.remainder : ℤ) + (D : ℤ) * (r.quotient : ℤ) = (n.natAbs : ℤ) := by
    exact_mod_cast hc.1
  have hr : (r.remainder : ℤ) < (D : ℤ) := by exact_mod_cast hc.2.1
  let out := gaussianSignedDivision n D
  have hinv : out.remainder + (D : ℤ) * out.quotient = n ∧
      0 ≤ out.remainder ∧ out.remainder < (D : ℤ) := by
    dsimp only [out, gaussianSignedDivision]
    rw [if_neg hD]
    by_cases hn : 0 ≤ n
    · simp only [if_pos hn]
      rw [Int.natCast_natAbs, abs_of_nonneg hn] at he
      exact ⟨he, by positivity, hr⟩
    · simp only [if_neg hn]
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hn)] at he
      by_cases hz : r.remainder = 0
      · simp only [show (gaussianNaturalDivision D n.natAbs).remainder = 0 from hz, if_true]
        simp only [hz, Nat.cast_zero, zero_add] at he
        exact ⟨by nlinarith only [he], le_refl _, hdZ⟩
      · simp only [show (gaussianNaturalDivision D n.natAbs).remainder ≠ 0 from hz, if_false]
        have hpos : (0 : ℤ) < r.remainder := by exact_mod_cast Nat.pos_of_ne_zero hz
        exact ⟨by nlinarith only [he], sub_nonneg.mpr hr.le, sub_lt_self _ hpos⟩
  have hu := (Int.ediv_emod_unique hdZ).mpr hinv
  refine ⟨hu.1.symm, hu.2.symm, ?_⟩
  dsimp only [gaussianSignedDivision]
  simp only [if_neg hD]
  split_ifs <;> exact hc.2.2

private theorem charged_natural_bit (D n : ℕ) (bit : Bool) (hb : n = 0 → bit = true) :
    gaussianChargedNaturalDivision D (Nat.bit bit n) =
      ⟨gaussianDivisionStep D bit (gaussianChargedNaturalDivision D n).value,
        (gaussianChargedNaturalDivision D n).charge +
          gaussianDivisionStepCharge D n bit (gaussianChargedNaturalDivision D n).value⟩ := by
  unfold gaussianChargedNaturalDivision
  rw [Nat.binaryRec_eq bit n (.inr hb)]

theorem gaussian_charged_natural_value (D n : ℕ) :
    (gaussianChargedNaturalDivision D n).value = gaussianNaturalDivision D n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit bit n hb ih =>
    rw [charged_natural_bit D n bit hb]
    change gaussianDivisionStep D bit (gaussianChargedNaturalDivision D n).value = _
    rw [ih]
    unfold gaussianNaturalDivision
    rw [Nat.binaryRec_eq bit n (.inr hb)]

private theorem division_step_charge_bound (D n : ℕ) (bit : Bool) (hD : 0 < D)
    (hb : n = 0 → bit = true) :
    gaussianDivisionStepCharge D n bit (gaussianNaturalDivision D n) ≤
      16 * ((Nat.bit bit n).size + D.size + 2) := by
  have hc := gaussian_natural_division_correct D n hD
  have hm : (gaussianNaturalDivision D n).quotient ≤ D * (gaussianNaturalDivision D n).quotient :=
    Nat.le_mul_of_pos_left _ hD
  have hq : (gaussianNaturalDivision D n).quotient ≤ n := by nlinarith only [hc.1, hm]
  have hr : (gaussianNaturalDivision D n).remainder ≤ n := by nlinarith only [hc.1]
  have hqbits := Nat.size_le_size hq
  have hrbits := Nat.size_le_size hr
  have ht : Nat.bit bit (gaussianNaturalDivision D n).remainder ≤ Nat.bit bit n := by
    cases bit <;> simp [Nat.bit] <;> omega
  have htbits := Nat.size_le_size ht
  have hcBits : (gaussianNaturalDivision D n).rounds.size ≤ n.size := by
    rw [hc.2.2]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hn : (Nat.bit bit n).size = n.size + 1 := by
    exact Nat.size_bit (Nat.bit_ne_zero_iff.mpr hb)
  dsimp only [gaussianDivisionStepCharge]
  split_ifs <;> omega

theorem gaussian_charged_natural_bound (D n : ℕ) (hD : 0 < D) :
    (gaussianChargedNaturalDivision D n).charge ≤
      D.size + 1 + 16 * n.size * (n.size + D.size + 2) := by
  induction n using Nat.binaryRec' with
  | zero => simp [gaussianChargedNaturalDivision]
  | bit bit n hb ih =>
    rw [charged_natural_bit D n bit hb]
    dsimp only
    rw [gaussian_charged_natural_value]
    have hstep := division_step_charge_bound D n bit hD hb
    have hn : (Nat.bit bit n).size = n.size + 1 := Nat.size_bit (Nat.bit_ne_zero_iff.mpr hb)
    rw [hn] at hstep ⊢
    nlinarith only [ih, hstep]

theorem gaussian_charged_signed_certificate (n : ℤ) (D : ℕ) :
    let r := gaussianChargedSignedDivision n D
    r.value = gaussianSignedDivision n D ∧
    r.charge ≤ 64 * (n.natAbs.size + D.size + 2) ^ 2 := by
  by_cases hD : D = 0
  · subst D
    refine ⟨rfl, ?_⟩
    change n.natAbs.size + 1 ≤ 64 * (n.natAbs.size + 2) ^ 2
    nlinarith
  have hvalue : (gaussianChargedSignedDivision n D).value = gaussianSignedDivision n D := by
    dsimp only [gaussianChargedSignedDivision, gaussianSignedDivision]
    simp only [if_neg hD, gaussian_charged_natural_value]
  refine ⟨hvalue, ?_⟩
  let W := n.natAbs.size + D.size + 2
  have hW : 1 ≤ W := by dsimp only [W]; omega
  have hsq : W ≤ W ^ 2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hW (show (1 : ℕ) ≤ 2 by decide)
  have hm := Nat.mul_le_mul_right W (show n.natAbs.size ≤ W by dsimp only [W]; omega)
  have hcost := gaussian_charged_natural_bound D n.natAbs (Nat.pos_of_ne_zero hD)
  change (gaussianChargedSignedDivision n D).charge ≤ 64 * W ^ 2
  dsimp only [gaussianChargedSignedDivision]
  rw [if_neg hD]
  change (gaussianChargedNaturalDivision D n.natAbs).charge + 6 * W ≤ _
  have hDsmall : D.size + 1 ≤ W := by dsimp only [W]; omega
  change (gaussianChargedNaturalDivision D n.natAbs).charge ≤ D.size + 1 + 16 * n.natAbs.size * W at hcost
  nlinarith only [hcost, hm, hsq, hDsmall]

private theorem natural_mul_bit (x y : ℕ) (bit : Bool) (hb : x = 0 → bit = true) :
    gaussianNaturalMul (Nat.bit bit x) y =
      let r := gaussianNaturalMul x y
      ⟨r.value + r.value + (if bit then y else 0), r.rounds + 1,
        r.charge + gaussianMulStepCharge y x bit r⟩ := by
  unfold gaussianNaturalMul
  rw [Nat.binaryRec_eq bit x (.inr hb)]

theorem gaussian_natural_mul_value (x y : ℕ) :
    (gaussianNaturalMul x y).value = x * y ∧ (gaussianNaturalMul x y).rounds = x.size := by
  induction x using Nat.binaryRec' with
  | zero => simp [gaussianNaturalMul]
  | bit bit x hb ih =>
    rw [natural_mul_bit x y bit hb]
    dsimp only
    rw [ih.1, ih.2, Nat.size_bit (Nat.bit_ne_zero_iff.mpr hb)]
    constructor
    · cases bit <;> simp [Nat.bit] <;> ring
    · rfl

private theorem natural_mul_bits (x y : ℕ) : (x * y).size ≤ x.size + y.size := by
  have h := gaussian_integer_mul_bits (x : ℤ) (y : ℤ) x.size y.size
    (by simp) (by simp)
  simpa only [← Nat.cast_mul, Int.natAbs_natCast] using h

private theorem mul_step_charge_bound (x y : ℕ) (bit : Bool) (hb : x = 0 → bit = true) :
    gaussianMulStepCharge y x bit (gaussianNaturalMul x y) ≤
      16 * ((Nat.bit bit x).size + y.size + 2) := by
  have hc := gaussian_natural_mul_value x y
  have hp : (gaussianNaturalMul x y).value.size ≤ x.size + y.size := by
    rw [hc.1]; exact natural_mul_bits x y
  have hs := gaussian_integer_add_bits ((gaussianNaturalMul x y).value : ℤ)
    ((gaussianNaturalMul x y).value : ℤ) (x.size + y.size) (x.size + y.size)
    (by simpa only [Int.natAbs_natCast] using hp) (by simpa only [Int.natAbs_natCast] using hp)
  have hsum : ((gaussianNaturalMul x y).value + (gaussianNaturalMul x y).value).size ≤
      x.size + y.size + 1 := by
    simpa only [← Nat.cast_add, Int.natAbs_natCast, max_self] using hs
  have hr : (gaussianNaturalMul x y).rounds.size ≤ x.size := by
    rw [hc.2]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hn : (Nat.bit bit x).size = x.size + 1 := Nat.size_bit (Nat.bit_ne_zero_iff.mpr hb)
  dsimp only [gaussianMulStepCharge]
  split_ifs <;> omega

private theorem natural_mul_charge_bound (x y : ℕ) :
    (gaussianNaturalMul x y).charge ≤ y.size + 1 + 16 * x.size * (x.size + y.size + 2) := by
  induction x using Nat.binaryRec' with
  | zero => simp [gaussianNaturalMul]
  | bit bit x hb ih =>
    rw [natural_mul_bit x y bit hb]
    dsimp only
    have hs := mul_step_charge_bound x y bit hb
    have hn : (Nat.bit bit x).size = x.size + 1 := Nat.size_bit (Nat.bit_ne_zero_iff.mpr hb)
    rw [hn] at hs ⊢
    nlinarith only [ih, hs]

theorem gaussian_signed_mul_certificate (x y : ℤ) :
    let r := gaussianSignedMul x y
    r.value = x * y ∧ r.rounds = x.natAbs.size ∧
      r.charge ≤ 64 * (x.natAbs.size + y.natAbs.size + 2) ^ 2 := by
  have hc := gaussian_natural_mul_value x.natAbs y.natAbs
  refine ⟨?_, hc.2, ?_⟩
  · dsimp only [gaussianSignedMul]
    rw [hc.1]
    push_cast
    split_ifs with hx hy hy
    · rw [abs_of_neg hx, abs_of_neg hy]; ring
    · rw [abs_of_neg hx, abs_of_nonneg (le_of_not_gt hy)]; ring
    · rw [abs_of_nonneg (le_of_not_gt hx), abs_of_neg hy]; ring
    · rw [abs_of_nonneg (le_of_not_gt hx), abs_of_nonneg (le_of_not_gt hy)]
  · let W := x.natAbs.size + y.natAbs.size + 2
    have hW : 1 ≤ W := by dsimp only [W]; omega
    have hm : x.natAbs.size * W ≤ W ^ 2 := by
      have h := Nat.mul_le_mul_right W (show x.natAbs.size ≤ W by dsimp only [W]; omega)
      nlinarith only [h]
    have hs : W ≤ W ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hW (by decide : 1 ≤ 2)
    have hy : y.natAbs.size + 1 ≤ W := by dsimp only [W]; omega
    have hh := natural_mul_charge_bound x.natAbs y.natAbs
    change (gaussianNaturalMul x.natAbs y.natAbs).charge ≤ y.natAbs.size + 1 + 16 * x.natAbs.size * W at hh
    change (gaussianNaturalMul x.natAbs y.natAbs).charge + 6 * W ≤ 64 * W ^ 2
    nlinarith only [hh, hm, hs, hy]

theorem gaussian_signed_mul_operand_charge (x y : ℤ) :
    (gaussianSignedMul x y).charge ≤ y.natAbs.size + 1 +
      16 * x.natAbs.size * (x.natAbs.size + y.natAbs.size + 2) +
      6 * (x.natAbs.size + y.natAbs.size + 2) := by
  exact Nat.add_le_add_right (natural_mul_charge_bound x.natAbs y.natAbs) _

theorem gaussian_binary_complex_value (D : ℕ) (x y : GaussianDyadicScalar) :
    (gaussianBinaryComplexMul D x y).value = gaussianScalarMulShared (D : ℤ) x y := by
  dsimp only [gaussianBinaryComplexMul, gaussianScalarMulShared]
  simp only [(gaussian_signed_mul_certificate _ _).1,
    (gaussian_charged_signed_certificate _ _).1, (gaussian_signed_division_correct _ _).1]

theorem gaussian_binary_complex_certificate (D : ℕ) (x y : GaussianDyadicScalar) :
    (gaussianBinaryComplexMul D x y).value = gaussianScalarMulShared (D : ℤ) x y ∧
    (∀ W : ℕ, (∀ z ∈ gaussianMulWork (D : ℤ) x y, z.natAbs.size ≤ W) →
      (gaussianBinaryComplexMul D x y).charge ≤ 2048 * (W + 1) ^ 2) := by
  refine ⟨gaussian_binary_complex_value D x y, ?_⟩
  intro W hw
  have get (z : ℤ) (hz : z ∈ gaussianMulWork (D : ℤ) x y) : z.natAbs.size ≤ W := hw z hz
  have hd : D.size ≤ W := by
    simpa only [Int.natAbs_natCast] using get (D : ℤ) (by simp [gaussianMulWork])
  have mulCost (a b : ℤ) (ha : a.natAbs.size ≤ W) (hb : b.natAbs.size ≤ W) :
      (gaussianSignedMul a b).charge ≤ 256 * (W + 1) ^ 2 := by
    apply (gaussian_signed_mul_certificate a b).2.2.trans
    have h :=
        Nat.mul_le_mul_left 64
        (Nat.pow_le_pow_left (show a.natAbs.size + b.natAbs.size + 2 ≤ 2 * (W + 1) by omega) 2)
    nlinarith only [h]
  have divCost (a : ℤ) (ha : a.natAbs.size ≤ W) :
      (gaussianChargedSignedDivision a D).charge ≤ 256 * (W + 1) ^ 2 := by
    apply (gaussian_charged_signed_certificate a D).2.trans
    have h :=
        Nat.mul_le_mul_left 64
        (Nat.pow_le_pow_left (show a.natAbs.size + D.size + 2 ≤ 2 * (W + 1) by omega) 2)
    nlinarith only [h]
  have h1 := mulCost x.1 y.1 (get _ (by simp [gaussianMulWork])) (get _ (by simp [gaussianMulWork]))
  have h2 := mulCost x.2 y.2 (get _ (by simp [gaussianMulWork])) (get _ (by simp [gaussianMulWork]))
  have h3 := mulCost x.1 y.2 (get _ (by simp [gaussianMulWork])) (get _ (by simp [gaussianMulWork]))
  have h4 := mulCost x.2 y.1 (get _ (by simp [gaussianMulWork])) (get _ (by simp [gaussianMulWork]))
  have h5 := divCost (x.1 * y.1 - x.2 * y.2) (get _ (by simp [gaussianMulWork]))
  have h6 := divCost (x.1 * y.2 + x.2 * y.1) (get _ (by simp [gaussianMulWork]))
  have p1 := get (x.1 * y.1) (by simp [gaussianMulWork])
  have p2 := get (x.2 * y.2) (by simp [gaussianMulWork])
  have p3 := get (x.1 * y.2) (by simp [gaussianMulWork])
  have p4 := get (x.2 * y.1) (by simp [gaussianMulWork])
  have hadd : 2 * (max (x.1 * y.1).natAbs.size (x.2 * y.2).natAbs.size + 1) +
      2 * (max (x.1 * y.2).natAbs.size (x.2 * y.1).natAbs.size + 1) ≤ 4 * (W + 1) := by omega
  dsimp only [gaussianBinaryComplexMul]
  simp only [(gaussian_signed_mul_certificate _ _).1]
  nlinarith only [h1, h2, h3, h4, h5, h6, hadd, sq_nonneg (W : ℤ)]

end Qatlib.Concepts.FinitePrecision.ComputableInput
