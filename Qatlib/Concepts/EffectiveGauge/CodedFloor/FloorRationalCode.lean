/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Floor Rational Code

Coded Floor constructions for Effective Gauge.
Defines `FloorRationalCode`, `floorRationalCodeValue`, `floorRationalCodeNat`.
Proves `floorRationalCodeNat_value`, `floorRationalCodeNeg_value`, `floorRationalCode_product_den`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor

/-- Unreduced signed rational data. The stored denominator is one less than
the positive actual denominator, so every natural-number payload is legal. -/
abbrev FloorRationalCode := (ℕ × ℕ) × ℕ

/-- Definition of floor Rational Code Value in the Coded Floor construction. -/
def floorRationalCodeValue (q : FloorRationalCode) : ℚ :=
  ((q.1.1 : ℚ)-q.1.2)/((q.2+1 : ℕ) : ℚ)

/-- Definition of floor Rational Code Nat in the Coded Floor construction. -/
def floorRationalCodeNat (n : ℕ) : FloorRationalCode := ((n,0),0)
/-- Definition of floor Rational Code Neg in the Coded Floor construction. -/
def floorRationalCodeNeg (q : FloorRationalCode) : FloorRationalCode := ((q.1.2,q.1.1),q.2)

/-- Definition of floor Rational Code Add in the Coded Floor construction. -/
def floorRationalCodeAdd (q r : FloorRationalCode) : FloorRationalCode :=
  ((q.1.1*(r.2+1)+r.1.1*(q.2+1),q.1.2*(r.2+1)+r.1.2*(q.2+1)),
    (q.2+1)*(r.2+1)-1)

/-- Definition of floor Rational Code Mul in the Coded Floor construction. -/
def floorRationalCodeMul (q r : FloorRationalCode) : FloorRationalCode :=
  ((q.1.1*r.1.1+q.1.2*r.1.2,q.1.1*r.1.2+q.1.2*r.1.1),(q.2+1)*(r.2+1)-1)

/-- The code constructed from a natural number represents that number as a rational. -/
theorem floorRationalCodeNat_value (n : ℕ) :
    floorRationalCodeValue (floorRationalCodeNat n)=(n : ℚ) := by
  simp [floorRationalCodeValue,floorRationalCodeNat]

/-- Negating a rational code negates its decoded value. -/
theorem floorRationalCodeNeg_value (q : FloorRationalCode) :
    floorRationalCodeValue (floorRationalCodeNeg q)= -floorRationalCodeValue q := by
  dsimp [floorRationalCodeValue,floorRationalCodeNeg]
  ring

/-- Encoding the product of the two positive denominators by subtracting one and decoding by
adding one recovers the exact product. -/
theorem floorRationalCode_product_den (q r : FloorRationalCode) :
    (q.2+1)*(r.2+1)-1+1=(q.2+1)*(r.2+1) := by
  have h : 0<(q.2+1)*(r.2+1) := by positivity
  omega

/-- The coded sum represents the sum of the two decoded rational values. -/
theorem floorRationalCodeAdd_value (q r : FloorRationalCode) :
    floorRationalCodeValue (floorRationalCodeAdd q r)=
      floorRationalCodeValue q+floorRationalCodeValue r := by
  change (((q.1.1*(r.2+1)+r.1.1*(q.2+1) : ℕ) : ℚ)-
      ((q.1.2*(r.2+1)+r.1.2*(q.2+1) : ℕ) : ℚ))/
    (((q.2+1)*(r.2+1)-1+1 : ℕ) : ℚ)=_
  rw [floorRationalCode_product_den]
  dsimp only [floorRationalCodeValue]
  push_cast
  field_simp
  ring

/-- The coded product represents the product of the two decoded rational values. -/
theorem floorRationalCodeMul_value (q r : FloorRationalCode) :
    floorRationalCodeValue (floorRationalCodeMul q r)=
      floorRationalCodeValue q*floorRationalCodeValue r := by
  change (((q.1.1*r.1.1+q.1.2*r.1.2 : ℕ) : ℚ)-
      ((q.1.1*r.1.2+q.1.2*r.1.1 : ℕ) : ℚ))/
    (((q.2+1)*(r.2+1)-1+1 : ℕ) : ℚ)=_
  rw [floorRationalCode_product_den]
  dsimp only [floorRationalCodeValue]
  push_cast
  field_simp
  ring

/-- Encoding a natural as a rational with denominator one is primitive recursive. -/
theorem primrec_floorRationalCodeNat : Primrec floorRationalCodeNat :=
  (Primrec.id.pair (Primrec.const 0)).pair (Primrec.const 0)

/-- Negating a rational code is primitive recursive. -/
theorem primrec_floorRationalCodeNeg : Primrec floorRationalCodeNeg :=
  ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair Primrec.snd

/-- Coded rational addition is primitive recursive in the two input codes. -/
theorem primrec_floorRationalCodeAdd : Primrec₂ floorRationalCodeAdd := by
  have qp : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have qn : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have rp : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have rn : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have qd : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.2+1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)
  have rd : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.2+1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp qp rd) (Primrec.nat_mul.comp rp qd)).pair
    (Primrec.nat_add.comp (Primrec.nat_mul.comp qn rd) (Primrec.nat_mul.comp rn qd))).pair
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp qd rd) (Primrec.const 1))

/-- Coded rational multiplication is primitive recursive in the two input codes. -/
theorem primrec_floorRationalCodeMul : Primrec₂ floorRationalCodeMul := by
  have qp : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have qn : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have rp : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have rn : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have qd : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.2+1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)
  have rd : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.2+1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp qp rp) (Primrec.nat_mul.comp qn rn)).pair
    (Primrec.nat_add.comp (Primrec.nat_mul.comp qp rn) (Primrec.nat_mul.comp qn rp))).pair
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp qd rd) (Primrec.const 1))

/-- Definition of floor Rational Code LE in the Coded Floor construction. -/
def floorRationalCodeLE (q r : FloorRationalCode) : Prop :=
  q.1.1*(r.2+1)+r.1.2*(q.2+1) ≤ r.1.1*(q.2+1)+q.1.2*(r.2+1)

/-- Typeclass instance for floor Rational Code LE decidable in the Coded Floor construction. -/
instance floorRationalCodeLE_decidable : DecidableRel floorRationalCodeLE := fun q r =>
  inferInstanceAs (Decidable
    (q.1.1*(r.2+1)+r.1.2*(q.2+1) ≤ r.1.1*(q.2+1)+q.1.2*(r.2+1)))

/-- Definition of floor Rational Code Inv in the Coded Floor construction. -/
def floorRationalCodeInv (q : FloorRationalCode) : FloorRationalCode :=
  if q.1.1=q.1.2 then floorRationalCodeNat 0
  else if q.1.2 ≤ q.1.1 then ((q.2+1,0),q.1.1-q.1.2-1)
  else ((0,q.2+1),q.1.2-q.1.1-1)

/-- The order test on two rational codes holds exactly when their decoded values satisfy the same
weak inequality. -/
theorem floorRationalCodeLE_value (q r : FloorRationalCode) :
    floorRationalCodeLE q r ↔ floorRationalCodeValue q ≤ floorRationalCodeValue r := by
  unfold floorRationalCodeLE floorRationalCodeValue
  rw [div_le_div_iff₀ (by positivity : (0 : ℚ)<((q.2+1 : ℕ) : ℚ))
    (by positivity : (0 : ℚ)<((r.2+1 : ℕ) : ℚ))]
  push_cast
  constructor
  · intro h
    have hQ : (q.1.1 : ℚ)*((r.2 : ℚ)+1)+(r.1.2 : ℚ)*((q.2 : ℚ)+1) ≤
        (r.1.1 : ℚ)*((q.2 : ℚ)+1)+(q.1.2 : ℚ)*((r.2 : ℚ)+1) := by exact_mod_cast h
    nlinarith
  · intro h
    have hQ : (q.1.1 : ℚ)*((r.2 : ℚ)+1)+(r.1.2 : ℚ)*((q.2 : ℚ)+1) ≤
        (r.1.1 : ℚ)*((q.2 : ℚ)+1)+(q.1.2 : ℚ)*((r.2 : ℚ)+1) := by nlinarith
    exact_mod_cast hQ

/-- The inverse code represents the rational reciprocal of the decoded input, including the
totalized inverse at zero. -/
theorem floorRationalCodeInv_value (q : FloorRationalCode) :
    floorRationalCodeValue (floorRationalCodeInv q)=(floorRationalCodeValue q)⁻¹ := by
  by_cases he : q.1.1=q.1.2
  · simp [floorRationalCodeInv,he,floorRationalCodeValue,floorRationalCodeNat]
  · by_cases hp : q.1.2 ≤ q.1.1
    · have hd : q.1.1-q.1.2-1+1=q.1.1-q.1.2 := by omega
      have hcast : (q.1.1 : ℚ) ≠ (q.1.2 : ℚ) := by exact_mod_cast he
      have hne : (q.1.1 : ℚ)-(q.1.2 : ℚ) ≠ 0 := sub_ne_zero.mpr hcast
      simp only [floorRationalCodeInv,ite_eq_right he,ite_eq_left hp,floorRationalCodeValue,
        hd,Nat.cast_sub hp,Nat.cast_add,Nat.cast_one,Nat.cast_zero,sub_zero]
      field_simp [hne]
    · have hn : q.1.1 ≤ q.1.2 := (not_le.mp hp).le
      have hd : q.1.2-q.1.1-1+1=q.1.2-q.1.1 := by omega
      have hcast : (q.1.1 : ℚ) ≠ (q.1.2 : ℚ) := by exact_mod_cast he
      have hne : (q.1.1 : ℚ)-(q.1.2 : ℚ) ≠ 0 := sub_ne_zero.mpr hcast
      have hne' : (q.1.2 : ℚ)-(q.1.1 : ℚ) ≠ 0 := sub_ne_zero.mpr hcast.symm
      simp only [floorRationalCodeInv,ite_eq_right he,ite_eq_right hp,floorRationalCodeValue,
        hd,Nat.cast_sub hn,Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_sub]
      field_simp [hne,hne']
      ring

/-- Computing the code of a rational inverse is primitive recursive. -/
theorem primrec_floorRationalCodeInv : Primrec floorRationalCodeInv := by
  have qp : Primrec (fun q : FloorRationalCode => q.1.1) := Primrec.fst.comp Primrec.fst
  have qn : Primrec (fun q : FloorRationalCode => q.1.2) := Primrec.snd.comp Primrec.fst
  have qd : Primrec (fun q : FloorRationalCode => q.2+1) :=
    Primrec.nat_add.comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp qp qn) (Primrec.const (floorRationalCodeNat 0))
    (Primrec.ite (Primrec.nat_le.comp qn qp)
      ((qd.pair (Primrec.const 0)).pair (Primrec.nat_sub.comp (Primrec.nat_sub.comp qp qn) (Primrec.const 1)))
      (((Primrec.const 0).pair qd).pair (Primrec.nat_sub.comp (Primrec.nat_sub.comp qn qp) (Primrec.const 1))))

/-- The weak-order relation on rational codes is primitive recursive. -/
theorem primrec_floorRationalCodeLE : PrimrecRel floorRationalCodeLE := by
  have qp : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have qn : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have rp : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have rn : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have qd : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.1.2+1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)
  have rd : Primrec (fun q : FloorRationalCode × FloorRationalCode => q.2.2+1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)
  exact Primrec.nat_le.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp qp rd) (Primrec.nat_mul.comp rn qd))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp rp qd) (Primrec.nat_mul.comp qn rd))

end Qatlib.Concepts.EffectiveGauge.CodedFloor
