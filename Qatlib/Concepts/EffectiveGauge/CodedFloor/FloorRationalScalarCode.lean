/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorRationalCode
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.NegativeExpProgram
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Floor Rational Scalar Code

Coded Floor constructions for Effective Gauge.
Defines `floorRationalCodePow`, `floorRationalCodeCeil`, `floorRationalCodeAbs`.
Proves `floorRationalCodePow_value`, `primrec_floorRationalCodePow`, `floorRationalCodeCeil_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of floor Rational Code Pow in the Coded Floor construction. -/
def floorRationalCodePow (q : FloorRationalCode) : ℕ → FloorRationalCode
  | 0 => floorRationalCodeNat 1
  | n+1 => floorRationalCodeMul (floorRationalCodePow q n) q

/-- Definition of floor Rational Code Ceil in the Coded Floor construction. -/
def floorRationalCodeCeil (q : FloorRationalCode) : ℕ :=
  (q.1.1-q.1.2+q.2)/(q.2+1)

/-- Decoding the natural power of a rational code gives the corresponding power of its rational
value. -/
theorem floorRationalCodePow_value (q : FloorRationalCode) (n : ℕ) :
    floorRationalCodeValue (floorRationalCodePow q n)=(floorRationalCodeValue q)^n := by
  induction n with
  | zero => simp [floorRationalCodePow,floorRationalCodeNat_value]
  | succ n ih => rw [floorRationalCodePow,floorRationalCodeMul_value,ih,pow_succ]

/-- Exponentiation of a rational code is primitive recursive jointly in the code and the natural
exponent. -/
theorem primrec_floorRationalCodePow : Primrec₂ floorRationalCodePow := by
  have hs : Primrec₂ (fun (q : FloorRationalCode) (state : ℕ × FloorRationalCode) =>
      floorRationalCodeMul state.2 q) :=
    primrec_floorRationalCodeMul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  apply (Primrec.nat_rec (Primrec.const (floorRationalCodeNat 1)) hs).of_eq
  intro q n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one,floorRationalCodePow] using congrArg (fun x => floorRationalCodeMul x q) ih

/-- The ceiling computed from a rational code is the natural ceiling of its decoded value. -/
theorem floorRationalCodeCeil_value (q : FloorRationalCode) :
    floorRationalCodeCeil q=Nat.ceil (floorRationalCodeValue q) := by
  have he : floorRationalCodeCeil q=(q.1.1-q.1.2) ⌈/⌉ (q.2+1) := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    unfold floorRationalCodeCeil
    congr 1
  apply eq_of_forall_ge_iff
  intro k
  rw [he,ceilDiv_le_iff_le_mul (Nat.zero_lt_succ _),Nat.ceil_le,Nat.sub_le_iff_le_add]
  unfold floorRationalCodeValue
  rw [div_le_iff₀ (by positivity : (0 : ℚ)<((q.2+1 : ℕ) : ℚ))]
  push_cast
  constructor
  · intro h
    have hQ : (q.1.1 : ℚ) ≤ ((q.2 : ℚ)+1)*(k : ℚ)+(q.1.2 : ℚ) := by exact_mod_cast h
    nlinarith
  · intro h
    have hQ : (q.1.1 : ℚ) ≤ ((q.2 : ℚ)+1)*(k : ℚ)+(q.1.2 : ℚ) := by nlinarith
    exact_mod_cast hQ

/-- Computing the natural ceiling directly from a rational code is primitive recursive. -/
theorem primrec_floorRationalCodeCeil : Primrec floorRationalCodeCeil :=
  Primrec.nat_div.comp
    (Primrec.nat_add.comp
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))

/-- The ceiling base-two logarithm of `n` equals `k` exactly when `n ≤ 2^k` and either `k = 0` or
the previous power `2^(k - 1)` is strictly below `n`. -/
theorem floorClogTwo_graph (n k : ℕ) :
    Nat.clog 2 n=k ↔ n ≤ 2^k ∧ (k=0 ∨ 2^(k-1)<n) := by
  constructor
  · intro he
    subst k
    refine ⟨Nat.le_pow_clog (by decide) _,?_⟩
    by_cases hz : Nat.clog 2 n=0
    · exact Or.inl hz
    · exact Or.inr ((Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega))
  · rintro ⟨hupper,hminimal⟩
    have hu := (Nat.clog_le_iff_le_pow (by decide)).mpr hupper
    rcases hminimal with rfl|hminimal
    · omega
    · have hl := (Nat.lt_clog_iff_pow_lt (by decide)).mpr hminimal
      omega

/-- The natural ceiling logarithm to base two is primitive recursive. -/
theorem primrec_floorClogTwo : Primrec (Nat.clog 2) := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hgraph : PrimrecRel (fun n k : ℕ =>
      n ≤ 2^k ∧ (k=0 ∨ 2^(k-1)<n)) :=
    PrimrecPred.and (Primrec.nat_le.comp Primrec.fst (hpow.comp (Primrec.const 2) Primrec.snd))
      (PrimrecPred.or (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Primrec.nat_lt.comp
          (hpow.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))) Primrec.fst))
  apply Primrec.of_graph ⟨id,Primrec.id,?_⟩ (hgraph.of_eq (fun n k => (floorClogTwo_graph n k).symm))
  intro n
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  exact (Nat.lt_pow_self (by decide : 1<2)).le

/-- Definition of floor Rational Code Abs in the Coded Floor construction. -/
def floorRationalCodeAbs (q : FloorRationalCode) : FloorRationalCode :=
  if q.1.2 ≤ q.1.1 then q else floorRationalCodeNeg q

/-- Definition of floor Rational Code Min in the Coded Floor construction. -/
def floorRationalCodeMin (q r : FloorRationalCode) : FloorRationalCode :=
  if floorRationalCodeLE q r then q else r

/-- Definition of floor Rational Code Max in the Coded Floor construction. -/
def floorRationalCodeMax (q r : FloorRationalCode) : FloorRationalCode :=
  if floorRationalCodeLE q r then r else q

/-- Definition of floor Rational Code Arctan Fuel in the Coded Floor construction. -/
def floorRationalCodeArctanFuel (q : FloorRationalCode) : ℕ :=
  Nat.clog 2 (floorRationalCodeCeil (floorRationalCodeInv q))

/-- The absolute-value code decodes to the absolute value of the represented rational. -/
theorem floorRationalCodeAbs_value (q : FloorRationalCode) :
    floorRationalCodeValue (floorRationalCodeAbs q)=|floorRationalCodeValue q| := by
  unfold floorRationalCodeAbs
  split_ifs with h
  · apply (abs_of_nonneg _).symm
    unfold floorRationalCodeValue
    apply div_nonneg _ (by positivity)
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · rw [floorRationalCodeNeg_value]
    apply (abs_of_nonpos _).symm
    unfold floorRationalCodeValue
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact sub_nonpos.mpr (by exact_mod_cast (not_le.mp h).le)

/-- Selecting the minimum by coded comparison represents the minimum of the two rational values. -/
theorem floorRationalCodeMin_value (q r : FloorRationalCode) :
    floorRationalCodeValue (floorRationalCodeMin q r)=
      min (floorRationalCodeValue q) (floorRationalCodeValue r) := by
  unfold floorRationalCodeMin
  split_ifs with h
  · rw [min_eq_left ((floorRationalCodeLE_value q r).mp h)]
  · rw [min_eq_right (le_of_not_ge (fun hh => h ((floorRationalCodeLE_value q r).mpr hh)))]

/-- Selecting the maximum by coded comparison represents the maximum of the two rational values. -/
theorem floorRationalCodeMax_value (q r : FloorRationalCode) :
    floorRationalCodeValue (floorRationalCodeMax q r)=
      max (floorRationalCodeValue q) (floorRationalCodeValue r) := by
  unfold floorRationalCodeMax
  split_ifs with h
  · rw [max_eq_right ((floorRationalCodeLE_value q r).mp h)]
  · rw [max_eq_left (le_of_not_ge (fun hh => h ((floorRationalCodeLE_value q r).mpr hh)))]

/-- The fuel computed from a rational code equals the arctangent series fuel for the decoded
tolerance. -/
theorem floorRationalCodeArctanFuel_value (q : FloorRationalCode) :
    floorRationalCodeArctanFuel q=arctanFuel (floorRationalCodeValue q) := by
  simp only [floorRationalCodeArctanFuel,arctanFuel,floorRationalCodeCeil_value,
    floorRationalCodeInv_value,one_div]

/-- Taking the absolute value of a coded rational is primitive recursive. -/
theorem primrec_floorRationalCodeAbs : Primrec floorRationalCodeAbs :=
  Primrec.ite (Primrec.nat_le.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
    Primrec.id primrec_floorRationalCodeNeg

/-- Selecting the minimum rational code by value is primitive recursive in both input codes. -/
theorem primrec_floorRationalCodeMin : Primrec₂ floorRationalCodeMin :=
  Primrec.ite primrec_floorRationalCodeLE Primrec.fst Primrec.snd

/-- Selecting the maximum rational code by value is primitive recursive in both input codes. -/
theorem primrec_floorRationalCodeMax : Primrec₂ floorRationalCodeMax :=
  Primrec.ite primrec_floorRationalCodeLE Primrec.snd Primrec.fst

/-- Computing arctangent series fuel by taking the base-two ceiling logarithm of the natural
ceiling of the coded reciprocal is primitive recursive. -/
theorem primrec_floorRationalCodeArctanFuel : Primrec floorRationalCodeArctanFuel :=
  primrec_floorClogTwo.comp (primrec_floorRationalCodeCeil.comp primrec_floorRationalCodeInv)

end Qatlib.Concepts.EffectiveGauge.CodedFloor
