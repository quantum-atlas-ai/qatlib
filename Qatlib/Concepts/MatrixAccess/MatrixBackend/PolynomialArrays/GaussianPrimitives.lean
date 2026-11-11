/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Tactic
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.GaussianResponseData

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
/-! Exact shared-denominator Gaussian integer primitives used by polynomial Horner.
These declaration bodies retain the actual binary loops and declared scans from
the shared-denominator arithmetic model. No host-runtime interpretation is added. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped BigOperators

/-- A pair of integer numerators at an externally fixed common precision.
Unlike the specification-only real rounding, the operations below execute. -/
abbrev GaussianDyadicScalar := ℤ × ℤ

/-- Rational interpretation of an unreduced common-denominator pair.
Only correctness proofs use this interpretation; the integer kernels do not. -/
def gaussianFractionValue (x : GaussianDyadicScalar) (D : ℕ) : GaussianRat :=
  ((x.1 : ℚ) / D, (x.2 : ℚ) / D)

/-- Multiply both signed components by the same natural scale. -/
def gaussianIntegerScale (D : ℕ) (x : GaussianDyadicScalar) : GaussianDyadicScalar :=
  ((D : ℤ) * x.1, (D : ℤ) * x.2)

/-- The common scalar cancels without executing rational normalization. -/
theorem gaussian_fraction_scale (x : GaussianDyadicScalar) (c D : ℕ) (hc : 0 < c) :
    gaussianFractionValue (gaussianIntegerScale c x) (c * D) = gaussianFractionValue x D := by
  have hcq : (c : ℚ) ≠ 0 := by positivity
  apply Prod.ext <;> simp only [gaussianFractionValue, gaussianIntegerScale,
    Int.cast_mul, Int.cast_natCast, Nat.cast_mul] <;> field_simp

/-- Data and invariants for Gaussian Integer Fraction in the gaussian primitives model. -/
structure GaussianIntegerFraction where
  numerator : GaussianDyadicScalar
  denominator : ℕ

/-- Construction for gaussian Point Value in the gaussian primitives model. -/
noncomputable def gaussianPointValue (x : GaussianIntegerFraction) : ℂ :=
  (x.numerator.1 : ℂ) / (x.denominator : ℂ) +
    ((x.numerator.2 : ℂ) / (x.denominator : ℂ)) * Complex.I

/-- The finite construction in `Gaussian integer arithmetic` satisfies `gaussian_point_value_fraction` under the displayed hypotheses. -/
theorem gaussian_point_value_fraction (x : GaussianDyadicScalar) (D : ℕ) :
    gaussianPointValue ⟨x,D⟩ = gaussianRatComplex (gaussianFractionValue x D) := by
  simp only [gaussianPointValue,gaussianRatComplex,gaussianFractionValue,
    Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]

/-- Data and invariants for Gaussian Scan Result in the gaussian primitives model. -/
structure GaussianScanResult (α : Type) where
  value : α
  charge : ℕ

/-- Construction for gaussian Point Words in the gaussian primitives model. -/
def gaussianPointWords (x : GaussianIntegerFraction) : ℕ :=
  x.numerator.1.natAbs.size+x.numerator.2.natAbs.size+x.denominator.size+3

/-- Construction for gaussian Scan Int Add in the gaussian primitives model. -/
def gaussianScanIntAdd (x y : ℤ) : GaussianScanResult ℤ :=
  ⟨x + y, 4 * (x.natAbs.size + y.natAbs.size + 2)⟩

/-- Data and invariants for Gaussian Binary Mul Run in the gaussian primitives model. -/
structure GaussianBinaryMulRun where
  value : ℤ
  rounds : ℕ
  charge : ℕ
  deriving Repr, DecidableEq

/-- Data and invariants for Gaussian Natural Mul Run in the gaussian primitives model. -/
structure GaussianNaturalMulRun where
  value : ℕ
  rounds : ℕ
  charge : ℕ
  deriving Repr, DecidableEq

/-- Scan fees for input-bit extraction, doubling, the taken add and counter.
A scan of an L-bit field costs L+1, as in the division model. -/
def gaussianMulStepCharge (y tailInput : ℕ) (bit : Bool) (r : GaussianNaturalMulRun) : ℕ :=
  4 * (tailInput.size + 1) + 2 * (r.value.size + 1) +
    (if bit then max (r.value + r.value).size y.size + 1 else 0) +
    (r.rounds.size + 1) + 4

/-- Shift/add reads one multiplier bit and shares the previously computed value. -/
def gaussianNaturalMul (x y : ℕ) : GaussianNaturalMulRun :=
  Nat.binaryRec (motive := fun _ => GaussianNaturalMulRun) ⟨0, 0, y.size + 1⟩
    (fun bit tailInput r =>
      ⟨r.value + r.value + (if bit then y else 0), r.rounds + 1,
        r.charge + gaussianMulStepCharge y tailInput bit r⟩) x

/-- Six whole-input scans allow for signs and conversion; no signed product
is evaluated to determine its sign. The magnitude kernel is shared once. -/
def gaussianSignedMul (x y : ℤ) : GaussianBinaryMulRun :=
  let r := gaussianNaturalMul x.natAbs y.natAbs
  let value : ℤ := if x < 0 then (if y < 0 then r.value else -(r.value : ℤ))
    else (if y < 0 then -(r.value : ℤ) else r.value)
  ⟨value, r.rounds, r.charge + 6 * (x.natAbs.size + y.natAbs.size + 2)⟩

/-- Construction for gaussian Scan Int Mul in the gaussian primitives model. -/
def gaussianScanIntMul (x y : ℤ) : GaussianScanResult ℤ :=
  let r := gaussianSignedMul x y
  ⟨r.value, r.charge + r.value.natAbs.size + 1⟩

/-- Construction for gaussian Scan Int Sub in the gaussian primitives model. -/
def gaussianScanIntSub (x y : ℤ) : GaussianScanResult ℤ :=
  ⟨x - y, 4 * (x.natAbs.size + y.natAbs.size + 2)⟩

/-- Four executed binary products, then the two signed sums. -/
def gaussianScanComplexMul (x y : GaussianDyadicScalar) : GaussianScanResult GaussianDyadicScalar :=
  let rr := gaussianScanIntMul x.1 y.1
  let ii := gaussianScanIntMul x.2 y.2
  let ri := gaussianScanIntMul x.1 y.2
  let ir := gaussianScanIntMul x.2 y.1
  let re := gaussianScanIntSub rr.value ii.value
  let im := gaussianScanIntAdd ri.value ir.value
  ⟨(re.value, im.value), rr.charge + ii.charge + ri.charge + ir.charge + re.charge + im.charge⟩

/-- Construction for gaussian Scan Nat Cast in the gaussian primitives model. -/
def gaussianScanNatCast (x : ℕ) : GaussianScanResult ℤ :=
  ⟨x, x.size + 1⟩

/-- Cast both inputs, execute one binary product and copy its magnitude. -/
def gaussianScanNatMul (x y : ℕ) : GaussianScanResult ℕ :=
  let r := gaussianSignedMul (x : ℤ) (y : ℤ)
  ⟨r.value.natAbs, r.charge + x.size + y.size + r.value.natAbs.size + 3⟩

/-- Construction for gaussian Point Horner in the gaussian primitives model. -/
def gaussianPointHorner (z : GaussianDyadicScalar) (D : ℕ) :
    List GaussianDyadicScalar → GaussianScanResult GaussianIntegerFraction
  | [] => ⟨⟨(0,0),1⟩,z.1.natAbs.size+z.2.natAbs.size+D.size+8⟩
  | c::cs =>
    let r := gaussianPointHorner z D cs
    let scale := gaussianScanNatMul r.value.denominator D
    let sc := gaussianScanNatCast scale.value
    let mul := gaussianScanComplexMul r.value.numerator z
    let re := gaussianScanIntMul sc.value c.1
    let im := gaussianScanIntMul sc.value c.2
    let x := gaussianScanIntAdd re.value mul.value.1
    let y := gaussianScanIntAdd im.value mul.value.2
    let out : GaussianIntegerFraction := ⟨(x.value,y.value),scale.value⟩
    ⟨out,r.charge+scale.charge+sc.charge+mul.charge+re.charge+im.charge+x.charge+y.charge+
      8*(gaussianPointWords r.value+gaussianPointWords out+c.1.natAbs.size+c.2.natAbs.size+
        z.1.natAbs.size+z.2.natAbs.size+D.size+8)⟩

/-- Construction for gaussian Scalar Decode in the gaussian primitives model. -/
noncomputable def gaussianScalarDecode (b : ℕ) (x : GaussianDyadicScalar) : ℂ :=
  ⟨(x.1 : ℝ) / (2 : ℝ) ^ b, (x.2 : ℝ) / (2 : ℝ) ^ b⟩

/-- Exact integer complex multiplication: no denominator and no division. -/
def gaussianIntegerMul (x y : GaussianDyadicScalar) : GaussianDyadicScalar :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Construction for gaussian Scalar Add in the gaussian primitives model. -/
def gaussianScalarAdd (x y : GaussianDyadicScalar) : GaussianDyadicScalar :=
  (x.1 + y.1, x.2 + y.2)

/-- The finite construction in `Gaussian integer arithmetic` satisfies `natural_mul_bit` under the displayed hypotheses. -/
theorem natural_mul_bit (x y : ℕ) (bit : Bool) (hb : x = 0 → bit = true) :
    gaussianNaturalMul (Nat.bit bit x) y =
      let r := gaussianNaturalMul x y
      ⟨r.value + r.value + (if bit then y else 0), r.rounds + 1,
        r.charge + gaussianMulStepCharge y x bit r⟩ := by
  unfold gaussianNaturalMul
  rw [Nat.binaryRec_eq bit x (.inr hb)]

/-- The actual radix output, before adding a cost interpretation. -/
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

/-- One carry bit suffices for an integer sum, independent of operand signs. -/
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

/-- Signed integer products have the sum of the operand magnitude bits. -/
theorem gaussian_integer_mul_bits (x y : ℤ) (a b : ℕ)
    (hx : x.natAbs.size ≤ a) (hy : y.natAbs.size ≤ b) : (x * y).natAbs.size ≤ a + b := by
  apply Nat.size_le.mpr
  rw [Int.natAbs_mul, pow_add]
  exact (Nat.mul_le_mul_right y.natAbs (Nat.size_le.mp hx).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.size_le.mp hy) (by positivity))

/-- The finite construction in `Gaussian integer arithmetic` satisfies `natural_mul_bits` under the displayed hypotheses. -/
theorem natural_mul_bits (x y : ℕ) : (x * y).size ≤ x.size + y.size := by
  have h := gaussian_integer_mul_bits (x : ℤ) (y : ℤ) x.size y.size
    (by simp) (by simp)
  simpa only [← Nat.cast_mul, Int.natAbs_natCast] using h

/-- The estimate `mul_step_charge_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem mul_step_charge_bound (x y : ℕ) (bit : Bool) (hb : x = 0 → bit = true) :
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

/-- The estimate `natural_mul_charge_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem natural_mul_charge_bound (x y : ℕ) :
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

/-- G216: signed binary multiplication computes the true product and exposes
its radix length and a quadratic fee, without evaluating a product oracle. -/
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

/-- The finite construction in `Gaussian integer arithmetic` satisfies `gaussian_scan_int_mul_value` under the displayed hypotheses. -/
theorem gaussian_scan_int_mul_value (x y : ℤ) :
    (gaussianScanIntMul x y).value = x * y := (gaussian_signed_mul_certificate x y).1

/-- The finite construction in `Gaussian integer arithmetic` satisfies `gaussian_scan_complex_mul_value` under the displayed hypotheses. -/
theorem gaussian_scan_complex_mul_value (x y : GaussianDyadicScalar) :
    (gaussianScanComplexMul x y).value = gaussianIntegerMul x y := by
  simp only [gaussianScanComplexMul, gaussian_scan_int_mul_value,
    gaussianScanIntSub, gaussianScanIntAdd, gaussianIntegerMul]

/-- The finite construction in `Gaussian integer arithmetic` satisfies `gaussian_scan_nat_mul_value` under the displayed hypotheses. -/
theorem gaussian_scan_nat_mul_value (x y : ℕ) :
    (gaussianScanNatMul x y).value = x * y := by
  simp only [gaussianScanNatMul, (gaussian_signed_mul_certificate (x : ℤ) (y : ℤ)).1,
    Int.natAbs_mul, Int.natAbs_natCast]

/-- The finite construction in `Gaussian integer arithmetic` satisfies `gaussian_point_horner_cons` under the displayed hypotheses. -/
theorem gaussian_point_horner_cons (c : GaussianDyadicScalar) (cs : List GaussianDyadicScalar)
    (z : GaussianDyadicScalar) (D : ℕ) :
    (gaussianPointHorner z D (c::cs)).value =
      ⟨gaussianScalarAdd (gaussianIntegerScale ((gaussianPointHorner z D cs).value.denominator*D) c)
        (gaussianIntegerMul (gaussianPointHorner z D cs).value.numerator z),
        (gaussianPointHorner z D cs).value.denominator*D⟩ := by
  simp only [gaussianPointHorner,gaussian_scan_nat_mul_value,gaussianScanNatCast,
    gaussian_scan_complex_mul_value,gaussian_scan_int_mul_value,gaussianScanIntAdd,
    gaussianIntegerScale,gaussianScalarAdd]

/-- The finite construction in `Gaussian integer arithmetic` satisfies `gaussian_point_horner_denominator` under the displayed hypotheses. -/
theorem gaussian_point_horner_denominator (cs : List GaussianDyadicScalar)
    (z : GaussianDyadicScalar) (D : ℕ) :
    (gaussianPointHorner z D cs).value.denominator = D^cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [gaussian_point_horner_cons,ih,List.length_cons,pow_succ]

/-- Addition of common-denominator integer numerators is exact. -/
theorem gaussian_fraction_add (x y : GaussianDyadicScalar) (D : ℕ) :
    gaussianFractionValue (gaussianScalarAdd x y) D =
      gadd (gaussianFractionValue x D) (gaussianFractionValue y D) := by
  apply Prod.ext <;> simp only [gaussianFractionValue, gaussianScalarAdd, Int.cast_add, gadd] <;> ring

/-- Common-denominator multiplication agrees with rational pair multiplication. -/
theorem gaussian_fraction_mul (x y : GaussianDyadicScalar) (D E : ℕ) :
    gaussianFractionValue (gaussianIntegerMul x y) (D * E) =
      gmul (gaussianFractionValue x D) (gaussianFractionValue y E) := by
  apply Prod.ext <;>
    simp only [gaussianFractionValue, gaussianIntegerMul, gmul, Int.cast_sub,
      Int.cast_add, Int.cast_mul, Nat.cast_mul] <;> ring

/-- The finite construction in `Gaussian integer arithmetic` satisfies `gaussian_point_value_one` under the displayed hypotheses. -/
theorem gaussian_point_value_one (x : GaussianDyadicScalar) :
    gaussianPointValue ⟨x,1⟩ = gaussianScalarDecode 0 x := by
  apply Complex.ext <;> simp [gaussianPointValue,gaussianScalarDecode]

/-- The finite construction in `Gaussian integer arithmetic` satisfies `point_horner_step_value` under the displayed hypotheses. -/
theorem point_horner_step_value (c x z : GaussianDyadicScalar) (E D : ℕ)
    (hE : 0<E) (hD : 0<D) :
    gaussianPointValue ⟨gaussianScalarAdd (gaussianIntegerScale (E*D) c) (gaussianIntegerMul x z),E*D⟩ =
    gaussianScalarDecode 0 c+gaussianPointValue ⟨x,E⟩*gaussianPointValue ⟨z,D⟩ := by
  simp only [gaussian_point_value_fraction,gaussian_fraction_add,complex_gadd,
    gaussian_fraction_mul,complex_gmul]
  have hc := gaussian_fraction_scale c (E*D) 1 (Nat.mul_pos hE hD)
  simp only [Nat.mul_one] at hc
  rw [hc,← gaussian_point_value_fraction,gaussian_point_value_one]

/-- G545: all finite coefficients enter the exact same Horner value. -/
theorem gaussian_point_horner_correct : ∀ (n : ℕ) (c : Fin n → GaussianDyadicScalar)
    (z : GaussianDyadicScalar) (D : ℕ), 0<D →
    let r := gaussianPointHorner z D (List.ofFn c)
    r.value.denominator = D^n ∧
    gaussianPointValue r.value = ∑ i : Fin n,
      gaussianScalarDecode 0 (c i)*(gaussianPointValue ⟨z,D⟩)^i.val := by
  intro n c z D hD
  refine ⟨by simp only [gaussian_point_horner_denominator,List.length_ofFn],?_⟩
  induction n with
  | zero => simp [List.ofFn_zero,gaussianPointHorner,gaussianPointValue]
  | succ n ih =>
    rw [List.ofFn_succ,gaussian_point_horner_cons,point_horner_step_value]
    · rw [ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ,Finset.sum_mul]
      apply congrArg (fun v => gaussianScalarDecode 0 (c 0)+v)
      apply Finset.sum_congr rfl
      intro i _
      ring
    · rw [gaussian_point_horner_denominator]
      exact Nat.pow_pos hD
    · exact hD

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian
