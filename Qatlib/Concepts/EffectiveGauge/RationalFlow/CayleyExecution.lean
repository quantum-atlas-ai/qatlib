/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.RationalFlow.CayleyIntegers
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.RelativeTransport
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Exact Cayley factors and the integer recurrence of the value backend

The numerator is the native integer quaternion. The state update uses
right multiplication, exactly as in cayley_transport.py; no normalization
or rounding is inserted into multiplication.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of cayley Denominator in the Rational Flow construction. -/
def cayleyDenominator (k : ℍ) (t : ℝ) : ℝ := 4+Quaternion.normSq k*t^2

/-- The real Cayley denominator `4 + ‖k‖² t²` is strictly positive for every quaternion and time. -/
theorem cayleyDenominator_pos (k : ℍ) (t : ℝ) : 0<cayleyDenominator k t := by
  have h := mul_nonneg (Quaternion.normSq_nonneg (a := k)) (sq_nonneg t)
  dsimp [cayleyDenominator]
  linarith

/-- Definition of cayley Factor in the Rational Flow construction. -/
def cayleyFactor (k : ℍ) (t : ℝ) : ℍ :=
  ((4-Quaternion.normSq k*t^2)/cayleyDenominator k t) • (1 : ℍ)+
    ((4*t)/cayleyDenominator k t) • k

/-- For pure `k`, the squared norm of `a + b k` is the sum of `a²` and `b² ‖k‖²`. -/
private theorem normSq_scalar_pure (a b : ℝ) (k : ℍ) (hk : k.re=0) :
    Quaternion.normSq (a • (1 : ℍ)+b • k)=a^2+b^2*Quaternion.normSq k := by
  simp [Quaternion.normSq_def',hk]
  ring

/-- The Cayley factor of a pure quaternion has unit norm at every real time. -/
theorem cayleyFactor_unit (k : ℍ) (hk : k.re=0) (t : ℝ) : ‖cayleyFactor k t‖=1 := by
  apply (normSq_eq_one_iff _).mp
  rw [cayleyFactor,normSq_scalar_pure _ _ k hk]
  have hn := (cayleyDenominator_pos k t).ne'
  calc
    _ = ((4-Quaternion.normSq k*t^2)^2+(4*t)^2*Quaternion.normSq k)/(cayleyDenominator k t)^2 := by
      simp only [div_pow]
      ring
    _ = (cayleyDenominator k t)^2/(cayleyDenominator k t)^2 := by
      congr 1
      dsimp [cayleyDenominator]
      ring
    _ = 1 := div_self (pow_ne_zero 2 hn)

/-- At time zero the Cayley factor is the identity for every quaternion parameter. -/
@[simp] theorem cayleyFactor_zero (k : ℍ) : cayleyFactor k 0=1 := by
  simp [cayleyFactor,cayleyDenominator]

/-- Definition of integer Quaternion Cast in the Rational Flow construction. -/
def integerQuaternionCast : Quaternion ℤ →+* ℍ where
  toFun q := ⟨(q.re : ℝ),(q.imI : ℝ),(q.imJ : ℝ),(q.imK : ℝ)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [sub_eq_add_neg]

/-- Definition of decode Cayley State in the Rational Flow construction. -/
def decodeCayleyState (s : CayleyIntegerState) : ℍ :=
  ((s.denominator : ℝ)⁻¹) • integerQuaternionCast s.numerator

/-- Casting integer quaternion coordinates to the reals commutes with computing the squared norm. -/
theorem integerQuaternionCast_normSq (q : Quaternion ℤ) :
    Quaternion.normSq (integerQuaternionCast q)=((Quaternion.normSq q : ℤ) : ℝ) := by
  simp [integerQuaternionCast,Quaternion.normSq_def']

/-- Decoding a single integer Cayley step gives the product of the decoded state and factor in that
order. -/
theorem decodeCayleyState_mul (s f : CayleyIntegerState) :
    decodeCayleyState (cayleyIntegerStep s f)=decodeCayleyState s*decodeCayleyState f := by
  simp [decodeCayleyState,cayleyIntegerStep,map_mul,smul_smul]

/-- With positive grid size, any finite integer Cayley run decodes to a unit quaternion for
arbitrary integer samples. -/
theorem cayleyIntegerRun_unit (D p : ℕ) (hD : 0<D) (a : ℕ → Fin 3 → ℤ) (n : ℕ) :
    ‖decodeCayleyState (cayleyIntegerRun D p a n)‖=1 := by
  have h := cayleyIntegerRun_certificate D p hD a n
  apply (normSq_eq_one_iff _).mp
  rw [decodeCayleyState,Quaternion.normSq_smul,integerQuaternionCast_normSq,h.2]
  have hd : ((cayleyIntegerRun D p a n).denominator : ℝ)≠0 := by exact_mod_cast h.1.ne'
  push_cast
  field_simp

/-- Definition of dyadic Coefficient in the Rational Flow construction. -/
def dyadicCoefficient (p : ℕ) (a : Fin 3 → ℤ) : ℍ :=
  ((2^p : ℝ)⁻¹) • (⟨0,(a 0 : ℝ),(a 1 : ℝ),(a 2 : ℝ)⟩ : ℍ)

/-- The coefficient uses the three integers scaled by `2⁻ᵖ` as its imaginary coordinates and has
zero real part. -/
@[simp] theorem dyadicCoefficient_re (p : ℕ) (a : Fin 3 → ℤ) : (dyadicCoefficient p a).re=0 := by
  simp [dyadicCoefficient]

/-- With positive grid size `D`, the decoded integer factor equals the real Cayley factor at time
`1 / D` for the decoded dyadic coefficient. -/
theorem decodeCayleyIntegerFactor (D p : ℕ) (hD : 0<D) (a : Fin 3 → ℤ) :
    decodeCayleyState (cayleyIntegerFactor D p a)=cayleyFactor (dyadicCoefficient p a) (1/(D : ℝ)) := by
  have hd : (0 : ℝ)<D := by exact_mod_cast hD
  have hb : (0 : ℝ)<2^p := pow_pos (by norm_num) p
  have hn : (0 : ℝ)<4*(D : ℝ)^2*(2^p : ℝ)^2+((a 0 : ℝ)^2+(a 1 : ℝ)^2+(a 2 : ℝ)^2) := by positivity
  ext <;> simp [decodeCayleyState,cayleyIntegerFactor,integerQuaternionCast,cayleyFactor,
    cayleyDenominator,dyadicCoefficient,Quaternion.normSq_def'] <;>
    field_simp [hd.ne',hb.ne',hn.ne']

/-- Definition of real Cayley Run in the Rational Flow construction. -/
def realCayleyRun (D p : ℕ) (a : ℕ → Fin 3 → ℤ) : ℕ → ℍ
  | 0 => 1
  | n+1 => realCayleyRun D p a n*cayleyFactor (dyadicCoefficient p (a n)) (1/(D : ℝ))

/-- With positive grid size, decoding the integer state after `n` samples gives exactly the
corresponding real Cayley product. -/
theorem decodeCayleyIntegerRun (D p : ℕ) (hD : 0<D) (a : ℕ → Fin 3 → ℤ) (n : ℕ) :
    decodeCayleyState (cayleyIntegerRun D p a n)=realCayleyRun D p a n := by
  induction n with
  | zero => simp [cayleyIntegerRun,decodeCayleyState,realCayleyRun]
  | succ n ih =>
    rw [cayleyIntegerRun,decodeCayleyState_mul,decodeCayleyIntegerFactor D p hD,ih]
    rfl

/-- Right multiplication by a unit quaternion preserves the distance between the initial and exact
states. -/
theorem cayley_initial_error (word initial exact : ℍ) (hw : ‖word‖=1) :
    ‖initial*word-exact*word‖=‖initial-exact‖ := by
  rw [← sub_mul,norm_mul,hw,mul_one]

end Qatlib.Concepts.EffectiveGauge.RationalFlow
