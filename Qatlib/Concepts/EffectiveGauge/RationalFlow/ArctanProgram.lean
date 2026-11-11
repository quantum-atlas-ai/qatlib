/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.ArctanSeries

/-!
# A finite version of the actual rational alternating-series loop

The fuel is an explicit upper bound. The loop still stops at the first
successful next-term test, preserving the Python program's returned value
and remainder, including negative and zero arguments.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Data and hypotheses for Rational Scalar Result in the Rational Flow construction. -/
structure RationalScalarResult where
  value : ℚ
  error : ℚ
  terms : ℕ
  deriving Repr, DecidableEq

/-- Definition of arctan Fuel in the Rational Flow construction. -/
def arctanFuel (tolerance : ℚ) : ℕ := Nat.clog 2 (Nat.ceil (1/tolerance))

/-- Definition of arctan Rational Loop in the Rational Flow construction. -/
def arctanRationalLoop (x tolerance : ℚ) (j : ℕ) (answer power : ℚ) : ℕ → RationalScalarResult
  | 0 => ⟨answer,|power|/((2*j+1 : ℕ) : ℚ),j⟩
  | fuel+1 =>
    if |power|/((2*j+1 : ℕ) : ℚ) ≤ tolerance then ⟨answer,|power|/((2*j+1 : ℕ) : ℚ),j⟩
    else arctanRationalLoop x tolerance (j+1)
      (answer+(-1 : ℚ)^j*power/((2*j+1 : ℕ) : ℚ)) (power*x*x) fuel

/-- Definition of rational Arctan in the Rational Flow construction. -/
def rationalArctan (x tolerance : ℚ) : RationalScalarResult :=
  arctanRationalLoop x tolerance 0 0 x (arctanFuel tolerance)

/-- Original `arctanTermMagnitude_dyadic` guarantee for the `ArctanProgram` construction; the complete source hypotheses are retained. -/
theorem arctanTermMagnitude_dyadic (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (n : ℕ) :
    arctanTermMagnitude x n ≤ (2^n : ℚ)⁻¹ := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  calc
    _ ≤ |x|^(2*n+1) := div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ 2*n+1))
    _ ≤ |x|^n := pow_le_pow_of_le_one (abs_nonneg _) hx1 (by omega)
    _ ≤ (1/2 : ℚ)^n := pow_le_pow_left₀ (abs_nonneg _) hx n
    _ = _ := by rw [one_div,inv_pow]

/-- Original `arctanFuel_budget` guarantee for the `ArctanProgram` construction; the complete source hypotheses are retained. -/
theorem arctanFuel_budget (tolerance : ℚ) (ht : 0<tolerance) :
    (2^arctanFuel tolerance : ℚ)⁻¹ ≤ tolerance := by
  have hpow : Nat.ceil (1/tolerance) ≤ 2^arctanFuel tolerance := Nat.le_pow_clog (by decide) _
  have h : 1/tolerance ≤ (2^arctanFuel tolerance : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpow)
  apply (inv_le_iff_one_le_mul₀ (by positivity : (0 : ℚ)<2^arctanFuel tolerance)).mpr
  simpa only [mul_comm] using (div_le_iff₀ ht).mp h

/-- Original `arctanFuel_inverse_power_two` guarantee for the `ArctanProgram` construction; the complete source hypotheses are retained. -/
theorem arctanFuel_inverse_power_two (k : ℕ) : arctanFuel ((2^k : ℚ)⁻¹)=k := by
  unfold arctanFuel
  rw [one_div,inv_inv]
  have hp : (2^k : ℚ)=((2^k : ℕ) : ℚ) := by norm_cast
  rw [hp,Nat.ceil_natCast,Nat.clog_pow 2 k (by decide)]

/-- Original `arctanRationalLoop_spec` guarantee for the `ArctanProgram` construction; the complete source hypotheses are retained. -/
theorem arctanRationalLoop_spec (x tolerance : ℚ) (fuel j : ℕ)
    (hstop : arctanTermMagnitude x (j+fuel) ≤ tolerance) :
    let r := arctanRationalLoop x tolerance j (arctanPartial x j) (x^(2*j+1)) fuel
    r.value=arctanPartial x r.terms ∧ r.error=arctanTermMagnitude x r.terms ∧
      j ≤ r.terms ∧ r.terms ≤ j+fuel ∧ r.error ≤ tolerance ∧
      ∀ k, j ≤ k → k<r.terms → tolerance<arctanTermMagnitude x k := by
  induction fuel generalizing j with
  | zero =>
    dsimp only [arctanRationalLoop]
    refine ⟨rfl,by simp [arctanTermMagnitude,abs_pow],le_rfl,by omega,?_,?_⟩
    · simpa [arctanRationalLoop,arctanTermMagnitude,abs_pow] using hstop
    · intro k hk hlt
      change k<j at hlt
      omega
  | succ fuel ih =>
    simp only [arctanRationalLoop]
    split_ifs with h
    · dsimp only
      refine ⟨rfl,by simp [arctanTermMagnitude,abs_pow],le_rfl,by omega,h,?_⟩
      intro k hk hlt
      omega
    · have hp : x^(2*j+1)*x*x=x^(2*(j+1)+1) := by
        calc
          _ = x^(2*j+1)*x^2 := by ring
          _ = x^((2*j+1)+2) := (pow_add _ _ _).symm
          _ = _ := by congr 1
      rw [← arctanPartial_succ x j,hp]
      have hs : arctanTermMagnitude x ((j+1)+fuel) ≤ tolerance := by
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hstop
      obtain ⟨hv,he,hlo,hhi,heps,hprior⟩ := ih (j+1) hs
      refine ⟨hv,he,by omega,by omega,heps,?_⟩
      intro k hk hlt
      by_cases hkj : k=j
      · subst k
        simpa only [arctanTermMagnitude,abs_pow] using lt_of_not_ge h
      · exact hprior k (by omega) hlt

/-- Original `rationalArctan_spec` guarantee for the `ArctanProgram` construction; the complete source hypotheses are retained. -/
theorem rationalArctan_spec (x tolerance : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (ht : 0<tolerance) :
    (rationalArctan x tolerance).value=arctanPartial x (rationalArctan x tolerance).terms ∧
    (rationalArctan x tolerance).error=arctanTermMagnitude x (rationalArctan x tolerance).terms ∧
    (rationalArctan x tolerance).terms ≤ arctanFuel tolerance ∧
    (rationalArctan x tolerance).error ≤ tolerance ∧
    ∀ k<(rationalArctan x tolerance).terms, tolerance<arctanTermMagnitude x k := by
  have hs := arctanRationalLoop_spec x tolerance (arctanFuel tolerance) 0
    (by simpa only [zero_add] using (arctanTermMagnitude_dyadic x hx (arctanFuel tolerance)).trans (arctanFuel_budget tolerance ht))
  simp only [arctanPartial_zero,mul_zero,zero_add,pow_one] at hs
  exact ⟨hs.1,hs.2.1,hs.2.2.2.1,hs.2.2.2.2.1,fun k hk => hs.2.2.2.2.2 k (Nat.zero_le k) hk⟩

noncomputable section

/-- Original `rationalArctan_error` guarantee for the `ArctanProgram` construction; the complete source hypotheses are retained. -/
theorem rationalArctan_error (x tolerance : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (ht : 0<tolerance) :
    |((rationalArctan x tolerance).value : ℝ)-Real.arctan (x : ℝ)| ≤ ((rationalArctan x tolerance).error : ℝ) := by
  obtain ⟨hv,he,_⟩ := rationalArctan_spec x tolerance hx ht
  rw [hv,he]
  exact arctanPartial_error x hx _

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
