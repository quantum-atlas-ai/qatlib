/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CisSeries

/-! # Finite rational cis execution, including first stopping and squaring -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Data and hypotheses for Rational Cis Result in the Rational Flow construction. -/
structure RationalCisResult where
  value : RationalCircleSample
  error : ℚ
  terms : ℕ
  deriving Repr, DecidableEq

/-- Definition of cis Taylor Loop in the Rational Flow construction. -/
def cisTaylorLoop (x tolerance : ℚ) (n : ℕ) (answer term : RationalCircleSample)
    (scalar : ℚ) : ℕ → RationalCisResult
  | 0 => ⟨answer,2*scalar,n⟩
  | fuel+1 =>
    if 2*scalar ≤ tolerance then ⟨answer,2*scalar,n⟩
    else cisTaylorLoop x tolerance (n+1) (cisPairAdd answer term)
      (cisTermStep x (n+1) term) (scalar*|x|/((n+1 : ℕ) : ℚ)) fuel

/-- Definition of reduced Cis in the Rational Flow construction. -/
def reducedCis (x tolerance : ℚ) : RationalCisResult :=
  cisTaylorLoop x tolerance 1 (1,0) (0,x) |x| (arctanFuel (tolerance/2))

/-- Definition of cis Pair Square in the Rational Flow construction. -/
def cisPairSquare (a : RationalCircleSample) : RationalCircleSample :=
  (a.1^2-a.2^2,2*a.1*a.2)

/-- Definition of cis Squares in the Rational Flow construction. -/
def cisSquares : ℕ → RationalCisResult → RationalCisResult
  | 0,r => r
  | n+1,r =>
    let p := cisSquares n r
    ⟨cisPairSquare p.value,p.error*(2+p.error),p.terms⟩

/-- Definition of cis Error Iter in the Rational Flow construction. -/
def cisErrorIter : ℕ → ℚ → ℚ
  | 0,e => e
  | n+1,e => let d := cisErrorIter n e; d*(2+d)

/-- Definition of cis Halvings in the Rational Flow construction. -/
def cisHalvings (x : ℚ) : ℕ := negativeExpHalvings |x|

/-- Definition of rational Cis in the Rational Flow construction. -/
def rationalCis (x tolerance : ℚ) : RationalCisResult :=
  let h := cisHalvings x
  cisSquares h (reducedCis (x/(2^h : ℚ)) (tolerance/(8*2^h : ℚ)))

/-- Original `cisTaylorLoop_spec` guarantee for the `CisProgram` construction; the complete source hypotheses are retained. -/
theorem cisTaylorLoop_spec (x tolerance : ℚ) (fuel n : ℕ)
    (hstop : 2*negativeExpMagnitude x (n+fuel) ≤ tolerance) :
    let r := cisTaylorLoop x tolerance n (cisTaylorPartial x n) (cisTaylorTerm x n)
      (negativeExpMagnitude x n) fuel
    r.value=cisTaylorPartial x r.terms ∧ r.error=2*negativeExpMagnitude x r.terms ∧
      n ≤ r.terms ∧ r.terms ≤ n+fuel ∧ r.error ≤ tolerance ∧
      ∀ k, n ≤ k → k<r.terms → tolerance<2*negativeExpMagnitude x k := by
  induction fuel generalizing n with
  | zero =>
    dsimp only [cisTaylorLoop]
    refine ⟨rfl,rfl,le_rfl,by omega,?_,?_⟩
    · simpa only [Nat.add_zero] using hstop
    · intro k hk hlt
      change k<n at hlt
      omega
  | succ fuel ih =>
    simp only [cisTaylorLoop]
    split_ifs with h
    · dsimp only
      refine ⟨rfl,rfl,le_rfl,by omega,h,?_⟩
      intro k hk hlt
      omega
    · rw [← cisTaylorPartial,← cisTaylorTerm,← cisMagnitude_step]
      have hs : 2*negativeExpMagnitude x ((n+1)+fuel) ≤ tolerance := by
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hstop
      obtain ⟨hv,he,hlo,hhi,hbudget,hprior⟩ := ih (n+1) hs
      refine ⟨hv,he,(Nat.le_succ n).trans hlo,?_,hbudget,?_⟩
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hhi
      intro k hk hlt
      by_cases hkn : k=n
      · subst k
        exact lt_of_not_ge h
      · exact hprior k (by omega) hlt

/-- Original `reducedCis_spec` guarantee for the `CisProgram` construction; the complete source hypotheses are retained. -/
theorem reducedCis_spec (x tolerance : ℚ) (hx : |x| ≤ 1/2) (ht : 0<tolerance) :
    let r := reducedCis x tolerance
    r.value=cisTaylorPartial x r.terms ∧ r.error=2*negativeExpMagnitude x r.terms ∧
      1 ≤ r.terms ∧ r.terms ≤ 1+arctanFuel (tolerance/2) ∧ r.error ≤ tolerance ∧
      ∀ k, 1 ≤ k → k<r.terms → tolerance<2*negativeExpMagnitude x k := by
  have hp : (2^arctanFuel (tolerance/2) : ℚ) ≤ 2^(1+arctanFuel (tolerance/2)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : (2^(1+arctanFuel (tolerance/2)) : ℚ)⁻¹ ≤ (2^arctanFuel (tolerance/2) : ℚ)⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hp
  have hmag := (negativeExpMagnitude_dyadic x hx (1+arctanFuel (tolerance/2))).trans
    (hi.trans (arctanFuel_budget (tolerance/2) (by positivity)))
  have hstop : 2*negativeExpMagnitude x (1+arctanFuel (tolerance/2)) ≤ tolerance := by linarith
  have hp1 : cisTaylorPartial x 1=(1,0) := by simp [cisTaylorPartial,cisTaylorTerm,cisPairAdd]
  have ht1 : cisTaylorTerm x 1=(0,x) := by simp [cisTaylorTerm,cisTermStep]
  have hm1 : negativeExpMagnitude x 1=|x| := by simp [negativeExpMagnitude]
  simpa only [reducedCis,hp1,ht1,hm1] using cisTaylorLoop_spec x tolerance (arctanFuel (tolerance/2)) 1 hstop

/-- Original `cisHalvings_reduced` guarantee for the `CisProgram` construction; the complete source hypotheses are retained. -/
theorem cisHalvings_reduced (x : ℚ) : |x/(2^cisHalvings x : ℚ)| ≤ 1/2 := by
  rw [abs_div,abs_of_nonneg (by positivity : (0 : ℚ) ≤ 2^cisHalvings x)]
  exact (negativeExpHalvings_reduced |x| (abs_nonneg x)).2

/-- Original `cisHalvings_first` guarantee for the `CisProgram` construction; the complete source hypotheses are retained. -/
theorem cisHalvings_first (x : ℚ) (k : ℕ) (hk : k<cisHalvings x) :
    1/2< |x/(2^k : ℚ)| := by
  rw [abs_div,abs_of_nonneg (by positivity : (0 : ℚ) ≤ 2^k)]
  exact negativeExpHalvings_first |x| k hk

/-- Original `cisSquares_fields` guarantee for the `CisProgram` construction; the complete source hypotheses are retained. -/
theorem cisSquares_fields (h : ℕ) (r : RationalCisResult) :
    (cisSquares h r).error=cisErrorIter h r.error ∧ (cisSquares h r).terms=r.terms := by
  induction h with
  | zero => exact ⟨rfl,rfl⟩
  | succ h ih => simp [cisSquares,cisErrorIter,ih.1,ih.2]

/-- A rational invariant bounds the nonlinear squaring ledger. No approximate
complex value is assumed unit magnitude. -/
theorem cisErrorIter_invariant (e : ℚ) (he : 0 ≤ e) (h : ℕ) (hsmall : (2^h : ℚ)*e ≤ 1/8) :
    0 ≤ cisErrorIter h e ∧ (1+cisErrorIter h e)*(1-(2^h : ℚ)*e) ≤ 1 := by
  induction h with
  | zero => dsimp [cisErrorIter]; constructor; exact he; nlinarith [sq_nonneg e]
  | succ h ih =>
    have hs : (2^h : ℚ)*e ≤ 1/8 := by rw [pow_succ] at hsmall; nlinarith [pow_pos (by norm_num : (0 : ℚ)<2) h]
    obtain ⟨hE,hI⟩ := ih hs
    let x : ℚ := (2^h : ℚ)*e
    have hx : x ≤ 1/8 := hs
    have hA : 0 ≤ (1+cisErrorIter h e)*(1-x) := mul_nonneg (by linarith) (by linarith)
    have hB : ((1+cisErrorIter h e)*(1-x))^2 ≤ (1 : ℚ) := by nlinarith [sq_nonneg ((1+cisErrorIter h e)*(1-x))]
    have hfactor : 1-2*x ≤ (1-x)^2 := by nlinarith [sq_nonneg x]
    refine ⟨mul_nonneg hE (by linarith),?_⟩
    change (1+cisErrorIter h e*(2+cisErrorIter h e))*(1-(2^(h+1) : ℚ)*e) ≤ 1
    calc
      _ = (1+cisErrorIter h e)^2*(1-2*x) := by dsimp [x]; rw [pow_succ]; ring
      _ ≤ (1+cisErrorIter h e)^2*(1-x)^2 := mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
      _ = ((1+cisErrorIter h e)*(1-x))^2 := by ring
      _ ≤ 1 := hB

/-- Original `cisErrorIter_budget` guarantee for the `CisProgram` construction; the complete source hypotheses are retained. -/
theorem cisErrorIter_budget (e tolerance : ℚ) (h : ℕ) (he : 0 ≤ e) (ht : 0<tolerance) (ht1 : tolerance ≤ 1)
    (heps : e ≤ tolerance/(8*2^h : ℚ)) : 0 ≤ cisErrorIter h e ∧ cisErrorIter h e ≤ tolerance := by
  have hp : (0 : ℚ)<2^h := by positivity
  have hmul : (2^h : ℚ)*e ≤ tolerance/8 := by
    have hm := (le_div_iff₀ (by positivity : (0 : ℚ)<8*2^h)).mp heps
    nlinarith
  have hsmall : (2^h : ℚ)*e ≤ 1/8 := by linarith
  obtain ⟨hE,hI⟩ := cisErrorIter_invariant e he h hsmall
  refine ⟨hE,?_⟩
  have hprod := mul_le_mul_of_nonneg_left hsmall hE
  nlinarith

end Qatlib.Concepts.EffectiveGauge.RationalFlow
