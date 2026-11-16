/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section


/-! # The original binomial majority core

The two old Lemma4 targets have identical binomial conclusions. The mass below
is the actual finite binomial law. A one-trial Hoeffding moment and its exact
binomial expansion give the explicit `18 * log (1/epsilon)` repetition bound.
The quantum estimation bins and their per-run probabilities are separate bridges.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate.BinomCore
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-- The literal old finite binomial mass. -/
def binomProb (k : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  (Nat.choose k j : ℝ)*q^j*(1-q)^(k-j)

/-- The literal old at-most-half failure event, including ties. -/
def atMostHalfFailures (k : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), if 2*j ≤ k then binomProb k q j else 0

/-- The actual binomial masses sum to one. -/
theorem totalMass (k : ℕ) (q : ℝ) :
    ∑ j ∈ Finset.range (k+1), binomProb k q j = 1 := by
  have h := add_pow q (1-q) k
  have he : q+(1-q)=1 := by ring
  rw [he,one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [binomProb]
  ring

/-- The exact binomial exponential moment is a power of the actual one-trial moment. -/
theorem expMoment (k : ℕ) (q t : ℝ) :
    ∑ j ∈ Finset.range (k+1), binomProb k q j*Real.exp (t*(j : ℝ)) =
      ((1-q)+q*Real.exp t)^k := by
  rw [add_comm (1-q),add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow,← Real.exp_nat_mul]
  dsimp [binomProb]
  rw [mul_comm (j : ℝ) t]
  ring

/-- A real Bernoulli failure probability at most one third has this Hoeffding moment. -/
theorem oneMoment (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/3) :
    (1-q)+q*Real.exp (2/3 : ℝ) ≤ Real.exp (5/18 : ℝ) := by
  let p : FinDist Bool := ⟨fun b => if b then q else 1-q,
    fun b => by cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith,
    by simp⟩
  let f : Bool → ℝ := fun b => if b then 1 else 0
  have hmean : p.expect f=q := by simp [FinDist.expect,p,f]
  have h := hoeffding_centered_mgf p f 0 1 (2/3) (by norm_num)
    (fun b => by cases b <;> norm_num [f])
  rw [hmean] at h
  have he0 : Real.exp ((2/3)*q)*Real.exp ((2/3)*(0-q))=1 := by
    rw [← Real.exp_add,show (2/3 : ℝ)*q+(2/3)*(0-q)=0 by ring,Real.exp_zero]
  have he1 : Real.exp ((2/3)*q)*Real.exp ((2/3)*(1-q))=Real.exp (2/3 : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : Real.exp ((2/3)*q)*p.expect (fun b => Real.exp ((2/3)*(f b-q))) =
      (1-q)+q*Real.exp (2/3 : ℝ) := by
    calc
      _ = (1-q)*(Real.exp ((2/3)*q)*Real.exp ((2/3)*(0-q)))+
          q*(Real.exp ((2/3)*q)*Real.exp ((2/3)*(1-q))) := by
        simp [FinDist.expect,p,f]
        ring
      _ = _ := by rw [he0,he1]; ring
  calc
    _ ≤ Real.exp ((2/3)*q)*Real.exp ((2/3 : ℝ)^2*(1-0)^2/8) := by
      rw [← he]
      exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp ((2/3)*q+1/18) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The genuine strict-majority failure mass has an exponential upper bound. -/
theorem failureBound (k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/3) :
    (∑ j ∈ Finset.range (k+1), if k < 2*j then binomProb k q j else 0) ≤
      Real.exp (-(k : ℝ)/18) := by
  have hp (j : ℕ) : 0 ≤ binomProb k q j := by
    dsimp [binomProb]
    apply mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hq0 _))
    apply pow_nonneg
    linarith
  have hpoint (j : ℕ) : Real.exp ((k : ℝ)/3)*
      (if k < 2*j then binomProb k q j else 0) ≤
      binomProb k q j*Real.exp ((2/3 : ℝ)*(j : ℝ)) := by
    split_ifs with hj
    · have hjr : (k : ℝ) < 2*(j : ℝ) := by exact_mod_cast hj
      have he : Real.exp ((k : ℝ)/3) ≤ Real.exp ((2/3 : ℝ)*(j : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (hp j)
    · simp only [mul_zero]
      exact mul_nonneg (hp j) (Real.exp_pos _).le
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (k+1)) => hpoint j)
  rw [← Finset.mul_sum,expMoment] at hsum
  have hm := pow_le_pow_left₀
    (by have := Real.exp_pos (2/3 : ℝ); nlinarith : 0 ≤ (1-q)+q*Real.exp (2/3 : ℝ))
    (oneMoment q hq0 hq) k
  have ht := hsum.trans hm
  rw [← Real.exp_nat_mul] at ht
  have he : Real.exp ((k : ℝ)*(5/18)) =
      Real.exp ((k : ℝ)/3)*Real.exp (-(k : ℝ)/18) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at ht
  exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp ht

/-- The complete binomial target used by both old Lemma4 cases. -/
theorem majorityBound (k : ℕ) (q ε : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/3)
    (hε0 : 0 < ε) (hkbound : 18*Real.log (1/ε) ≤ (k : ℝ)) :
    1-ε ≤ atMostHalfFailures k q := by
  have hb := failureBound k q hq0 hq
  have he : Real.exp (-(k : ℝ)/18) ≤ ε := by
    rw [← Real.exp_log hε0,Real.exp_le_exp]
    have hlog : Real.log (1/ε) = -Real.log ε := by simp
    rw [hlog] at hkbound
    linarith
  have hs : atMostHalfFailures k q+
      (∑ j ∈ Finset.range (k+1), if k < 2*j then binomProb k q j else 0)=1 := by
    rw [atMostHalfFailures,← Finset.sum_add_distrib,← totalMass k q]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : 2*j ≤ k <;> simp [hj,show (k < 2*j) ↔ ¬2*j ≤ k from lt_iff_not_ge]
  linarith

end Qatlib.Papers.VarTimeAmpAmp10.Estimate.BinomCore
