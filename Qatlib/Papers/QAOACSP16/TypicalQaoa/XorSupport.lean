/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOACSP16.PredicateFour.Typicality.SourceTypicality
public import Qatlib.Papers.QAOACSP16.TypicalQaoa.Concentration.SourceCSPConcentration
public import Mathlib.Tactic

@[expose] public section


/-! Centered XOR families and finite expectation witnesses. -/
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel
open Qatlib.Papers.QAOACSP16.PredicateFour.CSPFamily
open Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState
open Qatlib.Papers.QAOACSP16.PredicateFour.Typicality
open scoped BigOperators

namespace Qatlib.Papers.QAOACSP16.TypicalQaoa.XorSupport
variable {V : Type} [Fintype V] [DecidableEq V]
variable {P : Type} [Fintype P] [DecidableEq P]

/-- A generalized Max-XOR family: pure monomials `ψ̂_l χ_{S_l}` with zero-mean
random coefficients and a common variance bound (`maxVar[ψ̂_l]` of (4.17)). -/
structure XorFamily (V : Type) (P : Type) [Fintype V] [Fintype P] [DecidableEq P] where
  /-- Number of constraints. -/
  m : ℕ
  /-- Nonempty instance. -/
  hm : 0 < m
  /-- Scopes (nonempty, as required by the paper's XOR constraints). -/
  scope : Fin m → Finset V
  /-- Every scope is nonempty. -/
  scope_nonempty : ∀ l, (scope l).Nonempty
  /-- The random Fourier coefficient `ψ̂_l`. -/
  coeff : Fin m → P → ℝ
  /-- The law of the coefficients. -/
  law : FinDist P
  /-- Typicality: every coefficient has zero mean (equation (2.3)). -/
  coeff_zero_mean : ∀ l, law.expect (coeff l) = 0
  /-- The common variance bound `maxVar[ψ̂_l]` appearing in (4.16)/(4.17). -/
  varBound : ℝ
  /-- Every coefficient variance is bounded by `varBound`. -/
  coeff_var_le : ∀ l, law.variance (coeff l) ≤ varBound

/-- The monomial predicate `z ↦ ψ̂_l χ_{S_l}(z)` of equation (4.1). -/
def XorFamily.pred (F : XorFamily V P) (l : Fin F.m) (p : P) : Predicate V where
  scope := F.scope l
  val := fun z => F.coeff l p * charFun (F.scope l) z
  locality := by
    intro z z' h
    have hχ : charFun (F.scope l) z = charFun (F.scope l) z' := by
      unfold charFun
      apply Finset.prod_congr rfl
      intro v hv
      rw [h v hv]
    rw [hχ]

/-- A generalized Max-XOR family as a `CSPFamily`. -/
def XorFamily.toFamily (F : XorFamily V P) : CSPFamily V P where
  m := F.m
  hm := F.hm
  scope := F.scope
  pred := F.pred
  pred_scope := fun _ _ => rfl
  law := F.law

/-- A pure monomial has uniform mean zero (its scope is nonempty). -/
theorem XorFamily.constraintMean_pred (F : XorFamily V P) (l : Fin F.m) (p : P) :
    constraintMean (F.pred l p) = 0 := by
  have hS : (F.scope l).Nonempty := F.scope_nonempty l
  simp only [XorFamily.pred, constraintMean, uniformExpect]
  rw [← Finset.mul_sum, sum_charFun_eq_zero hS, mul_zero, zero_div]

/-- `μ = 0` for generalized Max-XOR: every constraint has uniform mean zero. -/
theorem XorFamily.muFamily_eq_zero (F : XorFamily V P) :
    F.toFamily.muFamily = 0 := by
  unfold CSPFamily.muFamily
  have hzero : ∀ l : Fin F.m,
      F.toFamily.law.expect (fun p => constraintMean (F.toFamily.pred l p)) = 0 := by
    intro l
    have hfun : (fun p : P => constraintMean (F.toFamily.pred l p))
        = fun _ => (0 : ℝ) := by
      funext p
      exact F.constraintMean_pred l p
    rw [hfun]
    exact expect_const F.law 0
  have hsum : (∑ l : Fin F.toFamily.m,
      F.toFamily.law.expect (fun p => constraintMean (F.toFamily.pred l p))) = 0 := by
    exact Finset.sum_eq_zero fun l _ => hzero l
  rw [hsum]
  simp

/-- Generalized Max-XOR families are typical (equation (2.3)): the coefficient
has zero mean, and the character is deterministic. -/
theorem XorFamily.toFamily_typical (F : XorFamily V P) : F.toFamily.Typical := by
  intro l z
  have hfun : (fun p : P => (F.pred l p).val z - constraintMean (F.pred l p))
      = fun p => charFun (F.scope l) z * F.coeff l p := by
    funext p
    rw [F.constraintMean_pred l p]
    show F.coeff l p * charFun (F.scope l) z - 0
        = charFun (F.scope l) z * F.coeff l p
    ring
  show F.law.expect (fun p : P =>
      (F.pred l p).val z - constraintMean (F.pred l p)) = 0
  rw [hfun, expect_const_mul, F.coeff_zero_mean l, mul_zero]


/-- A finite real family summing to one has a strictly positive entry. -/
theorem exists_positive_atom {Ω : Type*} [Fintype Ω] {f : Ω → ℝ}
    (h1 : ∑ x, f x = 1) : ∃ x, 0 < f x := by
  by_contra h
  push Not at h
  have hle : ∑ x, f x ≤ 0 := Finset.sum_nonpos fun x _ => h x
  linarith

/-- If a statistic has expectation at least `B`, a positive-probability atom
has value at least `B`. No sign
assumption on the statistic is needed: at a zero-probability atom both sides of
the comparison vanish. -/
theorem exists_instance_ge_expect {Ω : Type*} [Fintype Ω]
    (law : FinDist Ω) (g : Ω → ℝ) (B : ℝ)
    (hB : B ≤ law.expect g) : ∃ ω, 0 < law.prob ω ∧ B ≤ g ω := by
  classical
  by_contra hcon
  push Not at hcon
  have hterm_le : ∀ ω, law.prob ω * g ω ≤ law.prob ω * B := by
    intro ω
    rcases eq_or_lt_of_le (law.nonneg ω) with hz | hpos
    · rw [← hz]; simp
    · exact mul_le_mul_of_nonneg_left (hcon ω hpos).le (law.nonneg ω)
  obtain ⟨ω₀, hω₀⟩ := exists_positive_atom law.sum_one
  have hstrict : law.prob ω₀ * g ω₀ < law.prob ω₀ * B :=
    mul_lt_mul_of_pos_left (hcon ω₀ hω₀) hω₀
  have hlt : (∑ ω, law.prob ω * g ω) < ∑ ω, law.prob ω * B :=
    Finset.sum_lt_sum (fun ω _ => hterm_le ω) ⟨ω₀, Finset.mem_univ _, hstrict⟩
  rw [← Finset.sum_mul, law.sum_one, one_mul] at hlt
  unfold FinDist.expect at hB
  linarith


end Qatlib.Papers.QAOACSP16.TypicalQaoa.XorSupport
