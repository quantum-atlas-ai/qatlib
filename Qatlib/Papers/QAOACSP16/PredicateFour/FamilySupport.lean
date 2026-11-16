/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOACSP16.PredicateFour.Typicality.SourceTypicality
public import Mathlib.Tactic

@[expose] public section


/-! Finite XOR and SAT predicate families with their elementary range and expectation laws. -/

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

namespace Qatlib.Papers.QAOACSP16.PredicateFour.FamilySupport
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A character takes only the values `±1`. -/
theorem charFun_eq_one_or_neg_one (S : Finset V) (z : V → Bool) :
    charFun S z = 1 ∨ charFun S z = -1 := by
  classical
  unfold charFun
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases ih with h | h
      · rw [h, mul_one]
        cases z a <;> simp [sgn]
      · rw [h, mul_neg, mul_one]
        cases z a <;> simp [sgn]

/-- The kXOR predicate takes values in `[0,1]`. -/
theorem xorPredicate_mem (S : Finset V) (p : Bool) (z : V → Bool) :
    (xorPredicate S (sgn p)).val z ∈ Set.Icc (0 : ℝ) 1 := by
  have hp : sgn p = 1 ∨ sgn p = -1 := by cases p <;> simp [sgn]
  have hχ := charFun_eq_one_or_neg_one S z
  rcases hp with h1 | h1 <;> rcases hχ with h2 | h2 <;>
    simp [xorPredicate, h1, h2]

/-- The Max-kXOR family: independent uniform sign per constraint. -/
def xorFamily (m : ℕ) (hm : 0 < m) (scope : Fin m → Finset V) : CSPFamily V Bool where
  m := m
  hm := hm
  scope := scope
  pred := fun l p => xorPredicate (scope l) (sgn p)
  pred_scope := fun _ _ => rfl
  law := uniformBool

/-- Max-kXOR is typical (Corollary 5, p.11). -/
theorem xorFamily_typical (m : ℕ) (hm : 0 < m) (scope : Fin m → Finset V)
    (hne : ∀ l, (scope l).Nonempty) : (xorFamily m hm scope).Typical := by
  intro l
  show IsTypical (fun p : Bool => xorPredicate (scope l) (sgn p)) uniformBool
  exact typical_xor (hne l)

/-- The kXOR family has Boolean-range predicates. -/
theorem xorFamily_booleanValues (m : ℕ) (hm : 0 < m) (scope : Fin m → Finset V) :
    (xorFamily m hm scope).BooleanValues := by
  intro l p z
  exact xorPredicate_mem (scope l) p z

/-- `μ = 1/2` for Max-kXOR with nonempty scopes. -/
theorem xorFamily_muFamily (m : ℕ) (hm : 0 < m) (scope : Fin m → Finset V)
    (hne : ∀ l, (scope l).Nonempty) : (xorFamily m hm scope).muFamily = 1 / 2 := by
  unfold CSPFamily.muFamily
  show (∑ l : Fin m, (xorFamily m hm scope).law.expect
        (fun p : Bool => constraintMean ((xorFamily m hm scope).pred l p)))
      / (m : ℝ) = 1 / 2
  have hone : ∀ l : Fin m,
      (xorFamily m hm scope).law.expect
        (fun p : Bool => constraintMean ((xorFamily m hm scope).pred l p)) = 1 / 2 := by
    intro l
    have hfun : (fun p : Bool => constraintMean ((xorFamily m hm scope).pred l p))
        = fun _ => (1 / 2 : ℝ) := by
      funext p
      exact constraintMean_xor (hne l) (sgn p)
    rw [hfun, expect_const]
  have hsum : (∑ l : Fin m, (xorFamily m hm scope).law.expect
        (fun p : Bool => constraintMean ((xorFamily m hm scope).pred l p)))
      = ∑ _l : Fin m, (1 / 2 : ℝ) :=
    Finset.sum_congr rfl fun l _ => hone l
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  field_simp [hmR.ne']


omit [Fintype V] [DecidableEq V] in
/-- One kSAT factor `(1 ± x_v)/2` lies in `[0,1]`. -/
theorem ksat_factor_mem (σ z : V → Bool) (v : V) :
    (1 + sgn (σ v) * sgn (z v)) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  cases hσ : σ v <;> cases hz : z v <;> simp [sgn]

omit [Fintype V] [DecidableEq V] in
/-- The kSAT clause value lies in `[0,1]`. -/
theorem ksatVal_mem (S : Finset V) (σ z : V → Bool) :
    ksatVal S σ z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold ksatVal
  have hnonneg : 0 ≤ ∏ v ∈ S, ((1 + sgn (σ v) * sgn (z v)) / 2) :=
    Finset.prod_nonneg fun v _ => (ksat_factor_mem σ z v).1
  have hle : (∏ v ∈ S, ((1 + sgn (σ v) * sgn (z v)) / 2)) ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ => (ksat_factor_mem σ z v).1)
      (fun v _ => (ksat_factor_mem σ z v).2)
  exact ⟨by linarith, by linarith⟩

/-- The Max-kSAT family: independent uniform sign per literal. -/
def ksatFamily (m : ℕ) (hm : 0 < m) (scope : Fin m → Finset V) :
    CSPFamily V (V → Bool) where
  m := m
  hm := hm
  scope := scope
  pred := fun l σ => ksatPredicate (scope l) σ
  pred_scope := fun _ _ => rfl
  law := uniformCube

/-- Max-kSAT is typical (Corollary 5, p.11). -/
theorem ksatFamily_typical (m : ℕ) (hm : 0 < m) (scope : Fin m → Finset V) :
    (ksatFamily m hm scope).Typical := by
  intro l
  show IsTypical (fun σ : V → Bool => ksatPredicate (scope l) σ) uniformCube
  exact typical_ksat (scope l)

/-- The kSAT family has Boolean-range predicates. -/
theorem ksatFamily_booleanValues (m : ℕ) (hm : 0 < m) (scope : Fin m → Finset V) :
    (ksatFamily m hm scope).BooleanValues := by
  intro l σ z
  exact ksatVal_mem (scope l) σ z


end Qatlib.Papers.QAOACSP16.PredicateFour.FamilySupport
