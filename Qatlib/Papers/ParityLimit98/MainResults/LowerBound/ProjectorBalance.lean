/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.ParityBalance
import Qatlib.Concepts.ProbabilityCore.Concentration.CubeQueryInterfaces
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.ProbabilityCore.DistributionAA

theorem subset_monomial_signed_sum {n : ℕ} (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    ∑ f : Fin n → Bool, boolSign f * (∏ i ∈ S, if f i then (1 : ℝ) else 0) = 0 := by
  classical
  have hex : ∃ j, j ∉ S := by
    by_contra h
    push Not at h
    exact hS (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨j,hj⟩ := hex
  calc
    _ = ∑ f : Fin n → Bool, ∏ i,
        (if f i then (-1 : ℝ) else 1) * (if i ∈ S then if f i then 1 else 0 else 1) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem]
      rfl
    _ = ∏ i : Fin n, ∑ b : Bool,
        (if b then (-1 : ℝ) else 1) * (if i ∈ S then if b then 1 else 0 else 1) :=
      (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
        (if b then (-1 : ℝ) else 1) * (if i ∈ S then if b then 1 else 0 else 1))).symm
    _ = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj, Fintype.univ_bool])

theorem cube_degree_signed_sum {n d : ℕ} (a : (Fin n → Bool) → ℝ)
    (ha : CubeDegreeLE d a) (hd : d < n) :
    ∑ f : Fin n → Bool, boolSign f * a f = 0 := by
  classical
  obtain ⟨c,hc,he⟩ := ha
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hs : S.card ≤ d
  · have hS : S ≠ Finset.univ := by
      intro h
      simp only [h, Finset.card_univ, Fintype.card_fin] at hs
      omega
    have hz := subset_monomial_signed_sum S hS
    calc
      _ = c S * ∑ f : Fin n → Bool, boolSign f * (∏ i ∈ S, if f i then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        ring
      _ = 0 := by rw [hz, mul_zero]
  · simp [hc S (by omega)]

def projectorAcceptance {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (f : Fin n → Bool) : ℝ :=
  MeasureProb (ApplyGate P (Run (TensorGate (BitOracleOn f) 1) C ψ)) Finset.univ

theorem projectorAcceptance_degree {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ) :
    CubeDegreeLE (2 * QueryCount C) (projectorAcceptance C ψ P) := by
  have h := Qatlib.Concepts.ProbabilityCore.Concentration.circuit_cube_degree
    n W (C ++ [Step.gate P]) ψ Finset.univ
  simpa only [queryCount_append, queryCount_gate, queryCount_nil, Nat.add_zero,
    run_append, Run, projectorAcceptance] using! h

theorem projector_signed_sum {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hk : 2 * QueryCount C < n) :
    ∑ f : Fin n → Bool, boolSign f * projectorAcceptance C ψ P f = 0 :=
  cube_degree_signed_sum _ (projectorAcceptance_degree C ψ P) hk

theorem projector_acceptance_balance {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hk : 2 * QueryCount C < n) :
    (∑ f ∈ Finset.univ.filter (fun f => parityOddB f = false), projectorAcceptance C ψ P f) =
      ∑ f ∈ Finset.univ.filter (fun f => parityOddB f = true), projectorAcceptance C ψ P f :=
  sum_balance_of_signed_sum_zero _ (projector_signed_sum C ψ P hk)

theorem projector_centered_sum {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hk : 2 * QueryCount C < n) :
    (∑ f : Fin n → Bool, boolSign f * (projectorAcceptance C ψ P f - 1 / 2)) = 0 := by
  classical
  have hne : (∅ : Finset (Fin n)) ≠ Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hsign : (∑ f : Fin n → Bool, boolSign f) = 0 := by
    simpa using subset_monomial_signed_sum ∅ hne
  have hz : (∑ f : Fin n → Bool, boolSign f * (projectorAcceptance C ψ P f - 1 / 2)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, projector_signed_sum C ψ P hk, hsign]
    ring
  exact hz

theorem projector_no_positive_bias {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hk : 2 * QueryCount C < n) (ε : ℝ) (hε : 0 < ε)
    (hplus : ∀ f, parityOddB f = false → 1 / 2 + ε ≤ projectorAcceptance C ψ P f)
    (hminus : ∀ f, parityOddB f = true → projectorAcceptance C ψ P f ≤ 1 / 2 - ε) :
    False := by
  classical
  have hz := projector_centered_sum C ψ P hk
  have hp : ∀ f, 0 < boolSign f * (projectorAcceptance C ψ P f - 1 / 2) := by
    intro f
    rw [boolSign_eq_ite]
    cases he : parityOddB f
    · have h := hplus f he
      simp only [Bool.false_eq_true, if_false, one_mul]
      linarith
    · have h := hminus f he
      simp only [if_true, neg_one_mul]
      linarith
  have hs := Finset.sum_pos (s := (Finset.univ : Finset (Fin n → Bool)))
    (fun f _ => hp f) ⟨fun _ => false, Finset.mem_univ _⟩
  linarith

theorem projector_positive_bias_query_bound {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (ε : ℝ) (hε : 0 < ε)
    (hplus : ∀ f, parityOddB f = false → 1 / 2 + ε ≤ projectorAcceptance C ψ P f)
    (hminus : ∀ f, parityOddB f = true → projectorAcceptance C ψ P f ≤ 1 / 2 - ε) :
    n ≤ 2 * QueryCount C := by
  by_contra h
  exact projector_no_positive_bias C ψ P (by omega) ε hε hplus hminus

theorem projector_half_rigidity {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W))
    (P : Matrix (PolynomialWorkspace (Fin n) W) (PolynomialWorkspace (Fin n) W) ℂ)
    (hk : 2 * QueryCount C < n)
    (hplus : ∀ f, parityOddB f = false → 1 / 2 ≤ projectorAcceptance C ψ P f)
    (hminus : ∀ f, parityOddB f = true → projectorAcceptance C ψ P f ≤ 1 / 2) :
    ∀ f, projectorAcceptance C ψ P f = 1 / 2 := by
  classical
  have hnonneg : ∀ f, 0 ≤ boolSign f * (projectorAcceptance C ψ P f - 1 / 2) := by
    intro f
    rw [boolSign_eq_ite]
    cases he : parityOddB f
    · have h := hplus f he
      simp only [Bool.false_eq_true, if_false, one_mul]
      linarith
    · have h := hminus f he
      simp only [if_true, neg_one_mul]
      linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun f _ => hnonneg f)).mp
    (projector_centered_sum C ψ P hk)
  intro f
  have hf := hz f (Finset.mem_univ f)
  rw [boolSign_eq_ite] at hf
  cases hp : parityOddB f
  · simp only [hp, Bool.false_eq_true, if_false, one_mul] at hf
    linarith
  · simp only [hp, if_true, neg_one_mul] at hf
    linarith

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
