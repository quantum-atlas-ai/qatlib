/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
set_option warningAsError false

namespace Qatlib.Papers.ParityLimit98.MainResults.LowerBound

open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def boolSign (f : I → Bool) : ℝ := ∏ i, if f i then (-1 : ℝ) else 1

def flipAt (i : I) (f : I → Bool) : I → Bool := Function.update f i (!f i)

noncomputable def monomialValue (m : I →₀ ℕ) (f : I → Bool) : ℝ :=
  ∏ i, (boolPoint f i) ^ (m i)

theorem boolSign_flipAt (i : I) (f : I → Bool) : boolSign (flipAt i f) = - boolSign f := by
  unfold boolSign flipAt
  conv_lhs => rw [← Finset.mul_prod_erase (Finset.univ : Finset I)
    (fun j => if Function.update f i (!f i) j then (-1 : ℝ) else 1) (Finset.mem_univ i)]
  conv_rhs => rw [← Finset.mul_prod_erase (Finset.univ : Finset I)
    (fun j => if f j then (-1 : ℝ) else 1) (Finset.mem_univ i)]
  have hsame : (∏ j ∈ (Finset.univ : Finset I).erase i,
      (if Function.update f i (!f i) j then (-1 : ℝ) else 1))
      = ∏ j ∈ (Finset.univ : Finset I).erase i, (if f j then (-1 : ℝ) else 1) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1]
  rw [hsame]
  have hval : Function.update f i (!f i) i = !f i := Function.update_self i (!f i) f
  rw [hval]
  by_cases hfi : f i = true
  · simp [hfi]
  · have hf : f i = false := by simpa using hfi
    simp [hf]

omit [Fintype I] in

theorem flipAt_involutive (i : I) : Function.Involutive (flipAt i) := by
  intro f
  unfold flipAt
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

omit [DecidableEq I] in

theorem eval_eq_monomial_sum (p : MvPolynomial I ℝ) (f : I → Bool) :
    MvPolynomial.eval (boolPoint f) p =
      ∑ m ∈ p.support, p.coeff m * monomialValue m f := by
  rw [MvPolynomial.eval_eq']
  rfl

omit [DecidableEq I] in

theorem boolSign_mul_monomialValue (m : I →₀ ℕ) (f : I → Bool) :
    boolSign f * monomialValue m f =
      ∏ i, (if f i then (-1 : ℝ) else 1) * (boolPoint f i) ^ (m i) := by
  unfold boolSign monomialValue
  rw [Finset.prod_mul_distrib]

theorem sum_boolSign_mul_monomialValue (m : I →₀ ℕ) (hm : m.support ≠ Finset.univ) :
    ∑ f : I → Bool, boolSign f * monomialValue m f = 0 := by
  classical
  have hex : ∃ i, m i = 0 := by
    by_contra h
    push Not at h
    exact hm (Finset.eq_univ_iff_forall.mpr fun i => by
      rw [Finsupp.mem_support_iff]
      exact h i)
  obtain ⟨i0, hi0⟩ := hex
  have hfac : (∑ f : I → Bool,
        ∏ i, (if f i then (-1 : ℝ) else 1) * (boolPoint f i) ^ (m i))
      = ∏ i, ∑ b : Bool,
          ((if b then (-1 : ℝ) else 1) * (if b = true then (1 : ℝ) else 0) ^ (m i)) := by
    simp only [boolPoint]
    exact (Fintype.prod_sum (fun (i : I) (b : Bool) => ((if b then (-1 : ℝ) else 1) *
      (if b = true then (1 : ℝ) else 0) ^ (m i)))).symm
  have hzero : (∏ i, ∑ b : Bool,
      ((if b then (-1 : ℝ) else 1) * (if b = true then (1 : ℝ) else 0) ^ (m i))) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
    rw [hi0]
    simp [Fintype.univ_bool]
  calc ∑ f : I → Bool, boolSign f * monomialValue m f
      = ∑ f : I → Bool, ∏ i, (if f i then (-1 : ℝ) else 1) * (boolPoint f i) ^ (m i) :=
        Finset.sum_congr rfl fun f _ => boolSign_mul_monomialValue m f
    _ = ∏ i, ∑ b : Bool,
          ((if b then (-1 : ℝ) else 1) * (if b = true then (1 : ℝ) else 0) ^ (m i)) := hfac
    _ = 0 := hzero

theorem signed_sum_eval_eq_zero (p : MvPolynomial I ℝ) (hdeg : p.totalDegree < Fintype.card I) :
    ∑ f : I → Bool, boolSign f * MvPolynomial.eval (boolPoint f) p = 0 := by
  classical
  have hnotuniv : ∀ m ∈ p.support, m.support ≠ Finset.univ := by
    intro m hm hsupp
    have hle := MvPolynomial.le_totalDegree (p := p) hm
    have hge : Fintype.card I ≤ m.sum (fun _ e => e) := by
      rw [Finsupp.sum, hsupp]
      calc Fintype.card I = ∑ _i : I, (1 : ℕ) := by simp
        _ ≤ ∑ i : I, m i := Finset.sum_le_sum fun i _ => by
              have hpos : m i ≠ 0 := by
                rw [← Finsupp.mem_support_iff]
                simp [hsupp]
              omega
    omega
  have hstep : ∀ f : I → Bool, boolSign f * MvPolynomial.eval (boolPoint f) p
      = ∑ m ∈ p.support, p.coeff m * (boolSign f * monomialValue m f) := by
    intro f
    rw [eval_eq_monomial_sum p f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  calc ∑ f : I → Bool, boolSign f * MvPolynomial.eval (boolPoint f) p
      = ∑ f : I → Bool, ∑ m ∈ p.support, p.coeff m * (boolSign f * monomialValue m f) :=
        Finset.sum_congr rfl fun f _ => hstep f
    _ = ∑ m ∈ p.support, ∑ f : I → Bool, p.coeff m * (boolSign f * monomialValue m f) :=
        Finset.sum_comm
    _ = ∑ m ∈ p.support, p.coeff m * (∑ f : I → Bool, boolSign f * monomialValue m f) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [sum_boolSign_mul_monomialValue m (hnotuniv m hm), mul_zero]

def parityOddB (f : I → Bool) : Bool := decide ((boolSupp f).card % 2 = 1)

omit [DecidableEq I] in

theorem boolSign_eq_neg_one_pow (f : I → Bool) :
    boolSign f = (-1 : ℝ) ^ (boolSupp f).card := by
  have h1 : (∏ i ∈ Finset.univ.filter (fun i => f i = true), (if f i then (-1 : ℝ) else 1))
      = (-1 : ℝ) ^ (boolSupp f).card := by
    rw [show (∏ i ∈ Finset.univ.filter (fun i => f i = true),
          (if f i then (-1 : ℝ) else 1))
        = ∏ _i ∈ Finset.univ.filter (fun i => f i = true), (-1 : ℝ) from by
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [if_pos hi.2]]
    rw [Finset.prod_const, boolSupp]
  have h2 : (∏ i ∈ Finset.univ.filter (fun i => ¬ f i = true),
        (if f i then (-1 : ℝ) else 1)) = 1 := by
    rw [Finset.prod_eq_one]
    intro i hi
    rw [Finset.mem_filter] at hi
    have hf : f i = false := by simpa using hi.2
    simp [hf]
  unfold boolSign
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ)
    (fun i => f i = true) (fun i => (if f i then (-1 : ℝ) else 1))]
  rw [h1, h2, mul_one]

omit [DecidableEq I] in

theorem boolSign_eq_ite (f : I → Bool) :
    boolSign f = if parityOddB f then (-1 : ℝ) else 1 := by
  rw [boolSign_eq_neg_one_pow]
  unfold parityOddB
  rw [neg_one_pow_eq_ite]
  by_cases h : (boolSupp f).card % 2 = 1
  · have hne : ¬ Even (boolSupp f).card := by
      intro he
      rw [Nat.even_iff] at he
      omega
    have hdec : decide ((boolSupp f).card % 2 = 1) = true := by simp [h]
    simp [hne, hdec]
  · have he : Even (boolSupp f).card := by
      rw [Nat.even_iff]
      have := Nat.mod_lt (boolSupp f).card (by norm_num : 0 < 2)
      omega
    have hdec : decide ((boolSupp f).card % 2 = 1) = false := by simp [h]
    simp [he, hdec]

theorem parityOddB_flipAt (i : I) (f : I → Bool) :
    parityOddB (flipAt i f) = !(parityOddB f) := by
  have hf := boolSign_eq_ite f
  have hfl := boolSign_eq_ite (flipAt i f)
  have hsign := boolSign_flipAt i f
  by_cases hp : parityOddB f
  · have hv : (if parityOddB f then (-1 : ℝ) else 1) = -1 := by simp [hp]
    have h1 : boolSign (flipAt i f) = 1 := by rw [hsign, hf, hv]; norm_num
    rw [hfl] at h1
    by_cases hp' : parityOddB (flipAt i f)
    · rw [if_pos hp'] at h1
      exact absurd h1 (by norm_num)
    · simp [hp, hp']
  · have hv : (if parityOddB f then (-1 : ℝ) else 1) = 1 := by simp [hp]
    have h1 : boolSign (flipAt i f) = -1 := by rw [hsign, hf, hv]
    rw [hfl] at h1
    by_cases hp' : parityOddB (flipAt i f)
    · simp [hp, hp']
    · rw [if_neg hp'] at h1
      exact absurd h1 (by norm_num)

theorem signed_sum_eq_balance (a : (I → Bool) → ℝ) :
    (∑ f : I → Bool, boolSign f * a f)
      = (∑ f ∈ Finset.univ.filter (fun f => parityOddB f = false), a f)
        - (∑ f ∈ Finset.univ.filter (fun f => parityOddB f = true), a f) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (I → Bool)))
    (p := fun f => parityOddB f = true) (f := fun f => boolSign f * a f)
  have hset : Finset.univ.filter (fun f : I → Bool => ¬ parityOddB f = true)
      = Finset.univ.filter (fun f : I → Bool => parityOddB f = false) := by
    refine Finset.filter_congr fun f _ => ?_
    cases parityOddB f <;> simp
  have hnot : (∑ f ∈ Finset.univ.filter (fun f => ¬ parityOddB f = true), boolSign f * a f)
      = ∑ f ∈ Finset.univ.filter (fun f => parityOddB f = false), a f := by
    rw [hset]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [Finset.mem_filter] at hf
    rw [boolSign_eq_ite, hf.2]
    simp
  have hpos : (∑ f ∈ Finset.univ.filter (fun f => parityOddB f = true), boolSign f * a f)
      = - ∑ f ∈ Finset.univ.filter (fun f => parityOddB f = true), a f := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [Finset.mem_filter] at hf
    rw [boolSign_eq_ite, hf.2]
    simp
  rw [← hsplit, hnot, hpos]
  ring

theorem sum_balance_of_signed_sum_zero (a : (I → Bool) → ℝ)
    (h : ∑ f : I → Bool, boolSign f * a f = 0) :
    (∑ f ∈ Finset.univ.filter (fun f => parityOddB f = false), a f)
      = ∑ f ∈ Finset.univ.filter (fun f => parityOddB f = true), a f := by
  have hb := signed_sum_eq_balance a
  rw [h] at hb
  linarith

variable {W : Type} [Fintype W] [DecidableEq W]

noncomputable def parityAcceptance (C : Circuit (PolynomialWorkspace I W))
    (ψ : QState (PolynomialWorkspace I W)) (E : Finset (PolynomialWorkspace I W))
    (f : I → Bool) : ℝ :=
  MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
