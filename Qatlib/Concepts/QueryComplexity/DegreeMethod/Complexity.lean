/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Circuit families and fixed-space query bounds

This module defines polynomial-size `CircuitFamily` objects and an `InBQP` acceptance predicate
on positive input lengths. It also gives explicit upper and lower query bound predicates for a
fixed finite state space, including unitary oracle and normalized state requirements. The
surrounding circuit complexity framework is described in [NielsenChuang2010].

The fixed-space bounds are monotone in their numerical budgets, and any lower bound is at most
any upper bound for the same oracle problem and error parameter.

## Main statements

* `inBQP_firstBit`: the first-bit language satisfies the acceptance predicate.
* `FixedSpaceQueryUpperBound` and `FixedSpaceQueryLowerBound`: explicit query bounds in a fixed
  state space.
* `FixedSpaceQueryLowerBound.le_of_upperBound`: compatible lower and upper bounds are ordered.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix

/-- A family of circuits indexed by register length, with a size bound of the form `c * n ^ k +
c`. -/
structure CircuitFamily where
  build : (n : ℕ) → Circuit (Reg n)
  poly : ∃ k c : ℕ, ∀ n, Size (build n) ≤ c * n ^ k + c

variable {n : ℕ}

/-- The probability that the first register bit is true, defined for a positive register length. -/
noncomputable def AcceptProb (ψ : QState (Reg n)) (h : 0 < n) : ℝ :=
  MeasureProb ψ (Finset.univ.filter fun x => x ⟨0, h⟩ = true)

/-- The existence of a polynomial-size circuit family whose first-bit acceptance probabilities
are at least two-thirds on members of `L` and at most one-third on nonmembers, for positive
input lengths. -/
def InBQP (L : (n : ℕ) → Reg n → Prop) : Prop :=
  ∃ F : CircuitFamily, ∀ (n : ℕ) (hn : 0 < n) (x : Reg n),
    (L n x → (2 / 3 : ℝ) ≤ AcceptProb (Run 1 (F.build n) (Ket x)) hn) ∧
    (¬ L n x → AcceptProb (Run 1 (F.build n) (Ket x)) hn ≤ (1 / 3 : ℝ))

/-- The language requiring the first input bit to be true whenever the input length is positive. -/
def FirstBitLang (n : ℕ) (x : Reg n) : Prop := ∀ h : 0 < n, x ⟨0, h⟩ = true

/-- The first-bit language satisfies `InBQP`, witnessed by the empty circuit family. -/
theorem inBQP_firstBit : InBQP FirstBitLang := by
  refine ⟨⟨fun _ => [], ⟨0, 0, fun n => by simp [Size]⟩⟩, ?_⟩
  intro n hn x
  have hrun : Run 1 ([] : Circuit (Reg n)) (Ket x) = Ket x := rfl
  rw [hrun]
  constructor
  · intro hL
    have hx : x ⟨0, hn⟩ = true := hL hn
    rw [AcceptProb, MeasureProb,
      Finset.sum_eq_single x (fun y _ hyx => by rw [bornProb_ket, if_neg hyx])
        (fun hnot => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩) hnot)]
    rw [bornProb_ket, if_pos rfl]
    norm_num
  · intro hnL
    unfold FirstBitLang at hnL
    rw [not_forall] at hnL
    obtain ⟨h0, hh0⟩ := hnL
    have hx0 : x ⟨0, hn⟩ = false := by
      have e : (⟨0, hn⟩ : Fin n) = ⟨0, h0⟩ := rfl
      rw [e]
      exact (Bool.not_eq_true _).mp hh0
    have hz : (∑ y ∈ Finset.univ.filter (fun y => y ⟨0, hn⟩ = true), BornProb (Ket x) y)
        = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨-, hy2⟩ := hy
      rw [bornProb_ket, if_neg]
      rintro rfl
      rw [hx0] at hy2
      exact Bool.noConfusion hy2
    rw [AcceptProb, MeasureProb, hz]
    norm_num

section QueryDefs

variable {I : Type*} [Fintype I] {F : Type*}

/-- The condition that running `C` from `ψ₀` yields the designated success event with
probability at least `1 - ε` for every oracle input. -/
def SolvesWithError (O : F → Matrix I I ℂ) (Acc : F → Finset I) (C : Circuit I)
    (ψ₀ : QState I) (ε : ℝ) : Prop :=
  ∀ f : F, 1 - ε ≤ MeasureProb (Run (O f) C ψ₀) (Acc f)

variable [DecidableEq I]

/-- A fixed-space query upper bound witnessed by a unitary circuit and normalized initial state
using at most `k` queries, with unitary oracles and `0 ≤ ε < 1`. -/
def FixedSpaceQueryUpperBound (O : F → Matrix I I ℂ) (Acc : F → Finset I)
    (ε : ℝ) (k : ℕ) : Prop :=
  (0 ≤ ε ∧ ε < 1) ∧ (∀ f, O f ∈ Matrix.unitaryGroup I ℂ) ∧
    ∃ (C : Circuit I) (ψ₀ : QState I),
      IsUnitaryCircuit C ∧ Normalized ψ₀ ∧ QueryCount C ≤ k ∧
        SolvesWithError O Acc C ψ₀ ε

/-- A fixed-space query lower bound requiring every unitary circuit and normalized initial state
solving the problem at error `ε` to use at least `k` queries, with unitary oracles and `0 ≤
ε < 1`. -/
def FixedSpaceQueryLowerBound (O : F → Matrix I I ℂ) (Acc : F → Finset I)
    (ε : ℝ) (k : ℕ) : Prop :=
  (0 ≤ ε ∧ ε < 1) ∧ (∀ f, O f ∈ Matrix.unitaryGroup I ℂ) ∧
    ∀ (C : Circuit I) (ψ₀ : QState I),
      IsUnitaryCircuit C → Normalized ψ₀ → SolvesWithError O Acc C ψ₀ ε →
        k ≤ QueryCount C

/-- Increasing the numerical query budget preserves a fixed-space query upper bound. -/
theorem FixedSpaceQueryUpperBound.mono {O : F → Matrix I I ℂ} {Acc : F → Finset I}
    {ε : ℝ} {k k' : ℕ} (hk : k ≤ k') (h : FixedSpaceQueryUpperBound O Acc ε k) :
    FixedSpaceQueryUpperBound O Acc ε k' := by
  obtain ⟨hε, hO, C, ψ₀, hC, hψ, hcount, hsolve⟩ := h
  exact ⟨hε, hO, C, ψ₀, hC, hψ, hcount.trans hk, hsolve⟩

/-- Decreasing the numerical query threshold preserves a fixed-space query lower bound. -/
theorem FixedSpaceQueryLowerBound.anti {O : F → Matrix I I ℂ} {Acc : F → Finset I}
    {ε : ℝ} {k k' : ℕ} (hk : k' ≤ k) (h : FixedSpaceQueryLowerBound O Acc ε k) :
    FixedSpaceQueryLowerBound O Acc ε k' := by
  obtain ⟨hε, hO, hlo⟩ := h
  exact ⟨hε, hO, fun C ψ₀ hC hψ hsolve => hk.trans (hlo C ψ₀ hC hψ hsolve)⟩

/-- A fixed-space query lower bound is at most any upper bound for the same oracle family,
success events, and error parameter. -/
theorem FixedSpaceQueryLowerBound.le_of_upperBound {O : F → Matrix I I ℂ}
    {Acc : F → Finset I} {ε : ℝ} {k k' : ℕ}
    (hlo : FixedSpaceQueryLowerBound O Acc ε k')
    (hup : FixedSpaceQueryUpperBound O Acc ε k) : k' ≤ k := by
  obtain ⟨_, _, C, ψ₀, hC, hψ, hcount, hsolve⟩ := hup
  exact (hlo.2.2 C ψ₀ hC hψ hsolve).trans hcount

end QueryDefs

end Qatlib.Concepts.QueryComplexity.DegreeMethod
