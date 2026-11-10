/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix

structure CircuitFamily where
  build : (n : ℕ) → Circuit (Reg n)
  poly : ∃ k c : ℕ, ∀ n, Size (build n) ≤ c * n ^ k + c

variable {n : ℕ}

noncomputable def AcceptProb (ψ : QState (Reg n)) (h : 0 < n) : ℝ :=
  MeasureProb ψ (Finset.univ.filter fun x => x ⟨0, h⟩ = true)

def InBQP (L : (n : ℕ) → Reg n → Prop) : Prop :=
  ∃ F : CircuitFamily, ∀ (n : ℕ) (hn : 0 < n) (x : Reg n),
    (L n x → (2 / 3 : ℝ) ≤ AcceptProb (Run 1 (F.build n) (Ket x)) hn) ∧
    (¬ L n x → AcceptProb (Run 1 (F.build n) (Ket x)) hn ≤ (1 / 3 : ℝ))

def FirstBitLang (n : ℕ) (x : Reg n) : Prop := ∀ h : 0 < n, x ⟨0, h⟩ = true

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

def SolvesWithError (O : F → Matrix I I ℂ) (Acc : F → Finset I) (C : Circuit I)
    (ψ₀ : QState I) (ε : ℝ) : Prop :=
  ∀ f : F, 1 - ε ≤ MeasureProb (Run (O f) C ψ₀) (Acc f)

variable [DecidableEq I]

def FixedSpaceQueryUpperBound (O : F → Matrix I I ℂ) (Acc : F → Finset I)
    (ε : ℝ) (k : ℕ) : Prop :=
  (0 ≤ ε ∧ ε < 1) ∧ (∀ f, O f ∈ Matrix.unitaryGroup I ℂ) ∧
    ∃ (C : Circuit I) (ψ₀ : QState I),
      IsUnitaryCircuit C ∧ Normalized ψ₀ ∧ QueryCount C ≤ k ∧
        SolvesWithError O Acc C ψ₀ ε

def FixedSpaceQueryLowerBound (O : F → Matrix I I ℂ) (Acc : F → Finset I)
    (ε : ℝ) (k : ℕ) : Prop :=
  (0 ≤ ε ∧ ε < 1) ∧ (∀ f, O f ∈ Matrix.unitaryGroup I ℂ) ∧
    ∀ (C : Circuit I) (ψ₀ : QState I),
      IsUnitaryCircuit C → Normalized ψ₀ → SolvesWithError O Acc C ψ₀ ε →
        k ≤ QueryCount C

theorem FixedSpaceQueryUpperBound.mono {O : F → Matrix I I ℂ} {Acc : F → Finset I}
    {ε : ℝ} {k k' : ℕ} (hk : k ≤ k') (h : FixedSpaceQueryUpperBound O Acc ε k) :
    FixedSpaceQueryUpperBound O Acc ε k' := by
  obtain ⟨hε, hO, C, ψ₀, hC, hψ, hcount, hsolve⟩ := h
  exact ⟨hε, hO, C, ψ₀, hC, hψ, hcount.trans hk, hsolve⟩

theorem FixedSpaceQueryLowerBound.anti {O : F → Matrix I I ℂ} {Acc : F → Finset I}
    {ε : ℝ} {k k' : ℕ} (hk : k' ≤ k) (h : FixedSpaceQueryLowerBound O Acc ε k) :
    FixedSpaceQueryLowerBound O Acc ε k' := by
  obtain ⟨hε, hO, hlo⟩ := h
  exact ⟨hε, hO, fun C ψ₀ hC hψ hsolve => hk.trans (hlo C ψ₀ hC hψ hsolve)⟩

theorem FixedSpaceQueryLowerBound.le_of_upperBound {O : F → Matrix I I ℂ}
    {Acc : F → Finset I} {ε : ℝ} {k k' : ℕ}
    (hlo : FixedSpaceQueryLowerBound O Acc ε k')
    (hup : FixedSpaceQueryUpperBound O Acc ε k) : k' ≤ k := by
  obtain ⟨_, _, C, ψ₀, hC, hψ, hcount, hsolve⟩ := hup
  exact (hlo.2.2 C ψ₀ hC hψ hsolve).trans hcount

end QueryDefs

end Qatlib.Concepts.QueryComplexity.DegreeMethod
