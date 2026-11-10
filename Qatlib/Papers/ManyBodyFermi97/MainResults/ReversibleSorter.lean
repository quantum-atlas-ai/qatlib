/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.CircuitReversal.ReversalAlgebra.CircuitReversalAlgebra
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.ReversibleSorter
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open scoped Classical BigOperators

variable {n : ℕ}

def permute {m : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → Fin m) : Fin n → Fin m :=
  a ∘ (σ : Fin n → Fin n)

theorem permute_comp {m : ℕ} (σ τ : Equiv.Perm (Fin n)) (a : Fin n → Fin m) :
    permute σ (permute τ a) = permute (τ * σ) a := by
  funext i
  simp [permute]

theorem swap_inv {α : Type*} [DecidableEq α] (i j : α) :
    (Equiv.swap i j)⁻¹ = Equiv.swap i j := by
  rw [show (Equiv.swap i j)⁻¹ = Equiv.symm (Equiv.swap i j) from rfl, Equiv.symm_swap]

theorem isSwap_inv {g : Equiv.Perm (Fin n)} (hg : g.IsSwap) : g⁻¹ = g := by
  obtain ⟨i, j, _hij, rfl⟩ := hg
  exact swap_inv i j

theorem permute_swap_involutive {m : ℕ} (i j : Fin n) :
    Function.Involutive (permute (m := m) (Equiv.swap i j)) := by
  intro a
  funext k
  show a ((Equiv.swap i j) ((Equiv.swap i j) k)) = a k
  have h : (Equiv.swap i j * Equiv.swap i j) = 1 := by
    rw [Equiv.Perm.mul_def]
    exact Equiv.swap_swap i j
  rw [← Equiv.Perm.mul_apply, h]
  rfl

theorem permute_involutive_of_isSwap {m : ℕ} {g : Equiv.Perm (Fin n)} (hg : g.IsSwap) :
    Function.Involutive (permute (m := m) g) := by
  obtain ⟨i, j, _hij, rfl⟩ := hg
  exact permute_swap_involutive i j

def swapGate {m : ℕ} (g : Equiv.Perm (Fin n)) : Matrix (Fin n → Fin m) (Fin n → Fin m) ℂ :=
  permMatrix (permute (m := m) g)

theorem swapGate_unitary {m : ℕ} {g : Equiv.Perm (Fin n)} (hg : g.IsSwap) :
    swapGate (m := m) g ∈ Matrix.unitaryGroup (Fin n → Fin m) ℂ :=
  permMatrix_unitary (permute_involutive_of_isSwap hg)

theorem swapGate_action {m : ℕ} {g : Equiv.Perm (Fin n)} (hg : g.IsSwap)
    (ψ : QState (Fin n → Fin m)) (k : Fin n → Fin m) :
    ApplyGate (swapGate (m := m) g) ψ k = ψ (permute g k) :=
  applyGate_permMatrix (permute_involutive_of_isSwap hg) ψ k

def exchangeWord {m : ℕ} (l : List (Equiv.Perm (Fin n))) : Circuit (Fin n → Fin m) :=
  l.map (fun g => .gate (swapGate (m := m) g))

def wordPerm (l : List (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) := l.prod

theorem run_exchangeWord_action {m : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, g.IsSwap) (ψ : QState (Fin n → Fin m)) (k : Fin n → Fin m) :
    Run 1 (exchangeWord (m := m) l) ψ k = ψ (permute ((wordPerm l)⁻¹) k) := by
  induction l generalizing ψ with
  | nil => simp [exchangeWord, wordPerm, permute]
  | cons g rest ih =>
    have hg : g.IsSwap := hl g List.mem_cons_self
    have hr : ∀ h ∈ rest, h.IsSwap := fun h hh => hl h (List.mem_cons_of_mem g hh)
    have hinv : g⁻¹ = g := isSwap_inv hg
    change Run 1 (Step.gate (swapGate (m := m) g) :: exchangeWord (m := m) rest) ψ k =
      ψ (permute ((wordPerm (g :: rest))⁻¹) k)
    rw [run_gate, ih hr, swapGate_action hg, permute_comp]
    congr 1
    simp only [wordPerm, List.prod_cons, _root_.mul_inv_rev, hinv]

theorem exchangeWord_unitary {m : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, g.IsSwap) : IsUnitaryCircuit (exchangeWord (m := m) l) := by
  induction l with
  | nil => exact isUnitaryCircuit_nil
  | cons g rest ih =>
    have hg : g.IsSwap := hl g List.mem_cons_self
    have hr : ∀ h ∈ rest, h.IsSwap := fun h hh => hl h (List.mem_cons_of_mem g hh)
    exact (isUnitaryCircuit_gate _ _).mpr ⟨swapGate_unitary hg, ih hr⟩

theorem exchangeWord_queryCount {m : ℕ} (l : List (Equiv.Perm (Fin n))) :
    QueryCount (exchangeWord (m := m) l) = 0 := by
  induction l with
  | nil => rfl
  | cons g rest ih => exact (queryCount_gate _ _).trans ih

theorem exchangeWord_gateCount {m : ℕ} (l : List (Equiv.Perm (Fin n))) :
    GateCount (exchangeWord (m := m) l) = l.length := by
  induction l with
  | nil => rfl
  | cons g rest ih =>
    change GateCount (Step.gate (swapGate (m := m) g) :: exchangeWord (m := m) rest) =
      (g :: rest).length
    rw [gateCount_gate, ih]
    rfl

theorem exchangeWord_correct {m : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, g.IsSwap) :
    IsUnitaryCircuit (exchangeWord (m := m) l) ∧
      QueryCount (exchangeWord (m := m) l) = 0 ∧
      GateCount (exchangeWord (m := m) l) = l.length :=
  ⟨exchangeWord_unitary l hl, exchangeWord_queryCount l, exchangeWord_gateCount l⟩

theorem prod_reverse_eq_inv (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, g.IsSwap) :
    l.reverse.prod = (l.prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons g rest ih =>
    have hg : g.IsSwap := hl g List.mem_cons_self
    have hr : ∀ h ∈ rest, h.IsSwap := fun h hh => hl h (List.mem_cons_of_mem g hh)
    have hinv : g⁻¹ = g := isSwap_inv hg
    rw [List.reverse_cons, List.prod_append, ih hr]
    simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [_root_.mul_inv_rev, hinv]

theorem reverse_word_fixes {m : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, g.IsSwap) (a : Fin n → Fin m) :
    permute ((wordPerm (l ++ l.reverse))⁻¹) a = a := by
  have h1 : wordPerm (l ++ l.reverse) = 1 := by
    rw [wordPerm, List.prod_append, prod_reverse_eq_inv l hl, mul_inv_cancel]
  rw [h1]
  funext k
  simp [permute]

theorem exists_swap_word (σ : Equiv.Perm (Fin n)) :
    ∃ l : List (Equiv.Perm (Fin n)), (∀ g ∈ l, g.IsSwap) ∧ wordPerm l = σ := by
  obtain ⟨l, hprod, hisSwap⟩ := Equiv.Perm.swapFactors σ
  exact ⟨l, hisSwap, hprod⟩

theorem sorting_identity (σ : Equiv.Perm (Fin n)) :
    ∃ l : List (Equiv.Perm (Fin n)), (∀ g ∈ l, g.IsSwap) ∧
      wordPerm l = σ ∧ permute ((wordPerm l)⁻¹) (fun i => σ i) = id := by
  obtain ⟨l, hisSwap, hprod⟩ := exists_swap_word σ
  refine ⟨l, hisSwap, hprod, ?_⟩
  rw [hprod]
  funext k
  simp [permute]

theorem sorting_input {m : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → Fin m) :
    ∃ l : List (Equiv.Perm (Fin n)), (∀ g ∈ l, g.IsSwap) ∧
      wordPerm l = σ ∧ permute ((wordPerm l)⁻¹) a = permute σ⁻¹ a := by
  obtain ⟨l, hisSwap, hprod⟩ := exists_swap_word σ
  exact ⟨l, hisSwap, hprod, by rw [hprod]⟩

theorem exchangeWord_phase (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, g.IsSwap) :
    (Equiv.Perm.sign (wordPerm l) : ℤ) = (-1 : ℤ) ^ l.length := by
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (Equiv.Perm.sign_prod_list_swap (l := l) hl)
  simpa [wordPerm] using h

theorem sorting_phase (σ : Equiv.Perm (Fin n)) :
    ∃ l : List (Equiv.Perm (Fin n)), (∀ g ∈ l, g.IsSwap) ∧
      wordPerm l = σ ∧ (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ l.length := by
  obtain ⟨l, hisSwap, hprod⟩ := exists_swap_word σ
  refine ⟨l, hisSwap, hprod, ?_⟩
  rw [← hprod]
  exact exchangeWord_phase l hisSwap

end Qatlib.Papers.ManyBodyFermi97.MainResults.ReversibleSorter
