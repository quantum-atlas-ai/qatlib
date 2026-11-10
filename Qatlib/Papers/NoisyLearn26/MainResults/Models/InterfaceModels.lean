/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults

open scoped BigOperators

abbrev Reg (n : ℕ) : Type := Fin n → Bool

def tvDist {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

def StrictSubset {α : Type*} (A B : Set α) : Prop :=
  A ⊆ B ∧ ∃ a, a ∈ B ∧ a ∉ A

def IsPolynomial (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

def IsPolylog (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * (Nat.log 2 (n + 1) + 1) ^ k

def IsBigO (g f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → f n ≤ c * g n

def IsBigOmega (g f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → c * g n ≤ f n

def IsTheta (g f : ℕ → ℝ) : Prop := IsBigO g f ∧ IsBigOmega g f

structure Oracle where

  width : ℕ

  eval : Reg width → Reg width

def firstHalf {n : ℕ} (x : Reg (n + n)) : Reg n :=
  fun i => x ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n n)⟩

def secondHalf {n : ℕ} (x : Reg (n + n)) : Reg n :=
  fun i => x ⟨i.val + n, Nat.add_lt_add_right i.isLt n⟩

def fLift {n : ℕ} (f : Reg n → Reg n) (x : Reg (n + n)) : Reg n :=
  fun i => if (∀ k, secondHalf x k = false) then f (firstHalf x) i else false

def liftedSimonOracle {n : ℕ} (f : Reg n → Reg n) : Oracle where
  width := n + n
  eval := fun x i =>
    if h : i.val < n then x i
    else Bool.xor (x i) (fLift f x ⟨i.val - n, by omega⟩)

structure EncodedShufflingOracle (n d : ℕ) extends Oracle where

  isShuffling : Prop

  shadow : Oracle

structure RelAlgorithm (O : Oracle) where

  qubits : ℕ

  depth : ℕ → ℕ

  noise : ℝ

  queries : ℕ → ℕ

  successProb : List Bool → ℝ

def SolvesPromise {O : Oracle} (A : RelAlgorithm O) (yes no : Prop) : Prop :=
  (yes → (2 : ℝ) / 3 ≤ A.successProb []) ∧ (no → A.successProb [] ≤ (1 : ℝ) / 3)

def InRelClass {O : Oracle} (admissible : RelAlgorithm O → Prop)
    (yes no : Prop) : Prop :=
  ∃ A : RelAlgorithm O, admissible A ∧ SolvesPromise A yes no

def NBQP (O : Oracle) (yes no : Prop) : Prop :=
  InRelClass (O := O)
    (fun A => 0 < A.noise ∧ A.noise < 1 ∧ IsPolynomial A.queries) yes no

def BQP (O : Oracle) (yes no : Prop) : Prop :=
  InRelClass (O := O) (fun A => IsPolynomial A.queries) yes no

def NISQ (O : Oracle) (yes no : Prop) : Prop :=
  InRelClass (O := O)
    (fun A => 0 < A.noise ∧ A.noise < 1 ∧ IsPolynomial A.queries ∧
      IsPolylog A.depth) yes no

def ClassStrict (C D : Prop → Prop → Prop) : Prop :=
  (∀ yes no, C yes no → D yes no) ∧ ∃ yes no, D yes no ∧ ¬ C yes no

structure LayerTree (A : Type*) [Fintype A] (N : ℕ) where

  kernel : (i : Fin N) → (Fin i.val → A) → A → ℝ

  kernel_nonneg : ∀ (i : Fin N) (u : Fin i.val → A) (a : A), 0 ≤ kernel i u a

  kernel_sum_one : ∀ (i : Fin N) (u : Fin i.val → A), ∑ a, kernel i u a = 1

def LayerTree.pathPrefix {A : Type*} [Fintype A] {N : ℕ} (x : Fin N → A) (i : Fin N) :
    Fin i.val → A :=
  fun j => x ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt i.isLt)⟩

def LayerTree.pathProb {A : Type*} [Fintype A] {N : ℕ} (T : LayerTree A N)
    (x : Fin N → A) : ℝ :=
  ∏ i : Fin N, T.kernel i (pathPrefix x i) (x i)

def leafTV {A : Type*} [Fintype A] {N : ℕ} (T T' : LayerTree A N) : ℝ :=
  (∑ x : Fin N → A, |T.pathProb x - T'.pathProb x|) / 2

def IsInjective {n : ℕ} (f : Reg n → Reg n) : Prop := Function.Injective f

def HasPeriod {n : ℕ} (f : Reg n → Reg n) : Prop :=
  ∃ s : Reg n, s ≠ (fun _ => false) ∧ ∀ x, f (fun i => Bool.xor (x i) (s i)) = f x

abbrev PauliChar : Type := Fin 4

abbrev Pauli (n : ℕ) : Type := Fin n → PauliChar

def pauliWeight {n : ℕ} (P : Pauli n) : ℕ :=
  (Finset.univ.filter (fun i => P i ≠ 0)).card

def depolarizePauli {n : ℕ} (_lam : ℝ) (P : Pauli n) : Pauli n := P

def depolScale {n : ℕ} (lam : ℝ) (P : Pauli n) : ℝ := (1 - lam) ^ pauliWeight P

def fLambda (lam : ℝ) : ℝ := 1 - lam + lam ^ 2 / 2

def twoCopySampleCost (n : ℕ) (lam : ℝ) : ℝ := (n : ℝ) * (1 - lam) ^ (-(4 * (n : ℝ)))

def corollary27Exponent (n : ℕ) (lam : ℝ) : ℝ :=
  (n : ℝ) * Real.log (2 / fLambda lam) /
    (Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam))

structure Channel (E : Type*) [NormedAddCommGroup E] [Module ℝ E] where

  toFun : E → E

  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

  map_smul' : ∀ (c : ℝ) x, toFun (c • x) = c • toFun x

  contract : ∀ x, ‖toFun x‖ ≤ ‖x‖

def Channel.iterate {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (Φ : Channel E) : ℕ → E → E
  | 0, x => x
  | (N + 1), x => Φ.toFun (iterate Φ N x)

theorem Channel.map_sub {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (Φ : Channel E) (x y : E) : Φ.toFun (x - y) = Φ.toFun x - Φ.toFun y := by
  have hneg : Φ.toFun (-y) = -Φ.toFun y := by
    have := Φ.map_smul' (-1) y
    rwa [neg_one_smul, neg_one_smul] at this
  rw [sub_eq_add_neg, Φ.map_add', hneg, sub_eq_add_neg]

end Qatlib.Papers.NoisyLearn26.MainResults
