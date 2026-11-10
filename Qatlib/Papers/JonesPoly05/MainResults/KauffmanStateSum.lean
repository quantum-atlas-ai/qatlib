/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.JonesPoly05.MainResults.Kauffman

structure SignedGen (n : ℕ) where

  idx : Fin (n - 1)

  pos : Bool

abbrev BraidWord (n : ℕ) := List (SignedGen n)

def writhe {n : ℕ} (B : BraidWord n) : ℤ :=
  (B.map fun g => if g.pos then (1 : ℤ) else -1).sum

def lowerPos {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩

def upperPos {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1 + 1, by
    have hn : 0 < n :=
      Nat.pos_of_ne_zero fun h => by subst h; exact Nat.not_lt_zero i.1 i.isLt
    have h : i.1 + 1 < (n - 1) + 1 := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ i.isLt
    rwa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] at h⟩

def smoothingPerm {n : ℕ} (g : SignedGen n) (straight : Bool) : Equiv.Perm (Fin n) :=
  if straight then 1 else Equiv.swap (lowerPos g.idx) (upperPos g.idx)

def statePerm {n : ℕ} (B : BraidWord n) (σ : Fin B.length → Bool) : Equiv.Perm (Fin n) :=
  (List.ofFn (fun j : Fin B.length => smoothingPerm (B.get j) (σ j))).prod

def loops {n : ℕ} (B : BraidWord n) (σ : Fin B.length → Bool) : ℕ :=
  (statePerm B σ).cycleFactorsFinset.card

def stepWeight {n : ℕ} (A : ℂ) (g : SignedGen n) (straight : Bool) : ℂ :=
  if straight = g.pos then A⁻¹ else A

def stateWeight {n : ℕ} (A : ℂ) (B : BraidWord n) (σ : Fin B.length → Bool) : ℂ :=
  ∏ j : Fin B.length, stepWeight A (B.get j) (σ j)

def bracketTrace {n : ℕ} (A d : ℂ) (B : BraidWord n) : ℂ :=
  ∑ σ : Fin B.length → Bool, stateWeight A B σ * d ^ ((loops B σ : ℤ) - 1)

def jonesTrace {n : ℕ} (A d : ℂ) (B : BraidWord n) : ℂ :=
  (-A) ^ (3 * writhe B : ℤ) * bracketTrace A d B

def markovTrace {n : ℕ} (A d : ℂ) (B : BraidWord n) : ℂ :=
  ∑ σ : Fin B.length → Bool, stateWeight A B σ * d ^ ((loops B σ : ℤ) - (n : ℤ))

theorem bracket_weight_eq_trace_weight {n : ℕ} {A d : ℂ} (hd : d ≠ 0)
    (B : BraidWord n) (σ : Fin B.length → Bool) :
    stateWeight A B σ * d ^ ((loops B σ : ℤ) - 1) =
      d ^ ((n : ℤ) - 1) *
        (stateWeight A B σ * d ^ ((loops B σ : ℤ) - (n : ℤ))) := by
  have hz : d ^ ((loops B σ : ℤ) - 1) =
      d ^ ((n : ℤ) - 1) * d ^ ((loops B σ : ℤ) - (n : ℤ)) := by
    rw [← zpow_add₀ hd]
    congr 1
    ring
  rw [hz]
  ring

theorem jonesTrace_eq_markovTrace {n : ℕ} {A d : ℂ} (hd : d ≠ 0) (B : BraidWord n) :
    jonesTrace A d B =
      (-A) ^ (3 * writhe B : ℤ) * d ^ ((n : ℤ) - 1) * markovTrace A d B := by
  unfold jonesTrace bracketTrace markovTrace
  have hsum : (∑ σ : Fin B.length → Bool,
        stateWeight A B σ * d ^ ((loops B σ : ℤ) - 1)) =
      d ^ ((n : ℤ) - 1) * ∑ σ : Fin B.length → Bool,
        (stateWeight A B σ * d ^ ((loops B σ : ℤ) - (n : ℤ))) := by
    rw [Finset.mul_sum (s := Finset.univ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact bracket_weight_eq_trace_weight hd B σ
  rw [hsum, mul_assoc]

end Qatlib.Papers.JonesPoly05.MainResults.Kauffman
