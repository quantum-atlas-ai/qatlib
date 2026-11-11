/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Permutation state sums and trace normalization

`SignedGen` and `BraidWord` provide signed generator data for a finite permutation-based state
sum. The definitions `bracketTrace`, `jonesTrace`, and `markovTrace` use smoothing weights and
the cycle count `loops`; their normalization factors are related algebraically when the loop
parameter is nonzero. See [AharonovJonesLandau2009].

## Main statements

* `bracket_weight_eq_trace_weight`: For nonzero d, each bracket summand equals d^(n − 1) times
  the corresponding Markov-trace summand.
* `jonesTrace_eq_markovTrace`: For nonzero d, `jonesTrace` equals the Markov state sum
  multiplied by (−A)^(3 writhe) and d^(n − 1).

## References

* [Aharonov et al., 2009][AharonovJonesLandau2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.JonesPoly05.MainResults.Kauffman

/-- A generator index on n strands together with a Boolean crossing sign. -/
structure SignedGen (n : ℕ) where

  idx : Fin (n - 1)

  pos : Bool

/-- A finite list of signed generator indices on n strands. -/
abbrev BraidWord (n : ℕ) := List (SignedGen n)

/-- The integer sum of crossing signs, with positive crossings contributing one and negative
crossings contributing minus one. -/
def writhe {n : ℕ} (B : BraidWord n) : ℤ :=
  (B.map fun g => if g.pos then (1 : ℤ) else -1).sum

/-- The lower strand position associated with a generator index. -/
def lowerPos {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩

/-- The upper strand position, one greater than the generator index. -/
def upperPos {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1 + 1, by
    have hn : 0 < n :=
      Nat.pos_of_ne_zero fun h => by subst h; exact Nat.not_lt_zero i.1 i.isLt
    have h : i.1 + 1 < (n - 1) + 1 := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ i.isLt
    rwa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] at h⟩

/-- The identity permutation for a straight smoothing and the adjacent transposition otherwise. -/
def smoothingPerm {n : ℕ} (g : SignedGen n) (straight : Bool) : Equiv.Perm (Fin n) :=
  if straight then 1 else Equiv.swap (lowerPos g.idx) (upperPos g.idx)

/-- The ordered product of the smoothing permutations selected by a Boolean state. -/
def statePerm {n : ℕ} (B : BraidWord n) (σ : Fin B.length → Bool) : Equiv.Perm (Fin n) :=
  (List.ofFn (fun j : Fin B.length => smoothingPerm (B.get j) (σ j))).prod

/-- The number of nontrivial cycle factors in the state permutation. -/
def loops {n : ℕ} (B : BraidWord n) (σ : Fin B.length → Bool) : ℕ :=
  (statePerm B σ).cycleFactorsFinset.card

/-- The smoothing coefficient A⁻¹ when the smoothing bit equals the crossing sign, and A
otherwise. -/
def stepWeight {n : ℕ} (A : ℂ) (g : SignedGen n) (straight : Bool) : ℂ :=
  if straight = g.pos then A⁻¹ else A

/-- The product of the smoothing coefficients over all crossings of a braid word. -/
def stateWeight {n : ℕ} (A : ℂ) (B : BraidWord n) (σ : Fin B.length → Bool) : ℂ :=
  ∏ j : Fin B.length, stepWeight A (B.get j) (σ j)

/-- The sum over Boolean smoothing states of their weights times d raised to the cycle count
minus one. -/
def bracketTrace {n : ℕ} (A d : ℂ) (B : BraidWord n) : ℂ :=
  ∑ σ : Fin B.length → Bool, stateWeight A B σ * d ^ ((loops B σ : ℤ) - 1)

/-- The writhe-normalized state sum obtained by multiplying `bracketTrace` by (−A)^(3 writhe). -/
def jonesTrace {n : ℕ} (A d : ℂ) (B : BraidWord n) : ℂ :=
  (-A) ^ (3 * writhe B : ℤ) * bracketTrace A d B

/-- The state sum with loop exponent equal to the cycle count minus the number of strands. -/
def markovTrace {n : ℕ} (A d : ℂ) (B : BraidWord n) : ℂ :=
  ∑ σ : Fin B.length → Bool, stateWeight A B σ * d ^ ((loops B σ : ℤ) - (n : ℤ))

/-- For nonzero d, each bracket summand equals d^(n − 1) times the corresponding Markov-trace
summand; see [AharonovJonesLandau2009]. -/
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

/-- For nonzero d, `jonesTrace` equals the Markov state sum multiplied by (−A)^(3 writhe) and
d^(n − 1); see [AharonovJonesLandau2009]. -/
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
