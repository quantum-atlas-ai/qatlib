/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNativeDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs

/-!
# Native arithmetic and finite-precision bounds

This module proves correctness and numeric bounds for the bit-list operations `bitAdd`,
`bitMul`, `bitGcd`, and `bitModPow`. The theorem `native_add_run` realizes addition on a
three-stack machine with explicit turn, clock, and stack-space bounds.

It also constructs exact and rounded rational names, proves error budgets for `NativeWord`, and
verifies forward-access arithmetic programs and a uniform Boolean sampler. These finite
encodings and precision estimates provide concrete arithmetic infrastructure in the setting of
[KitaevShenVyalyi2002]; the phase example `offGridQpeWord` uses the phase-estimation setting
discussed in [NielsenChuang2010].

## Main statements

* `bitAdd_value` and `bitMul_value`: correctness of binary arithmetic.
* `native_add_run`: a halted addition run with explicit resource bounds.
* `nativeWordErrorActual_budget`: the selected precision achieves the target word error.
* `nativeSamplerProgram_probLaw`: the exact output probability law of the Boolean sampler.
* `clause3_program_complete`: the program correctness and access-restriction package.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Call

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ValidatorSemantics
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs

open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.QueryComplexity.DegreeMethod.ParseFramed
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs (FairCoinLaw)
open Qatlib.Foundations.IntervalArith.IntervalOps (unit roundDown)
open Turing

/-- The sum bit and twice the outgoing carry equal the sum of the two input bits and incoming
carry. -/
theorem carryStep_value (c xb yb : Bool) :
    bitNat (carryStep c xb yb).1 + 2 * bitNat (carryStep c xb yb).2
      = bitNat xb + bitNat yb + bitNat c := by
  rcases c <;> rcases xb <;> rcases yb <;> decide

/-- The empty bit list represents zero. -/
@[simp] theorem binaryValue_nil : binaryValue ([] : Bits) = 0 := rfl

/-- Prepending a bit contributes its value in the least significant position and doubles the
value of the remaining bits. -/
@[simp] theorem binaryValue_cons' (b : Bool) (bs : Bits) :
    binaryValue (b :: bs) = 2 * binaryValue bs + bitNat b := by
  rw [binaryValue_cons]; rfl

/-- A singleton bit list represents the natural number associated with its bit. -/
@[simp] theorem binaryValue_singleton (b : Bool) : binaryValue [b] = bitNat b := by
  simp [binaryValue_cons', binaryValue_nil]

/-- The list containing one true bit when the condition holds, and no bits otherwise, represents
the condition's bit value. -/
theorem binaryValue_if_true (b : Bool) :
    binaryValue (if b then [true] else []) = bitNat b := by
  cases b <;> rfl

/-- Appending two bit lists shifts the value of the second list by the length of the first. -/
theorem binaryValue_append (l1 l2 : Bits) :
    binaryValue (l1 ++ l2) = binaryValue l1 + 2 ^ l1.length * binaryValue l2 := by
  induction l1 with
  | nil => simp
  | cons b l1 ih =>
    rw [List.cons_append, binaryValue_cons, binaryValue_cons, ih, List.length_cons,
      Nat.pow_succ]
    ring

/-- The value of the first `n + 1` bits is twice the value of the first `n` tail bits plus the
head bit, defaulting to false. -/
theorem binaryValue_take_succ (bs : Bits) (n : ℕ) :
    binaryValue (bs.take (n+1)) = 2 * binaryValue ((bs.tail).take n)
      + bitNat (bs.head?.getD false) := by
  cases bs with
  | nil => simp [bitNat]
  | cons b bs => rw [List.take_succ_cons, binaryValue_cons']; rfl

/-- One addition turn removes the head of the first input list. -/
@[simp] theorem addTurn_xs (s : AddState) : (addTurn s).xs = s.xs.tail := rfl

/-- One addition turn removes the head of the second input list. -/
@[simp] theorem addTurn_ys (s : AddState) : (addTurn s).ys = s.ys.tail := rfl

/-- One addition turn updates the carry using `carryStep` on the current carry and input heads,
defaulting missing bits to false. -/
@[simp] theorem addTurn_carry (s : AddState) : (addTurn s).carry =
    (carryStep s.carry (s.xs.head?.getD false) (s.ys.head?.getD false)).2 := rfl

/-- One addition turn prepends the sum bit produced by `carryStep` to the output accumulator. -/
@[simp] theorem addTurn_os (s : AddState) : (addTurn s).os =
    (carryStep s.carry (s.xs.head?.getD false) (s.ys.head?.getD false)).1 :: s.os := rfl

/-- After `k` addition turns, the reversed output value plus the appropriately weighted carry
equals the initial reversed output value plus the weighted sum of the consumed input
prefixes and initial carry. -/
theorem addTurns_value : ∀ (k : ℕ) (c : Bool) (x y os : Bits),
    let s := addTurns k ⟨c, x, y, os⟩
    binaryValue (List.reverse s.os) + 2 ^ (os.length + k) * bitNat s.carry
      = binaryValue (List.reverse os)
        + 2 ^ os.length
          * (binaryValue (x.take k) + binaryValue (y.take k) + bitNat c) := by
  intro k
  induction k with
  | zero =>
    intro c x y os
    simp [addTurns]
  | succ k ih =>
    intro c x y os
    have h := ih (addTurn ⟨c, x, y, os⟩).carry (addTurn ⟨c, x, y, os⟩).xs
      (addTurn ⟨c, x, y, os⟩).ys (addTurn ⟨c, x, y, os⟩).os
    have hval : addTurns (k+1) ⟨c, x, y, os⟩ = addTurns k (addTurn ⟨c, x, y, os⟩) := rfl
    have hlen : (addTurn ⟨c, x, y, os⟩).os.length = os.length + 1 := by simp
    have hexp : os.length + (k+1) = os.length + 1 + k := by omega
    have hL : binaryValue (List.reverse (addTurns k (addTurn ⟨c, x, y, os⟩)).os)
          + 2 ^ (os.length + (k+1))
              * bitNat (addTurns k (addTurn ⟨c, x, y, os⟩)).carry
        = binaryValue (List.reverse (addTurns k (addTurn ⟨c, x, y, os⟩)).os)
          + 2 ^ ((addTurn ⟨c, x, y, os⟩).os.length + k)
              * bitNat (addTurns k (addTurn ⟨c, x, y, os⟩)).carry := by
      rw [hlen, hexp]
    simp only [hval]
    rw [hL, h]
    have hx : binaryValue (x.take (k+1)) = 2 * binaryValue ((x.tail).take k)
        + bitNat (x.head?.getD false) := binaryValue_take_succ x k
    have hy : binaryValue (y.take (k+1)) = 2 * binaryValue ((y.tail).take k)
        + bitNat (y.head?.getD false) := binaryValue_take_succ y k
    have hcs := carryStep_value c (x.head?.getD false) (y.head?.getD false)
    have hbr : binaryValue (x.take (k+1)) + binaryValue (y.take (k+1)) + bitNat c
        = bitNat (carryStep c (x.head?.getD false) (y.head?.getD false)).1
          + 2 * (binaryValue ((x.tail).take k) + binaryValue ((y.tail).take k)
              + bitNat (carryStep c (x.head?.getD false) (y.head?.getD false)).2) := by
      omega
    simp only [addTurn_os, addTurn_xs, addTurn_ys, addTurn_carry, List.reverse_cons]
    rw [binaryValue_append]
    simp only [List.length_reverse, List.length_cons, binaryValue_singleton, Nat.pow_succ]
    rw [hbr]
    ring

/-- Performing `k` addition turns increases the output accumulator length by exactly `k`. -/
theorem addTurns_os_length (k : ℕ) (c : Bool) (x y os : Bits) :
    (addTurns k ⟨c, x, y, os⟩).os.length = os.length + k := by
  induction k generalizing c x y os with
  | zero => rfl
  | succ k ih =>
    rw [addTurns, ih, addTurn_os]
    simp only [List.length_cons]
    omega

/-- Taking at least the length of a bit list returns the original list. -/
theorem take_eq_self (l : Bits) : ∀ {n : ℕ}, l.length ≤ n → l.take n = l := by
  induction l with
  | nil => intro n h; simp
  | cons b l ih =>
    intro n h
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.length_cons] at h
      rw [List.take_succ_cons, ih (by omega)]

/-- The natural value of a bit list is strictly less than two raised to its length. -/
theorem binaryValue_lt_pow_length (l : Bits) : binaryValue l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb : bitNat b < 2 := by unfold bitNat; split <;> omega
    calc binaryValue (b :: l) = 2 * binaryValue l + bitNat b := binaryValue_cons' b l
      _ < 2 * 2 ^ l.length := by omega
      _ = 2 ^ (l.length + 1) := by rw [Nat.pow_succ]; ring

/-- The output of `n` carry-addition turns, together with its carry weighted by `2 ^ n`,
represents the sum of the first `n` bits of each input and the incoming carry. -/
theorem carryAddAux_value (n : ℕ) (c : Bool) (x y : Bits) :
    let r := carryAddAux n c x y
    binaryValue r.1 + 2 ^ n * bitNat r.2
      = binaryValue (x.take n) + binaryValue (y.take n) + bitNat c := by
  simp only [carryAddAux]
  simpa using! addTurns_value n c x y []

/-- Carry addition represents the sum of the two input values and the incoming carry bit. -/
theorem carryAdd_value (c : Bool) (x y : Bits) :
    binaryValue (carryAdd c x y) = binaryValue x + binaryValue y + bitNat c := by
  have hn : x.length ≤ max x.length y.length := le_max_left _ _
  have hn2 : y.length ≤ max x.length y.length := le_max_right _ _
  have h := carryAddAux_value (max x.length y.length) c x y
  have hres : (carryAddAux (max x.length y.length) c x y).1.length
      = max x.length y.length := by
    simp [carryAddAux, addTurns_os_length]
  have hx : x.take (max x.length y.length) = x := take_eq_self x hn
  have hy : y.take (max x.length y.length) = y := take_eq_self y hn2
  simp only at h
  rw [hx, hy] at h
  simp only [carryAdd]
  rw [binaryValue_append]
  simp only [hres]
  rw [binaryValue_if_true]
  exact h

/-- Binary addition represents the sum of the input values. -/
theorem bitAdd_value (x y : Bits) :
    binaryValue (bitAdd x y) = binaryValue x + binaryValue y := by
  have h := carryAdd_value false x y
  simp [bitNat] at h
  rw [bitAdd]
  omega

/-- Carry addition produces at most one more bit than the longer input. -/
theorem carryAdd_length (c : Bool) (x y : Bits) :
    (carryAdd c x y).length ≤ max x.length y.length + 1 := by
  have hres : (carryAddAux (max x.length y.length) c x y).1.length
      = max x.length y.length := by
    simp [carryAddAux, addTurns_os_length]
  unfold carryAdd
  rw [List.length_append, hres]
  split <;> simp_all

/-- Shifting a bit list left by `i` positions multiplies its value by `2 ^ i`. -/
theorem shiftLeft_value (b : Bits) (i : ℕ) :
    binaryValue (shiftLeft b i) = 2 ^ i * binaryValue b := by
  rw [shiftLeft, binaryValue_append, binaryValue_replicate_false]
  simp only [List.length_replicate]
  ring

/-- Prepending a most significant bit adds its value weighted by two raised to the tail length. -/
theorem msbValue_cons (b : Bool) (l : Bits) :
    msbValue (b :: l) = msbValue l + 2 ^ l.length * bitNat b := by
  simp only [msbValue, List.reverse_cons, binaryValue_append, binaryValue_singleton,
    List.length_reverse]

/-- The multiplication accumulator returns the product of the first input value and the most
significant bit interpretation of the remaining multiplier, plus the initial accumulator
shifted by the multiplier length. -/
theorem bitMulAux_value : ∀ (x ys acc : Bits),
    binaryValue (bitMulAux x ys acc)
      = 2 ^ ys.length * binaryValue acc + binaryValue x * msbValue ys := by
  intro x ys
  induction ys with
  | nil =>
    intro acc
    simp [bitMulAux, msbValue, binaryValue_nil]
  | cons b ys ih =>
    intro acc
    have h1 : binaryValue (shiftLeft acc 1) = 2 * binaryValue acc := shiftLeft_value acc 1
    have h2 : binaryValue (carryAdd false (shiftLeft acc 1) x)
        = binaryValue (shiftLeft acc 1) + binaryValue x := carryAdd_value false (shiftLeft acc 1) x
    rw [bitMulAux]
    by_cases hb : b
    · simp [hb]
      rw [ih, h2, h1, msbValue_cons]
      simp only [List.length_cons, Nat.pow_succ]
      have hbt : bitNat true = 1 := rfl
      rw [hbt]
      ring
    · simp [hb]
      rw [ih, h1, msbValue_cons]
      simp only [List.length_cons, Nat.pow_succ]
      have hbf : bitNat false = 0 := rfl
      rw [hbf]
      ring

/-- Binary multiplication represents the product of the input values. -/
theorem bitMul_value (x y : Bits) :
    binaryValue (bitMul x y) = binaryValue x * binaryValue y := by
  rw [bitMul]
  have h := bitMulAux_value x y.reverse []
  simp only [List.length_reverse, binaryValue_nil, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at h
  rw [h]
  have hrev : msbValue y.reverse = binaryValue y := by
    simp [msbValue]
  rw [hrev]
  ring

/-- The numeric value of a binary product is strictly less than two raised to the sum of the
input lengths. -/
theorem bitMul_value_lt (x y : Bits) :
    binaryValue (bitMul x y) < 2 ^ (x.length + y.length) := by
  rw [bitMul_value, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (binaryValue_lt_pow_length x)
    (binaryValue_lt_pow_length y)

/-- Stack zero of `addStacks` is the first input. -/
@[simp] theorem addStacks_zero (x y out : Bits) : addStacks x y out 0 = x := by
  simp [addStacks]

/-- Stack one of `addStacks` is the second input. -/
@[simp] theorem addStacks_one (x y out : Bits) : addStacks x y out 1 = y := by
  simp [addStacks]

/-- Stack two of `addStacks` is the output accumulator. -/
@[simp] theorem addStacks_two (x y out : Bits) : addStacks x y out 2 = out := by
  simp [addStacks]

/-- Updating stack zero replaces the first input while preserving the other stacks. -/
theorem addStacks_update_zero (x y out w : Bits) :
    Function.update (addStacks x y out) 0 w = addStacks w y out := by
  funext i
  fin_cases i <;> simp [Function.update, addStacks]

/-- Updating stack one replaces the second input while preserving the other stacks. -/
theorem addStacks_update_one (x y out w : Bits) :
    Function.update (addStacks x y out) 1 w = addStacks x w out := by
  funext i
  fin_cases i <;> simp [Function.update, addStacks]

/-- Updating stack two replaces the output accumulator while preserving the input stacks. -/
theorem addStacks_update_two (x y out w : Bits) :
    Function.update (addStacks x y out) 2 w = addStacks x y w := by
  funext i
  fin_cases i <;> simp [Function.update, addStacks]

/-- One loop step of `addProgram` either halts on empty inputs, appending any final carry to the
output stack, or consumes the input heads and pushes their sum bit. -/
theorem addProgram_step (c : Bool) (x y out : Bits) :
    TM2.stepAux (addProgram .loop) ⟨c, none, none⟩ (addStacks x y out)
      = if x = [] ∧ y = [] then
          ⟨none, ⟨c, none, none⟩, addStacks [] [] (if c then true :: out else out)⟩
        else
          ⟨some .loop,
            ⟨(carryStep c (x.head?.getD false) (y.head?.getD false)).2, none, none⟩,
            addStacks x.tail y.tail
              ((carryStep c (x.head?.getD false) (y.head?.getD false)).1 :: out)⟩ := by
  cases x <;> cases y <;> cases c <;>
    simp [addProgram, TM2.stepAux, addStacks, addStacks_update_zero,
      addStacks_update_one, addStacks_update_two, List.head?_cons, AddVar,
      Option.getD_none, Option.getD_some]

/-- Dropping `n` bits produces the empty list exactly when the original list has length at most
`n`. -/
theorem drop_eq_nil_iff (l : Bits) (n : ℕ) : l.drop n = [] ↔ l.length ≤ n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp
    | succ n => simp [ih, Nat.succ_le]

/-- Dropping `n + 1` bits is the same as taking the tail after dropping `n` bits. -/
theorem drop_succ_tail (l : Bits) (n : ℕ) : l.drop (n+1) = (l.drop n).tail := by
  induction n generalizing l with
  | zero => cases l <;> rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons a l => exact ih l

/-- Dropping `n` bits from a tail is the same as dropping `n + 1` bits from the original list. -/
theorem drop_tail (l : Bits) (n : ℕ) : (l.tail).drop n = l.drop (n+1) := by
  cases l with
  | nil => simp
  | cons a l => exact (List.drop_succ_cons).symm

/-- After `k` addition turns, the first input consists of its original bits with the first `k`
positions removed. -/
theorem addTurns_xs (k : ℕ) (c : Bool) (x y os : Bits) :
    (addTurns k ⟨c, x, y, os⟩).xs = x.drop k := by
  induction k generalizing c x y os with
  | zero => rfl
  | succ k ih =>
    rw [addTurns, ih]
    simp only [addTurn_xs]
    exact drop_tail x k

/-- After `k` addition turns, the second input consists of its original bits with the first `k`
positions removed. -/
theorem addTurns_ys (k : ℕ) (c : Bool) (x y os : Bits) :
    (addTurns k ⟨c, x, y, os⟩).ys = y.drop k := by
  induction k generalizing c x y os with
  | zero => rfl
  | succ k ih =>
    rw [addTurns, ih]
    simp only [addTurn_ys]
    exact drop_tail y k

/-- The state after `k + 1` turns is obtained by one addition turn from the carry, remaining
input suffixes, and output after `k` turns. -/
theorem addTurns_step (k : ℕ) (c : Bool) (x y os : Bits) :
    addTurns (k+1) ⟨c, x, y, os⟩
      = addTurn ⟨(addTurns k ⟨c, x, y, os⟩).carry, x.drop k, y.drop k,
          (addTurns k ⟨c, x, y, os⟩).os⟩ := by
  induction k generalizing c x y os with
  | zero => rfl
  | succ k ih =>
    rw [addTurns]
    have h := ih (addTurn ⟨c, x, y, os⟩).carry (addTurn ⟨c, x, y, os⟩).xs
      (addTurn ⟨c, x, y, os⟩).ys (addTurn ⟨c, x, y, os⟩).os
    rw [h]
    simp only [addTurn_xs, addTurn_ys]
    rw [drop_tail x k, drop_tail y k]
    rfl

/-- The loop configuration after `k` addition turns, with the remaining input suffixes and
accumulated output on its three stacks. -/
def addCfgLoop (k : ℕ) (x y : Bits) : TM2.Cfg (fun _ : Fin 3 => Bool) AddLabel AddVar :=
  ⟨some .loop, ⟨(addTurns k ⟨false, x, y, []⟩).carry, none, none⟩,
    addStacks (x.drop k) (y.drop k) (addTurns k ⟨false, x, y, []⟩).os⟩

/-- The halted addition configuration with empty input stacks and any final carry prepended to
the output stack. -/
def addCfgFinal (x y : Bits) : TM2.Cfg (fun _ : Fin 3 => Bool) AddLabel AddVar :=
  ⟨none, ⟨(addTurns (max x.length y.length) ⟨false, x, y, []⟩).carry, none, none⟩,
    addStacks [] []
      (if (addTurns (max x.length y.length) ⟨false, x, y, []⟩).carry
        then true :: (addTurns (max x.length y.length) ⟨false, x, y, []⟩).os
        else (addTurns (max x.length y.length) ⟨false, x, y, []⟩).os)⟩

/-- The addition configuration indexed by a turn count, using the loop configuration through the
input width and the final configuration afterward. -/
def addCfgAt (k : ℕ) (x y : Bits) : TM2.Cfg (fun _ : Fin 3 => Bool) AddLabel AddVar :=
  if k ≤ max x.length y.length then addCfgLoop k x y else addCfgFinal x y

/-- At a turn count no larger than the maximum input length, `addCfgAt` is the corresponding
loop configuration. -/
theorem addCfgAt_eq_loop (x y : Bits) {k : ℕ} (hk : k ≤ max x.length y.length) :
    addCfgAt k x y = addCfgLoop k x y := by
  rw [addCfgAt, if_pos hk]

/-- Beyond the maximum input length, `addCfgAt` is the final configuration. -/
theorem addCfgAt_eq_final (x y : Bits) {k : ℕ} (hk : max x.length y.length < k) :
    addCfgAt k x y = addCfgFinal x y := by
  have h : ¬ (k ≤ max x.length y.length) := by omega
  rw [addCfgAt, if_neg h]

/-- A machine step advances the indexed addition configuration by one while the turn count is at
most the maximum input length. -/
theorem addProgram_step_at (x y : Bits) (k : ℕ) (hk : k ≤ max x.length y.length) :
    TM2.step addProgram (addCfgAt k x y) = some (addCfgAt (k+1) x y) := by
  have hcfg0 : addCfgAt k x y = addCfgLoop k x y := addCfgAt_eq_loop x y hk
  rw [hcfg0]
  unfold addCfgLoop
  rw [TM2.step]
  rw [addProgram_step]
  by_cases hempty : x.drop k = [] ∧ y.drop k = []
  · have hx := hempty.1
    have hy := hempty.2
    rw [if_pos hempty]
    have hkx : x.length ≤ k := by
      have hz : (x.drop k).length = 0 := by rw [hx]; rfl
      rw [List.length_drop] at hz
      omega
    have hky : y.length ≤ k := by
      have hz : (y.drop k).length = 0 := by rw [hy]; rfl
      rw [List.length_drop] at hz
      omega
    have hkmax : k = max x.length y.length := by omega
    have hcfg1 : addCfgAt (k+1) x y = addCfgFinal x y := by
      rw [hkmax]
      exact addCfgAt_eq_final x y (by omega)
    rw [hcfg1, hkmax]
    rfl
  · rw [if_neg hempty]
    have hkx : x.length ≤ k → ¬ (y.length ≤ k) := by
      intro hx' hy'
      apply hempty
      exact ⟨(drop_eq_nil_iff x k).mpr hx', (drop_eq_nil_iff y k).mpr hy'⟩
    have hk1 : k + 1 ≤ max x.length y.length := by
      by_cases h1 : k + 1 ≤ max x.length y.length
      · exact h1
      · exfalso
        have hmax : max x.length y.length ≤ k := by omega
        have hx'' : x.length ≤ k := by omega
        have hy' : ¬ (y.length ≤ k) := hkx hx''
        have hy'' : y.length ≤ k := by omega
        exact hy' hy''
    have hcfg1 : addCfgAt (k+1) x y = addCfgLoop (k+1) x y := addCfgAt_eq_loop x y hk1
    rw [hcfg1]
    unfold addCfgLoop
    rw [addTurns_step]
    simp only [addTurn_carry, addTurn_os, drop_succ_tail]

/-- The stack height of a three-stack configuration is the sum of its three stack lengths. -/
theorem stackHeight_eq {Λ σ : Type} (c : TM2.Cfg (fun _ : Fin 3 => Bool) Λ σ) :
    stackHeight c = (c.stk 0).length + (c.stk 1).length + (c.stk 2).length := by
  simp only [stackHeight, Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

/-- Taking the tail of a bit list cannot increase its length. -/
theorem length_tail_le (l : Bits) : (l.tail).length ≤ l.length := by
  cases l with
  | nil => exact Nat.le_refl 0
  | cons a l => simp

/-- The clock cost of one addition loop statement is bounded by four times the total stack
height plus thirteen. -/
theorem stackClock_addProgram (v : AddVar) (S : Fin 3 → List Bool) :
    stackClock (addProgram .loop) v S
      ≤ 4 * ((S 0).length + (S 1).length + (S 2).length) + 13 := by
  simp [addProgram, stackClock]
  have h0 : (S 0).tail.length ≤ (S 0).length := length_tail_le (S 0)
  have h1 : (S 1).tail.length ≤ (S 1).length := length_tail_le (S 1)
  split
  · omega
  · split <;> omega

/-- Before the final addition step, the total stack height is bounded by the sum of the original
input lengths. -/
theorem stackHeight_addCfg (x y : Bits) (k : ℕ) (hk : k ≤ max x.length y.length) :
    stackHeight (addCfgAt k x y) ≤ x.length + y.length := by
  rw [addCfgAt_eq_loop x y hk]
  simp only [addCfgLoop]
  rw [stackHeight_eq]
  simp only [addStacks_zero, addStacks_one, addStacks_two]
  have hx : (x.drop k).length = x.length - k := List.length_drop
  have hy : (y.drop k).length = y.length - k := List.length_drop
  have hos : (addTurns k ⟨false, x, y, []⟩).os.length = k := by
    rw [addTurns_os_length]; simp
  by_cases h1 : k ≤ x.length
  · by_cases h2 : k ≤ y.length
    · rw [hx, hy, hos]; omega
    · have : (y.drop k).length = 0 := by
        rw [List.length_drop]; omega
      rw [this, hos]; omega
  · by_cases h2 : k ≤ y.length
    · have : (x.drop k).length = 0 := by
        rw [List.length_drop]; omega
      rw [this, hy, hos]; omega
    · have hx0 : (x.drop k).length = 0 := by
        rw [List.length_drop]; omega
      have hy0 : (y.drop k).length = 0 := by
        rw [List.length_drop]; omega
      rw [hx0, hy0, hos]; omega

/-- Running `s` steps from the configuration at turn `k` reaches the configuration at turn `k +
s` when this is within the final turn, with the stated linear bound in `s` on clock cost. -/
theorem addProgram_advance (x y : Bits) (k s : ℕ)
    (hk : k + s ≤ max x.length y.length + 1) :
    stackRun addProgram s (addCfgAt k x y) = some (addCfgAt (k+s) x y) ∧
    stackRunClock addProgram s (addCfgAt k x y)
      ≤ s * (4 * (x.length + y.length + max x.length y.length) + 14) := by
  induction s generalizing k with
  | zero =>
    constructor
    · rw [stackRun]
      rfl
    · rw [stackRunClock]
      omega
  | succ s ih =>
    have hk1 : k ≤ max x.length y.length := by omega
    have hstep : TM2.step addProgram (addCfgAt k x y) = some (addCfgAt (k+1) x y) :=
      addProgram_step_at x y k hk1
    have hrest := ih (k+1) (by omega)
    constructor
    · rw [stackRun, hstep, Option.bind_some, hrest.1]
      have heq : k + 1 + s = k + (s + 1) := by omega
      rw [heq]
    · have hlabel : (addCfgAt k x y).l = some .loop := by
        rw [addCfgAt_eq_loop x y hk1]
        rfl
      rw [stackRunClock]
      simp only [hstep, hlabel]
      have hh := stackHeight_addCfg x y k hk1
      rw [stackHeight_eq] at hh
      have hh' : ((addCfgAt k x y).stk 0).length + ((addCfgAt k x y).stk 1).length
          + ((addCfgAt k x y).stk 2).length
          ≤ x.length + y.length + max x.length y.length := by omega
      have hclock' : stackClock (addProgram .loop) (addCfgAt k x y).var (addCfgAt k x y).stk
          ≤ 4 * (x.length + y.length + max x.length y.length) + 13 := by
        have h := stackClock_addProgram (addCfgAt k x y).var (addCfgAt k x y).stk
        have h4 := Nat.mul_le_mul_left 4 hh'
        omega
      have hrest' := hrest.2
      rw [Nat.succ_mul]
      omega

/-- The final addition configuration has stack height at most one more than the maximum input
length. -/
theorem stackHeight_addCfgFinal (x y : Bits) :
    stackHeight (addCfgFinal x y) ≤ max x.length y.length + 1 := by
  rw [stackHeight_eq]
  simp only [addCfgFinal, addStacks_zero, addStacks_one, addStacks_two]
  have hos : (addTurns (max x.length y.length) ⟨false, x, y, []⟩).os.length
      = max x.length y.length := by rw [addTurns_os_length]; simp
  cases hb : (addTurns (max x.length y.length) ⟨false, x, y, []⟩).carry with
  | true =>
    simp [hb]
    rw [hos]
    omega
  | false =>
    simp [hb]
    rw [hos]
    omega

/-- The native addition machine halts with the correct sum and satisfies the specified turn,
clock, and intermediate stack-space bounds. -/
theorem native_add_run (x y : Bits) : NativeAddRun x y := by
  have hn : max x.length y.length + 1 = addTicks x y := by
    simp [addTicks, carryAddPositions]
  have hstart : addStart x y = addCfgAt 0 x y := by
    rw [addCfgAt_eq_loop x y (by simp)]
    rfl
  have hfinal : addCfgAt (max x.length y.length + 1) x y = addCfgFinal x y :=
    addCfgAt_eq_final x y (by simp)
  have hadv := addProgram_advance x y 0 (max x.length y.length + 1) (by simp)
  have hval : binaryValue (List.reverse ((addCfgFinal x y).stk 2))
      = binaryValue x + binaryValue y := by
    simp only [addCfgFinal, addStacks_two]
    have hn := addTurns_value (max x.length y.length) false x y []
    simp only at hn
    have hx : x.take (max x.length y.length) = x := take_eq_self x (le_max_left _ _)
    have hy : y.take (max x.length y.length) = y := take_eq_self y (le_max_right _ _)
    rw [hx, hy, List.reverse_nil, List.length_nil, binaryValue_nil, Nat.pow_zero,
      Nat.zero_add, Nat.one_mul] at hn
    have hos : (addTurns (max x.length y.length) ⟨false, x, y, []⟩).os.length
        = max x.length y.length := by rw [addTurns_os_length]; simp
    cases hb : (addTurns (max x.length y.length) ⟨false, x, y, []⟩).carry with
    | true =>
      simp [hb, List.reverse_cons, List.length_reverse, binaryValue_append,
        binaryValue_singleton, hos] at hn ⊢
      exact hn
    | false =>
      simp [hb, List.reverse_cons, List.length_reverse, binaryValue_append,
        binaryValue_singleton, hos] at hn ⊢
      exact hn
  refine ⟨addCfgFinal x y, max x.length y.length + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstart, ← hfinal]
    simpa using! hadv.1
  · rfl
  · exact hval
  · omega
  · rw [hstart]
    unfold addClockBound
    simp only [carryAddPositions]
    simpa using! hadv.2
  · intro s hs
    have hadvs := addProgram_advance x y 0 s (by omega)
    have hrun : stackRun addProgram s (addStart x y) = some (addCfgAt s x y) := by
      rw [hstart]
      simpa using! hadvs.1
    rw [hrun]
    by_cases hcase : s ≤ max x.length y.length
    · have hh := stackHeight_addCfg x y s hcase
      have hle : x.length + y.length ≤ addSpaceBound x y := by
        unfold addSpaceBound
        simp only [carryAddPositions]
        omega
      omega
    · have hs2 : s = max x.length y.length + 1 := by omega
      rw [hs2, hfinal]
      have hh := stackHeight_addCfgFinal x y
      have hle : max x.length y.length + 1 ≤ addSpaceBound x y := by
        unfold addSpaceBound
        simp only [carryAddPositions]
        omega
      omega

/-- Decoding the rational encoding of a natural number returns that number. -/
theorem RatEnc.ofNat_toRat (n : ℕ) : (RatEnc.ofNat n).toRat = n := by
  rw [RatEnc.toRat, RatEnc.ofNat]
  norm_num

/-- The encoding size of a natural number is at most its binary size plus three. -/
theorem RatEnc.ofNat_size (n : ℕ) : (RatEnc.ofNat n).size ≤ n.size + 3 := by
  rw [RatEnc.size, RatEnc.ofNat]
  simp only [Int.natAbs_of_nonneg (by norm_num : (0 : ℤ) ≤ n)]
  norm_num

/-- The fixed denominator encoding of `m` at scale `e` decodes to `m / 2 ^ e`. -/
theorem RatEnc.fixed_toRat (m e : ℕ) :
    (RatEnc.fixed m e).toRat = (m : ℚ) / (2 : ℚ) ^ e := by
  rw [RatEnc.toRat, RatEnc.fixed]
  push_cast
  ring

/-- Casting a natural number to an integer and taking its absolute value preserves its binary
size. -/
theorem intNatAbs_size (m : ℕ) : ((m : ℤ).natAbs).size = m.size := by
  have h1 : ((m : ℤ).natAbs : ℕ) = m := by
    have h := Int.natAbs_of_nonneg (by norm_num : (0 : ℤ) ≤ m)
    exact_mod_cast h
  rw [h1]

/-- A native name for a rational number that returns its exact rational encoding at every
precision and has zero error. -/
def NativeName.exact (q : ℚ) : NativeName where
  eval := fun _ => ⟨q.num, q.den, by positivity⟩
  value := (q : ℝ)
  errAt := fun _ => 0
  descBits := q.num.natAbs.size + q.den.size + 2
  sizeSpec := by
    intro p
    simp only [RatEnc.size]
    omega
  errSpec := by
    intro p
    have h : (⟨q.num, q.den, by positivity⟩ : RatEnc).toRat = q := by
      rw [RatEnc.toRat, Rat.num_div_den]
    simp only [RatEnc.toReal]
    rw [h]
    simp
  errBudget := by
    intro p
    simp

/-- A native name for a nonnegative rational number obtained by rounding down to multiples of `1
/ 2 ^ p` at precision `p`, with the prescribed encoding-size and error bounds. -/
def NativeName.rounded (q : ℚ) (hq : 0 ≤ q) : NativeName where
  eval := fun p => RatEnc.fixed (⌊q * (2 : ℚ) ^ p⌋.toNat) p
  value := (q : ℝ)
  errAt := fun _ => unit _
  descBits := q.num.natAbs.size + q.den.size + 2
  sizeSpec := by
    intro p
    have hfloor : 0 ≤ ⌊q * (2 : ℚ) ^ p⌋ := (Int.floor_nonneg).2 (by positivity)
    have hnat : (⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat = ⌊q * (2 : ℚ) ^ p⌋ :=
      Int.toNat_of_nonneg hfloor
    have hnum : (0 : ℤ) ≤ q.num := by
      have heq : (q.num : ℚ) / q.den = q := Rat.num_div_den q
      have h2 : (0 : ℚ) < q.den := by
        have h1 : (0 : ℕ) < q.den := Rat.den_pos q
        exact_mod_cast h1
      have h3 : (0 : ℚ) ≤ (q.num : ℚ) / q.den := by
        rw [heq]
        exact hq
      have h4 : (0 : ℚ) ≤ (q.num : ℚ) := by
        have h5 := (le_div_iff₀ h2).1 h3
        simpa using! h5
      exact_mod_cast h4
    have hle : ((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℚ)
        ≤ (q.num.natAbs : ℚ) * (2 : ℚ) ^ p := by
      calc (↑(⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℚ) = ⌊q * (2 : ℚ) ^ p⌋ := by
            exact_mod_cast hnat
        _ ≤ q * (2 : ℚ) ^ p := Int.floor_le _
        _ ≤ (q.num.natAbs : ℚ) * (2 : ℚ) ^ p := by
            have h2 : (q : ℚ) ≤ (q.num.natAbs : ℚ) := by
              have h2 : ((q.num.natAbs : ℕ) : ℤ) = (q.num : ℤ) := by
                rw [Int.natCast_natAbs, abs_of_nonneg hnum]
              have h3 : ((q.num.toNat : ℕ) : ℤ) = (q.num : ℤ) := Int.toNat_of_nonneg hnum
              have h4 : ((q.num.natAbs : ℕ) : ℤ) = ((q.num.toNat : ℕ) : ℤ) :=
                h2.trans h3.symm
              have h5 : (q.num.natAbs : ℕ) = q.num.toNat := by exact_mod_cast h4
              have h1 : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
                rw [h5]
                rw [← Int.cast_natCast (q.num.toNat), h3]
              have hden : (0 : ℚ) < (q.den : ℚ) := by
                have h1 : (0 : ℕ) < q.den := Rat.den_pos q
                exact_mod_cast h1
              have h7 : ((q.num : ℚ) / q.den : ℚ) ≤ (q.num : ℚ) := by
                have h7' : (q.num : ℚ) * 1 ≤ (q.num : ℚ) * (q.den : ℚ) := by
                  apply mul_le_mul_of_nonneg_left
                  · have h1 : (0 : ℕ) < q.den := Rat.den_pos q
                    have h2 : (1 : ℕ) ≤ q.den := by omega
                    exact_mod_cast h2
                  · exact_mod_cast hnum
                simp only [mul_one] at h7'
                exact (div_le_iff₀ (G₀ := ℚ) (a := (q.num : ℚ)) (b := (q.num : ℚ))
                  (c := (q.den : ℚ)) hden).mpr h7'
              have h6 : (q : ℚ) ≤ (q.num : ℚ) := by
                have h9 : (q : ℚ) = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
                have htr : ∀ (X : ℚ), ((q.num : ℚ) / q.den : ℚ) ≤ X → (q : ℚ) ≤ X := by
                  intro X hX
                  exact Eq.mpr (congrArg (fun z : ℚ => z ≤ X) h9) hX
                exact htr (q.num : ℚ) h7
              rw [h1.symm] at h6
              exact h6
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hle' : (⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat ≤ q.num.natAbs * 2 ^ p := by
      have h2 : (2 : ℚ) ^ p = ((2 ^ p : ℕ) : ℚ) := by
        rw [Nat.cast_pow]
        rfl
      rw [h2] at hle
      exact_mod_cast hle
    have hnumsize : q.num.natAbs < 2 ^ q.num.natAbs.size :=
      (Nat.size_le).mp (le_refl _)
    have hmsize : ((↑(⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℤ).natAbs).size
        ≤ q.num.natAbs.size + p := by
      rw [intNatAbs_size]
      rw [Nat.size_le]
      have h1 : q.num.natAbs * 2 ^ p < 2 ^ q.num.natAbs.size * 2 ^ p := by
        exact Nat.mul_lt_mul_of_pos_right hnumsize (by positivity)
      rw [← Nat.pow_add] at h1
      omega
    have hdense : (2 ^ p).size ≤ p + 1 := by
      rw [Nat.size_le]
      have h1 : 2 ^ p < 2 ^ (p + 1) := by
        rw [Nat.pow_succ, Nat.mul_two]
        exact Nat.lt_add_of_pos_left (by positivity)
      exact h1
    simp only [RatEnc.size, RatEnc.fixed]
    omega
  errSpec := by
    intro p
    have hfloor : 0 ≤ ⌊q * (2 : ℚ) ^ p⌋ := (Int.floor_nonneg).2 (by positivity)
    have hnat : (⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat = ⌊q * (2 : ℚ) ^ p⌋ :=
      Int.toNat_of_nonneg hfloor
    have hpos : (0 : ℚ) < (2 : ℚ) ^ p := by positivity
    have hcast : (((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ) : ℚ)
        = ((⌊q * (2 : ℚ) ^ p⌋ : ℤ) : ℚ) := by
      rw [← hnat]
      rfl
    have hlo : (((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ) : ℚ) / (2 : ℚ) ^ p ≤ q := by
      apply (div_le_iff₀ (a := q) (b := ((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ))
        (c := (2 : ℚ) ^ p) hpos).2
      rw [hcast]
      exact_mod_cast (Int.floor_le (q * (2 : ℚ) ^ p))
    have hhi : q < (((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ) : ℚ) / (2 : ℚ) ^ p
        + 1 / (2 : ℚ) ^ p := by
      have h1 : q * (2 : ℚ) ^ p < ((⌊q * (2 : ℚ) ^ p⌋ : ℤ) : ℚ) + 1 := by
        exact_mod_cast (Int.lt_floor_add_one (q * (2 : ℚ) ^ p))
      have hsum : (((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ) : ℚ) / (2 : ℚ) ^ p
          + 1 / (2 : ℚ) ^ p
          = ((((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ) : ℚ) + 1) / (2 : ℚ) ^ p := by
        field_simp
      rw [hsum]
      apply (lt_div_iff₀ (a := q) (b := ((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ) + 1)
        (c := (2 : ℚ) ^ p) hpos).2
      rw [hcast]
      exact h1
    have hval : (RatEnc.fixed (⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat p).toReal
        = (((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ) : ℚ) / (2 : ℚ) ^ p := by
      rw [RatEnc.toReal, RatEnc.fixed_toRat]
      norm_num
    have habs : |((((⌊q * (2 : ℚ) ^ p⌋ : ℤ).toNat : ℕ) : ℚ) / (2 : ℚ) ^ p - q)| ≤ unit p := by
      rw [abs_of_nonpos (by linarith)]
      unfold unit
      linarith
    rw [hval]
    exact_mod_cast habs
  errBudget := by
    intro p
    constructor
    · unfold unit
      positivity
    · unfold unit
      have h2 : ((2 : ℚ) ^ p : ℚ) = ((2 ^ p : ℕ) : ℚ) := by
        rw [Nat.cast_pow]
        rfl
      rw [h2]
      have hne : ((2 ^ p : ℕ) : ℚ) ≠ 0 := by positivity
      have h3 : (1 / ((2 ^ p : ℕ) : ℚ)) * ((2 ^ p : ℕ) : ℚ) = 1 := by
        field_simp
      rw [h3]

/-- Every natural number `n` is at most `2 ^ n`. -/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ]
    have h2 : (0:ℕ) < 2 ^ n := by positivity
    omega

/-- Reading a native parameter at precision `k` yields an encoding of size at most its
description bits plus `2 * k + 4`. -/
theorem native_param_encoding (p : NativeParam) (k : ℕ) :
    (p.name.eval k).size ≤ p.name.descBits + 2 * k + 4 :=
  p.name.sizeSpec k

/-- The public precision choice is the sum of the word's error units, target error bits, and
two. -/
theorem precisionChoice_public (w : NativeWord) :
    precisionChoice w.publicParams
      = w.publicParams.errUnits + w.publicParams.epsBits + 2 := rfl

/-- The selected public precision makes its power of two at least the error-unit count
multiplied by the target inverse error scale. -/
theorem nativeWordErrorUnits_bound (w : NativeWord) :
    w.publicParams.errUnits * 2 ^ w.publicParams.epsBits
      ≤ 2 ^ (precisionChoice w.publicParams) := by
  rw [precisionChoice_public, Nat.pow_add, Nat.pow_add]
  have h := nat_le_two_pow w.publicParams.errUnits
  have h2 : (0:ℕ) < 2 ^ w.publicParams.epsBits := pow_pos (by norm_num) _
  calc w.publicParams.errUnits * 2 ^ w.publicParams.epsBits
      ≤ 2 ^ w.publicParams.errUnits * 2 ^ w.publicParams.epsBits :=
        Nat.mul_le_mul_right _ h
    _ ≤ 2 ^ w.publicParams.errUnits * 2 ^ w.publicParams.epsBits * 4 := by omega
    _ = _ := by ring

/-- The error bound of a native name at precision `k` is at most `1 / 2 ^ k`. -/
theorem nativeName_err_le (N : NativeName) (k : ℕ) :
    (N.errAt k : ℚ) ≤ 1 / (2 : ℚ) ^ k := by
  have h := N.errBudget k
  have h2 : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  have h3 : (N.errAt k : ℚ) * (2 : ℚ) ^ k ≤ 1 := h.2
  rw [le_div_iff₀ h2]
  exact h3

/-- The sum of the error bounds in a native parameter slot is nonnegative. -/
theorem nativeSlotError_nonneg (s : List NativeParam) (k : ℕ) :
    0 ≤ nativeSlotError s k := by
  induction s with
  | nil => simp [nativeSlotError]
  | cons p ps ih =>
    have h1 : (0 : ℚ) ≤ p.name.errAt k := (p.name.errBudget k).1
    simp only [nativeSlotError]
    linarith

/-- The sum of the error bounds for a specified kind in a native slot is nonnegative. -/
theorem nativeSlotKindError_nonneg (s : List NativeParam) (k : ℕ) (kd : NativeParamKind) :
    0 ≤ nativeSlotKindError s k kd := by
  induction s with
  | nil => simp [nativeSlotKindError]
  | cons p ps ih =>
    have h1 : (0 : ℚ) ≤ p.name.errAt k := (p.name.errBudget k).1
    simp only [nativeSlotKindError]
    by_cases hk : p.kind = kd
    · rw [if_pos hk]
      linarith
    · rw [if_neg hk]
      linarith

/-- The total slot error multiplied by `2 ^ k` is at most the number of parameters in the slot. -/
theorem nativeSlotError_le (s : List NativeParam) (k : ℕ) :
    nativeSlotError s k * (2 : ℚ) ^ k ≤ s.length := by
  induction s with
  | nil => simp [nativeSlotError]
  | cons p ps ih =>
    have h1 : (p.name.errAt k : ℚ) * (2 : ℚ) ^ k ≤ 1 := (p.name.errBudget k).2
    have h2 : nativeSlotError ps k * (2 : ℚ) ^ k ≤ ps.length := ih
    simp only [nativeSlotError, List.length_cons, Nat.cast_add]
    rw [add_mul]
    have h3 : p.name.errAt k * (2 : ℚ) ^ k + nativeSlotError ps k * (2 : ℚ) ^ k
        ≤ ↑ps.length + ↑1 := by
      calc p.name.errAt k * (2 : ℚ) ^ k + nativeSlotError ps k * (2 : ℚ) ^ k
          ≤ 1 + nativeSlotError ps k * (2 : ℚ) ^ k := add_le_add_left h1 _
        _ ≤ 1 + ↑ps.length := add_le_add_right h2 1
        _ = ↑ps.length + ↑1 := by ring
    exact h3

/-- The error contribution from one parameter kind is bounded by the total slot error. -/
theorem nativeSlotKindError_le (s : List NativeParam) (k : ℕ) (kd : NativeParamKind) :
    nativeSlotKindError s k kd ≤ nativeSlotError s k := by
  induction s with
  | nil => simp [nativeSlotKindError, nativeSlotError]
  | cons p ps ih =>
    have h1 : (0 : ℚ) ≤ p.name.errAt k := (p.name.errBudget k).1
    have h2 : (0 : ℚ) ≤ nativeSlotKindError ps k kd := nativeSlotKindError_nonneg ps k kd
    simp only [nativeSlotKindError, nativeSlotError]
    by_cases hk : p.kind = kd
    · rw [if_pos hk]
      linarith
    · rw [if_neg hk]
      linarith

/-- The weighted word error multiplied by `2 ^ k` is at most the public error-unit count. -/
theorem nativeWordErrorActual_le (w : NativeWord) (k : ℕ) :
    nativeWordErrorActual w k * (2 : ℚ) ^ k ≤ w.publicParams.errUnits := by
  have hfold : ∀ (l : List (List NativeParam × ℕ)),
      nativeWordErrorActualAux l k * (2 : ℚ) ^ k ≤ nativeWordErrorUnitsAux l := by
    intro l
    induction l with
    | nil => simp [nativeWordErrorActualAux, nativeWordErrorUnitsAux]
    | cons hd tl ih =>
      rcases hd with ⟨s, a⟩
      have h1 : nativeSlotError s k * (2 : ℚ) ^ k ≤ s.length := nativeSlotError_le s k
      have h2 : (0 : ℚ) ≤ (a : ℚ) := Nat.cast_nonneg a
      have h3 : (a : ℚ) * nativeSlotError s k * (2 : ℚ) ^ k ≤ (a : ℚ) * s.length := by
        calc (a : ℚ) * nativeSlotError s k * (2 : ℚ) ^ k
            = (a : ℚ) * (nativeSlotError s k * (2 : ℚ) ^ k) := by ring
          _ ≤ (a : ℚ) * s.length :=
            mul_le_mul_of_nonneg_left
              (b := nativeSlotError s k * (2 : ℚ) ^ k) (c := s.length) h1 h2
      simp only [nativeWordErrorActualAux, nativeWordErrorUnitsAux, Nat.cast_add,
        Nat.cast_mul]
      rw [add_mul]
      linarith
  have h1 := hfold (w.slots.zip w.amp)
  exact h1

/-- The weighted error computed from the parameter names is bounded by the uniform word error
estimate. -/
theorem nativeWordErrorActual_le_error (w : NativeWord) (k : ℕ) :
    nativeWordErrorActual w k ≤ nativeWordError w k := by
  have h1 : nativeWordErrorActual w k * (2 : ℚ) ^ k ≤ w.publicParams.errUnits :=
    nativeWordErrorActual_le w k
  have h2 : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  rw [nativeWordError, le_div_iff₀ h2]
  exact h1

/-- At the public precision choice, the weighted word error is at most the target `1 / 2 ^
epsBits`. -/
theorem nativeWordErrorActual_budget (w : NativeWord) :
    nativeWordErrorActual w (precisionChoice w.publicParams)
      ≤ 1 / (2 : ℚ) ^ w.publicParams.epsBits := by
  have h1 : nativeWordErrorActual w (precisionChoice w.publicParams)
      ≤ w.publicParams.errUnits / (2 : ℚ) ^ (precisionChoice w.publicParams) := by
    have h2 : (0 : ℚ) < (2 : ℚ) ^ (precisionChoice w.publicParams) := by positivity
    rw [le_div_iff₀ h2]
    exact nativeWordErrorActual_le w (precisionChoice w.publicParams)
  have h3 : w.publicParams.errUnits * 2 ^ w.publicParams.epsBits
      ≤ 2 ^ (precisionChoice w.publicParams) := nativeWordErrorUnits_bound w
  have h4 : (0 : ℚ) < (2 : ℚ) ^ (precisionChoice w.publicParams) := by positivity
  have h5 : (0 : ℚ) < (2 : ℚ) ^ w.publicParams.epsBits := by positivity
  refine le_trans h1 ?_
  rw [div_le_div_iff₀ h4 h5]
  have h3' : (w.publicParams.errUnits : ℚ) * (2 : ℚ) ^ w.publicParams.epsBits
      ≤ (2 : ℚ) ^ (precisionChoice w.publicParams) := by
    exact_mod_cast h3
  simpa only [one_mul] using! h3'

/-- The weighted error from any one parameter kind is bounded by the total weighted word error. -/
theorem nativeKindErrorActual_le (w : NativeWord) (k : ℕ) (kd : NativeParamKind) :
    nativeKindErrorActual w k kd ≤ nativeWordErrorActual w k := by
  have hfold : ∀ (l : List (List NativeParam × ℕ)),
      nativeKindErrorActualAux l k kd ≤ nativeWordErrorActualAux l k := by
    intro l
    induction l with
    | nil => simp [nativeKindErrorActualAux, nativeWordErrorActualAux]
    | cons hd tl ih =>
      rcases hd with ⟨s, a⟩
      have h1 : nativeSlotKindError s k kd ≤ nativeSlotError s k := nativeSlotKindError_le s k kd
      have h2 : (0 : ℚ) ≤ (a : ℚ) := Nat.cast_nonneg a
      have h3 : (a : ℚ) * nativeSlotKindError s k kd ≤ (a : ℚ) * nativeSlotError s k := by
        exact mul_le_mul_of_nonneg_left
          (b := nativeSlotKindError s k kd) (c := nativeSlotError s k) h1 h2
      simp only [nativeKindErrorActualAux, nativeWordErrorActualAux]
      linarith
  rw [nativeKindErrorActual, nativeWordErrorActual]
  exact hfold (w.slots.zip w.amp)

/-- The rational phase `1 / 5` is distinct from every point of the three-bit dyadic grid. -/
theorem offGrid_one_five : OffGrid (1 / 5) 3 := by
  intro i hi h
  have h1 : (1 : ℚ) * (2 : ℚ) ^ 3 = (i : ℚ) * 5 :=
    (div_eq_div_iff (by norm_num) (by norm_num)).mp h
  have h2 : (8 : ℕ) = i * 5 := by
    have : (1 : ℚ) * (2 : ℚ) ^ 3 = 8 := by norm_num
    rw [this] at h1
    exact_mod_cast h1
  have h3 : (5 : ℕ) ∣ 8 := ⟨i, h2.trans (Nat.mul_comm i 5)⟩
  have h4 : (8 : ℕ) % 5 = 0 := (Nat.dvd_iff_mod_eq_zero).mp h3
  omega

/-- A native word with one exact phase parameter `1 / 5`, unit amplification, and a three-bit
error target. -/
def offGridQpeWord : NativeWord :=
  { slots := [[{ kind := .phase, name := NativeName.exact (1 / 5), marginBits := 0 }]]
    amp := [1]
    phaseBits := 3 }

/-- The off-grid phase example has one parameter, one error unit, and a three-bit error target. -/
theorem offGridQpeWord_params :
    offGridQpeWord.publicParams.paramCount = 1 ∧
    offGridQpeWord.publicParams.errUnits = 1 ∧
    offGridQpeWord.publicParams.epsBits = 3 := by
  simp [offGridQpeWord, NativeWord.publicParams, nativeWordErrorUnits,
    nativeWordErrorUnitsAux]

/-- The public precision choice for the off-grid phase example is `1 + 3 + 2`. -/
theorem offGridQpeWord_precision :
    precisionChoice offGridQpeWord.publicParams = 1 + 3 + 2 := by
  simp [offGridQpeWord, NativeWord.publicParams, nativeWordErrorUnits,
    nativeWordErrorUnitsAux, precisionChoice]

/-- At its selected precision, the off-grid phase example satisfies the error budget `1 / 2 ^
3`. -/
theorem offGridQpeWord_budget :
    nativeWordErrorActual offGridQpeWord (precisionChoice offGridQpeWord.publicParams)
      ≤ 1 / (2 : ℚ) ^ 3 := by
  have h := nativeWordErrorActual_budget offGridQpeWord
  have h2 : offGridQpeWord.publicParams.epsBits = 3 := offGridQpeWord_params.2.2
  rw [h2] at h
  exact h

/-- Mapping native parameter kinds to numerical kinds is injective. -/
theorem nativeParamKind_injective : Function.Injective nativeParamKind := by
  intro a b h
  cases a <;> cases b <;> simp [nativeParamKind] at h ⊢

/-- Every numerical kind is the image of a native parameter kind. -/
theorem nativeParamKind_surjective : Function.Surjective nativeParamKind := by
  intro k
  cases k with
  | phase => exact ⟨.phase, rfl⟩
  | rotation => exact ⟨.rotation, rfl⟩
  | prepareCoeff => exact ⟨.prepareCoeff, rfl⟩
  | spectralGap => exact ⟨.spectralGap, rfl⟩

/-- A native parameter's error is at most its stated dyadic margin when the chosen precision is
at least its margin bit count. -/
theorem native_margin_explicit (p : NativeParam) (k : ℕ) (hk : p.marginBits ≤ k) :
    (p.name.errAt k : ℚ) ≤ 1 / (2 : ℚ) ^ p.marginBits := by
  have h := nativeName_err_le p.name k
  have h2 : (1 : ℚ) / 2 ^ k ≤ 1 / 2 ^ p.marginBits := by
    have hpow : (2 : ℚ) ^ p.marginBits ≤ (2 : ℚ) ^ k := by
      have hnat : (2 : ℕ) ^ p.marginBits ≤ (2 : ℕ) ^ k :=
        Nat.pow_le_pow_right (by norm_num) hk
      exact_mod_cast hnat
    exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using! hpow)
  exact h.trans h2

/-- A native word containing exact phase, preparation-coefficient, and spectral-gap parameters
with unit amplification and explicit gap and target precision bits. -/
def lcuWord (coeffs phases : List ℚ) (gap : ℚ) (gapBits phaseBits : ℕ) : NativeWord :=
  { slots :=
      [ phases.map (fun q => { kind := .phase, name := NativeName.exact q, marginBits := 0 })
      , coeffs.map (fun q => { kind := .prepareCoeff, name := NativeName.exact q, marginBits := 0 })
      , [{ kind := .spectralGap, name := NativeName.exact gap, marginBits := gapBits }] ]
    amp := [1, 1, 1]
    phaseBits := phaseBits }

/-- The concrete linear-combination-of-unitaries parameter word with coefficients `1 / 3` and `1
/ 5`, phase `1 / 5`, gap `1 / 16`, and margin and target bit counts four and three. -/
def lcuConsumerWord : NativeWord :=
  lcuWord [1 / 3, 1 / 5] [1 / 5] (1 / 16) 4 3

/-- The concrete parameter word has four parameters, four error units, and a three-bit error
target. -/
theorem lcuConsumerWord_params :
    lcuConsumerWord.publicParams.paramCount = 4 ∧
    lcuConsumerWord.publicParams.errUnits = 4 ∧
    lcuConsumerWord.publicParams.epsBits = 3 := by
  simp [lcuConsumerWord, lcuWord, NativeWord.publicParams, nativeWordErrorUnits,
    nativeWordErrorUnitsAux]

/-- The public precision choice for the concrete parameter word is `4 + 3 + 2`. -/
theorem lcuConsumerWord_precision :
    precisionChoice lcuConsumerWord.publicParams = 4 + 3 + 2 := by
  simp [lcuConsumerWord, lcuWord, NativeWord.publicParams, nativeWordErrorUnits,
    nativeWordErrorUnitsAux, precisionChoice]

/-- At its selected precision, the concrete parameter word satisfies the error budget `1 / 2 ^
3`. -/
theorem lcuConsumerWord_budget :
    nativeWordErrorActual lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams)
      ≤ 1 / (2 : ℚ) ^ 3 := by
  have h := nativeWordErrorActual_budget lcuConsumerWord
  have h2 : lcuConsumerWord.publicParams.epsBits = 3 := lcuConsumerWord_params.2.2
  rw [h2] at h
  exact h

/-- At the selected precision, each phase, preparation-coefficient, and spectral-gap error
contribution is bounded by the total word error. -/
theorem lcuConsumerWord_kinds :
    nativeKindErrorActual lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams) .phase
        ≤ nativeWordErrorActual lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams) ∧
      nativeKindErrorActual lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams) .prepareCoeff
        ≤ nativeWordErrorActual lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams) ∧
      nativeKindErrorActual lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams) .spectralGap
        ≤ nativeWordErrorActual lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams) := by
  refine ⟨nativeKindErrorActual_le _ _ _, nativeKindErrorActual_le _ _ _,
    nativeKindErrorActual_le _ _ _⟩

/-- The reading cost of the concrete parameter word at its selected precision is eight times
that precision plus forty-one. -/
theorem lcuConsumerWord_readCost :
    nativeReadCost lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams)
      = 8 * (precisionChoice lcuConsumerWord.publicParams) + 41 := by
  have h1 : Nat.size 1 = 1 := by decide
  have h3 : Nat.size 3 = 2 := by decide
  have h5 : Nat.size 5 = 3 := by decide
  have h16 : Nat.size 16 = 5 := by decide
  have hi3 : (Int.sign 3).natAbs.size = 1 := by decide
  have hi5 : (Int.sign 5).natAbs.size = 1 := by decide
  have hi16 : (Int.sign 16).natAbs.size = 1 := by decide
  simp [nativeReadCost, lcuConsumerWord, lcuWord, NativeName.exact, h1, h3, h5, h16,
    hi3, hi5, hi16]
  ring

/-- The concrete parameter word has margin bit count four and spectral-gap error at most `1 / 2
^ 4` at its selected precision. -/
theorem lcuConsumerWord_gap :
    nativeMarginBits lcuConsumerWord = 4 ∧
    (nativeGapError lcuConsumerWord (precisionChoice lcuConsumerWord.publicParams) : ℚ)
      ≤ 1 / (2 : ℚ) ^ 4 := by
  refine ⟨?_, ?_⟩
  · simp [nativeMarginBits, lcuConsumerWord, lcuWord]
  · simp [nativeGapError, nativeKindErrorActual, nativeKindErrorActualAux, nativeSlotKindError,
      lcuConsumerWord, lcuWord, NativeName.exact]

/-- During the addition loop, the input stacks contain the unconsumed suffixes and the output
stack is the accumulator obtained from the corresponding number of addition turns. -/
theorem native_add_access (x y : Bits) (k : ℕ) (hk : k ≤ max x.length y.length) :
    (addCfgAt k x y).stk 0 = x.drop k ∧
    (addCfgAt k x y).stk 1 = y.drop k ∧
    (addCfgAt k x y).stk 2 = (addTurns k ⟨false, x, y, []⟩).os := by
  rw [addCfgAt_eq_loop x y hk]
  simp only [addCfgLoop, addStacks_zero, addStacks_one, addStacks_two]
  trivial

/-- There exists a probability assignment on Boolean outcomes satisfying `FairCoinLaw`. -/
theorem native_fair_coin : ∃ p : Bool → ℝ, FairCoinLaw p := by
  refine ⟨fun _ => 1 / 2, ?_⟩
  simp [FairCoinLaw]

/-- Encoding a natural number as bits and decoding it returns the original number. -/
theorem natToBits_value (n : ℕ) : binaryValue (natToBits n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [natToBits, natToBitsAux, binaryValue_nil]
    | succ k =>
      have hdiv : (k + 1) / 2 < k + 1 := by omega
      have h1 : binaryValue (natToBitsAux ((k + 1) / 2)) = (k + 1) / 2 := by
        simpa [natToBits] using! ih _ hdiv
      have h2 : (k + 1) % 2 = 0 ∨ (k + 1) % 2 = 1 := by
        have := Nat.mod_lt (k + 1) (by norm_num : (0 : ℕ) < 2)
        omega
      rw [natToBits, natToBitsAux, binaryValue_cons']
      have h3 : bitNat (decide ((k + 1) % 2 = 1)) = (k + 1) % 2 := by
        rcases h2 with h2 | h2
        · rw [h2]
          simp [bitNat]
        · rw [h2]
          simp [bitNat]
      rw [h3, h1]
      have h4 := Nat.mod_add_div (k + 1) 2
      omega

/-- The bit-list greatest common divisor represents the greatest common divisor of the input
values. -/
theorem bitGcd_value (x y : Bits) :
    binaryValue (bitGcd x y) = Nat.gcd (binaryValue x) (binaryValue y) := by
  rw [bitGcd, natToBits_value]

/-- Modular bit-list multiplication represents the product of the input values reduced modulo
the modulus value. -/
theorem bitModMul_value (x y m : Bits) :
    binaryValue (bitModMul x y m)
      = (binaryValue x * binaryValue y) % binaryValue m := by
  rw [bitModMul, natToBits_value]

/-- Modular bit-list exponentiation represents the base value raised to the exponent value and
reduced modulo the modulus value. -/
theorem bitModPow_value (x e m : Bits) :
    binaryValue (bitModPow x e m)
      = (binaryValue x) ^ (binaryValue e) % binaryValue m := by
  rw [bitModPow, natToBits_value]

/-- For a positive modulus value, the numeric result of modular multiplication is smaller than
two raised to the modulus bit length. -/
theorem bitModMul_size (x y m : Bits) (hm : 0 < binaryValue m) :
    binaryValue (bitModMul x y m) < 2 ^ m.length := by
  have h1 : (binaryValue x * binaryValue y) % binaryValue m < binaryValue m :=
    Nat.mod_lt _ hm
  have h2 : binaryValue m < 2 ^ m.length := binaryValue_lt_pow_length m
  have h3 : binaryValue (bitModMul x y m) < binaryValue m := by
    rw [bitModMul_value]
    exact h1
  exact h3.trans h2

/-- For a positive modulus value, the numeric result of modular exponentiation is smaller than
two raised to the modulus bit length. -/
theorem bitModPow_size (x e m : Bits) (hm : 0 < binaryValue m) :
    binaryValue (bitModPow x e m) < 2 ^ m.length := by
  have h1 : (binaryValue x) ^ (binaryValue e) % binaryValue m < binaryValue m :=
    Nat.mod_lt _ hm
  have h2 : binaryValue m < 2 ^ m.length := binaryValue_lt_pow_length m
  have h3 : binaryValue (bitModPow x e m) < binaryValue m := by
    rw [bitModPow_value]
    exact h1
  exact h3.trans h2

/-- The numeric value of the bit-list greatest common divisor is at most the larger input value. -/
theorem bitGcd_size (x y : Bits) :
    binaryValue (bitGcd x y) ≤ max (binaryValue x) (binaryValue y) := by
  by_cases hx : binaryValue x = 0
  · rw [bitGcd_value, hx, Nat.gcd_zero_left]
    exact Nat.le_max_right _ _
  · have h1 : Nat.gcd (binaryValue x) (binaryValue y) ∣ binaryValue x :=
      Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (binaryValue x) (binaryValue y) ≤ binaryValue x :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hx) h1
    rw [bitGcd_value]
    exact h2.trans (Nat.le_max_left _ _)

/-- For every bit count, there exists a uniform normalized probability assignment satisfying
`NativeSamplerLaw`. -/
theorem native_sampler_law (m : ℕ) :
    ∃ p : (Fin m → Bool) → ℝ, NativeSamplerLaw m p := by
  refine ⟨fun _ => 1 / (2 : ℝ) ^ m, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro w
    rfl
  · positivity
  · have h1 : (Fintype.card (Fin m → Bool) : ℝ) = (2 : ℝ) ^ m := by
      rw [Fintype.card_fun]
      simp only [Fintype.card_bool, Fintype.card_fin]
      norm_num
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, h1]
    field_simp

/-- The value of a bit vector of length `m` is a legal address for an address width of `m`. -/
theorem native_slot_legal (m : ℕ) (w : Fin m → Bool) :
    LegalSlot m (binaryValue (List.ofFn w)) := by
  unfold LegalSlot
  have h1 : (List.ofFn w).length = m := List.length_ofFn
  have h2 := binaryValue_lt_pow_length (List.ofFn w)
  rw [h1] at h2
  exact h2

/-- For fixed input lists and a fixed number of turns, equality of the output-and-carry pairs
determines the incoming carry. -/
theorem carryAddAux_injective_c (n : ℕ) (x y : Bits) (c c' : Bool) :
    carryAddAux n c x y = carryAddAux n c' x y → c = c' := by
  intro h
  have h1 : binaryValue (carryAddAux n c x y).1 + 2 ^ n * bitNat (carryAddAux n c x y).2
      = binaryValue (x.take n) + binaryValue (y.take n) + bitNat c :=
    carryAddAux_value n c x y
  have h2 : binaryValue (carryAddAux n c' x y).1 + 2 ^ n * bitNat (carryAddAux n c' x y).2
      = binaryValue (x.take n) + binaryValue (y.take n) + bitNat c' :=
    carryAddAux_value n c' x y
  rw [h] at h1
  have h3 : bitNat c = bitNat c' := by linarith
  cases c <;> cases c' <;> simp_all [bitNat]

/-- The final addition output stack is the accumulated sum bits with a true bit prepended
exactly when the last carry is true. -/
theorem native_add_final_output (x y : Bits) :
    (addCfgFinal x y).stk 2 =
      (if (addTurns (max x.length y.length) ⟨false, x, y, []⟩).carry
        then true :: (addTurns (max x.length y.length) ⟨false, x, y, []⟩).os
        else (addTurns (max x.length y.length) ⟨false, x, y, []⟩).os) := by
  simp only [addCfgFinal, addStacks_two]

/-- For fixed inputs, equality of both the output bits and outgoing carry of carry addition
forces the incoming carries to coincide. -/
theorem native_add_reversible (x y : Bits) (c c' : Bool) :
    (carryAddAux (max x.length y.length) c x y).1
        = (carryAddAux (max x.length y.length) c' x y).1 ∧
      (carryAddAux (max x.length y.length) c x y).2
        = (carryAddAux (max x.length y.length) c' x y).2 →
      c = c' := by
  intro h
  rcases h with ⟨h1, h2⟩
  exact carryAddAux_injective_c (max x.length y.length) x y c c' (Prod.ext h1 h2)

end Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNativeProb
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)

/-- Recursive execution of an instruction list agrees with its left fold using `probStep`. -/
theorem runSteps_eq_foldl {w L : ℕ} (c : AccessContract L) (steps : List (ProbInstr w L))
    (s : ProbState w) : runSteps c steps s = steps.foldl (probStep c) s := by
  induction steps generalizing s with
  | nil => rfl
  | cons i is ih => simp [runSteps, ih]

/-- Program execution is recursive instruction execution initialized with zero registers, the
supplied coin record, and empty output. -/
theorem runProb_eq_runSteps {w L : ℕ} (c : AccessContract L) (p : ProbProgram w L)
    (record : List Bool) :
    runProb c p record
      = runSteps c p.steps { regs := fun _ => 0, coins := record, out := [] } := by
  rw [runProb, runSteps_eq_foldl]

/-- The native forward access contract is well formed. -/
theorem nativeForwardContract_wellFormed (L : ℕ) (g : Fin L → ℕ → ℕ) :
    (nativeForwardContract L g).WellFormed := by
  intro s f
  by_cases h : f = .forward
  · subst h
    simp [nativeForwardContract]
  · simp [nativeForwardContract, h]

/-- The native forward access contract marks inverse access as unavailable at every slot. -/
theorem nativeForwardContract_inverse_not_supplied (L : ℕ) (g : Fin L → ℕ → ℕ)
    (s : Fin L) :
    (nativeForwardContract L g).supplied s .inverse = false := by
  simp [nativeForwardContract]

/-- The native forward access contract marks controlled access as unavailable at every slot. -/
theorem nativeForwardContract_controlled_not_supplied (L : ℕ) (g : Fin L → ℕ → ℕ)
    (s : Fin L) :
    (nativeForwardContract L g).supplied s .controlled = false := by
  simp [nativeForwardContract]

/-- The native forward access contract provides no implementation of inverse access. -/
theorem nativeForwardContract_inverse_not_supplied_impl (L : ℕ) (g : Fin L → ℕ → ℕ)
    (s : Fin L) :
    (nativeForwardContract L g).impl s .inverse = none := by
  simp [nativeForwardContract]

/-- The native forward access contract provides no implementation of controlled access. -/
theorem nativeForwardContract_controlled_not_supplied_impl (L : ℕ) (g : Fin L → ℕ → ℕ)
    (s : Fin L) :
    (nativeForwardContract L g).impl s .controlled = none := by
  simp [nativeForwardContract]

/-- The native forward access contract marks forward access as supplied and provides an
implementation at every slot. -/
theorem nativeForwardContract_forward_supplied (L : ℕ) (g : Fin L → ℕ → ℕ)
    (s : Fin L) :
    (nativeForwardContract L g).supplied s .forward = true ∧
      ((nativeForwardContract L g).impl s .forward).isSome = true := by
  simp [nativeForwardContract]

/-- Address zero is legal for every natural address width. -/
theorem native_legal_slot (aw : ℕ) : LegalSlot aw 0 := by
  unfold LegalSlot
  positivity

/-- The native modular exponentiation program is legal under its specified input access
contract. -/
theorem nativeModPowProgram_legal :
    ∀ (a e m : ℕ), nativeModPowProgram.LegalFor (nativeModPowContract a e m) := by
  intro a e m s hs
  have hs' : s = ProbInstr.oracle (0 : Fin 3) .forward (0 : Fin 5) (1 : Fin 5)
      ∨ s = ProbInstr.oracle (1 : Fin 3) .forward (0 : Fin 5) (2 : Fin 5)
      ∨ s = ProbInstr.oracle (2 : Fin 3) .forward (0 : Fin 5) (3 : Fin 5)
      ∨ s = ProbInstr.arith .modexp [(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)]
      ∨ s = ProbInstr.emit (4 : Fin 5) := by
    simpa [nativeModPowProgram] using! hs
  rcases hs' with rfl | rfl | rfl | rfl | rfl
  · simp [nativeModPowContract]
  · simp [nativeModPowContract]
  · simp [nativeModPowContract]
  · trivial
  · trivial

/-- The native modular exponentiation program emits the singleton output `[a ^ e % m]` on its
specified input contract. -/
theorem nativeModPowProgram_out (a e m : ℕ) :
    (runProb (nativeModPowContract a e m) nativeModPowProgram []).out = [a ^ e % m] := by
  rfl

/-- The native modular exponentiation program uses zero fair-coin instructions. -/
theorem nativeModPowProgram_coins (_a _e _m : ℕ) :
    nativeModPowProgram.coins = 0 := by
  simp [ProbProgram.coins, nativeModPowProgram]

/-- Every oracle instruction of the modular exponentiation program uses address register zero,
and every arithmetic instruction avoids that register. -/
theorem nativeModPowProgram_address_zero :
    ∀ s ∈ nativeModPowProgram.steps, match s with
      | ProbInstr.oracle _ _ addr _ => addr.val = 0
      | ProbInstr.arith _ ws => ws.all (fun i => i.val ≠ 0)
      | _ => True := by
  intro s hs
  have hs' : s = ProbInstr.oracle (0 : Fin 3) .forward (0 : Fin 5) (1 : Fin 5)
      ∨ s = ProbInstr.oracle (1 : Fin 3) .forward (0 : Fin 5) (2 : Fin 5)
      ∨ s = ProbInstr.oracle (2 : Fin 3) .forward (0 : Fin 5) (3 : Fin 5)
      ∨ s = ProbInstr.arith .modexp [(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)]
      ∨ s = ProbInstr.emit (4 : Fin 5) := by
    simpa [nativeModPowProgram] using! hs
  rcases hs' with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The native greatest-common-divisor program is legal under its specified input access
contract. -/
theorem nativeGcdProgram_legal :
    ∀ (x y : ℕ), nativeGcdProgram.LegalFor (nativeGcdContract x y) := by
  intro x y s hs
  have hs' : s = ProbInstr.oracle (0 : Fin 2) .forward (0 : Fin 4) (1 : Fin 4)
      ∨ s = ProbInstr.oracle (1 : Fin 2) .forward (0 : Fin 4) (2 : Fin 4)
      ∨ s = ProbInstr.arith .gcd [(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)]
      ∨ s = ProbInstr.emit (3 : Fin 4) := by
    simpa [nativeGcdProgram] using! hs
  rcases hs' with rfl | rfl | rfl | rfl
  · simp [nativeGcdContract]
  · simp [nativeGcdContract]
  · trivial
  · trivial

/-- The native greatest-common-divisor program emits the singleton output `[Nat.gcd x y]` on its
specified input contract. -/
theorem nativeGcdProgram_out (x y : ℕ) :
    (runProb (nativeGcdContract x y) nativeGcdProgram []).out = [Nat.gcd x y] := by
  rfl

/-- The native greatest-common-divisor program uses zero fair-coin instructions. -/
theorem nativeGcdProgram_coins (_x _y : ℕ) :
    nativeGcdProgram.coins = 0 := by
  simp [ProbProgram.coins, nativeGcdProgram]

/-- Every oracle instruction of the greatest-common-divisor program uses address register zero,
and every arithmetic instruction avoids that register. -/
theorem nativeGcdProgram_address_zero :
    ∀ s ∈ nativeGcdProgram.steps, match s with
      | ProbInstr.oracle _ _ addr _ => addr.val = 0
      | ProbInstr.arith _ ws => ws.all (fun i => i.val ≠ 0)
      | _ => True := by
  intro s hs
  have hs' : s = ProbInstr.oracle (0 : Fin 2) .forward (0 : Fin 4) (1 : Fin 4)
      ∨ s = ProbInstr.oracle (1 : Fin 2) .forward (0 : Fin 4) (2 : Fin 4)
      ∨ s = ProbInstr.arith .gcd [(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)]
      ∨ s = ProbInstr.emit (3 : Fin 4) := by
    simpa [nativeGcdProgram] using! hs
  rcases hs' with rfl | rfl | rfl | rfl <;> simp

/-- The native sampler for `m` bits uses exactly `m` fair-coin instructions. -/
theorem nativeSamplerProgram_coins (m : ℕ) :
    (nativeSamplerProgram m).coins = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hsteps : nativeSamplerSteps (m + 1)
        = ProbInstr.fairCoin (0 : Fin 1) :: ProbInstr.emit (0 : Fin 1)
          :: nativeSamplerSteps m := rfl
    simp only [nativeSamplerProgram, ProbProgram.coins] at ih ⊢
    rw [hsteps]
    simp [ih]

/-- Executing `m` sampling steps with a coin record of length `m` appends that record, encoded
as zeros and ones, to the existing output. -/
theorem nativeSampler_out_runSteps (m : ℕ) (c : AccessContract 1) (s : ProbState 1)
    (record : List Bool) (hlen : record.length = m) (hcoins : s.coins = record) :
    (runSteps c (nativeSamplerSteps m) s).out
      = s.out ++ record.map (fun b => if b then 1 else 0) := by
  induction m generalizing s record with
  | zero =>
    have hrec : record = [] := by
      cases record with
      | nil => rfl
      | cons a l => simp at hlen
    subst hrec
    simp [nativeSamplerSteps, runSteps]
  | succ m ih =>
    have hne : record ≠ [] := by
      intro h
      simp [h] at hlen
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hbs : bs.length = m := by
      simp at hlen
      omega
    have hfc : probStep c s (ProbInstr.fairCoin (0 : Fin 1))
        = ProbState.mk (regs := Function.update s.regs (0 : Fin 1) (if b then 1 else 0))
          (coins := bs) (out := s.out) := by
      simp [probStep, hcoins]
    have hem : probStep c
        (ProbState.mk (regs := Function.update s.regs (0 : Fin 1) (if b then 1 else 0))
          (coins := bs) (out := s.out))
        (ProbInstr.emit (0 : Fin 1))
        = ProbState.mk (regs := Function.update s.regs (0 : Fin 1) (if b then 1 else 0))
          (coins := bs) (out := s.out ++ [if b then 1 else 0]) := by
      simp [probStep]
    rw [nativeSamplerSteps, runSteps, runSteps, hfc, hem]
    have hrec := ih
      (ProbState.mk (regs := Function.update s.regs (0 : Fin 1) (if b then 1 else 0))
        (coins := bs) (out := s.out ++ [if b then 1 else 0])) bs hbs rfl
    rw [hrec]
    simp [List.append_assoc]

/-- The native sampler emits its length-`m` coin record encoded as zeros and ones. -/
theorem nativeSamplerProgram_out (m : ℕ) (c : AccessContract 1) (record : List Bool)
    (hlen : record.length = m) :
    (runProb c (nativeSamplerProgram m) record).out
      = record.map (fun b => if b then 1 else 0) := by
  rw [runProb_eq_runSteps, nativeSamplerProgram]
  have h := nativeSampler_out_runSteps m c
    { regs := fun _ => 0, coins := record, out := [] } record hlen rfl
  simpa using! h

/-- Running the native sampler on a coin record formed from a finite Boolean vector produces
`nativeSamplerOut` of that vector. -/
theorem nativeSamplerProgram_out_ofFn (m : ℕ) (c : AccessContract 1)
    (r : Fin m → Bool) :
    (runProb c (nativeSamplerProgram m) (List.ofFn r)).out
        = nativeSamplerOut m r := by
  have h := nativeSamplerProgram_out m c (List.ofFn r) (List.length_ofFn (f := r))
  simpa [nativeSamplerOut] using! h

/-- The native sampler's encoding of finite Boolean vectors as natural-number output lists is
injective. -/
theorem nativeSamplerOut_injective (m : ℕ) :
    Function.Injective (nativeSamplerOut m) := by
  intro r r' h
  funext i
  have hi : i.val < m := i.isLt
  have h' : (List.ofFn (fun j : Fin m => if r j then 1 else 0))[i.val]?
      = (List.ofFn (fun j : Fin m => if r' j then 1 else 0))[i.val]? := by
    simpa [nativeSamplerOut] using! congrArg (fun l : List ℕ => l[i.val]?) h
  rw [List.getElem?_ofFn, List.getElem?_ofFn] at h'
  simp only [dif_pos hi, Option.some.injEq] at h'
  have h'' : (if r i then 1 else 0) = (if r' i then 1 else 0) := by
    simpa only [show r ⟨i.val, _⟩ = r i from rfl, show r' ⟨i.val, _⟩ = r' i from rfl] using! h'
  by_cases hr : r i = true
  · by_cases hr' : r' i = true
    · simp [hr, hr']
    · have hcontra : (1 : ℕ) = 0 := by
        have h''2 : (if r i = true then 1 else 0) = (if r' i = true then 1 else 0) := h''
        rw [if_pos hr, if_neg hr'] at h''2
        exact h''2
      omega
  · by_cases hr' : r' i = true
    · have hcontra : (0 : ℕ) = 1 := by
        have h''2 : (if r i = true then 1 else 0) = (if r' i = true then 1 else 0) := h''
        rw [if_neg hr, if_pos hr'] at h''2
        exact h''2
      omega
    · simp [hr, hr']

/-- The native sampler assigns probability `1 / 2 ^ m` to every output encoding a length-`m`
Boolean vector and zero to every other output. -/
theorem nativeSamplerProgram_probLaw (m : ℕ) (c : AccessContract 1) (ω : List ℕ) :
    ProbLaw c (nativeSamplerProgram m) ω =
      if ∃ r : Fin m → Bool, nativeSamplerOut m r = ω
      then (1 : ℝ) / 2 ^ m
      else 0 := by
  have hcoins := nativeSamplerProgram_coins m
  classical
  rw [ProbLaw, hcoins]
  have hfilter :
      (Finset.univ.filter fun r : Fin m → Bool =>
        (runProb c (nativeSamplerProgram m) (List.ofFn r)).out = ω)
        = Finset.filter (fun r : Fin m → Bool => nativeSamplerOut m r = ω) Finset.univ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [nativeSamplerProgram_out_ofFn]
  rw [hfilter]
  by_cases hex : ∃ r : Fin m → Bool, nativeSamplerOut m r = ω
  · rw [if_pos hex]
    let r₀ : Fin m → Bool := Classical.choose hex
    have hr₀ : nativeSamplerOut m r₀ = ω := Classical.choose_spec hex
    have hcard : (Finset.filter (fun r : Fin m → Bool => nativeSamplerOut m r = ω)
        Finset.univ).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨r₀, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hx
        exact nativeSamplerOut_injective m (hx.trans hr₀.symm)
      · intro hx
        subst hx
        simp [hr₀]
    rw [hcard]
    simp [one_div]
  · rw [if_neg hex]
    have hcard : (Finset.filter (fun r : Fin m → Bool => nativeSamplerOut m r = ω)
        Finset.univ).card = 0 := by
      rw [Finset.card_eq_zero]
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact (hex ⟨x, hx⟩).elim
      · intro hx
        simp at hx
    rw [hcard]
    simp

/-- The arithmetic addition instruction preserves its first input and replaces its second entry
with the sum. -/
theorem arithSem_add (a b : ℕ) : arithSem .add [a, b] = [a, a + b] := rfl

/-- The arithmetic multiplication instruction preserves its first input and replaces its second
entry with the product. -/
theorem arithSem_mul (a b : ℕ) : arithSem .mul [a, b] = [a, a * b] := rfl

/-- On two inputs and a zero output entry, the greatest-common-divisor instruction preserves
both inputs and writes their greatest common divisor. -/
theorem arithSem_gcd (a b : ℕ) : arithSem .gcd [a, b, 0] = [a, b, Nat.gcd a b] := rfl

/-- On base, exponent, modulus, and a zero output entry, the modular exponentiation instruction
preserves its inputs and writes the modular power. -/
theorem arithSem_modexp (a e m : ℕ) :
    arithSem .modexp [a, e, m, 0] = [a, e, m, a ^ e % m] := rfl

/-- The decoded binary addition of encoded natural inputs equals the addition instruction's
output entry. -/
theorem native_kernel_add_agrees (a b : ℕ) :
    binaryValue (bitAdd (natToBits a) (natToBits b))
      = (arithSem .add [a, b]).getD 1 0 := by
  rw [bitAdd_value, natToBits_value, natToBits_value]
  rfl

/-- The decoded binary multiplication of encoded natural inputs equals the multiplication
instruction's output entry. -/
theorem native_kernel_mul_agrees (a b : ℕ) :
    binaryValue (bitMul (natToBits a) (natToBits b))
      = (arithSem .mul [a, b]).getD 1 0 := by
  rw [bitMul_value, natToBits_value, natToBits_value]
  rfl

/-- The decoded bit-list greatest common divisor of encoded inputs equals the
greatest-common-divisor instruction's output entry. -/
theorem native_kernel_gcd_agrees (x y : ℕ) :
    binaryValue (bitGcd (natToBits x) (natToBits y))
      = (arithSem .gcd [x, y, 0]).getD 2 0 := by
  rw [bitGcd_value, natToBits_value, natToBits_value]
  rfl

/-- The decoded modular bit-list power of encoded inputs equals the modular exponentiation
instruction's output entry. -/
theorem native_kernel_modexp_agrees (a e m : ℕ) :
    binaryValue (bitModPow (natToBits a) (natToBits e) (natToBits m))
      = (arithSem .modexp [a, e, m, 0]).getD 3 0 := by
  rw [bitModPow_value, natToBits_value, natToBits_value, natToBits_value]
  rfl

/-- The native modular exponentiation program emits the decoded output of the corresponding
bit-list operation on encoded inputs. -/
theorem native_modpow_program_matches_kernel (a e m : ℕ) :
    (runProb (nativeModPowContract a e m) nativeModPowProgram []).out
      = [binaryValue (bitModPow (natToBits a) (natToBits e) (natToBits m))] := by
  rw [nativeModPowProgram_out]
  rw [native_kernel_modexp_agrees]
  rfl

/-- The native greatest-common-divisor program emits the decoded output of the corresponding
bit-list operation on encoded inputs. -/
theorem native_gcd_program_matches_kernel (x y : ℕ) :
    (runProb (nativeGcdContract x y) nativeGcdProgram []).out
      = [binaryValue (bitGcd (natToBits x) (natToBits y))] := by
  rw [nativeGcdProgram_out]
  rw [native_kernel_gcd_agrees]
  rfl

/-- Legal probabilistic programs preserve the access restrictions of a well-formed access
contract. -/
theorem native_access_restriction_preserved : AccessRestrictionPreserved := by
  intro w L p c hc hl s hs
  cases s with
  | fairCoin dst => trivial
  | oracle slot form addr val =>
    exact ⟨hl (ProbInstr.oracle slot form addr val) hs,
      by rw [hc slot form, hl (ProbInstr.oracle slot form addr val) hs]⟩
  | arith code ws => trivial
  | emit src => trivial

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNativeProb

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs (FairCoinLaw)
open Qatlib.Foundations.IntervalArith.IntervalOps (unit roundDown)
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNativeProb
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
open Turing

/-- Collects binary addition correctness and its length bound, binary multiplication correctness
and its numeric bound, and the bounded native addition run. -/
theorem clause1_complete :
    (∀ (x y : Bits), binaryValue (bitAdd x y) = binaryValue x + binaryValue y) ∧
    (∀ (x y : Bits), (bitAdd x y).length ≤ max x.length y.length + 1) ∧
    (∀ (x y : Bits), binaryValue (bitMul x y) = binaryValue x * binaryValue y) ∧
    (∀ (x y : Bits), binaryValue (bitMul x y) < 2 ^ (x.length + y.length)) ∧
    (∀ (x y : Bits), NativeAddRun x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y; exact bitAdd_value x y
  · intro x y; exact carryAdd_length false x y
  · intro x y; exact bitMul_value x y
  · intro x y; exact bitMul_value_lt x y
  · intro x y; exact native_add_run x y

/-- Collects the public precision formula, parameter encoding-size and dyadic error bounds,
total word error budget, and bounds on error contributions by kind. -/
theorem clause2_complete :
    (∀ w : NativeWord,
        precisionChoice w.publicParams = w.publicParams.errUnits + w.publicParams.epsBits + 2) ∧
    (∀ (p : NativeParam) (k : ℕ),
        (p.name.eval k).size ≤ p.name.descBits + 2 * k + 4) ∧
    (∀ w : NativeWord,
        w.publicParams.errUnits * 2 ^ w.publicParams.epsBits
          ≤ 2 ^ (precisionChoice w.publicParams)) ∧
    (∀ (N : NativeName) (k : ℕ), (N.errAt k : ℚ) ≤ 1 / (2 : ℚ) ^ k) ∧
    (∀ (w : NativeWord) (k : ℕ),
        nativeWordErrorActual w k ≤ nativeWordError w k) ∧
    (∀ w : NativeWord,
        nativeWordErrorActual w (precisionChoice w.publicParams)
          ≤ 1 / (2 : ℚ) ^ w.publicParams.epsBits) ∧
    (∀ (w : NativeWord) (k : ℕ) (kd : NativeParamKind),
        nativeKindErrorActual w k kd ≤ nativeWordErrorActual w k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w; exact precisionChoice_public w
  · intro p k; exact native_param_encoding p k
  · intro w; exact nativeWordErrorUnits_bound w
  · intro N k; exact nativeName_err_le N k
  · intro w k; exact nativeWordErrorActual_le_error w k
  · intro w; exact nativeWordErrorActual_budget w
  · intro w k kd; exact nativeKindErrorActual_le w k kd

/-- Collects addition stack access, fair and uniform sampling laws, address legality, recovery
of the incoming carry, and correctness of greatest common divisor and modular arithmetic on
bit lists. -/
theorem clause3_complete :
    (∀ (x y : Bits) (k : ℕ), k ≤ max x.length y.length →
        (addCfgAt k x y).stk 0 = x.drop k ∧
        (addCfgAt k x y).stk 1 = y.drop k ∧
        (addCfgAt k x y).stk 2 = (addTurns k ⟨false, x, y, []⟩).os) ∧
    (∃ p : Bool → ℝ, FairCoinLaw p) ∧
    (∀ m : ℕ, ∃ p : (Fin m → Bool) → ℝ, NativeSamplerLaw m p) ∧
    (∀ (m : ℕ) (w : Fin m → Bool), LegalSlot m (binaryValue (List.ofFn w))) ∧
    (∀ (x y : Bits) (c c' : Bool),
        (carryAddAux (max x.length y.length) c x y).1
            = (carryAddAux (max x.length y.length) c' x y).1 ∧
          (carryAddAux (max x.length y.length) c x y).2
            = (carryAddAux (max x.length y.length) c' x y).2 → c = c') ∧
    (∀ (x y : Bits), binaryValue (bitGcd x y) = Nat.gcd (binaryValue x) (binaryValue y)) ∧
    (∀ (x y m : Bits),
        binaryValue (bitModMul x y m) = (binaryValue x * binaryValue y) % binaryValue m) ∧
    (∀ (x e m : Bits),
        binaryValue (bitModPow x e m) = (binaryValue x) ^ (binaryValue e) % binaryValue m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y k hk; exact native_add_access x y k hk
  · exact native_fair_coin
  · intro m; exact native_sampler_law m
  · intro m w; exact native_slot_legal m w
  · intro x y c c' h; exact native_add_reversible x y c c' h
  · intro x y; exact bitGcd_value x y
  · intro x y m; exact bitModMul_value x y m
  · intro x e m; exact bitModPow_value x e m

/-- Collects access restrictions, legal modular exponentiation and greatest-common-divisor
program outputs, the sampler probability law, agreement of modular exponentiation with its
bit-list operation, and preservation of access restrictions. -/
theorem clause3_program_complete :
    (∀ (L : ℕ) (g : Fin L → ℕ → ℕ) (s : Fin L),
        (nativeForwardContract L g).supplied s .inverse = false ∧
        (nativeForwardContract L g).supplied s .controlled = false) ∧
    (∀ (a e m : ℕ),
        nativeModPowProgram.LegalFor (nativeModPowContract a e m) ∧
        (runProb (nativeModPowContract a e m) nativeModPowProgram []).out = [a ^ e % m]) ∧
    (∀ (x y : ℕ),
        nativeGcdProgram.LegalFor (nativeGcdContract x y) ∧
        (runProb (nativeGcdContract x y) nativeGcdProgram []).out = [Nat.gcd x y]) ∧
    (∀ (m : ℕ) (c : AccessContract 1) (ω : List ℕ),
        ProbLaw c (nativeSamplerProgram m) ω =
          if ∃ r : Fin m → Bool, nativeSamplerOut m r = ω
          then (1 : ℝ) / 2 ^ m
          else 0) ∧
    (∀ (a e m : ℕ),
        binaryValue (bitModPow (natToBits a) (natToBits e) (natToBits m))
          = (arithSem .modexp [a, e, m, 0]).getD 3 0) ∧
    AccessRestrictionPreserved := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L g s
    exact ⟨nativeForwardContract_inverse_not_supplied L g s,
      nativeForwardContract_controlled_not_supplied L g s⟩
  · intro a e m
    exact ⟨nativeModPowProgram_legal a e m, nativeModPowProgram_out a e m⟩
  · intro x y
    exact ⟨nativeGcdProgram_legal x y, nativeGcdProgram_out x y⟩
  · intro m c ω
    exact nativeSamplerProgram_probLaw m c ω
  · intro a e m
    exact native_kernel_modexp_agrees a e m
  · exact native_access_restriction_preserved

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
