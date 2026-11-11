/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionEffectiveDefs

/-!
# Certified finite-precision arithmetic and error bounds

This module proves the step semantics and numerical correctness of the six-stack multiplication
program `mulProgram`, culminating in `mulProgram_sweep` and `mulProgram_value`. It also
certifies rational interval division and square-root evaluation through `nativeDiv_certified`
and `nativeSqrt_certified`; [KitaevShenVyalyi2002] provides general background on effective
arithmetic in classical and quantum computation.

The predicate `NameCode.Faithful` records a rational approximation guarantee, while
`CompleteWord` ensures that pairing slots with amplification factors retains every slot. The
theorem `completeWord_telescope` bounds the error of products of bounded parameters, and
explicit phase-estimation and linear-combination-of-unitaries examples illustrate grid
separation and error accounting.

## Main statements

* `mulProgram_round`: execution of one multiplication round with its specified step count.
* `mulProgram_value`: the final accumulator represents the product of the input values.
* `nativeDiv_certified` and `nativeSqrt_certified`: interval enclosures with explicit width
  bounds.
* `completeWord_telescope`: a product error bound under boundedness and amplification
  assumptions.
* `nativeWord_account_undercounts`: a concrete error undercount caused by an unmatched slot.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false


open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open Qatlib.Foundations.IntervalArith.IntervalOps (Interval rounded divPositive)
open Turing

/-- One outer step finishes when the multiplier stack is empty; otherwise it shifts the
accumulator and consumes a multiplier bit, entering duplication exactly when that bit is
true. -/
theorem mulProgram_outer_step (v : MulVar) (u b a m y t : Bits) :
    TM2.stepAux (mulProgram .outer) v (mulStacks u b a m y t)
      = if y = [] then
          ⟨some .done, MulVar.init, mulStacks u b a m y t⟩
        else if y.head? = some true then
          ⟨some .dup, MulVar.init, mulStacks (false :: u) b a m y.tail t⟩
        else
          ⟨some .outer, MulVar.init, mulStacks (false :: u) b a m y.tail t⟩ := by
  cases y with
  | nil => simp [mulProgram, TM2.stepAux, mulStacks, MulVar.readBit]
  | cons c l =>
      cases c <;>
        simp [mulProgram, TM2.stepAux, mulStacks, MulVar.readBit,
          mulStacks_update_four_zero]

/-- One duplication step moves the head of the master stack onto both copy stacks, or enters
restoration with reset registers when the master stack is empty. -/
theorem mulProgram_dup_step (v : MulVar) (u b a m y t : Bits) :
    TM2.stepAux (mulProgram .dup) v (mulStacks u b a m y t)
      = match m with
        | [] => ⟨some .restore, MulVar.init, mulStacks u b a [] y t⟩
        | c :: m' =>
            ⟨some .dup, MulVar.readMbit v (some c),
              mulStacks u (c :: b) a m' y (c :: t)⟩ := by
  cases m with
  | nil => simp [mulProgram, TM2.stepAux, mulStacks, MulVar.readMbit]
  | cons c l =>
      simp [mulProgram, TM2.stepAux, mulStacks, MulVar.readMbit,
        mulStacks_update_three_one_five]

/-- One restoration step moves the head of the temporary stack back onto the master stack, or
enters addition with reset registers when the temporary stack is empty. -/
theorem mulProgram_restore_step (v : MulVar) (u b a m y t : Bits) :
    TM2.stepAux (mulProgram .restore) v (mulStacks u b a m y t)
      = match t with
        | [] => ⟨some .add, MulVar.init, mulStacks u b a m y t⟩
        | c :: t' =>
            ⟨some .restore, MulVar.readMbit v (some c),
              mulStacks u b a (c :: m) y t'⟩ := by
  cases t with
  | nil => simp [mulProgram, TM2.stepAux, mulStacks, MulVar.readMbit]
  | cons c l =>
      simp [mulProgram, TM2.stepAux, mulStacks, MulVar.readMbit,
        mulStacks_update_five_three]

/-- One addition step consumes the available operand heads, writes their sum bit, and updates
the carry. When both operands are empty, it writes the final carry and enters the flip
phase. -/
theorem mulProgram_add_step (v : MulVar) (u b a m y t : Bits) :
    TM2.stepAux (mulProgram .add) v (mulStacks u b a m y t)
      = if u = [] ∧ b = [] then
          ⟨some .flip, MulVar.addEnd v, mulStacks [] [] (v.carry :: a) m y t⟩
        else
          ⟨some .add,
            MulVar.addPosition v none none
              (carryStep v.carry (u.head?.getD false) (b.head?.getD false)).2,
            mulStacks u.tail b.tail
              ((carryStep v.carry (u.head?.getD false) (b.head?.getD false)).1 :: a)
              m y t⟩ := by
  cases u with
  | nil =>
      cases b with
      | nil =>
          simp [mulProgram, TM2.stepAux, mulStacks, MulVar.addEnd,
            mulStacks_update_two]
      | cons c l =>
          simp [mulProgram, TM2.stepAux, mulStacks, MulVar.addPosition,
            mulAddBit, mulAddCarry, mulStacks_update_zero_one_two]
  | cons c l =>
      simp [mulProgram, TM2.stepAux, mulStacks, MulVar.addPosition,
        mulAddBit, mulAddCarry, mulStacks_update_zero_one_two]

/-- One flip step transfers the head of the addition output onto the accumulator, or returns to
the outer phase with reset registers when the addition output is empty. -/
theorem mulProgram_flip_step (v : MulVar) (u b a m y t : Bits) :
    TM2.stepAux (mulProgram .flip) v (mulStacks u b a m y t)
      = match a with
        | [] => ⟨some .outer, MulVar.init, mulStacks u b [] m y t⟩
        | c :: a' =>
            ⟨some .flip, MulVar.readAbit v (some c),
              mulStacks (c :: u) b a' m y t⟩ := by
  cases a with
  | nil => simp [mulProgram, TM2.stepAux, mulStacks]
  | cons c l =>
      simp [mulProgram, TM2.stepAux, mulStacks, MulVar.readAbit,
        mulStacks_update_two_zero]

/-- The duplication phase takes `m.length + 1` steps to empty the master stack, prepend its
reverse to both copy stacks, and enter restoration with reset registers. -/
theorem mulProgram_dup_run (v : MulVar) (u b a m y t : Bits) :
    stackRun mulProgram (m.length + 1) ⟨some .dup, v, mulStacks u b a m y t⟩
      = some ⟨some .restore, MulVar.init,
          mulStacks u (m.reverse ++ b) a [] y (m.reverse ++ t)⟩ := by
  induction m generalizing v b t with
  | nil =>
      have hstep : TM2.step mulProgram ⟨some .dup, v, mulStacks u b a [] y t⟩
          = some ⟨some .restore, MulVar.init, mulStacks u b a [] y t⟩ := by
        rw [TM2.step, mulProgram_dup_step]
      rw [stackRun, hstep, Option.bind_some]
      rfl
  | cons c m ih =>
      have hstep : TM2.step mulProgram ⟨some .dup, v, mulStacks u b a (c :: m) y t⟩
          = some ⟨some .dup, MulVar.readMbit v (some c),
              mulStacks u (c :: b) a m y (c :: t)⟩ := by
        rw [TM2.step, mulProgram_dup_step]
      rw [stackRun, hstep, Option.bind_some]
      rw [show (c :: m).length = m.length + 1 by rfl]
      rw [ih (MulVar.readMbit v (some c)) (c :: b) (c :: t)]
      congr 1
      simp [List.reverse_cons, List.append_assoc]

/-- The restoration phase takes `t.length + 1` steps to prepend the reverse of the temporary
stack to the master stack and enter addition with an empty temporary stack. -/
theorem mulProgram_restore_run (v : MulVar) (u b a m y t : Bits) :
    stackRun mulProgram (t.length + 1) ⟨some .restore, v, mulStacks u b a m y t⟩
      = some ⟨some .add, MulVar.init,
          mulStacks u b a (t.reverse ++ m) y []⟩ := by
  induction t generalizing v m with
  | nil =>
      have hstep : TM2.step mulProgram ⟨some .restore, v, mulStacks u b a m y []⟩
          = some ⟨some .add, MulVar.init, mulStacks u b a m y []⟩ := by
        rw [TM2.step, mulProgram_restore_step]
      rw [stackRun, hstep, Option.bind_some]
      rfl
  | cons c t ih =>
      have hstep : TM2.step mulProgram ⟨some .restore, v, mulStacks u b a m y (c :: t)⟩
          = some ⟨some .restore, MulVar.readMbit v (some c),
              mulStacks u b a (c :: m) y t⟩ := by
        rw [TM2.step, mulProgram_restore_step]
      rw [stackRun, hstep, Option.bind_some]
      rw [show (c :: t).length = t.length + 1 by rfl]
      rw [ih (MulVar.readMbit v (some c)) (c :: m)]
      congr 1
      simp [List.reverse_cons, List.append_assoc]

/-- The flip phase takes `a.length + 1` steps to prepend the reversed addition output to the
accumulator and return to the outer phase with reset registers. -/
theorem mulProgram_flip_run (v : MulVar) (u b a m y t : Bits) :
    stackRun mulProgram (a.length + 1) ⟨some .flip, v, mulStacks u b a m y t⟩
      = some ⟨some .outer, MulVar.init,
          mulStacks (a.reverse ++ u) b [] m y t⟩ := by
  induction a generalizing v u with
  | nil =>
      have hstep : TM2.step mulProgram ⟨some .flip, v, mulStacks u b [] m y t⟩
          = some ⟨some .outer, MulVar.init, mulStacks u b [] m y t⟩ := by
        rw [TM2.step, mulProgram_flip_step]
      rw [stackRun, hstep, Option.bind_some]
      rfl
  | cons c a ih =>
      have hstep : TM2.step mulProgram ⟨some .flip, v, mulStacks u b (c :: a) m y t⟩
          = some ⟨some .flip, MulVar.readAbit v (some c),
              mulStacks (c :: u) b a m y t⟩ := by
        rw [TM2.step, mulProgram_flip_step]
      rw [stackRun, hstep, Option.bind_some]
      rw [show (c :: a).length = a.length + 1 by rfl]
      rw [ih (MulVar.readAbit v (some c)) (c :: u)]
      congr 1
      simp [List.reverse_cons, List.append_assoc]

/-- For `k ≤ max u.length b.length`, one machine step advances the indexed addition
configuration from `k` to `k + 1`. -/
theorem mulProgram_add_step_at (u b a0 m y t : Bits) (k : ℕ)
    (hk : k ≤ max u.length b.length) :
    TM2.step mulProgram (mulAddCfgAt MulVar.init k u b a0 m y t)
      = some (mulAddCfgAt MulVar.init (k+1) u b a0 m y t) := by
  have hcfg0 : mulAddCfgAt MulVar.init k u b a0 m y t
      = mulAddCfg MulVar.init k u b a0 m y t := by
    rw [mulAddCfgAt, if_pos hk]
  rw [hcfg0]
  unfold mulAddCfg
  rw [TM2.step]
  have hstep := mulProgram_add_step
    (MulVar.addPosition MulVar.init none none (addTurns k ⟨false, u, b, []⟩).carry)
    (u.drop k) (b.drop k) ((addTurns k ⟨false, u, b, []⟩).os ++ a0) m y t
  rw [hstep]
  by_cases hempty : u.drop k = [] ∧ b.drop k = []
  · have hx := hempty.1
    have hy := hempty.2
    rw [if_pos hempty]
    have hkx : u.length ≤ k := by
      have hz : (u.drop k).length = 0 := by rw [hx]; rfl
      rw [List.length_drop] at hz
      omega
    have hky : b.length ≤ k := by
      have hz : (b.drop k).length = 0 := by rw [hy]; rfl
      rw [List.length_drop] at hz
      omega
    have hkmax : k = max u.length b.length := by omega
    have hcfg1 : mulAddCfgAt MulVar.init (k+1) u b a0 m y t
        = mulAddFinal MulVar.init u b a0 m y t := by
      rw [mulAddCfgAt, if_neg (by omega)]
    rw [hcfg1, hkmax]
    simp [MulVar.addEnd, MulVar.addPosition, mulAddFinal]
  · rw [if_neg hempty]
    have hk1 : k + 1 ≤ max u.length b.length := by
      by_cases h1 : k + 1 ≤ max u.length b.length
      · exact h1
      · exfalso
        have hmax : max u.length b.length ≤ k := by omega
        have hu'' : u.length ≤ k := by omega
        have hb' : ¬ (b.length ≤ k) := by
          intro hb''
          apply hempty
          exact ⟨(drop_eq_nil_iff u k).mpr hu'', (drop_eq_nil_iff b k).mpr hb''⟩
        have hb'' : b.length ≤ k := by omega
        exact hb' hb''
    have hcfg1 : mulAddCfgAt MulVar.init (k+1) u b a0 m y t
        = mulAddCfg MulVar.init (k+1) u b a0 m y t := by
      rw [mulAddCfgAt, if_pos hk1]
    rw [hcfg1]
    unfold mulAddCfg
    rw [addTurns_step]
    simp only [addTurn_carry, addTurn_os, drop_succ_tail]
    simp [MulVar.addPosition, List.append_assoc]

/-- Running `s` steps advances the indexed addition configuration from `k` to `k + s`, provided
the latter index is at most `max u.length b.length + 1`. -/
theorem mulProgram_add_advance (u b a0 m y t : Bits) (k s : ℕ)
    (hk : k + s ≤ max u.length b.length + 1) :
    stackRun mulProgram s (mulAddCfgAt MulVar.init k u b a0 m y t)
      = some (mulAddCfgAt MulVar.init (k+s) u b a0 m y t) := by
  induction s generalizing k with
  | zero =>
      have hcfg : mulAddCfgAt MulVar.init k u b a0 m y t
          = mulAddCfgAt MulVar.init (k+0) u b a0 m y t := by
        simp [Nat.add_zero]
      rw [hcfg]
      simp [stackRun]
  | succ s ih =>
      have hk1 : k ≤ max u.length b.length := by omega
      have hstep : TM2.step mulProgram (mulAddCfgAt MulVar.init k u b a0 m y t)
          = some (mulAddCfgAt MulVar.init (k+1) u b a0 m y t) :=
        mulProgram_add_step_at u b a0 m y t k hk1
      rw [stackRun, hstep, Option.bind_some]
      have hrest := ih (k+1) (by omega)
      rw [hrest]
      have heq : (k+1) + s = k + (s+1) := by omega
      rw [heq]

/-- The addition phase reaches `mulAddFinal` after `max u.length b.length + 1` steps from the
initial addition configuration. -/
theorem mulProgram_add_run (u b a0 m y t : Bits) :
    stackRun mulProgram (max u.length b.length + 1)
      (mulAddCfg MulVar.init 0 u b a0 m y t)
      = some (mulAddFinal MulVar.init u b a0 m y t) := by
  have h0 : mulAddCfg MulVar.init 0 u b a0 m y t
      = mulAddCfgAt MulVar.init 0 u b a0 m y t := by
    rw [mulAddCfgAt, if_pos (by simp)]
  rw [h0]
  have h := mulProgram_add_advance u b a0 m y t 0 (max u.length b.length + 1) (by simp)
  rw [h]
  congr 1
  rw [mulAddCfgAt, if_neg (by simp)]

/-- The optional head after dropping `n` elements from a Boolean list equals its optional
element at index `n`. -/
theorem drop_head?_eq_getElem? (l : List Bool) (n : ℕ) :
    (l.drop n).head? = l[n]? := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
      cases n with
      | zero => simp
      | succ n => simp [ih]

/-- For an index `j` within a Boolean list, taking `j + 1` elements appends the element at `j`
to the first `j` elements. -/
theorem take_succ_getElem (l : List Bool) (j : ℕ) (hj : j < l.length) :
    l.take (j+1) = l.take j ++ [l[j]] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [List.take_succ_cons]
          have hj' : j < l.length := by simp at hj; omega
          have h := ih j hj'
          simp only [List.getElem_cons_succ]
          rw [h]
          simp [List.cons_append]

/-- With initially empty addition output, reversing stack 2 of `mulAddFinal` yields `mulAddBits
u b`. -/
theorem mulAddFinal_sum (u b m y t : Bits) :
    ((mulAddFinal MulVar.init u b [] m y t).stk 2).reverse = mulAddBits u b := by
  rw [mulAddFinal]
  simp [mulAddBits, carryAddAux, List.reverse_append, List.append_nil]

/-- For `j < y.length`, one multiplication round takes `mulRoundTicks x y j` steps and advances
`mulCfg x y j` to `mulCfg x y (j + 1)`. -/
theorem mulProgram_round (x y : Bits) (j : ℕ) (hj : j < y.length) :
    stackRun mulProgram (mulRoundTicks x y j) (mulCfg x y j)
      = some (mulCfg x y (j+1)) := by
  have hdrop : ((y.reverse).drop j).tail = (y.reverse).drop (j+1) :=
    (drop_succ_tail (y.reverse) j).symm
  have hj' : j < (y.reverse).length := by simp [hj]
  by_cases hb : mulBit y j
  · have hbit : ((y.reverse).drop j).head? = some true := by
      have h := hb
      simp only [mulBit] at h
      have hd : ((y.reverse).drop j).head? = (y.reverse)[j]? := drop_head?_eq_getElem? _ _
      cases he : (y.reverse)[j]? with
      | none => simp [he] at h
      | some c =>
          cases c with
          | false => simp [he] at h
          | true => rw [hd, he]
    have h1 : stackRun mulProgram 1 (mulCfg x y j)
        = some ⟨some .dup, MulVar.init,
            mulStacks (false :: mulAcc x y j) [] [] (x.reverse) ((y.reverse).drop (j+1)) []⟩ := by
      rw [stackRun, mulCfg, TM2.step, mulProgram_outer_step]
      simp [stackRun, hbit, hdrop, hj, hj', mulStacks_update_four_zero]
    have h2 : stackRun mulProgram (x.length + 1)
        ⟨some .dup, MulVar.init,
          mulStacks (false :: mulAcc x y j) [] [] (x.reverse) ((y.reverse).drop (j+1)) []⟩
        = some ⟨some .restore, MulVar.init,
            mulStacks (false :: mulAcc x y j) x [] [] ((y.reverse).drop (j+1)) x⟩ := by
      have hh := mulProgram_dup_run (v := MulVar.init) (u := false :: mulAcc x y j)
        (b := []) (a := []) (m := x.reverse) (y := (y.reverse).drop (j+1)) (t := [])
      simpa [List.length_reverse] using! hh
    have h3 : stackRun mulProgram (x.length + 1)
        ⟨some .restore, MulVar.init,
          mulStacks (false :: mulAcc x y j) x [] [] ((y.reverse).drop (j+1)) x⟩
        = some ⟨some .add, MulVar.init,
            mulStacks (false :: mulAcc x y j) x [] (x.reverse) ((y.reverse).drop (j+1)) []⟩ := by
      have hh := mulProgram_restore_run (v := MulVar.init) (u := false :: mulAcc x y j)
        (b := x) (a := []) (m := []) (y := (y.reverse).drop (j+1)) (t := x)
      simpa [List.length_reverse] using! hh
    have h4 : stackRun mulProgram (max (false :: mulAcc x y j).length x.length + 1)
        ⟨some .add, MulVar.init,
          mulStacks (false :: mulAcc x y j) x [] (x.reverse) ((y.reverse).drop (j+1)) []⟩
        = some (mulAddFinal MulVar.init (false :: mulAcc x y j) x []
            (x.reverse) ((y.reverse).drop (j+1)) []) := by
      have hh := mulProgram_add_run (false :: mulAcc x y j) x [] (x.reverse)
        ((y.reverse).drop (j+1)) []
      simpa only [mulAddCfg, MulVar.addPosition, MulVar.init] using! hh
    have h5 : stackRun mulProgram ((mulRoundResult x y j).length + 1)
        (mulAddFinal MulVar.init (false :: mulAcc x y j) x []
          (x.reverse) ((y.reverse).drop (j+1)) [])
        = some ⟨some .outer, MulVar.init,
            mulStacks (mulRoundResult x y j).reverse [] []
              (x.reverse) ((y.reverse).drop (j+1)) []⟩ := by
      have hh := mulProgram_flip_run (v := (mulAddFinal MulVar.init (false :: mulAcc x y j) x []
          (x.reverse) ((y.reverse).drop (j+1)) []).var)
        (u := []) (b := [])
        (a := (mulAddFinal MulVar.init (false :: mulAcc x y j) x []
          (x.reverse) ((y.reverse).drop (j+1)) []).stk 2)
        (m := x.reverse) (y := (y.reverse).drop (j+1)) (t := [])
      simpa only [mulRoundResult, mulAddFinal, mulStacks_zero, mulStacks_one,
        mulStacks_two, List.append_nil] using! hh
    have htot : mulRoundTicks x y j
        = 1 + ((x.length + 1)
          + ((x.length + 1)
            + ((max (false :: mulAcc x y j).length x.length + 1)
              + ((mulRoundResult x y j).length + 1)))) := by
      simp [mulRoundTicks, hb]
    rw [htot, run_add, h1, Option.bind_some]
    rw [run_add, h2, Option.bind_some]
    rw [run_add, h3, Option.bind_some]
    rw [run_add, h4, Option.bind_some]
    rw [h5]
    congr 1
    rw [mulRoundResult, mulAddFinal_sum]
    simp [mulCfg, mulStacks_zero, mulStacks_one, mulStacks_two, mulStacks_three,
      mulStacks_four, mulStacks_five, mulAcc, hb]
  · have hbit : ((y.reverse).drop j).head? = none ∨ ((y.reverse).drop j).head? = some false := by
      have h := hb
      simp only [mulBit] at h
      have hd : ((y.reverse).drop j).head? = (y.reverse)[j]? := drop_head?_eq_getElem? _ _
      cases he : (y.reverse)[j]? with
      | none => rw [hd, he]; exact Or.inl rfl
      | some c =>
          cases c with
          | false => rw [hd, he]; exact Or.inr rfl
          | true => simp [he] at h
    have h1 : stackRun mulProgram 1 (mulCfg x y j)
        = some ⟨some .outer, MulVar.init,
            mulStacks (false :: mulAcc x y j) [] [] (x.reverse) ((y.reverse).drop (j+1)) []⟩ := by
      rw [stackRun, mulCfg, TM2.step, mulProgram_outer_step]
      rcases hbit with hbit | hbit
      · simp [stackRun, hbit, hdrop, hj, hj', mulStacks_update_four_zero]
      · simp [stackRun, hbit, hdrop, hj, hj', mulStacks_update_four_zero]
    have htot : mulRoundTicks x y j = 1 := by
      simp [mulRoundTicks, hb]
    rw [htot, h1]
    congr 1
    simp [mulCfg, mulStacks_zero, mulStacks_one, mulStacks_two, mulStacks_three,
      mulStacks_four, mulStacks_five, mulAcc, hb]

/-- The binary value of `mulAddBits u b` is the sum of the binary values of `u` and `b`. -/
theorem mulAddBits_value (u b : Bits) :
    binaryValue (mulAddBits u b) = binaryValue u + binaryValue b := by
  have h := carryAddAux_value (max u.length b.length) false u b
  have hres : (carryAddAux (max u.length b.length) false u b).1.length
      = max u.length b.length := by
    simp [carryAddAux, addTurns_os_length]
  have hu : u.take (max u.length b.length) = u := take_eq_self u (le_max_left _ _)
  have hb : b.take (max u.length b.length) = b := take_eq_self b (le_max_right _ _)
  rw [hu, hb] at h
  rw [mulAddBits]
  simp only [binaryValue_append, binaryValue_singleton, List.length_append]
  rw [hres]
  simpa [bitNat] using! h

/-- Extending the processed multiplier prefix doubles its value and adds the next multiplier
bit. -/
theorem mulPrefix_step (y : Bits) (j : ℕ) (hj : j < y.length) :
    mulPrefix y (j+1) = 2 * mulPrefix y j + bitNat (mulBit y j) := by
  have hlen : j < (y.reverse).length := by simp [hj]
  have hbit : mulBit y j = (y.reverse)[j] := by
    rw [mulBit, List.getElem?_eq_getElem hlen]
    simp
  have htake : (y.reverse).take (j+1) = (y.reverse).take j ++ [mulBit y j] := by
    rw [take_succ_getElem (y.reverse) j hlen, hbit]
  have hrev : ((y.reverse).take (j+1)).reverse
      = mulBit y j :: ((y.reverse).take j).reverse := by
    rw [htake, List.reverse_append]
    rfl
  rw [mulPrefix, mulPrefix, hrev]
  simp [binaryValue_cons']

/-- After `j ≤ y.length` rounds, the accumulator value is the processed multiplier prefix times
the binary value of `x`. -/
theorem mulAcc_value (x y : Bits) (j : ℕ) (hj : j ≤ y.length) :
    binaryValue (mulAcc x y j) = mulPrefix y j * binaryValue x := by
  induction j with
  | zero => simp [mulAcc, mulPrefix]
  | succ j ih =>
      have hj' : j < y.length := by omega
      rw [mulAcc]
      by_cases hb : mulBit y j
      · rw [if_pos hb, mulAddBits_value, binaryValue_cons']
        rw [ih (by omega), mulPrefix_step y j hj']
        simp [bitNat, hb]
        ring
      · rw [if_neg hb, binaryValue_cons']
        rw [ih (by omega), mulPrefix_step y j hj']
        simp [bitNat, hb]
        ring

/-- After all multiplier bits have been processed, the accumulator represents the product of the
binary values of `x` and `y`. -/
theorem mulAcc_value_full (x y : Bits) :
    binaryValue (mulAcc x y y.length) = binaryValue x * binaryValue y := by
  have hprefix : mulPrefix y y.length = binaryValue y := by
    rw [mulPrefix, show y.length = (y.reverse).length by simp, List.take_length,
      List.reverse_reverse]
  rw [mulAcc_value x y y.length (le_refl _), hprefix]
  ring

/-- For `n ≤ y.length`, running the total tick count for `n` rounds advances the initial round
configuration to `mulCfg x y n`. -/
theorem mulProgram_rounds (x y : Bits) (n : ℕ) (hn : n ≤ y.length) :
    stackRun mulProgram (mulTotalTicks x y n) (mulCfg x y 0)
      = some (mulCfg x y n) := by
  induction n with
  | zero =>
      simp [mulTotalTicks, stackRun]
  | succ n ih =>
      have hn' : n < y.length := by omega
      have hround := mulProgram_round x y n hn'
      have hn0 : n ≤ y.length := by omega
      rw [mulTotalTicks, run_add, ih hn0, Option.bind_some]
      rw [hround]

/-- Running the total tick count for all multiplier bits takes `mulStart x y` to the final round
configuration. -/
theorem mulProgram_sweep (x y : Bits) :
    stackRun mulProgram (mulTotalTicks x y y.length) (mulStart x y)
      = some (mulCfg x y y.length) := by
  have hstart : mulStart x y = mulCfg x y 0 := by
    rw [mulStart, mulCfg]
    congr 1
  rw [hstart]
  exact mulProgram_rounds x y y.length (le_refl _)

/-- The final multiplication accumulator has binary value equal to the product of the two input
values. -/
theorem mulProgram_value (x y : Bits) :
    binaryValue (mulAcc x y y.length) = binaryValue x * binaryValue y :=
  mulAcc_value_full x y

/-- The rounded interval for an encoded rational is valid, has width `1 / 2 ^ k`, and contains
the represented real value. -/
theorem nativeInterval_certified (e : RatEnc) (k : ℕ) :
    Qatlib.Foundations.IntervalArith.IntervalOps.Valid (nativeInterval e k) ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.width (nativeInterval e k)
        = 1 / (2 : ℚ) ^ k ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.Contains (nativeInterval e k) e.toReal := by
  obtain ⟨hv, hc, hw, -⟩ :=
    Qatlib.Foundations.IntervalArith.IntervalOps.g1.1 e.toRat k
  refine ⟨?_, ?_, ?_⟩
  · simpa [nativeInterval] using! hv
  · simpa [nativeInterval, Qatlib.Foundations.IntervalArith.IntervalOps.unit] using! hw
  · simpa [nativeInterval, RatEnc.toReal] using! hc

/-- The lower endpoint of the rounded interval does not exceed the encoded rational value. -/
theorem nativeInterval_lo_le (e : RatEnc) (k : ℕ) :
    (nativeInterval e k).lo ≤ e.toRat := by
  obtain ⟨-, hc, -⟩ :=
    Qatlib.Foundations.IntervalArith.IntervalOps.g1.1 e.toRat k
  have h := hc.1
  have h' : (↑((nativeInterval e k).lo) : ℝ) ≤ (↑e.toRat : ℝ) := by
    simpa [nativeInterval, RatEnc.toReal] using! h
  exact_mod_cast h'

/-- If a positive `gap` bounds the denominator interval from below, `nativeDiv` returns a valid
interval containing the quotient and the denominator is nonzero. Its width is bounded by the
numerator width divided by `gap` plus the numerator radius times the denominator width
divided by `gap ^ 2`. -/
theorem nativeDiv_certified (a b : RatEnc) (gap : ℚ) (k : ℕ)
    (hg : 0 < gap) (hgap : gap ≤ (nativeInterval b k).lo) :
    ∃ c, nativeDiv a b gap k = some c ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.Valid c ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.width c
        ≤ Qatlib.Foundations.IntervalArith.IntervalOps.width (nativeInterval a k) / gap
          + Qatlib.Foundations.IntervalArith.IntervalOps.radius (nativeInterval a k)
            * Qatlib.Foundations.IntervalArith.IntervalOps.width (nativeInterval b k) / gap ^ 2 ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.Contains c
        ((a.toRat : ℝ) / (b.toRat : ℝ)) ∧
      (b.toRat : ℝ) ≠ 0 := by
  obtain ⟨hva, hwa, hca⟩ := nativeInterval_certified a k
  obtain ⟨hvb, hwb, hcb⟩ := nativeInterval_certified b k
  obtain ⟨c, hc, hvc, hwc, hcontains⟩ :=
    Qatlib.Foundations.IntervalArith.IntervalOps.g3.1 (nativeInterval a k) (nativeInterval b k)
      gap hg hgap hva hvb
  have hca' : Qatlib.Foundations.IntervalArith.IntervalOps.Contains (nativeInterval a k)
      (a.toRat : ℝ) := by simpa [RatEnc.toReal] using! hca
  have hcb' : Qatlib.Foundations.IntervalArith.IntervalOps.Contains (nativeInterval b k)
      (b.toRat : ℝ) := by simpa [RatEnc.toReal] using! hcb
  refine ⟨c, ?_, hvc, hwc, ?_, ?_⟩
  · simpa [nativeDiv] using! hc
  · obtain ⟨-, hcont⟩ := hcontains (a.toRat : ℝ) (b.toRat : ℝ) hca' hcb'
    exact hcont
  · obtain ⟨hne, -⟩ := hcontains (a.toRat : ℝ) (b.toRat : ℝ) hca' hcb'
    exact hne

/-- Division returns `none` when the denominator encoding has zero numerator. -/
theorem nativeDiv_rejects_zero (a b : RatEnc) (hb : b.num = 0) (gap : ℚ) (k : ℕ) :
    nativeDiv a b gap k = none := by
  have hnum : b.toRat = 0 := by
    rw [RatEnc.toRat, hb]
    simp
  have hlo : (nativeInterval b k).lo = 0 := by
    have hrd : Qatlib.Foundations.IntervalArith.IntervalOps.roundDown (0 : ℚ) k = 0 := by
      simp [Qatlib.Foundations.IntervalArith.IntervalOps.roundDown]
    simp [nativeInterval, Qatlib.Foundations.IntervalArith.IntervalOps.rounded, hnum, hrd]
  by_cases hg : 0 < gap
  · have hlt : (nativeInterval b k).lo < gap := by
      rw [hlo]
      exact hg
    have hnone := Qatlib.Foundations.IntervalArith.IntervalOps.g3.2
      (nativeInterval a k) (nativeInterval b k) gap (Or.inr (Or.inl hlt))
    simpa [nativeDiv] using! hnone
  · have hnone := Qatlib.Foundations.IntervalArith.IntervalOps.g3.2
      (nativeInterval a k) (nativeInterval b k) gap (Or.inl (le_of_not_gt hg))
    simpa [nativeDiv] using! hnone

/-- Division returns `none` when the encoded denominator is negative. -/
theorem nativeDiv_rejects_negative (a b : RatEnc) (hb : b.toRat < 0) (gap : ℚ) (k : ℕ) :
    nativeDiv a b gap k = none := by
  have hlo : (nativeInterval b k).lo ≤ b.toRat := nativeInterval_lo_le b k
  by_cases hg : 0 < gap
  · have hlt : (nativeInterval b k).lo < gap := by
      have hneg : (nativeInterval b k).lo < 0 := lt_of_le_of_lt hlo hb
      linarith
    have hnone := Qatlib.Foundations.IntervalArith.IntervalOps.g3.2
      (nativeInterval a k) (nativeInterval b k) gap (Or.inr (Or.inl hlt))
    simpa [nativeDiv] using! hnone
  · have hnone := Qatlib.Foundations.IntervalArith.IntervalOps.g3.2
      (nativeInterval a k) (nativeInterval b k) gap (Or.inl (le_of_not_gt hg))
    simpa [nativeDiv] using! hnone

/-- Under the positive denominator gap condition, the returned quotient interval has width at
most `2⁻ᵏ / gap` plus the numerator interval radius times `2⁻ᵏ / gap²`. -/
theorem nativeDiv_rounding_account (a b : RatEnc) (gap : ℚ) (k : ℕ)
    (hg : 0 < gap) (hgap : gap ≤ (nativeInterval b k).lo) (c : Interval)
    (hc : nativeDiv a b gap k = some c) :
    Qatlib.Foundations.IntervalArith.IntervalOps.width c
      ≤ 1 / (2 : ℚ) ^ k / gap
        + Qatlib.Foundations.IntervalArith.IntervalOps.radius (nativeInterval a k)
          * (1 / (2 : ℚ) ^ k) / gap ^ 2 := by
  obtain ⟨c', hc', -, hwidth, -, -⟩ := nativeDiv_certified a b gap k hg hgap
  have hcne : c' = c := by
    rw [hc] at hc'
    exact (Option.some.inj hc').symm
  rw [hcne] at hwidth
  obtain ⟨-, hwa, -⟩ := nativeInterval_certified a k
  obtain ⟨-, hwb, -⟩ := nativeInterval_certified b k
  rw [hwa, hwb] at hwidth
  exact hwidth

/-- For positive `S` and an encoded rational between zero and `S * S`, `nativeSqrt` returns the
valid bracket enclosing its real square root. The bracket has width `S / 2 ^ k`. -/
theorem nativeSqrt_certified (q : RatEnc) (S : ℚ) (k : ℕ)
    (hS : 0 < S) (hq : 0 ≤ q.toRat) (hSq : q.toRat ≤ S * S) :
    nativeSqrt q S k = some (sqrtBracket q.toRat S k) ∧
      Qatlib.Foundations.IntervalArith.IntervalOps.Valid (sqrtBracket q.toRat S k) ∧
      ((sqrtBracket q.toRat S k).lo : ℝ) ≤ Real.sqrt q.toReal ∧
      Real.sqrt q.toReal ≤ ((sqrtBracket q.toRat S k).hi : ℝ) ∧
      (sqrtBracket q.toRat S k).hi - (sqrtBracket q.toRat S k).lo = S / (2 : ℚ) ^ k := by
  have hbr := Qatlib.Concepts.ScaledSqrt.SqrtBounds.g1 q.toRat S k hS hq hSq
  (try dsimp only at hbr)
  obtain ⟨hlo, hlo2, hhi, -, -, hwidth, -, hsqlo, hsqhi⟩ := hbr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [nativeSqrt, hS, hq, hSq, sqrtBracket]
  · simpa [sqrtBracket] using! hlo2
  · simpa [RatEnc.toReal, sqrtBracket] using! hsqlo
  · simpa [RatEnc.toReal, sqrtBracket] using! hsqhi
  · simpa [sqrtBracket, Qatlib.Concepts.ScaledSqrt.SqrtBounds.bracket] using! hwidth

/-- Square-root evaluation returns `none` for a negative encoded rational. -/
theorem nativeSqrt_rejects_negative (q : RatEnc) (hq : q.toRat < 0) (S : ℚ) (k : ℕ) :
    nativeSqrt q S k = none := by
  simp [nativeSqrt, hq]

/-- Square-root evaluation returns `none` when the scale `S` is nonpositive. -/
theorem nativeSqrt_rejects_nonpositive_scale (q : RatEnc) (S : ℚ) (hS : S ≤ 0) (k : ℕ) :
    nativeSqrt q S k = none := by
  simp [nativeSqrt, not_lt_of_ge hS]

/-- A rational name code is faithful to `q` when its decoded value differs from `q` by at most
`1 / 2 ^ c.prec`. -/
def NameCode.Faithful (c : NameCode) (q : ℚ) : Prop :=
  |c.decode - q| ≤ 1 / (2 : ℚ) ^ c.prec

/-- A faithful name code satisfies its stated approximation bound, together with the defining
formulas for its decoded rational and size. -/
theorem NameCode.read_certified (c : NameCode) (q : ℚ) (h : c.Faithful q) :
    c.decode = (binaryValue c.num : ℚ) / (binaryValue c.den : ℚ) ∧
      |c.decode - q| ≤ 1 / (2 : ℚ) ^ c.prec ∧
      c.size = c.num.length + c.den.length + c.prec :=
  ⟨rfl, h, rfl⟩

/-- Pairing the slots of a complete word with their amplification factors preserves the number
of slots. -/
theorem completeWord_zip_length (w : CompleteWord) :
    (w.slots.zip w.amp).length = w.slots.length := by
  rw [List.length_zip, w.matched]
  exact min_eq_left (Nat.le_refl _)

/-- The error-unit count of a complete word is the native error-unit count of its paired slots
and amplification factors. -/
theorem completeWord_error_units (w : CompleteWord) :
    completeWordErrorUnits w = nativeWordErrorUnitsAux (w.slots.zip w.amp) := rfl

/-- If a native word has fewer amplification factors than slots, pairing the two lists retains
only as many entries as there are amplification factors. -/
theorem nativeWord_zip_truncates (w : NativeWord) (h : w.amp.length < w.slots.length) :
    (w.slots.zip w.amp).length = w.amp.length := by
  rw [List.length_zip]
  exact Nat.min_eq_right (Nat.le_of_lt h)

/-- A native word whose slot and amplification lists have equal length has a complete-word
representation preserving both lists and the phase precision, with no loss of slots when
pairing. -/
theorem completeWord_of_native (w : NativeWord) (h : w.slots.length = w.amp.length) :
    ∃ (cw : CompleteWord),
      cw.slots = w.slots ∧ cw.amp = w.amp ∧ cw.phaseBits = w.phaseBits ∧
        (cw.slots.zip cw.amp).length = cw.slots.length := by
  refine ⟨{ slots := w.slots, amp := w.amp, phaseBits := w.phaseBits, matched := h }, rfl, rfl,
    rfl, ?_⟩
  exact completeWord_zip_length _

/-- Reading a native parameter at precision `k` approximates its ideal real value within the
error bound supplied by its name. -/
theorem param_read_certified (p : NativeParam) (k : ℕ) :
    |(p.name.eval k).toReal - p.name.value| ≤ p.name.errReal k := by
  simpa [NativeName.errReal] using! p.name.errSpec k

/-- The recursive sum of the empty real list is zero. -/
@[simp] theorem rsum_nil : rsum ([] : List ℝ) = 0 := rfl

/-- The recursive sum of a nonempty real list is its head plus the recursive sum of its tail. -/
@[simp] theorem rsum_cons (a : ℝ) (l : List ℝ) : rsum (a :: l) = a + rsum l := rfl

/-- The recursive sum of an appended pair of real lists is the sum of their recursive sums. -/
theorem rsum_append (l₁ l₂ : List ℝ) : rsum (l₁ ++ l₂) = rsum l₁ + rsum l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, add_assoc]

/-- Summing the image of a nonempty list gives the image of its head plus the sum of the mapped
tail. -/
theorem rsum_map_cons {α : Type} (f : α → ℝ) (a : α) (l : List α) :
    rsum (List.map f (a :: l)) = f a + rsum (List.map f l) := by
  simp [rsum]

/-- Pointwise comparison on the elements of a list implies comparison of the recursive sums of
the mapped real values. -/
theorem rsum_le_sum_map {α : Type} (l : List α) (f g : α → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    rsum (List.map f l) ≤ rsum (List.map g l) := by
  induction l with
  | nil => simp [rsum]
  | cons a l ih =>
      rw [rsum_map_cons, rsum_map_cons]
      exact add_le_add (h a List.mem_cons_self)
        (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- A product of real factors each of absolute value at most one also has absolute value at most
one. -/
private theorem chainProduct_abs_le_one {l : List ℝ} (h : ∀ x ∈ l, |x| ≤ 1) :
    |chainProduct l| ≤ 1 := by
  induction l with
  | nil => simp [chainProduct]
  | cons a l ih =>
      have ha : |a| ≤ 1 := h a List.mem_cons_self
      have hl : ∀ x ∈ l, |x| ≤ 1 := by
        intro x hx
        exact h x (List.mem_cons_of_mem a hx)
      have hb := ih hl
      rw [chainProduct, abs_mul]
      have hmul : |a| * |chainProduct l| ≤ 1 * 1 :=
        mul_le_mul ha hb (abs_nonneg _) (by norm_num)
      calc
        |a| * |chainProduct l| ≤ 1 * 1 := hmul
        _ = 1 := by ring

/-- For equally long lists of real factors bounded in absolute value by one, the absolute
difference of their products is at most the sum of the absolute differences of paired
factors. -/
private theorem telescope_chain : ∀ (a b : List ℝ),
    a.length = b.length →
    (∀ x ∈ a, |x| ≤ 1) → (∀ x ∈ b, |x| ≤ 1) →
    |chainProduct a - chainProduct b|
      ≤ rsum (List.map (fun p => |p.1 - p.2|) (a.zip b)) := by
  intro a
  induction a with
  | nil =>
      intro b hlen ha hb
      have hbempty : b = [] := by
        cases b with
        | nil => rfl
        | cons c l => simp at hlen
      rw [hbempty]
      simp [chainProduct]
  | cons a₀ a ih =>
      intro b hlen ha hb
      cases b with
      | nil => simp at hlen
      | cons b₀ b =>
          have ha0 : |a₀| ≤ 1 := ha a₀ List.mem_cons_self
          have hb0 : |b₀| ≤ 1 := hb b₀ List.mem_cons_self
          have ha' : ∀ x ∈ a, |x| ≤ 1 := fun x hx => ha x (List.mem_cons_of_mem a₀ hx)
          have hb' : ∀ x ∈ b, |x| ≤ 1 := fun x hx => hb x (List.mem_cons_of_mem b₀ hx)
          have hA : |chainProduct a| ≤ 1 := chainProduct_abs_le_one ha'
          have hB : |chainProduct b| ≤ 1 := chainProduct_abs_le_one hb'
          have htail : |chainProduct a - chainProduct b|
              ≤ rsum (List.map (fun p => |p.1 - p.2|) (a.zip b)) :=
            ih b (by simp at hlen; omega) ha' hb'
          have hkey : a₀ * chainProduct a - b₀ * chainProduct b
              = (a₀ - b₀) * chainProduct a + b₀ * (chainProduct a - chainProduct b) := by
            ring
          have habs : |(a₀ - b₀) * chainProduct a + b₀ * (chainProduct a - chainProduct b)|
              ≤ |(a₀ - b₀) * chainProduct a| + |b₀ * (chainProduct a - chainProduct b)| :=
            abs_add_le _ _
          have habs' : |(a₀ - b₀) * chainProduct a + b₀ * (chainProduct a - chainProduct b)|
              ≤ |a₀ - b₀| * |chainProduct a| + |b₀| * |chainProduct a - chainProduct b| := by
            simpa [abs_mul] using! habs
          have h1 : |a₀ - b₀| * |chainProduct a| ≤ |a₀ - b₀| :=
            mul_le_of_le_one_right (abs_nonneg _) (by simpa using! hA)
          have h2 : |b₀| * |chainProduct a - chainProduct b| ≤ |chainProduct a - chainProduct b| := by
            have hmul : |b₀| * |chainProduct a - chainProduct b|
                ≤ 1 * |chainProduct a - chainProduct b| :=
              mul_le_mul (by simpa using! hb0) (le_refl (|chainProduct a - chainProduct b|))
                (abs_nonneg (chainProduct a - chainProduct b)) (by norm_num)
            simpa using! hmul
          have hstep : |a₀ - b₀| * |chainProduct a|
                + |b₀| * |chainProduct a - chainProduct b|
              ≤ |a₀ - b₀| + |chainProduct a - chainProduct b| :=
            add_le_add h1 h2
          have hstep2 : |a₀ - b₀| + |chainProduct a - chainProduct b|
              ≤ |a₀ - b₀| + rsum (List.map (fun p => |p.1 - p.2|) (a.zip b)) := by
            linarith [htail]
          have hfin : |a₀ - b₀| + rsum (List.map (fun p => |p.1 - p.2|) (a.zip b))
              = rsum (List.map (fun p => |p.1 - p.2|) ((a₀ :: a).zip (b₀ :: b))) := by
            have hz : ((a₀ :: a).zip (b₀ :: b)) = (a₀, b₀) :: (a.zip b) := rfl
            rw [hz, rsum_map_cons]
          calc
            |a₀ * chainProduct a - b₀ * chainProduct b|
                = |(a₀ - b₀) * chainProduct a + b₀ * (chainProduct a - chainProduct b)| := by
                  rw [hkey]
            _ ≤ |a₀ - b₀| * |chainProduct a|
                + |b₀| * |chainProduct a - chainProduct b| := habs'
            _ ≤ |a₀ - b₀| + |chainProduct a - chainProduct b| := hstep
            _ ≤ |a₀ - b₀| + rsum (List.map (fun p => |p.1 - p.2|) (a.zip b)) := hstep2
            _ = rsum (List.map (fun p => |p.1 - p.2|) ((a₀ :: a).zip (b₀ :: b))) := hfin

/-- The sum of the individual rational name-error bounds, viewed in the reals, equals the slot
error at precision `k`. -/
private theorem slot_error_sum (s : List NativeParam) (k : ℕ) :
    rsum (List.map (fun p => (p.name.errAt k : ℝ)) s) = (nativeSlotError s k : ℝ) := by
  induction s with
  | nil => simp [nativeSlotError]
  | cons p s ih =>
      rw [rsum_map_cons, nativeSlotError, ih]
      push_cast
      ring

/-- Summing name-error bounds over flattened slots equals summing the slot errors. -/
private theorem flatten_errorSum (slots : List (List NativeParam)) (k : ℕ) :
    rsum (List.map (fun p => (p.name.errAt k : ℝ)) (paramsOfSlots slots))
      = rsum (List.map (fun s => (nativeSlotError s k : ℝ)) slots) := by
  induction slots with
  | nil => simp [paramsOfSlots]
  | cons s slots ih =>
      rw [paramsOfSlots, List.map_append, rsum_append, ih]
      rw [slot_error_sum]
      rfl

/-- The absolute differences of paired images of a parameter list form the image of that list
under the pointwise absolute difference. -/
private theorem zip_map_map (l : List NativeParam) (f g : NativeParam → ℝ) :
    List.map (fun p => |p.1 - p.2|) ((List.map f l).zip (List.map g l))
      = List.map (fun x => |f x - g x|) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- If both the read and ideal parameter values in a slot have absolute value at most one, the
difference of their products is bounded by `nativeSlotError s k`. -/
theorem slot_error_bound : ∀ (s : List NativeParam) (k : ℕ),
    (∀ p ∈ s, |(p.name.eval k).toReal| ≤ 1) →
    (∀ p ∈ s, |p.name.value| ≤ 1) →
    |chainProduct (List.map (fun p => (p.name.eval k).toReal) s)
        - chainProduct (List.map (fun p => p.name.value) s)|
      ≤ (nativeSlotError s k : ℝ) := by
  intro s
  induction s with
  | nil =>
      intro k hread hideal
      simp [chainProduct, nativeSlotError]
  | cons p s ih =>
      intro k hread hideal
      have hread' : ∀ q ∈ s, |(q.name.eval k).toReal| ≤ 1 := by
        intro q hq
        exact hread q (List.mem_cons_of_mem p hq)
      have hideal' : ∀ q ∈ s, |q.name.value| ≤ 1 := by
        intro q hq
        exact hideal q (List.mem_cons_of_mem p hq)
      have htail := ih k hread' hideal'
      have herr : |(p.name.eval k).toReal - p.name.value| ≤ p.name.errReal k :=
        param_read_certified p k
      have hread'' : ∀ x ∈ List.map (fun q => (q.name.eval k).toReal) s, |x| ≤ 1 := by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        exact hread' q hq
      set R := chainProduct (List.map (fun q => (q.name.eval k).toReal) s) with hR
      set I := chainProduct (List.map (fun q => q.name.value) s) with hI
      set rp := (p.name.eval k).toReal with hrp
      set ip := p.name.value with hip
      have hRabs : |R| ≤ 1 := by simpa [hR] using! chainProduct_abs_le_one hread''
      have hipabs : |ip| ≤ 1 := by simpa [hip] using! hideal p List.mem_cons_self
      have herr' : 0 ≤ p.name.errReal k := by
        have h := (p.name.errBudget k).1
        rw [NativeName.errReal]
        exact_mod_cast h
      have h1 : |rp - ip| * |R| ≤ p.name.errReal k * 1 :=
        mul_le_mul (by simpa [hrp, hip] using! herr) (by simpa using! hRabs) (abs_nonneg R) herr'
      have h2 : |ip| * |R - I| ≤ |R - I| := by
        have hmul : |ip| * |R - I| ≤ 1 * |R - I| :=
          mul_le_mul (by simpa using! hipabs) (le_refl (|R - I|)) (abs_nonneg (R - I)) (by norm_num)
        simpa using! hmul
      have hstep : |rp - ip| * |R| + |ip| * |R - I| ≤ p.name.errReal k * 1 + |R - I| :=
        add_le_add h1 h2
      have hstep2 : p.name.errReal k * 1 + |R - I| ≤ p.name.errReal k + (nativeSlotError s k : ℝ) := by
        rw [mul_one]
        have hRI : |R - I| ≤ (nativeSlotError s k : ℝ) := by
          rw [hR, hI]
          exact htail
        exact add_le_add (le_refl _) hRI
      have hcons : (nativeSlotError (p :: s) k : ℝ) = p.name.errReal k + (nativeSlotError s k : ℝ) := by
        simp only [nativeSlotError, NativeName.errReal]
        rw [Rat.cast_add]
      have hkey : rp * R - ip * I = (rp - ip) * R + ip * (R - I) := by ring
      have habs : |(rp - ip) * R + ip * (R - I)| ≤ |(rp - ip) * R| + |ip * (R - I)| :=
          abs_add_le _ _
      have habs' : |(rp - ip) * R + ip * (R - I)| ≤ |rp - ip| * |R| + |ip| * |R - I| := by
        simpa [abs_mul] using! habs
      show |rp * R - ip * I| ≤ _
      calc
        |rp * R - ip * I| = |(rp - ip) * R + ip * (R - I)| := by rw [hkey]
        _ ≤ |rp - ip| * |R| + |ip| * |R - I| := habs'
        _ ≤ p.name.errReal k * 1 + |R - I| := hstep
        _ ≤ p.name.errReal k + (nativeSlotError s k : ℝ) := hstep2
        _ = (nativeSlotError (p :: s) k : ℝ) := hcons.symm

/-- For equally long slot and amplification lists with every amplification factor at least one,
the native word error account bounds the sum of the slot errors. -/
private theorem account_ge_slots : ∀ (slots : List (List NativeParam)) (amps : List ℕ),
    slots.length = amps.length →
    (∀ a ∈ amps, 1 ≤ a) →
    ∀ k : ℕ,
      rsum (List.map (fun s => (nativeSlotError s k : ℝ)) slots)
        ≤ (nativeWordErrorActualAux (slots.zip amps) k : ℝ) := by
  intro slots
  induction slots with
  | nil =>
      intro amps hlen hamp k
      have hempty : amps = [] := by
        cases amps with
        | nil => rfl
        | cons c l => simp at hlen
      rw [hempty]
      simp [nativeWordErrorActualAux]
  | cons s slots ih =>
      intro amps hlen hamp k
      cases amps with
      | nil => simp at hlen
      | cons a amps =>
          simp at hlen
          have hamp0 : 1 ≤ a := hamp a List.mem_cons_self
          have hamp' : ∀ x ∈ amps, 1 ≤ x := by
            intro x hx
            exact hamp x (List.mem_cons_of_mem a hx)
          have hrest := ih amps (by omega) hamp' k
          have hnonneg : 0 ≤ (nativeSlotError s k : ℝ) := by
            have h := nativeSlotError_nonneg s k
            exact_mod_cast h
          have hmul : (nativeSlotError s k : ℝ) ≤ (a : ℝ) * (nativeSlotError s k : ℝ) := by
            have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hamp0
            nlinarith
          show (nativeSlotError s k : ℝ)
                + rsum (List.map (fun s => (nativeSlotError s k : ℝ)) slots)
              ≤ (nativeWordErrorActualAux ((s, a) :: (slots.zip amps)) k : ℝ)
          rw [nativeWordErrorActualAux]
          have hcast : (((a : ℚ) * nativeSlotError s k
                + nativeWordErrorActualAux (slots.zip amps) k : ℚ) : ℝ)
              = (a : ℝ) * (nativeSlotError s k : ℝ)
                + (nativeWordErrorActualAux (slots.zip amps) k : ℝ) := by
            push_cast
            ring
          rw [hcast]
          exact add_le_add hmul hrest

/-- If all read and ideal parameter values have absolute value at most one and every
amplification factor is at least one, the complete word error account bounds the absolute
difference between its read and ideal products. -/
theorem completeWord_telescope (w : CompleteWord) (k : ℕ)
    (hread : ∀ p ∈ wordParams w, |(p.name.eval k).toReal| ≤ 1)
    (hideal : ∀ p ∈ wordParams w, |p.name.value| ≤ 1)
    (hamp : ∀ a ∈ w.amp, 1 ≤ a) :
    |completeWordReadProduct w k - completeWordIdealProduct w|
      ≤ (completeWordErrorActual w k : ℝ) := by
  have hread' : ∀ x ∈ List.map (fun p => (p.name.eval k).toReal) (wordParams w), |x| ≤ 1 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact hread p hp
  have hideal' : ∀ x ∈ List.map (fun p => p.name.value) (wordParams w), |x| ≤ 1 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact hideal p hp
  have htel : |chainProduct (List.map (fun p => (p.name.eval k).toReal) (wordParams w)) - chainProduct (List.map (fun p => p.name.value) (wordParams w))|
      ≤ rsum (List.map (fun p => |p.1 - p.2|) ((List.map (fun p => (p.name.eval k).toReal) (wordParams w)).zip (List.map (fun p => p.name.value) (wordParams w)))) :=
    telescope_chain (List.map (fun p => (p.name.eval k).toReal) (wordParams w))
      (List.map (fun p => p.name.value) (wordParams w)) (by simp) hread' hideal'
  have hpair : List.map (fun p => |p.1 - p.2|) ((List.map (fun p => (p.name.eval k).toReal) (wordParams w)).zip (List.map (fun p => p.name.value) (wordParams w)))
      = List.map (fun p => |(p.name.eval k).toReal - p.name.value|) (wordParams w) :=
    zip_map_map (wordParams w) (fun p => (p.name.eval k).toReal) (fun p => p.name.value)
  have hsum : rsum (List.map (fun p => |p.1 - p.2|) ((List.map (fun p => (p.name.eval k).toReal) (wordParams w)).zip (List.map (fun p => p.name.value) (wordParams w))))
      ≤ rsum (List.map (fun p => (p.name.errAt k : ℝ)) (wordParams w)) := by
    rw [hpair]
    refine rsum_le_sum_map (wordParams w) _ _ ?_
    intro p hp
    simpa [NativeName.errReal] using! param_read_certified p k
  have htotal : rsum (List.map (fun p => (p.name.errAt k : ℝ)) (wordParams w))
      = rsum (List.map (fun s => (nativeSlotError s k : ℝ)) w.slots) := by
    simpa [wordParams] using! flatten_errorSum w.slots k
  have hge := account_ge_slots w.slots w.amp w.matched hamp k
  have hcast : (nativeWordErrorActualAux (w.slots.zip w.amp) k : ℝ)
      = (completeWordErrorActual w k : ℝ) := rfl
  rw [hcast] at hge
  show |completeWordReadProduct w k - completeWordIdealProduct w| ≤ _
  rw [completeWordReadProduct, completeWordIdealProduct]
  have hfinal : rsum (List.map (fun p => (p.name.errAt k : ℝ)) (wordParams w))
      ≤ (completeWordErrorActual w k : ℝ) := htotal ▸ hge
  exact htel.trans (hsum.trans hfinal)

/-- The phase `1 / 5` is off the binary phase grid at precision three. -/
theorem offGridQpe_phase : OffGrid (1 / 5) 3 := offGrid_one_five

/-- Every point on the eight-point binary phase grid is at distance at least `1 / 20` from `1 /
5`. -/
theorem offGridQpe_grid_distance :
    ∀ i : Fin 8, |(1 / 5 : ℚ) - (i.val : ℚ) / 2 ^ 3| ≥ 1 / 20 := by
  intro i
  fin_cases i <;> norm_num

/-- The grid point with index two at precision three is `1 / 4`, whose distance from `1 / 5` is
exactly `1 / 20`. -/
theorem offGridQpe_grid_best :
    ((2 : ℚ) / 2 ^ 3 = 1 / 4) ∧ |(1 / 5 : ℚ) - 2 / 2 ^ 3| = 1 / 20 := by
  norm_num

/-- The dyadic error at the precision chosen for `offGridQpeWord` is at most `1 / 20`. -/
theorem offGridQpe_precision_dominates :
    1 / (2 : ℚ) ^ precisionChoice offGridQpeWord.publicParams ≤ 1 / 20 := by
  have h : precisionChoice offGridQpeWord.publicParams = 6 := by
    rw [offGridQpeWord_precision]
  rw [h]
  norm_num

/-- The second slot of `lcuConsumerWord` contains parameters with ideal values `1 / 3` and `1 /
5`. -/
theorem lcuConsumer_two_coefficients :
    (lcuConsumerWord.slots[1]?).map (fun s => List.map (fun p => p.name.value) s)
      = some [(1 / 3 : ℝ), (1 / 5 : ℝ)] := by
  simp [lcuConsumerWord, lcuWord, NativeName.exact]

/-- The real coefficients `1 / 3` and `1 / 5` are distinct. -/
theorem lcuConsumer_coefficients_distinct : (1 / 3 : ℝ) ≠ (1 / 5 : ℝ) := by
  norm_num

/-- Reading an exact rational name at any precision returns its rational value viewed in the
reals. -/
theorem exact_name_read (q : ℚ) (k : ℕ) : ((NativeName.exact q).eval k).toReal = (q : ℝ) := by
  have h := (NativeName.exact q).errSpec k
  have hz : (NativeName.exact q).errAt k = 0 := rfl
  have h' : |((NativeName.exact q).eval k).toReal - (NativeName.exact q).value| ≤ (0 : ℝ) := by
    simpa [NativeName.errReal, hz] using! h
  have hxy : ((NativeName.exact q).eval k).toReal = (NativeName.exact q).value := by
    have h1 := (abs_le.mp h').1
    have h2 := (abs_le.mp h').2
    linarith
  have hval : (NativeName.exact q).value = (q : ℝ) := rfl
  rw [hval] at hxy
  exact hxy

/-- The flattened parameters of `lcuCompleteWord` are the phase `1 / 5`, preparation
coefficients `1 / 3` and `1 / 5`, and spectral gap `1 / 16`, with respective margin-bit
counts zero, zero, zero, and four. -/
theorem lcuConsumer_params :
    wordParams lcuCompleteWord
      = ([⟨.phase, NativeName.exact (1 / 5), 0⟩, ⟨.prepareCoeff, NativeName.exact (1 / 3), 0⟩,
        ⟨.prepareCoeff, NativeName.exact (1 / 5), 0⟩, ⟨.spectralGap, NativeName.exact (1 / 16), 4⟩]
        : List NativeParam) := by
  simp [wordParams, paramsOfSlots, lcuCompleteWord, lcuConsumerWord, lcuWord]

/-- If the slot and amplification lists of `lcuConsumerWord` have equal length, a complete word
preserves both lists and retains every slot when pairing them. -/
theorem lcuConsumer_complete
    (h : lcuConsumerWord.slots.length = lcuConsumerWord.amp.length) :
    ∃ cw : CompleteWord,
      cw.slots = lcuConsumerWord.slots ∧ cw.amp = lcuConsumerWord.amp ∧
        (cw.slots.zip cw.amp).length = cw.slots.length := by
  obtain ⟨cw, hs, ha, -, hz⟩ := completeWord_of_native lcuConsumerWord h
  exact ⟨cw, hs, ha, hz⟩

/-- Under the matching-length condition, `lcuConsumerWord` has a complete-word representation
preserving its slots, amplification factors, and error account at precision `k`. -/
theorem lcuConsumer_complete_account (k : ℕ)
    (h : lcuConsumerWord.slots.length = lcuConsumerWord.amp.length) :
    ∃ cw : CompleteWord,
      cw.slots = lcuConsumerWord.slots ∧ cw.amp = lcuConsumerWord.amp ∧
        completeWordErrorActual cw k = nativeWordErrorActual lcuConsumerWord k := by
  obtain ⟨cw, hs, ha, -, -⟩ := completeWord_of_native lcuConsumerWord h
  refine ⟨cw, hs, ha, ?_⟩
  simp [completeWordErrorActual, nativeWordErrorActual, hs, ha]

/-- Under the matching-length condition, `lcuConsumerWord` has a complete-word representation
preserving its slots and amplification factors whose error account at the chosen precision
is at most `1 / 2 ^ 3`. -/
theorem lcuConsumer_complete_budget
    (h : lcuConsumerWord.slots.length = lcuConsumerWord.amp.length) :
    ∃ cw : CompleteWord,
      cw.slots = lcuConsumerWord.slots ∧ cw.amp = lcuConsumerWord.amp ∧
        completeWordErrorActual cw (precisionChoice lcuConsumerWord.publicParams)
          ≤ 1 / (2 : ℚ) ^ 3 := by
  obtain ⟨cw, hs, ha, -, -⟩ := completeWord_of_native lcuConsumerWord h
  refine ⟨cw, hs, ha, ?_⟩
  have hb := lcuConsumerWord_budget
  simpa [completeWordErrorActual, nativeWordErrorActual, hs, ha] using! hb

/-- A native word with two rounded-parameter slots, for phase `1 / 5` and preparation
coefficient `1 / 3`, but only one amplification factor. -/
def droppedSlotWord : NativeWord :=
  { slots :=
      [ [{ kind := .phase, name := NativeName.rounded (1 / 5) (by norm_num), marginBits := 0 }]
      , [{ kind := .prepareCoeff, name := NativeName.rounded (1 / 3) (by norm_num), marginBits := 0 }] ]
    amp := [1]
    phaseBits := 3 }

/-- For `droppedSlotWord`, the native error account is `1 / 2 ^ k`, whereas completing the
amplification list with two unit factors gives error `2 / 2 ^ k`. -/
theorem nativeWord_account_undercounts (k : ℕ) :
    nativeWordErrorActual droppedSlotWord k = 1 / (2 : ℚ) ^ k ∧
      completeWordErrorActual (completeWordOf droppedSlotWord [1, 1] (by rfl)) k
        = 2 / (2 : ℚ) ^ k := by
  refine ⟨?_, ?_⟩
  · simp [nativeWordErrorActual, nativeWordErrorActualAux, droppedSlotWord, nativeSlotError,
      NativeName.rounded, Qatlib.Foundations.IntervalArith.IntervalOps.unit]
  · simp [completeWordErrorActual, nativeWordErrorActualAux, completeWordOf, droppedSlotWord,
      nativeSlotError, NativeName.rounded, Qatlib.Foundations.IntervalArith.IntervalOps.unit]
    ring

end Qatlib.Concepts.QueryComplexity.DegreeMethod
