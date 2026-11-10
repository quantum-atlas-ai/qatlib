/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.PaidBinaryAddition
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.FramedBinaryAddition

open PaidBinaryAddition (digit carry columns digits output_value columns_length digits_length)
abbrev Local := Bool × Bool × Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 3) Local

def frame : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | [] => [false]
  | b :: bs => true :: b :: frame bs

def input (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
    (frame a.reverse ++ frame b.reverse).reverse

def state (i a b o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  fun k => if k = 0 then i else if k = 1 then a else if k = 2 then b else o

private theorem state_update (i a b o x : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (k : Fin 4) :
    Function.update (state i a b o) k x =
      state (if k = 0 then x else i) (if k = 1 then x else a)
        (if k = 2 then x else b) (if k = 3 then x else o) := by
  funext j
  fin_cases k <;> fin_cases j <;> simp [state, Fin.ext_iff]

def readWord (dest : Fin 4) (again next : Fin 3) :
    TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 3) Local :=
  .pop 0 (fun _ x => (false, false, false, x.getD false))
    (.branch (fun v => v.2.2.2)
      (.pop 0 (fun _ x => (false, x.getD false, false, false))
        (.push dest (fun v => v.2.1) (.load (fun _ => default) (.goto (fun _ => again)))))
      (.load (fun _ => default) (.goto (fun _ => next))))

def addWord : TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 3) Local :=
  .peek 1 (fun v x => (v.1, x.getD false, false, x.isSome))
    (.peek 2 (fun v x => (v.1, v.2.1, x.getD false, v.2.2.2 || x.isSome))
      (.branch (fun v => v.2.2.2)
        (.pop 1 (fun v _ => v) (.pop 2 (fun v _ => v)
          (.push 3 (fun v => digit v.2.1 v.2.2.1 v.1)
            (.load (fun v => (carry v.2.1 v.2.2.1 v.1, false, false, false))
              (.goto (fun _ => 2))))))
        (.branch (fun v => v.1)
          (.push 3 (fun _ => true) (.load (fun _ => default) .halt))
          (.load (fun _ => default) .halt))))

def program (l : Fin 3) : TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 3) Local :=
  if l = 0 then readWord 1 0 1 else if l = 1 then readWord 2 1 2 else addWord

def Exec (s t : Config) (cost : ℕ) : Prop :=
  ∃ steps, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun program steps s = some t ∧
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps s ≤ cost

private theorem exec_one (s t : Config) (cost : ℕ) (h : TM2.step program s = some t)
    (hc : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 s ≤ cost) : Exec s t cost :=
  ⟨1, (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_one program s).trans h, hc⟩

private theorem exec_trans {s t u : Config} {c d : ℕ} (h : Exec s t c) (g : Exec t u d) :
    Exec s u (c + d) := by
  obtain ⟨n, hn, hc⟩ := h
  obtain ⟨m, hm, hd⟩ := g
  refine ⟨n + m, ?_, ?_⟩
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_add, hn, Option.bind_some,
      hm]
  · rw [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.clock_add program n m s t hn]
    omega

private theorem exec_mono {s t : Config} {c d : ℕ} (h : Exec s t c) (hc : c ≤ d) : Exec s t d := by
  obtain ⟨n, hn, hb⟩ := h
  exact ⟨n, hn, hb.trans hc⟩

theorem frame_length (a : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (frame a).length = 2 * a.length + 1 := by
  induction a with
  | nil => rfl
  | cons b bs ih => simp only [frame, List.length_cons, ih]; omega

theorem input_length (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (input a b).length = 2 * (a.length + b.length) + 2 := by
  simp only [input, List.length_reverse, List.length_append, frame_length]
  omega

def parserLabel (which : Bool) : Fin 3 := if which then 1 else 0
def nextLabel (which : Bool) : Fin 3 := if which then 2 else 1

def parseState (which : Bool) (i dest other o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Fin 4 → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits :=
  if which then state i other dest o else state i dest other o

theorem parse_step (which x : Bool) (rest dest other o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    TM2.step program ⟨some (parserLabel which), default, parseState which (true :: x :: rest) dest other o⟩ =
      some ⟨some (parserLabel which), default, parseState which rest (x :: dest) other o⟩ := by
  cases which <;> simp [program, readWord, parserLabel, parseState, TM2.step, TM2.stepAux,
    state, state_update, Fin.ext_iff]

theorem parse_stop (which : Bool) (rest dest other o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    TM2.step program ⟨some (parserLabel which), default, parseState which (false :: rest) dest other o⟩ =
      some ⟨some (nextLabel which), default, parseState which rest dest other o⟩ := by
  cases which <;> simp [program, readWord, parserLabel, nextLabel, parseState, TM2.step, TM2.stepAux,
    state, state_update, Fin.ext_iff]

theorem parse_clock (which x : Bool) (rest dest other o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1
      ⟨some (parserLabel which), default, parseState which (true :: x :: rest) dest other o⟩ =
      4 * rest.length + 2 * dest.length + 12 := by
  cases which <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, TM2.step, TM2.stepAux,
    program, readWord, parserLabel, parseState, state, Fin.ext_iff] <;> omega

theorem parse_stop_clock (which : Bool) (rest dest other o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1
      ⟨some (parserLabel which), default, parseState which (false :: rest) dest other o⟩ =
      2 * rest.length + 4 := by
  cases which <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, TM2.step, TM2.stepAux,
    program, readWord, parserLabel, parseState, state, Fin.ext_iff] <;> omega

theorem parse_exec (which : Bool) (xs rest dest other o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Exec ⟨some (parserLabel which), default, parseState which (frame xs ++ rest) dest other o⟩
      ⟨some (nextLabel which), default, parseState which rest (xs.reverse ++ dest) other o⟩
      (20 * (xs.length + 1) * (xs.length + rest.length + dest.length + 1)) := by
  induction xs generalizing dest with
  | nil =>
    apply exec_mono (exec_one _ _ _ (parse_stop which rest dest other o)
      (le_of_eq (parse_stop_clock which rest dest other o)))
    simp only [List.length_nil]
    nlinarith
  | cons x xs ih =>
    have h := exec_trans (exec_one _ _ _ (parse_step which x (frame xs ++ rest) dest other o)
      (le_of_eq (parse_clock which x (frame xs ++ rest) dest other o))) (ih (x :: dest))
    apply exec_mono (by simpa only [frame, List.cons_append, List.reverse_cons,
      List.append_assoc, List.singleton_append] using! h)
    simp only [List.length_append, frame_length, List.length_cons]
    nlinarith

private theorem add_step (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (c : Bool) (o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (h : a ≠ [] ∨ b ≠ []) :
    TM2.step program ⟨some 2, (c, false, false, false), state [] a b o⟩ =
      some ⟨some 2, (carry (a.headD false) (b.headD false) c, false, false, false),
        state [] a.tail b.tail (digit (a.headD false) (b.headD false) c :: o)⟩ := by
  cases a <;> cases b <;> simp_all [program, addWord, TM2.step, TM2.stepAux, state_update, state,
      Fin.ext_iff]

private theorem add_clock (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (c : Bool) (o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (h : a ≠ [] ∨ b ≠ []) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 ⟨some 2, (c, false, false, false), state [] a b o⟩ ≤
      4 * (a.length + b.length) + 2 * o.length + 12 := by
  cases a <;> cases b <;> simp_all [program, addWord, TM2.step, TM2.stepAux, state,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, Fin.ext_iff] <;> omega

private theorem add_stop (c : Bool) (o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    TM2.step program ⟨some 2, (c, false, false, false), state [] [] [] o⟩ =
      some ⟨none, default, state [] [] [] (if c then true :: o else o)⟩ := by
  cases c <;> simp [program, addWord, TM2.step, TM2.stepAux, state_update, state, Fin.ext_iff]

private theorem add_stop_clock (c : Bool) (o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 ⟨some 2, (c, false, false, false), state [] [] [] o⟩ ≤
      2 * o.length + 8 := by
  cases c <;> simp [program, addWord, TM2.step, TM2.stepAux, state,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, Fin.ext_iff]
  all_goals omega

private theorem columns_nil (a : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : columns a [] = a.map (fun x => (x, false)) := by
  cases a <;> rfl

private theorem digits_tail (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (c : Bool) (h : a ≠ [] ∨ b ≠ []) :
    digits c (columns a b) = digit (a.headD false) (b.headD false) c ::
      digits (carry (a.headD false) (b.headD false) c) (columns a.tail b.tail) := by
  cases a <;> cases b <;> simp_all [columns, digits, columns_nil]

theorem add_exec (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) (c : Bool) (o : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Exec ⟨some 2, (c, false, false, false), state [] a b o⟩
      ⟨none, default, state [] [] [] ((digits c (columns a b)).reverse ++ o)⟩
      (30 * (a.length + b.length + 1) * (a.length + b.length + o.length + 1)) := by
  by_cases h : a = [] ∧ b = []
  · rcases h with ⟨rfl, rfl⟩
    cases c <;> apply exec_mono (exec_one _ _ _ (add_stop _ o) (add_stop_clock _ o)) <;>
      simp <;> omega
  · have hn : a ≠ [] ∨ b ≠ [] := by tauto
    have ih := add_exec a.tail b.tail (carry (a.headD false) (b.headD false) c)
      (digit (a.headD false) (b.headD false) c :: o)
    have hh := exec_trans (exec_one _ _ _ (add_step a b c o hn) (add_clock a b c o hn)) ih
    apply exec_mono (by simpa only [digits_tail a b c hn, List.reverse_cons,
      List.append_assoc, List.singleton_append] using! hh)
    have hlen : a.tail.length + b.tail.length < a.length + b.length := by
      cases a <;> cases b <;> simp_all
      all_goals omega
    have hlen' : a.tail.length + b.tail.length ≤ a.length + b.length := by omega
    simp only [List.length_cons]
    nlinarith
termination_by a.length + b.length
decreasing_by
  cases a <;> cases b <;> simp_all
  all_goals omega

theorem source_exec (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Exec (TM2.init (0 : Fin 4) (input a b).reverse)
      ⟨none, default, state [] [] [] ((PaidBinaryAddition.output a b).reverse)⟩
      (100 * (a.length + b.length + 1) ^ 2) := by
  have ha := parse_exec false a.reverse (frame b.reverse) [] [] []
  have hb := parse_exec true b.reverse [] [] a []
  have hs := add_exec a b false []
  have hh := exec_trans (exec_trans ha (by simpa [parseState, parserLabel, nextLabel] using! hb)) hs
  have hinit : (TM2.init (0 : Fin 4) (input a b).reverse : Config) =
      ⟨some 0, default, state (frame a.reverse ++ frame b.reverse) [] [] []⟩ := by
    have he : Function.update (fun _ => []) (0 : Fin 4) (frame a.reverse ++ frame b.reverse) =
        state (frame a.reverse ++ frame b.reverse) [] [] [] := by
      funext k
      fin_cases k <;> simp [state, Fin.ext_iff]
    simp only [input, List.reverse_reverse]
    change (⟨some 0, default, Function.update (fun _ => []) 0 _⟩ : Config) = _
    rw [he]
  rw [hinit]
  apply exec_mono
      (by simpa [parseState, parserLabel, nextLabel, PaidBinaryAddition.output] using! hh)
  simp only [List.length_reverse, frame_length]
  nlinarith

theorem raw_adder :
    ∃ (q c : ℕ) (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))), 0 < c ∧ ∀ a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits,
      ∃ result : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (input a b) result
          (c * (a.length + b.length + 1) ^ 2) (c * (a.length + b.length + 1) ^ 2) ∧
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue result = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b ∧
        result.length ≤ a.length + b.length + 1 := by
  obtain ⟨q, M, C, hC, hM⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.raw_compiler program 0 3
  refine ⟨q, 200 * C, M, Nat.mul_pos (by decide) hC, ?_⟩
  intro a b
  obtain ⟨steps, hrun, hclock⟩ := source_exec a b
  have hfinal (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : state [] [] [] bits = Function.update (fun _ => []) (3 : Fin 4) bits := by
    funext k
    fin_cases k <;> simp [state, Fin.ext_iff]
  rw [hfinal] at hrun
  have hr := hM (input a b) (PaidBinaryAddition.output a b) steps default hrun
  have hi : 1 + (input a b).length ≤ 3 * (a.length + b.length + 1) := by
    simp only [input, List.length_reverse, List.length_append, frame_length]
    omega
  have ho : (PaidBinaryAddition.output a b).length ≤ a.length + b.length + 1 :=
    (digits_length (columns a b) false).trans (Nat.add_le_add_right (columns_length a b) 1)
  have hout : 1 + (PaidBinaryAddition.output a b).length ≤ 2 * (a.length + b.length + 1) := by omega
  have hc : C * ((1 + (input a b).length) ^ 2 +
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps (TM2.init 0 (input a b).reverse) +
      (1 + (PaidBinaryAddition.output a b).length) ^ 2) ≤
      200 * C * (a.length + b.length + 1) ^ 2 := by
    have hi2 := Nat.pow_le_pow_left hi 2
    have ho2 := Nat.pow_le_pow_left hout 2
    have hh : (1 + (input a b).length) ^ 2 +
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program steps (TM2.init 0 (input a b).reverse) +
        (1 + (PaidBinaryAddition.output a b).length) ^ 2 ≤ 200 * (a.length + b.length + 1) ^ 2 := by nlinarith
    exact (Nat.mul_le_mul_left C hh).trans_eq (by ring)
  exact ⟨PaidBinaryAddition.output a b,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hr hc hc, output_value a b, ho⟩

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.FramedBinaryAddition
