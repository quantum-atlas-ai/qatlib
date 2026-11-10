/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidBinaryAddition

abbrev Column := Bool × Bool
abbrev Local := Bool × Bool × Bool

def digit (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def records : List Column → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | [] => [false]
  | (a, b) :: rest => true :: a :: b :: records rest

def digits : Bool → List Column → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | c, [] => if c then [true] else []
  | c, (a, b) :: rest => digit a b c :: digits (carry a b c) rest

def columns : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → List Column
  | [], b => b.map (fun y => (false, y))
  | a, [] => a.map (fun x => (x, false))
  | a :: as, b :: bs => (a, b) :: columns as bs

def input (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits := (records (columns a b)).reverse
def output (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits := digits false (columns a b)

theorem records_length (xs : List Column) : (records xs).length = 3 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons p xs ih => cases p; simp only [records, List.length_cons, ih]; omega

theorem digits_length (xs : List Column) (c : Bool) : (digits c xs).length ≤ xs.length + 1 := by
  induction xs generalizing c with
  | nil => cases c <;> decide
  | cons p xs ih => cases p; simp only [digits, List.length_cons]; exact Nat.add_le_add_right (ih _) 1

theorem digits_value (xs : List Column) (c : Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (digits c xs) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (xs.map Prod.fst) + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (xs.map Prod.snd) + if c then 1 else 0 := by
  induction xs generalizing c with
  | nil => cases c <;> rfl
  | cons p xs ih =>
    rcases p with ⟨a, b⟩
    simp only [digits, List.map_cons,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue, List.foldr_cons]
    have h := ih (carry a b c)
    simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue] at h
    rw [h]
    cases a <;> cases b <;> cases c <;> simp [digit, carry] <;> omega

private theorem false_value (xs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (xs.map (fun _ => false)) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue] using ih

theorem columns_values (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue ((columns a b).map Prod.fst) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a ∧
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue ((columns a b).map Prod.snd) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b := by
  induction a generalizing b with
  | nil =>
    constructor
    · simpa only [columns, List.map_map, Function.comp_def] using! false_value b
    · simp [columns, List.map_map, Function.comp_def]
  | cons x xs ih =>
    cases b with
    | nil =>
      constructor
      · simp [columns, List.map_map, Function.comp_def]
      · simpa only [columns, List.map_map, Function.comp_def] using! false_value (x :: xs)
    | cons y ys =>
      have h := ih ys
      simp only [columns, List.map_cons,
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue, List.foldr_cons]
      change _ + _ = _ + _ ∧ _ + _ = _ + _
      exact ⟨congrArg (fun z => 2 * z + if x then 1 else 0) h.1,
        congrArg (fun z => 2 * z + if y then 1 else 0) h.2⟩

theorem columns_length (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (columns a b).length ≤ a.length + b.length := by
  induction a generalizing b with
  | nil => simp [columns]
  | cons x xs ih =>
    cases b with
    | nil => simp [columns]
    | cons y ys => simp only [columns, List.length_cons]; have h := ih ys; omega

theorem output_value (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (output a b) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b := by
  rw [output, digits_value, (columns_values a b).1, (columns_values a b).2]
  rfl

def program (_ : Fin 1) : TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Local :=
  .pop 0 (fun v flag => (v.1, flag.getD false, v.2.2))
    (.branch (fun v => v.2.1)
      (.pop 0 (fun v bit => (v.1, bit.getD false, v.2.2))
        (.pop 0 (fun v bit => (v.1, v.2.1, bit.getD false))
          (.push 1 (fun v => digit v.2.1 v.2.2 v.1)
            (.load (fun v => (carry v.2.1 v.2.2 v.1, false, false)) (.goto (fun _ => 0))))))
      (.branch (fun v => v.1)
        (.push 1 (fun _ => true) (.load (fun _ => default) .halt))
        (.load (fun _ => default) .halt)))

private theorem pair_input (a b c : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair a b) 0 c = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair c b := by
  funext k
  fin_cases k <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair, Fin.ext_iff]

private theorem pair_output (a b c : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair a b) 1 c = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair a c := by
  funext k
  fin_cases k <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair, Fin.ext_iff]

theorem column_step (a b c : Bool) (rest out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    TM2.step program ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (true :: a :: b :: rest) out⟩ =
      some ⟨some 0, (carry a b c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair rest (digit a b c :: out)⟩ := by
  simp [TM2.step, program, TM2.stepAux]

theorem stop_step (c : Bool) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    TM2.step program ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [false] out⟩ =
      some ⟨none, default, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] (if c then true :: out else out)⟩ := by
  cases c <;> simp [TM2.step, program, TM2.stepAux]

theorem column_clock (a b c : Bool) (rest out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1
      ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (true :: a :: b :: rest) out⟩ =
      6 * rest.length + 2 * out.length + 19 := by
  simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, TM2.step, program, TM2.stepAux]
  omega

theorem stop_clock (c : Bool) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [false] out⟩ ≤
      2 * out.length + 7 := by
  cases c <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, TM2.step, program, TM2.stepAux]
  all_goals omega

theorem source_run (xs : List Column) (c : Bool) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun program (xs.length + 1)
      ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (records xs) out⟩ =
      some ⟨none, default, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] ((digits c xs).reverse ++ out)⟩ := by
  induction xs generalizing c out with
  | nil =>
    cases c <;> simpa [records, digits,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.run_one] using! stop_step _ out
  | cons p xs ih =>
    rcases p with ⟨a, b⟩
    change (TM2.step program ⟨some 0, (c, false, false),
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (true :: a :: b :: records xs) out⟩).bind
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun program (xs.length + 1)) = _
    rw [column_step, Option.bind_some, ih]
    simp [digits, List.reverse_cons, List.append_assoc]

theorem source_clock (xs : List Column) (c : Bool) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program (xs.length + 1)
      ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (records xs) out⟩ ≤
        20 * (xs.length + 1) * (xs.length + out.length + 1) := by
  induction xs generalizing c out with
  | nil =>
    have h := stop_clock c out
    simpa only [List.length_nil, zero_add, mul_one, records] using h.trans (by omega)
  | cons p xs ih =>
    rcases p with ⟨a, b⟩
    simp only [records, List.length_cons]
    rw [show xs.length + 1 + 1 = (xs.length + 1) + 1 from rfl,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock_step program (xs.length + 1) _ _ (column_step a b c (records xs) out), column_clock]
    have h := ih (carry a b c) (digit a b c :: out)
    simp only [List.length_cons] at h ⊢
    rw [records_length]
    nlinarith only [h]

private theorem init_eq (xs : List Column) :
    TM2.init (0 : Fin 2) (records xs) =
      (⟨some 0, default, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (records xs) []⟩ : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Local) := by
  have hs : Function.update (fun _ => []) (0 : Fin 2) (records xs) =
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (records xs) [] := by
    funext k
    fin_cases k <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair, Fin.ext_iff]
  change (⟨some 0, default, Function.update (fun _ => []) 0 (records xs)⟩ :
    TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Local) = _
  rw [hs]

private theorem final_eq (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] bits = Function.update (fun _ => []) (1 : Fin 2) bits := by
  funext k
  fin_cases k <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair, Fin.ext_iff]

theorem raw_machine :
    ∃ (q c : ℕ) (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))), 0 < c ∧ ∀ a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (input a b) (output a b)
        (c * (a.length + b.length + 1) ^ 2) (c * (a.length + b.length + 1) ^ 2) := by
  obtain ⟨q, M, C, hC, hM⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.raw_compiler program 0 1
  refine ⟨q, 40 * C, M, Nat.mul_pos (by decide) hC, ?_⟩
  intro a b
  let xs := columns a b
  have hr := source_run xs false []
  have hc := source_clock xs false []
  simp only [List.append_nil] at hr
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRun program _ ⟨some 0,
      default, _⟩ = _ at hr
  change Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program _ ⟨some 0, default, _⟩ ≤ _ at hc
  rw [final_eq, ← init_eq] at hr
  rw [← init_eq] at hc
  have he : (input a b).reverse = records xs := by simp [input, xs]
  have hraw := hM (input a b) (output a b) (xs.length + 1) default (by simpa only [he] using! hr)
  have hlen : xs.length ≤ a.length + b.length := columns_length a b
  have hi : 1 + (input a b).length ≤ 3 * (a.length + b.length + 1) := by
    simp only [input, List.length_reverse, records_length]
    have hh := columns_length a b
    omega
  have ho : 1 + (output a b).length ≤ 2 * (a.length + b.length + 1) := by
    have h := digits_length xs false
    change 1 + (digits false xs).length ≤ _
    omega
  have hs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program (xs.length + 1) (TM2.init 0 (input a b).reverse) ≤
      20 * (a.length + b.length + 1) ^ 2 := by
    rw [he]
    apply hc.trans
    simp only [List.length_nil, add_zero]
    have hh : xs.length ≤ a.length + b.length := hlen
    nlinarith
  have hb : C * ((1 + (input a b).length) ^ 2 +
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program (xs.length + 1) (TM2.init 0 (input a b).reverse) +
      (1 + (output a b).length) ^ 2) ≤ 40 * C * (a.length + b.length + 1) ^ 2 := by
    have hi2 := Nat.pow_le_pow_left hi 2
    have ho2 := Nat.pow_le_pow_left ho 2
    have hz : (1 + (input a b).length) ^ 2 +
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program (xs.length + 1) (TM2.init 0 (input a b).reverse) +
        (1 + (output a b).length) ^ 2 ≤ 40 * (a.length + b.length + 1) ^ 2 := by nlinarith
    exact (Nat.mul_le_mul_left C hz).trans_eq (by ring)
  exact Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hraw hb hb

theorem raw_adder :
    ∃ (q c : ℕ) (M : TM0.Machine Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Symbol (Fin (q + 1))), 0 < c ∧ ∀ a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits,
      ∃ result : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (input a b) result
          (c * (a.length + b.length + 1) ^ 2) (c * (a.length + b.length + 1) ^ 2) ∧
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue result = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b ∧
        result.length ≤ a.length + b.length + 1 := by
  obtain ⟨q, c, M, hc, hM⟩ := raw_machine
  refine ⟨q, c, M, hc, fun a b => ⟨output a b, hM a b, output_value a b, ?_⟩⟩
  exact (digits_length (columns a b) false).trans (Nat.add_le_add_right (columns_length a b) 1)

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidBinaryAddition
