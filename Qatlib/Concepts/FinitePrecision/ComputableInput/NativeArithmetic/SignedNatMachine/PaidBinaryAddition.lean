/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler

/-!
# Binary addition with explicit stack costs

`columns` aligns two binary words by padding missing bits with false. `records` encodes the
resulting columns, and `program` processes them using the full-adder functions `digit` and
`carry`.

`digits_value` proves the arithmetic meaning of the output. The source execution and clock
lemmas yield `raw_machine` and `raw_adder`, with quadratic bounds in the total operand length.

## Main statements

* `digits_value` and `output_value`: correctness of the binary sum.
* `source_run` and `source_clock`: source execution and its cost.
* `raw_adder`: a finite-state tape implementation with quadratic resource bounds.

For background on classical computation and resource bounds, see [KitaevShenVyalyi2002].

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Turing

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.PaidBinaryAddition

/-- A pair of Boolean operand bits forming one binary addition column. -/
abbrev Column := Bool × Bool
/-- Three Boolean registers holding the carry and the two current operand bits. -/
abbrev Local := Bool × Bool × Bool

/-- The sum bit of a binary full adder, computed as the exclusive-or of the two operand bits and
incoming carry. -/
def digit (a b c : Bool) : Bool := xor (xor a b) c
/-- The outgoing carry of a binary full adder, true exactly when at least two input bits are
true. -/
def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Encode each addition column as a true marker followed by its two bits, ending the sequence
with a false marker. -/
def records : List Column → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | [] => [false]
  | (a, b) :: rest => true :: a :: b :: records rest

/-- Compute sum digits from addition columns and an incoming carry, appending a final true bit
when needed. -/
def digits : Bool → List Column → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits
  | c, [] => if c then [true] else []
  | c, (a, b) :: rest => digit a b c :: digits (carry a b c) rest

/-- Align two binary words into columns, padding either exhausted operand with false bits. -/
def columns : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits → List Column
  | [], b => b.map (fun y => (false, y))
  | a, [] => a.map (fun x => (x, false))
  | a :: as, b :: bs => (a, b) :: columns as bs

/-- The reversed record encoding of the aligned operand columns. -/
def input (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits := (records (columns a b)).reverse
/-- The binary sum word obtained by processing the aligned columns with initial carry false. -/
def output (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits := digits false (columns a b)

/-- The record encoding of `xs` has length `3 * xs.length + 1`. -/
theorem records_length (xs : List Column) : (records xs).length = 3 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons p xs ih => cases p; simp only [records, List.length_cons, ih]; omega

/-- Processing `xs` produces at most `xs.length + 1` output bits, including a possible final
carry. -/
theorem digits_length (xs : List Column) (c : Bool) : (digits c xs).length ≤ xs.length + 1 := by
  induction xs generalizing c with
  | nil => cases c <;> decide
  | cons p xs ih => cases p; simp only [digits, List.length_cons]; exact Nat.add_le_add_right (ih _) 1

/-- The value of the sum digits equals the values of the two column projections plus the
incoming carry interpreted as zero or one. -/
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

/-- A word consisting entirely of false bits has binary value zero. -/
private theorem false_value (xs : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (xs.map (fun _ => false)) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue] using ih

/-- The two projections of the aligned columns retain the binary values of the original
operands. -/
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

/-- The number of aligned columns is at most the sum of the operand lengths. -/
theorem columns_length (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : (columns a b).length ≤ a.length + b.length := by
  induction a generalizing b with
  | nil => simp [columns]
  | cons x xs ih =>
    cases b with
    | nil => simp [columns]
    | cons y ys => simp only [columns, List.length_cons]; have h := ih ys; omega

/-- The binary value of `output a b` equals the sum of the binary values of `a` and `b`. -/
theorem output_value (a b : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (output a b) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b := by
  rw [output, digits_value, (columns_values a b).1, (columns_values a b).2]
  rfl

/-- The one-label stack program that consumes encoded addition columns, pushes sum digits, and
halts after handling the final carry. -/
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

/-- Updating input stack zero in a two-stack state preserves the output stack. -/
private theorem pair_input (a b c : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair a b) 0 c = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair c b := by
  funext k
  fin_cases k <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair, Fin.ext_iff]

/-- Updating output stack one in a two-stack state preserves the input stack. -/
private theorem pair_output (a b c : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Function.update (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair a b) 1 c = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair a c := by
  funext k
  fin_cases k <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair, Fin.ext_iff]

/-- One marked column is consumed in a machine step, pushing its sum digit and replacing the
incoming carry by the outgoing carry. -/
theorem column_step (a b c : Bool) (rest out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    TM2.step program ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (true :: a :: b :: rest) out⟩ =
      some ⟨some 0, (carry a b c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair rest (digit a b c :: out)⟩ := by
  simp [TM2.step, program, TM2.stepAux]

/-- The terminating false marker is consumed and the machine halts after pushing any final
carry. -/
theorem stop_step (c : Bool) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    TM2.step program ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [false] out⟩ =
      some ⟨none, default, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] (if c then true :: out else out)⟩ := by
  cases c <;> simp [TM2.step, program, TM2.stepAux]

/-- A column step has stack-clock cost `6 * rest.length + 2 * out.length + 19`. -/
theorem column_clock (a b c : Bool) (rest out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1
      ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair (true :: a :: b :: rest) out⟩ =
      6 * rest.length + 2 * out.length + 19 := by
  simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, TM2.step, program, TM2.stepAux]
  omega

/-- The terminating step has stack-clock cost at most `2 * out.length + 7`. -/
theorem stop_clock (c : Bool) (out : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock program 1 ⟨some 0, (c, false, false), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [false] out⟩ ≤
      2 * out.length + 7 := by
  cases c <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackRunClock,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackClock, TM2.step, program, TM2.stepAux]
  all_goals omega

/-- Processing the records of `xs` takes `xs.length + 1` steps and halts with the reversed
computed digits prepended to `out`. -/
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

/-- The stack-clock cost of processing `xs` is at most `20 * (xs.length + 1) * (xs.length +
out.length + 1)`. -/
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

/-- Initialization on the record word gives the initial control label, default registers, the
record input, and an empty output stack. -/
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

/-- A two-stack state with empty input is the all-empty state updated only at output stack one. -/
private theorem final_eq (bits : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair [] bits = Function.update (fun _ => []) (1 : Fin 2) bits := by
  funext k
  fin_cases k <;> simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackPair, Fin.ext_iff]

/-- There is a finite-state tape machine mapping `input a b` to `output a b`, with a uniform
positive quadratic bound for both resources in `Runs`. -/
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

/-- There is a finite-state tape machine producing the binary sum from encoded operand columns,
with quadratic bounds for both resources in `Runs` and output length at most `a.length +
b.length + 1`. -/
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
