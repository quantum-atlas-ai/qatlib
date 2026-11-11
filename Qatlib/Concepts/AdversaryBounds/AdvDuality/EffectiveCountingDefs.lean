/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CountingClasses.ClassTransport.CountingComplexityDefs
import Mathlib.Data.List.GetD
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Definitions for effective counting and finite samplers

This module defines delimiter-encoded inputs, polynomial budgets, witness counts, and effective
decision and counting predicates for `CcProgram`. It also records execution charges and proves
that oracle queries and query bits are bounded by elapsed time.

`EcHashSeed` and `EcHash` specify finite Boolean hash data, while `EcSampler` represents a
deterministic function of a uniform finite Boolean seed. These definitions supply explicit
finite models for the computational notions discussed in [KitaevShenVyalyi2002].

## Main statements

* `EcInNP` and `EcInSharpP`: polynomial-verifier witness existence and witness counting.
* `EcCharge_sound`: query and query-bit charges are bounded by elapsed time.
* `Fintype.card_ecHashSeed`: the exact hash-seed cardinality.
* `EcSamplerProb_sum`: sampler output probabilities sum to one for a finite output type.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped Classical BigOperators
open Qatlib.Concepts.CountingClasses.ClassTransport

/-- Encode a Boolean input by appending a true delimiter bit. -/
def EcEncode (x : List Bool) : List Bool := x ++ [true]

/-- Appending the delimiter increases the input length by one. -/
@[simp] theorem EcEncode_length (x : List Bool) : (EcEncode x).length = x.length + 1 := by
  simp [EcEncode]

/-- The delimiter-extended Boolean input encoding is injective. -/
theorem EcEncode_injective : Function.Injective EcEncode := by
  intro x y h
  simpa [EcEncode] using h

/-- The first encoded bit is true exactly when the original input is empty or its first bit is
true. -/
theorem EcEncode_getD_zero (x : List Bool) :
    (EcEncode x).getD 0 false = true ↔ x = [] ∨ x.getD 0 false = true := by
  cases x with
  | nil => simp [EcEncode]
  | cons a l =>
    simp only [EcEncode, List.cons_append]
    simp

/-- Encoding preserves every bit at an index below the original input length. -/
theorem EcEncode_getD_of_lt {x : List Bool} {i : ℕ} (hi : i < x.length) :
    (EcEncode x).getD i false = x.getD i false := by
  rw [EcEncode, List.getD_append x [true] false i hi]

/-- The witness length `p * (n + 1) ^ p + p` for parameter `p` and input length `n`. -/
def EcWitnessLen (p n : ℕ) : ℕ := p * (n + 1) ^ p + p

/-- The time budget `c * (EcEncode x).length ^ k + c` for an encoded input. -/
def EcBudget (c k : ℕ) (x : List Bool) : ℕ := c * (EcEncode x).length ^ k + c

/-- The property of possessing a polynomial-time program deciding the language on encoded inputs
for every coin sequence with the zero oracle. -/
def EcInP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ (ρ : ℕ → Bool) (x : List Bool),
      ccResult M ccZeroOracle ρ (EcEncode x) (EcBudget c k x)
        = some (if L x then true else false)

/-- The property that language membership is equivalent to existence of a fixed
polynomial-length Boolean witness accepted by a polynomial-time verifier. -/
def EcInNP (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ∃ w : Fin (EcWitnessLen p x.length) → Bool,
        ccVerifies V c k (EcEncode x) (List.ofFn w) = true)

/-- The set of fixed-length Boolean witnesses accepted by the given verifier on the encoded
input. -/
noncomputable def EcWitnessSet {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) :
    Set (Fin (EcWitnessLen p x.length) → Bool) :=
  fun w => ccVerifies V c k (EcEncode x) (List.ofFn w) = true

/-- The number of Boolean words in a finite relation. -/
noncomputable def EcRelCount {L : ℕ} (R : Set (Fin L → Bool)) : ℕ :=
  (Finset.univ.filter (fun w : Fin L → Bool => R w)).card

/-- The number of fixed-length witnesses accepted by the given verifier on the encoded input. -/
noncomputable def EcWitnessCount {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) : ℕ :=
  EcRelCount (EcWitnessSet V c k p x)

/-- The property that a function equals a polynomial-time verifier's witness-count function. -/
def EcInSharpP (f : List Bool → ℕ) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool, f x = EcWitnessCount V c k p x

/-- The property that membership is decided by a polynomial-time program whose accepting coin
strings form a strict majority at the encoded-input budget. -/
def EcInPP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x ↔ 2 * ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x)
          > 2 ^ (EcBudget c k x))

/-- The property of computing the specified output on at least two thirds of budget-length coin
strings with a polynomial-time program and some effective NP oracle. -/
def EcInFBPPNP (F : List Bool → List Bool) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q) (B : List Bool → Prop),
    EcInNP B ∧ CcPolyTime M c k ∧
      ∀ x : List Bool,
        3 * ccExactOutputCount M (ccOracleOf B) (EcEncode x) (EcBudget c k x) (F x)
          ≥ 2 * 2 ^ (EcBudget c k x)

/-- The effective hierarchy predicate defined by `lev` alternating fixed-length witness blocks,
starting existentially, followed by a polynomial-time verifier. -/
def EcInPHLevel (lev : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ccAlt true (EcWitnessLen p x.length)
        (fun z => ccAccepts V c k z = true) lev (EcEncode x))

/-- The effective PP predicate with the supplied Boolean oracle, using a strict majority of
accepting coin strings. -/
def EcInOraclePP (A : List Bool → Bool) (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x ↔ 2 * ccAcceptCount M A (EcEncode x) (EcBudget c k x)
          > 2 ^ (EcBudget c k x))

/-- The effective alternating hierarchy predicate with the supplied Boolean oracle and `lev`
witness blocks starting existentially. -/
def EcInOracleSigma (A : List Bool → Bool) (lev : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ccAlt true (EcWitnessLen p x.length)
        (fun z => ccOracleAccepts V A c k z = true) lev (EcEncode x))

/-- The number of polynomial-length witnesses for which the supplied oracle returns true on the
encoded input concatenated with the witness. -/
noncomputable def EcOracleWitnessCount (A : List Bool → Bool) (p : ℕ) (x : List Bool) : ℕ :=
  EcRelCount (fun w : Fin (EcWitnessLen p x.length) → Bool =>
    A (EcEncode x ++ List.ofFn w) = true)

/-- The property that a function counts polynomial-length witnesses accepted directly by the
supplied oracle on the concatenated encoding. -/
def EcInSharpPOracle (A : List Bool → Bool) (f : List Bool → ℕ) : Prop :=
  ∃ p : ℕ, ∀ x : List Bool, f x = EcOracleWitnessCount A p x

/-- The property that membership in `B` is verified by a polynomial-time program with oracle `A`
and a polynomial-length Boolean witness. -/
def EcInNPOracleSet (A : List Bool → Bool) (B : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (B x ↔ ∃ w : Fin (EcWitnessLen p x.length) → Bool,
        ccOracleVerifies V A c k (EcEncode x) (List.ofFn w) = true)

/-- An execution-charge record containing elapsed time, query count, query-bit count, coin
count, and output length. -/
structure EcCharge where

  time : ℕ

  queries : ℕ

  queryBits : ℕ

  coins : ℕ

  outputBits : ℕ

/-- The charge record extracted from a program execution with the given oracle, coin sequence,
input, and step budget. -/
def EcChargeOf {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : EcCharge where
  time := ccTime P A ρ x t
  queries := ccQueries P A ρ x t
  queryBits := ccQueryBits P A ρ x t
  coins := ccCoinsRead P A ρ x t
  outputBits := (ccOutput P A ρ x t).length

/-- Twice the query count plus the query-bit count is at most the elapsed time. -/
theorem EcCharge_sound {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) :
    2 * (EcChargeOf P A ρ x t).queries + (EcChargeOf P A ρ x t).queryBits
      ≤ (EcChargeOf P A ρ x t).time := by
  induction t with
  | zero =>
    show 2 * (ccInit q x).queries + (ccInit q x).queryBits ≤ (ccInit q x).time
    rfl
  | succ n ih =>
    have hb : 2 * (ccRun P A ρ x n).queries + (ccRun P A ρ x n).queryBits
        ≤ (ccRun P A ρ x n).time := ih
    show 2 * (ccStep P A ρ (ccRun P A ρ x n)).queries
        + (ccStep P A ρ (ccRun P A ρ x n)).queryBits
        ≤ (ccStep P A ρ (ccRun P A ρ x n)).time
    cases h : P.states (ccRun P A ρ x n).state <;> simp [ccStep, h] <;> omega

/-- The query count is at most the elapsed time. -/
theorem EcCharge_queries_le_time {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) :
    (EcChargeOf P A ρ x t).queries ≤ (EcChargeOf P A ρ x t).time := by
  have h := EcCharge_sound P A ρ x t
  omega

/-- Twice the query count is at most the elapsed time. -/
theorem EcCharge_queries_le_half_time {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) :
    2 * (EcChargeOf P A ρ x t).queries ≤ (EcChargeOf P A ρ x t).time := by
  have h := EcCharge_sound P A ρ x t
  omega

/-- The type of length-`n` Boolean words has cardinality `2 ^ n`. -/
theorem card_fin_fun_bool (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun]
  simp [Fintype.card_bool, Fintype.card_fin]

/-- The type of `a`-by-`b` Boolean arrays has cardinality `2 ^ (a * b)`. -/
theorem card_fin_fun_fun_bool (a b : ℕ) :
    Fintype.card (Fin a → Fin b → Bool) = 2 ^ (a * b) := by
  rw [Fintype.card_fun, card_fin_fun_bool, Fintype.card_fin]
  have hpow : ((2 : ℕ) ^ b) ^ a = 2 ^ (b * a) := (Nat.pow_mul 2 b a).symm
  rw [hpow, Nat.mul_comm b a]

/-- A hash seed consisting of an `ℓ`-by-`L` Boolean matrix and a length-`ℓ` Boolean offset. -/
def EcHashSeed (L ℓ : ℕ) : Type := (Fin ℓ → Fin L → Bool) × (Fin ℓ → Bool)

instance (L ℓ : ℕ) : Fintype (EcHashSeed L ℓ) :=
  inferInstanceAs (Fintype ((Fin ℓ → Fin L → Bool) × (Fin ℓ → Bool)))

/-- The hash seed whose matrix and offset are identically false. -/
def ecZeroHashSeed (L ℓ : ℕ) : EcHashSeed L ℓ := (fun _ => (fun _ => false), fun _ => false)

instance (L ℓ : ℕ) : Nonempty (EcHashSeed L ℓ) := ⟨ecZeroHashSeed L ℓ⟩

/-- The hash-seed type has cardinality `2 ^ (ℓ * L + ℓ)`. -/
theorem Fintype.card_ecHashSeed (L ℓ : ℕ) :
    Fintype.card (EcHashSeed L ℓ) = 2 ^ (ℓ * L + ℓ) := by
  change Fintype.card ((Fin ℓ → Fin L → Bool) × (Fin ℓ → Bool)) = 2 ^ (ℓ * L + ℓ)
  rw [Fintype.card_prod, card_fin_fun_fun_bool, card_fin_fun_bool, pow_add]

/-- Apply the Boolean hash `ccHash` determined by the seed's matrix and offset. -/
def EcHash {L ℓ : ℕ} (s : EcHashSeed L ℓ) (w : Fin L → Bool) : Fin ℓ → Bool :=
  ccHash s.1 s.2 w

/-- The condition that every output bit of a seeded hash is false. -/
def EcHashZero {L ℓ : ℕ} (s : EcHashSeed L ℓ) (w : Fin L → Bool) : Prop :=
  ∀ i : Fin ℓ, EcHash s w i = false

/-- The number `ℓ * L + ℓ` of bits in a hash seed's matrix and offset. -/
def EcHashSeedBits (L ℓ : ℕ) : ℕ := ℓ * L + ℓ

/-- The Boolean seed-bit space has cardinality `2 ^ (ℓ * L + ℓ)`. -/
theorem Fintype.card_ecHashSeedBits (L ℓ : ℕ) :
    Fintype.card (Fin (EcHashSeedBits L ℓ) → Bool) = 2 ^ (ℓ * L + ℓ) := by
  rw [card_fin_fun_bool]
  rfl

/-- The number of words in a relation that hash to the all-false output under the given seed. -/
noncomputable def EcRelFiberCount {L ℓ : ℕ} (R : Set (Fin L → Bool))
    (s : EcHashSeed L ℓ) : ℕ :=
  (Finset.univ.filter (fun w : Fin L → Bool => R w ∧ EcHashZero s w)).card

/-- The number of accepted witnesses in the given hash's zero fiber. -/
noncomputable def EcFiberCount {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool)
    (ℓ : ℕ) (s : EcHashSeed (EcWitnessLen p x.length) ℓ) : ℕ :=
  EcRelFiberCount (EcWitnessSet V c k p x) s

/-- The zero-fiber witness count multiplied by `2 ^ ℓ`. -/
noncomputable def EcStockmeyerEstimate {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool)
    (ℓ : ℕ) (s : EcHashSeed (EcWitnessLen p x.length) ℓ) : ℕ :=
  2 ^ ℓ * EcFiberCount V c k p x ℓ s

/-- The full witness count multiplied by `2 ^ ℓ`. -/
noncomputable def EcStockmeyerScale {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) (ℓ : ℕ) : ℕ :=
  2 ^ ℓ * EcWitnessCount V c k p x

/-- A sampler represented by a function from length-`L` Boolean seeds to the output type. -/
structure EcSampler (L : ℕ) (Out : Type) where

  O : (Fin L → Bool) → Out

/-- The probability of output `y` under a uniform length-`L` Boolean seed. -/
noncomputable def EcSamplerProb {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) : ℝ :=
  (∑ r : Fin L → Bool, if Sam.O r = y then (1 : ℝ) else 0) / ((2 : ℕ) ^ L : ℝ)

/-- The numerator of a sampler output probability equals the real-valued cardinality of its
matching-seed set. -/
theorem EcSamplerProb_numer {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    (∑ r : Fin L → Bool, if Sam.O r = y then (1 : ℝ) else 0)
      = ((Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card : ℝ) := by
  calc _ = ∑ r ∈ (Finset.univ.filter (fun r => Sam.O r = y)), (1 : ℝ) :=
      (Finset.sum_filter (s := Finset.univ) (p := fun r => Sam.O r = y)
        (f := fun _ => (1 : ℝ))).symm
    _ = ((Finset.univ.filter (fun r => Sam.O r = y)).card : ℝ) := by
      simp [Finset.sum_const]

/-- For a finite output type, the sampler's output probabilities sum to one. -/
theorem EcSamplerProb_sum {L : ℕ} {Out : Type} [Fintype Out] (Sam : EcSampler L Out) :
    (∑ y : Out, EcSamplerProb Sam y) = 1 := by
  have hinner : ∀ r : Fin L → Bool,
      (∑ y : Out, if Sam.O r = y then (1 : ℝ) else 0) = 1 := by
    intro r
    have hite : (∑ y : Out, if Sam.O r = y then (1 : ℝ) else 0)
        = if Sam.O r ∈ (Finset.univ : Finset Out) then (1 : ℝ) else 0 :=
      Finset.sum_ite_eq (s := Finset.univ) (a := Sam.O r) (b := fun _ => (1 : ℝ))
    rw [hite]
    simp
  simp only [EcSamplerProb, div_eq_mul_inv]
  rw [← Finset.sum_mul (s := Finset.univ), Finset.sum_comm]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, card_fin_fun_bool]
  rw [nsmul_eq_mul, mul_one, Nat.cast_pow]
  simp

end Qatlib.Concepts.AdversaryBounds.AdvDuality
