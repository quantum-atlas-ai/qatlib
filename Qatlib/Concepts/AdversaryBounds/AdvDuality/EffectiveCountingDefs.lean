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

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped Classical BigOperators
open Qatlib.Concepts.CountingClasses.ClassTransport

def EcEncode (x : List Bool) : List Bool := x ++ [true]

@[simp] theorem EcEncode_length (x : List Bool) : (EcEncode x).length = x.length + 1 := by
  simp [EcEncode]

theorem EcEncode_injective : Function.Injective EcEncode := by
  intro x y h
  simpa [EcEncode] using h

theorem EcEncode_getD_zero (x : List Bool) :
    (EcEncode x).getD 0 false = true ↔ x = [] ∨ x.getD 0 false = true := by
  cases x with
  | nil => simp [EcEncode]
  | cons a l =>
    simp only [EcEncode, List.cons_append]
    simp

theorem EcEncode_getD_of_lt {x : List Bool} {i : ℕ} (hi : i < x.length) :
    (EcEncode x).getD i false = x.getD i false := by
  rw [EcEncode, List.getD_append x [true] false i hi]

def EcWitnessLen (p n : ℕ) : ℕ := p * (n + 1) ^ p + p

def EcBudget (c k : ℕ) (x : List Bool) : ℕ := c * (EcEncode x).length ^ k + c

def EcInP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ (ρ : ℕ → Bool) (x : List Bool),
      ccResult M ccZeroOracle ρ (EcEncode x) (EcBudget c k x)
        = some (if L x then true else false)

def EcInNP (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ∃ w : Fin (EcWitnessLen p x.length) → Bool,
        ccVerifies V c k (EcEncode x) (List.ofFn w) = true)

noncomputable def EcWitnessSet {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) :
    Set (Fin (EcWitnessLen p x.length) → Bool) :=
  fun w => ccVerifies V c k (EcEncode x) (List.ofFn w) = true

noncomputable def EcRelCount {L : ℕ} (R : Set (Fin L → Bool)) : ℕ :=
  (Finset.univ.filter (fun w : Fin L → Bool => R w)).card

noncomputable def EcWitnessCount {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) : ℕ :=
  EcRelCount (EcWitnessSet V c k p x)

def EcInSharpP (f : List Bool → ℕ) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool, f x = EcWitnessCount V c k p x

def EcInPP (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x ↔ 2 * ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x)
          > 2 ^ (EcBudget c k x))

def EcInFBPPNP (F : List Bool → List Bool) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q) (B : List Bool → Prop),
    EcInNP B ∧ CcPolyTime M c k ∧
      ∀ x : List Bool,
        3 * ccExactOutputCount M (ccOracleOf B) (EcEncode x) (EcBudget c k x) (F x)
          ≥ 2 * 2 ^ (EcBudget c k x)

def EcInPHLevel (lev : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ccAlt true (EcWitnessLen p x.length)
        (fun z => ccAccepts V c k z = true) lev (EcEncode x))

def EcInOraclePP (A : List Bool → Bool) (L : List Bool → Prop) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : List Bool,
      (L x ↔ 2 * ccAcceptCount M A (EcEncode x) (EcBudget c k x)
          > 2 ^ (EcBudget c k x))

def EcInOracleSigma (A : List Bool → Bool) (lev : ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (L x ↔ ccAlt true (EcWitnessLen p x.length)
        (fun z => ccOracleAccepts V A c k z = true) lev (EcEncode x))

noncomputable def EcOracleWitnessCount (A : List Bool → Bool) (p : ℕ) (x : List Bool) : ℕ :=
  EcRelCount (fun w : Fin (EcWitnessLen p x.length) → Bool =>
    A (EcEncode x ++ List.ofFn w) = true)

def EcInSharpPOracle (A : List Bool → Bool) (f : List Bool → ℕ) : Prop :=
  ∃ p : ℕ, ∀ x : List Bool, f x = EcOracleWitnessCount A p x

def EcInNPOracleSet (A : List Bool → Bool) (B : List Bool → Prop) : Prop :=
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : List Bool,
      (B x ↔ ∃ w : Fin (EcWitnessLen p x.length) → Bool,
        ccOracleVerifies V A c k (EcEncode x) (List.ofFn w) = true)

structure EcCharge where

  time : ℕ

  queries : ℕ

  queryBits : ℕ

  coins : ℕ

  outputBits : ℕ

def EcChargeOf {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : EcCharge where
  time := ccTime P A ρ x t
  queries := ccQueries P A ρ x t
  queryBits := ccQueryBits P A ρ x t
  coins := ccCoinsRead P A ρ x t
  outputBits := (ccOutput P A ρ x t).length

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

theorem EcCharge_queries_le_time {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) :
    (EcChargeOf P A ρ x t).queries ≤ (EcChargeOf P A ρ x t).time := by
  have h := EcCharge_sound P A ρ x t
  omega

theorem EcCharge_queries_le_half_time {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) :
    2 * (EcChargeOf P A ρ x t).queries ≤ (EcChargeOf P A ρ x t).time := by
  have h := EcCharge_sound P A ρ x t
  omega

theorem card_fin_fun_bool (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun]
  simp [Fintype.card_bool, Fintype.card_fin]

theorem card_fin_fun_fun_bool (a b : ℕ) :
    Fintype.card (Fin a → Fin b → Bool) = 2 ^ (a * b) := by
  rw [Fintype.card_fun, card_fin_fun_bool, Fintype.card_fin]
  have hpow : ((2 : ℕ) ^ b) ^ a = 2 ^ (b * a) := (Nat.pow_mul 2 b a).symm
  rw [hpow, Nat.mul_comm b a]

def EcHashSeed (L ℓ : ℕ) : Type := (Fin ℓ → Fin L → Bool) × (Fin ℓ → Bool)

instance (L ℓ : ℕ) : Fintype (EcHashSeed L ℓ) :=
  inferInstanceAs (Fintype ((Fin ℓ → Fin L → Bool) × (Fin ℓ → Bool)))

def ecZeroHashSeed (L ℓ : ℕ) : EcHashSeed L ℓ := (fun _ => (fun _ => false), fun _ => false)

instance (L ℓ : ℕ) : Nonempty (EcHashSeed L ℓ) := ⟨ecZeroHashSeed L ℓ⟩

theorem Fintype.card_ecHashSeed (L ℓ : ℕ) :
    Fintype.card (EcHashSeed L ℓ) = 2 ^ (ℓ * L + ℓ) := by
  change Fintype.card ((Fin ℓ → Fin L → Bool) × (Fin ℓ → Bool)) = 2 ^ (ℓ * L + ℓ)
  rw [Fintype.card_prod, card_fin_fun_fun_bool, card_fin_fun_bool, pow_add]

def EcHash {L ℓ : ℕ} (s : EcHashSeed L ℓ) (w : Fin L → Bool) : Fin ℓ → Bool :=
  ccHash s.1 s.2 w

def EcHashZero {L ℓ : ℕ} (s : EcHashSeed L ℓ) (w : Fin L → Bool) : Prop :=
  ∀ i : Fin ℓ, EcHash s w i = false

def EcHashSeedBits (L ℓ : ℕ) : ℕ := ℓ * L + ℓ

theorem Fintype.card_ecHashSeedBits (L ℓ : ℕ) :
    Fintype.card (Fin (EcHashSeedBits L ℓ) → Bool) = 2 ^ (ℓ * L + ℓ) := by
  rw [card_fin_fun_bool]
  rfl

noncomputable def EcRelFiberCount {L ℓ : ℕ} (R : Set (Fin L → Bool))
    (s : EcHashSeed L ℓ) : ℕ :=
  (Finset.univ.filter (fun w : Fin L → Bool => R w ∧ EcHashZero s w)).card

noncomputable def EcFiberCount {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool)
    (ℓ : ℕ) (s : EcHashSeed (EcWitnessLen p x.length) ℓ) : ℕ :=
  EcRelFiberCount (EcWitnessSet V c k p x) s

noncomputable def EcStockmeyerEstimate {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool)
    (ℓ : ℕ) (s : EcHashSeed (EcWitnessLen p x.length) ℓ) : ℕ :=
  2 ^ ℓ * EcFiberCount V c k p x ℓ s

noncomputable def EcStockmeyerScale {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) (ℓ : ℕ) : ℕ :=
  2 ^ ℓ * EcWitnessCount V c k p x

structure EcSampler (L : ℕ) (Out : Type) where

  O : (Fin L → Bool) → Out

noncomputable def EcSamplerProb {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) : ℝ :=
  (∑ r : Fin L → Bool, if Sam.O r = y then (1 : ℝ) else 0) / ((2 : ℕ) ^ L : ℝ)

theorem EcSamplerProb_numer {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    (∑ r : Fin L → Bool, if Sam.O r = y then (1 : ℝ) else 0)
      = ((Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card : ℝ) := by
  calc _ = ∑ r ∈ (Finset.univ.filter (fun r => Sam.O r = y)), (1 : ℝ) :=
      (Finset.sum_filter (s := Finset.univ) (p := fun r => Sam.O r = y)
        (f := fun _ => (1 : ℝ))).symm
    _ = ((Finset.univ.filter (fun r => Sam.O r = y)).card : ℝ) := by
      simp [Finset.sum_const]

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
