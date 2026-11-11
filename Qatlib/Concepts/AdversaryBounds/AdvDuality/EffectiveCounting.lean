/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCountingDefs

/-!
# Effective witness counting and hash-fiber identities

This module proves elementary bridges between the effective decision and counting predicates,
gives a concrete head-bit language, and derives exact affine-hash seed and fiber counts. It also
expresses finite sampler probabilities and events as counts of uniform Boolean seeds.

The counting results include exact finite identities and an existence bound for a scaled zero
fiber. The computational background is the classical and quantum complexity framework of
[KitaevShenVyalyi2002].

## Main statements

* `clause1_complete`: collects effective-class inclusions, witness-count bridges, and query
  charges.
* `clause2_complete`: collects hash-seed cardinalities and zero-fiber bounds.
* `clause3_complete`: collects sampler probability, fiber, and event-count identities.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false

open Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCounting

open scoped Classical BigOperators
open Qatlib.Concepts.CountingClasses.ClassTransport

/-- The cardinality of a predicate-filtered finite type equals the sum of its natural-number
indicators. -/
theorem ecCard_eq_sum {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ a : α, if P a then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Filtering a finite type by a constant Boolean condition yields its full cardinality when
true and zero otherwise. -/
theorem ecCard_filter_const {α : Type} [Fintype α] (c0 : Bool) :
    (Finset.univ.filter (fun _ : α => c0 = true)).card
      = if c0 then Fintype.card α else 0 := by
  by_cases hc : c0 = true
  · simp [hc]
  · simp [hc]

/-- An effective NP language is characterized by positivity of some effective sharp-P
witness-count function. -/
theorem ecInNP_count_bridge {L : List Bool → Prop} (h : EcInNP L) :
    ∃ f : List Bool → ℕ, EcInSharpP f ∧ ∀ x : List Bool, (L x ↔ 0 < f x) := by
  rcases h with ⟨q, c, k, p, V, hpoly, hiff⟩
  refine ⟨fun x => EcWitnessCount V c k p x, ⟨q, c, k, p, V, hpoly, fun x => rfl⟩, fun x => ?_⟩
  rw [hiff x]
  constructor
  · rintro ⟨w, hw⟩
    exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
  · intro hpos
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩

/-- Every effective sharp-P function can be expressed by `EcInSharpPOracle` for a suitable
Boolean oracle. -/
theorem ecInSharpP_oracle_transport {f : List Bool → ℕ} (h : EcInSharpP f) :
    ∃ A : List Bool → Bool, EcInSharpPOracle A f := by
  rcases h with ⟨q, c, k, p, V, hpoly, heq⟩
  refine ⟨fun z => ccAccepts V c k z, ⟨p, fun x => ?_⟩⟩
  rw [heq]
  show EcWitnessCount V c k p x = EcOracleWitnessCount (fun z => ccAccepts V c k z) p x
  congr 1

/-- An effective PP language has a polynomial-time program whose normalized acceptance count is
greater than one half exactly on that language. -/
theorem ecInPP_mass {L : List Bool → Prop} (h : EcInPP L) :
    ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
      ∀ x : List Bool,
        (L x ↔ (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ)
            / ((2 : ℕ) : ℝ) ^ (EcBudget c k x) > 1 / 2) := by
  rcases h with ⟨q, c, k, M, hpoly, hiff⟩
  refine ⟨q, c, k, M, hpoly, fun x => ?_⟩
  rw [hiff x]
  have hpos : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ (EcBudget c k x) := by
    have hone : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hone]
    exact pow_pos (by norm_num) _
  have hle : (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ)
      ≤ ((2 : ℕ) : ℝ) ^ (EcBudget c k x) := by
    have hcard : ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x)
        ≤ Fintype.card (Fin (EcBudget c k x) → Bool) := Finset.card_le_univ _
    have hcard' : Fintype.card (Fin (EcBudget c k x) → Bool) = 2 ^ (EcBudget c k x) :=
      card_fin_fun_bool _
    have hcast : ((2 ^ (EcBudget c k x) : ℕ) : ℝ) = ((2 : ℕ) : ℝ) ^ (EcBudget c k x) := by
      rw [Nat.cast_pow]
    rw [← hcast, ← hcard']
    exact Nat.cast_le.2 hcard
  have hmul : (2 : ℝ) * (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ)
      = ((2 * ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    simp
  have hcast : ((2 ^ (EcBudget c k x) : ℕ) : ℝ) = ((2 : ℕ) : ℝ) ^ (EcBudget c k x) := by
    rw [Nat.cast_pow]
  constructor
  · intro hgt
    have hgt' : (2 : ℝ) * (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ)
        > ((2 : ℕ) : ℝ) ^ (EcBudget c k x) := by
      rw [hmul, ← hcast]
      exact Nat.cast_lt.mpr hgt
    have hT' : ((2 : ℕ) : ℝ) ^ (EcBudget c k x)
        < (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ) * 2 := by
      rw [← mul_comm] at hgt'
      exact hgt'
    have h2 : ((2 : ℕ) : ℝ) ^ (EcBudget c k x) / 2
        < (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ) := by
      exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr hT'
    have hhalf : (1 / 2) * ((2 : ℕ) : ℝ) ^ (EcBudget c k x)
        = ((2 : ℕ) : ℝ) ^ (EcBudget c k x) / 2 := by ring
    have h1 : (1 / 2) * ((2 : ℕ) : ℝ) ^ (EcBudget c k x)
        < (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ) := by
      rw [hhalf]
      exact h2
    exact (lt_div_iff₀ hpos).mpr h1
  · intro hgt
    have h1 : (1 / 2) * ((2 : ℕ) : ℝ) ^ (EcBudget c k x)
        < (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ) :=
      (lt_div_iff₀ hpos).mp hgt
    have hhalf : (1 / 2) * ((2 : ℕ) : ℝ) ^ (EcBudget c k x)
        = ((2 : ℕ) : ℝ) ^ (EcBudget c k x) / 2 := by ring
    have h2 : ((2 : ℕ) : ℝ) ^ (EcBudget c k x) / 2
        < (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ) := by
      rw [← hhalf]
      exact h1
    have hT' : ((2 : ℕ) : ℝ) ^ (EcBudget c k x)
        < (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ) * 2 := by
      exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mp h2
    have hgt' : (2 : ℝ) * (ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x) : ℝ)
        > ((2 : ℕ) : ℝ) ^ (EcBudget c k x) := by
      rw [mul_comm]
      exact hT'
    rw [hmul, ← hcast] at hgt'
    exact Nat.cast_lt.mp hgt'

/-- The acceptance count at time budget `t` is at most the number `2 ^ t` of Boolean coin
strings. -/
theorem ecAcceptCount_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (x : List Bool) (t : ℕ) :
    ccAcceptCount P A x t ≤ 2 ^ t := by
  have hcard : ccAcceptCount P A x t ≤ Fintype.card (Fin t → Bool) := Finset.card_le_univ _
  have hcard' : Fintype.card (Fin t → Bool) = 2 ^ t := card_fin_fun_bool t
  rw [← hcard']
  exact hcard

/-- Every language satisfying `EcInP` also satisfies `EcInNP`. -/
theorem ecInP_subset_ecInNP {L : List Bool → Prop} (h : EcInP L) : EcInNP L := by
  rcases h with ⟨q, c, k, M, hpoly, hdet⟩
  refine ⟨q, c, k, 0, M, hpoly, fun x => ?_⟩
  have hlen0 : EcWitnessLen 0 x.length = 0 := by
    show 0 * (x.length + 1) ^ 0 + 0 = 0
    simp
  rw [hlen0]
  constructor
  · intro hLx
    refine ⟨fun i : Fin 0 => (Fin.elim0 i : Bool), ?_⟩
    have hofn : List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool)) = [] := by
      have h1 : (List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool))).length = 0 := List.length_ofFn
      exact List.eq_nil_of_length_eq_zero h1
    show ccAccepts M c k (EcEncode x ++ List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool))) = true
    show decide (ccResult M ccZeroOracle ccDefaultCoin
        (EcEncode x ++ List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool)))
        (c * (EcEncode x ++ List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool))).length ^ k + c)
        = some true) = true
    rw [hofn, List.append_nil]
    show decide (ccResult M ccZeroOracle ccDefaultCoin (EcEncode x) (EcBudget c k x)
        = some true) = true
    rw [hdet ccDefaultCoin x]
    simp [hLx]
  · rintro ⟨w, hw⟩
    have hofn : List.ofFn w = [] := by
      have h1 : (List.ofFn w).length = 0 := List.length_ofFn
      exact List.eq_nil_of_length_eq_zero h1
    have h1 : ccAccepts M c k (EcEncode x ++ List.ofFn w) = true := by
      simpa only [ccVerifies] using hw
    rw [hofn, List.append_nil] at h1
    have hres : ccResult M ccZeroOracle ccDefaultCoin (EcEncode x) (EcBudget c k x) = some true := by
      have h2 := h1
      simp only [ccAccepts, ccOracleAccepts, decide_eq_true_eq] at h2
      exact h2
    have hdet' := hdet ccDefaultCoin x
    rw [hres] at hdet'
    by_cases hLx : L x
    · exact hLx
    · simp [hLx] at hdet'

/-- Every language satisfying `EcInP` also satisfies `EcInPP`. -/
theorem ecInP_subset_ecInPP {L : List Bool → Prop} (h : EcInP L) : EcInPP L := by
  rcases h with ⟨q, c, k, M, hpoly, hdet⟩
  refine ⟨q, c, k, M, hpoly, fun x => ?_⟩
  have hres : ∀ ω : Fin (EcBudget c k x) → Bool,
      ccResult M ccZeroOracle (ccCoinString ω) (EcEncode x) (EcBudget c k x)
        = some (if L x then true else false) := by
    intro ω
    exact hdet (ccCoinString ω) x
  have hcard : (Finset.univ.filter (fun ω : Fin (EcBudget c k x) → Bool =>
      ccResult M ccZeroOracle (ccCoinString ω) (EcEncode x) (EcBudget c k x) = some true)).card
      = if L x then 2 ^ (EcBudget c k x) else 0 := by
    rw [ecCard_eq_sum]
    calc (∑ ω : Fin (EcBudget c k x) → Bool,
        if ccResult M ccZeroOracle (ccCoinString ω) (EcEncode x) (EcBudget c k x) = some true
          then 1 else 0)
        = ∑ ω : Fin (EcBudget c k x) → Bool,
          if (if L x then true else false) = true then 1 else 0 := by
          simp_rw [hres]
          simp
      _ = if L x then ∑ ω : Fin (EcBudget c k x) → Bool, 1
          else ∑ ω : Fin (EcBudget c k x) → Bool, 0 := by
          by_cases hL : L x
          · simp [hL]
          · simp [hL]
      _ = if L x then 2 ^ (EcBudget c k x) else 0 := by
          by_cases hL : L x
          · simp [hL, Finset.sum_const]
          · simp [hL]
  have hacc : ccAcceptCount M ccZeroOracle (EcEncode x) (EcBudget c k x)
      = if L x then 2 ^ (EcBudget c k x) else 0 := by
    show (Finset.univ.filter (fun ω : Fin (EcBudget c k x) → Bool =>
      ccResult M ccZeroOracle (ccCoinString ω) (EcEncode x) (EcBudget c k x) = some true)).card
      = _
    exact hcard
  rw [hacc]
  have hpos : (0 : ℕ) < 2 ^ (EcBudget c k x) := by positivity
  constructor
  · intro hLx
    rw [if_pos hLx]
    omega
  · intro hgt
    by_cases hLx : L x
    · exact hLx
    · rw [if_neg hLx] at hgt
      omega

/-- Alternating quantification over zero-length Boolean witnesses leaves the underlying
predicate unchanged at every level. -/
private theorem ecAlt_zero_len (D : List Bool → Prop) :
    ∀ (lev : ℕ) (z : List Bool) (ex : Bool), ccAlt ex 0 D lev z ↔ D z := by
  intro lev
  induction lev with
  | zero =>
    intro z ex
    exact Iff.rfl
  | succ n ih =>
    intro z ex
    cases ex with
    | false =>
      simp [ccAlt]
      exact ih z true
    | true =>
      simp [ccAlt]
      exact ih z false

/-- The first effective polynomial-hierarchy level is equivalent to `EcInNP`. -/
theorem ecInPHLevel_one_iff {L : List Bool → Prop} : EcInPHLevel 1 L ↔ EcInNP L := by
  constructor
  · rintro ⟨q, c, k, p, V, hpoly, hiff⟩
    refine ⟨q, c, k, p, V, hpoly, fun x => ?_⟩
    rw [hiff x]
    simp only [ccAlt, ↓reduceIte]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      simpa [ccVerifies] using hw
    · rintro ⟨w, hw⟩
      exact ⟨w, by simpa [ccVerifies] using hw⟩
  · rintro ⟨q, c, k, p, V, hpoly, hiff⟩
    refine ⟨q, c, k, p, V, hpoly, fun x => ?_⟩
    rw [hiff x]
    simp only [ccAlt, ↓reduceIte]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, by simpa [ccVerifies] using hw⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, by simpa [ccVerifies] using hw⟩

/-- A language in the zeroth effective polynomial-hierarchy level lies in every effective level. -/
theorem ecInPHLevel_zero_subset {L : List Bool → Prop} {lev : ℕ}
    (h : EcInPHLevel 0 L) : EcInPHLevel lev L := by
  rcases h with ⟨q, c, k, p, V, hpoly, hiff⟩
  refine ⟨q, c, k, 0, V, hpoly, fun x => ?_⟩
  have hlen0 : EcWitnessLen 0 x.length = 0 := by
    show 0 * (x.length + 1) ^ 0 + 0 = 0
    simp
  rw [hlen0]
  have htarget : ccAlt true 0 (fun z => ccAccepts V c k z = true) lev (EcEncode x)
      ↔ (ccAccepts V c k (EcEncode x) = true) := by
    exact ecAlt_zero_len (fun z => ccAccepts V c k z = true) lev (EcEncode x) true
  rw [htarget]
  exact hiff x

/-- The first bit of the delimiter-extended input, defaulting to false. -/
def EcHeadBit (x : List Bool) : Bool := (EcEncode x).getD 0 false

/-- The language whose delimiter-extended input begins with a true bit. -/
def EcBadL : List Bool → Prop := fun x => EcHeadBit x = true

/-- The program that branches on the input head bit and then accepts or rejects accordingly. -/
def EcBadLProgram : CcProgram 2 where
  states := fun i =>
    if (i : ℕ) = 0 then CcAct.branch ⟨1, by omega⟩ ⟨2, by omega⟩
    else if (i : ℕ) = 1 then CcAct.accept
    else CcAct.reject

/-- The head-bit language contains exactly the empty input and the inputs whose first bit is
true. -/
theorem ecBadL_iff_old (x : List Bool) :
    EcBadL x ↔ (x = [] ∨ x.getD 0 false = true) := by
  rw [EcBadL, EcHeadBit, EcEncode_getD_zero]

/-- After one step on an encoded input, the head-bit program is in its accepting or rejecting
state according to `EcHeadBit`, with the displayed unchanged tape and resource counters. -/
private theorem ecBadL_run1 {A : List Bool → Bool} {ρ : ℕ → Bool} {x : List Bool} :
    ccRun EcBadLProgram A ρ (EcEncode x) 1
      = { state := if EcHeadBit x then ⟨1, by omega⟩ else ⟨2, by omega⟩,
          tape := fun i => (EcEncode x).getD i false,
          head := 0, query := [], coinIdx := 0,
          time := 1, queries := 0, queryBits := 0, coins := 0 } := by
  show ccStep EcBadLProgram A ρ (ccInit 2 (EcEncode x)) = _
  simp [ccStep, ccInit, EcBadLProgram, EcHeadBit]

/-- After two steps on an encoded input, the head-bit program returns the value of `EcHeadBit`. -/
private theorem ecBadL_result2 {A : List Bool → Bool} {ρ : ℕ → Bool} {x : List Bool} :
    ccResult EcBadLProgram A ρ (EcEncode x) 2
      = some (if EcHeadBit x then true else false) := by
  have hrun2 : ccRun EcBadLProgram A ρ (EcEncode x) 2
      = ccStep EcBadLProgram A ρ (ccRun EcBadLProgram A ρ (EcEncode x) 1) := rfl
  simp only [ccResult]
  rw [hrun2, ecBadL_run1]
  by_cases hbit : EcHeadBit x = true
  · rw [if_pos hbit]
    simp [EcBadLProgram, ccStep]
    exact hbit
  · rw [if_neg hbit]
    simp [EcBadLProgram, ccStep]
    exact Bool.eq_false_of_not_eq_true hbit

/-- The head-bit program terminates within the constant polynomial budget two and uses at most
that much time. -/
private theorem ecBadL_poly {A : List Bool → Bool} {ρ : ℕ → Bool} (x : List Bool) :
    ccResult EcBadLProgram A ρ x (1 * x.length ^ 0 + 1) ≠ none ∧
      ccTime EcBadLProgram A ρ x (1 * x.length ^ 0 + 1) ≤ 1 * x.length ^ 0 + 1 := by
  have hlen : x.length ^ 0 = 1 := by simp
  rw [hlen]
  have hrun1 : ccRun EcBadLProgram A ρ x 1
      = { state := if x.getD 0 false then ⟨1, by omega⟩ else ⟨2, by omega⟩,
          tape := fun i => x.getD i false,
          head := 0, query := [], coinIdx := 0,
          time := 1, queries := 0, queryBits := 0, coins := 0 } := by
    show ccStep EcBadLProgram A ρ (ccInit 2 x) = _
    simp [ccStep, ccInit, EcBadLProgram]
  have hrun2 : ccRun EcBadLProgram A ρ x 2
      = ccStep EcBadLProgram A ρ (ccRun EcBadLProgram A ρ x 1) := rfl
  simp only [ccResult, ccTime]
  rw [hrun2, hrun1]
  by_cases hbit : x.getD 0 false = true
  · rw [if_pos hbit]
    simp [EcBadLProgram, ccStep]
  · rw [if_neg hbit]
    simp [EcBadLProgram, ccStep]

/-- The head-bit language satisfies `EcInNP`. -/
theorem ecBadL_in_ecInNP : EcInNP EcBadL := by
  refine ⟨2, 1, 0, 0, EcBadLProgram, ?_, fun x => ?_⟩
  · intro A ρ x
    exact ecBadL_poly x
  · have hlen0 : EcWitnessLen 0 x.length = 0 := by
      show 0 * (x.length + 1) ^ 0 + 0 = 0
      simp
    rw [hlen0]
    constructor
    · intro hLx
      refine ⟨fun i : Fin 0 => (Fin.elim0 i : Bool), ?_⟩
      have hofn : List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool)) = [] := by
        have h1 : (List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool))).length = 0 :=
          List.length_ofFn
        exact List.eq_nil_of_length_eq_zero h1
      show ccAccepts EcBadLProgram 1 0
          (EcEncode x ++ List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool))) = true
      show decide (ccResult EcBadLProgram ccZeroOracle ccDefaultCoin
          (EcEncode x ++ List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool)))
          (1 * (EcEncode x ++ List.ofFn (fun i : Fin 0 => (Fin.elim0 i : Bool))).length ^ 0 + 1)
          = some true) = true
      rw [hofn, List.append_nil]
      show decide (ccResult EcBadLProgram ccZeroOracle ccDefaultCoin (EcEncode x)
          (1 * (EcEncode x).length ^ 0 + 1) = some true) = true
      rw [show 1 * (EcEncode x).length ^ 0 + 1 = 2 by simp]
      have hres := ecBadL_result2 (A := ccZeroOracle) (ρ := ccDefaultCoin) (x := x)
      rw [hres]
      simp only [decide_eq_true_eq, Option.some.injEq]
      by_cases hbit : EcHeadBit x = true
      · rw [if_pos hbit]
      · rw [if_neg hbit]
        exact absurd hLx hbit
    · rintro ⟨w, hw⟩
      have hofn : List.ofFn w = [] := by
        have h1 : (List.ofFn w).length = 0 := List.length_ofFn
        exact List.eq_nil_of_length_eq_zero h1
      have h1 : ccAccepts EcBadLProgram 1 0 (EcEncode x ++ List.ofFn w) = true := by
        simpa only [ccVerifies] using hw
      rw [hofn, List.append_nil] at h1
      have h2 := h1
      simp only [ccAccepts, ccOracleAccepts, decide_eq_true_eq] at h2
      rw [show 1 * (EcEncode x).length ^ 0 + 1 = 2 by simp] at h2
      have hres := ecBadL_result2 (A := ccZeroOracle) (ρ := ccDefaultCoin) (x := x)
      rw [hres] at h2
      simp only [Option.some.injEq] at h2
      by_cases hbit : EcHeadBit x = true
      · rw [EcBadL]
        exact hbit
      · rw [if_neg hbit] at h2
        simp at h2

/-- The exclusive-or of two Booleans is false exactly when they are equal. -/
private theorem bool_xor_eq_false (u v : Bool) : Bool.xor u v = false ↔ u = v := by
  cases u <;> cases v <;> simp [Bool.xor]

/-- A seed hashes a word to zero exactly when each offset bit equals the corresponding Boolean
matrix-row sum against that word. -/
private theorem ecHashZero_iff {L ℓ : ℕ} (mat : Fin ℓ → Fin L → Bool) (off : Fin ℓ → Bool)
    (w : Fin L → Bool) :
    EcHashZero (mat, off) w ↔ ∀ i : Fin ℓ, off i = ∑ j, (mat i j && w j) := by
  constructor
  · intro h i
    have hx := h i
    have hxor : Bool.xor (∑ j, (mat i j && w j)) (off i) = false := by
      simpa [EcHash, ccHash] using hx
    exact (Iff.mp (bool_xor_eq_false (∑ j, (mat i j && w j)) (off i)) hxor).symm
  · intro h i
    have hxor : Bool.xor (∑ j, (mat i j && w j)) (off i) = false := by
      have huv : (∑ j, (mat i j && w j)) = off i := by rw [h i]
      exact Iff.mpr (bool_xor_eq_false (∑ j, (mat i j && w j)) (off i)) huv
    simpa [EcHash, ccHash] using hxor

/-- For a fixed length-`L` word, exactly `2 ^ (ℓ * L)` seeds of output length `ℓ` hash it to
zero. -/
theorem ecHashZero_seed_count {L ℓ : ℕ} (w : Fin L → Bool) :
    (Finset.univ.filter (fun s : EcHashSeed L ℓ => EcHashZero s w)).card = 2 ^ (ℓ * L) := by
  have hone : ∀ (mat : Fin ℓ → Fin L → Bool),
      (∑ off : Fin ℓ → Bool,
        if ∀ i : Fin ℓ, off i = ∑ j, (mat i j && w j) then 1 else 0) = 1 := by
    intro mat
    set g : Fin ℓ → Bool := fun i => ∑ j, (mat i j && w j) with hg
    have hconv : (∑ off : Fin ℓ → Bool, if ∀ i : Fin ℓ, off i = g i then 1 else 0)
        = (∑ off : Fin ℓ → Bool, if off = g then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro off _
      by_cases hc : ∀ i : Fin ℓ, off i = g i
      · have ho : off = g := funext hc
        simp [ho]
      · have ho : off ≠ g := (funext_iff.not).mpr hc
        simp [hc, ho]
    rw [hconv]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin ℓ → Bool)) g (fun _ => 1)]
    simp
  rw [ecCard_eq_sum]
  calc (∑ s : EcHashSeed L ℓ, if EcHashZero s w then 1 else 0)
      = ∑ mat : Fin ℓ → Fin L → Bool, ∑ off : Fin ℓ → Bool,
          if EcHashZero (mat, off) w then 1 else 0 := Fintype.sum_prod_type _
    _ = ∑ mat : Fin ℓ → Fin L → Bool, ∑ off : Fin ℓ → Bool,
          if ∀ i : Fin ℓ, off i = ∑ j, (mat i j && w j) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro mat _
        apply Finset.sum_congr rfl
        intro off _
        simp only [ecHashZero_iff]
    _ = ∑ mat : Fin ℓ → Fin L → Bool, 1 := by
        apply Finset.sum_congr rfl
        intro mat _
        rw [hone mat]
    _ = 2 ^ (ℓ * L) := by
        have hpow : ((2 : ℕ) ^ L) ^ ℓ = 2 ^ (L * ℓ) := (Nat.pow_mul 2 L ℓ).symm
        have hcard : Fintype.card (Fin ℓ → Fin L → Bool) = 2 ^ (L * ℓ) := by
          rw [Fintype.card_fun, card_fin_fun_bool, Fintype.card_fin, hpow]
        simp [Finset.sum_const, hcard, Nat.mul_comm]

/-- The sum of zero-hash indicators over all seeds equals `2 ^ (ℓ * L)` for every fixed word. -/
theorem ecHashZero_seed_sum {L ℓ : ℕ} (w : Fin L → Bool) :
    (∑ s : EcHashSeed L ℓ, if EcHashZero s w then 1 else 0) = 2 ^ (ℓ * L) := by
  rw [← ecCard_eq_sum]
  exact ecHashZero_seed_count w

/-- The relation count equals the sum of its membership indicators over all Boolean words. -/
theorem ecRelCount_eq_sum {L : ℕ} (R : Set (Fin L → Bool)) :
    EcRelCount R = ∑ w : Fin L → Bool, if R w then 1 else 0 := by
  rw [EcRelCount, ecCard_eq_sum]

/-- The zero-fiber count equals the sum of indicators for words belonging to the relation and
hashing to zero. -/
theorem ecRelFiberCount_eq_sum {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) :
    EcRelFiberCount R s = ∑ w : Fin L → Bool, if R w ∧ EcHashZero s w then 1 else 0 := by
  unfold EcRelFiberCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : R w ∧ EcHashZero s w <;> simp [h]

/-- Summing the zero-fiber counts over all seeds gives the relation count multiplied by `2 ^ (ℓ
* L)`. -/
theorem ecRelFiberCount_sum {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ∑ s : EcHashSeed L ℓ, EcRelFiberCount R s = EcRelCount R * 2 ^ (ℓ * L) := by
  have h2 : ∀ s : EcHashSeed L ℓ,
      EcRelFiberCount R s = ∑ w : Fin L → Bool, if R w ∧ EcHashZero s w then 1 else 0 := by
    intro s
    exact ecRelFiberCount_eq_sum R s
  calc (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s)
      = ∑ s : EcHashSeed L ℓ, ∑ w : Fin L → Bool, if R w ∧ EcHashZero s w then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro s _
        rw [h2 s]
    _ = ∑ w : Fin L → Bool, ∑ s : EcHashSeed L ℓ, if R w ∧ EcHashZero s w then 1 else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ w : Fin L → Bool, (if R w then 1 else 0) * 2 ^ (ℓ * L) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : R w
        · have hzero : (∑ s : EcHashSeed L ℓ, if EcHashZero s w then 1 else 0) = 2 ^ (ℓ * L) :=
            ecHashZero_seed_sum w
          have hconv : (∑ s : EcHashSeed L ℓ, if R w ∧ EcHashZero s w then 1 else 0)
              = ∑ s : EcHashSeed L ℓ, if EcHashZero s w then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro s _
            simp [hw]
          rw [hconv, hzero, if_pos hw, Nat.one_mul]
        · rw [if_neg hw, Nat.zero_mul]
          apply Finset.sum_eq_zero
          intro s _
          rw [if_neg (fun h => absurd h.1 hw)]
    _ = (∑ w : Fin L → Bool, if R w then 1 else 0) * 2 ^ (ℓ * L) := by
        rw [Finset.sum_mul]
    _ = EcRelCount R * 2 ^ (ℓ * L) := by rw [ecRelCount_eq_sum]

/-- Summing witness zero-fiber counts over all seeds gives the witness count multiplied by `2 ^
(ℓ * EcWitnessLen p x.length)`. -/
theorem ecFiberCount_sum {q : ℕ} (V : CcProgram q) (c k p : ℕ) (x : List Bool) (ℓ : ℕ) :
    ∑ s : EcHashSeed (EcWitnessLen p x.length) ℓ, EcFiberCount V c k p x ℓ s
      = EcWitnessCount V c k p x * 2 ^ (ℓ * EcWitnessLen p x.length) := by
  have h := ecRelFiberCount_sum (L := EcWitnessLen p x.length) (ℓ := ℓ)
    (EcWitnessSet V c k p x)
  have hcount : EcRelCount (EcWitnessSet V c k p x) = EcWitnessCount V c k p x := by
    rfl
  rw [hcount] at h
  exact h

/-- If a relation has count zero, every hash zero fiber also has count zero. -/
theorem ecRelFiberCount_zero {L ℓ : ℕ} {R : Set (Fin L → Bool)} (hR : EcRelCount R = 0)
    (s : EcHashSeed L ℓ) : EcRelFiberCount R s = 0 := by
  have hR' : (Finset.univ.filter (fun w : Fin L → Bool => R w)).card = 0 := by
    unfold EcRelCount at hR
    exact hR
  have : ∀ w : Fin L → Bool, ¬ (R w) := by
    intro w hwR
    have hpos : 0 < EcRelCount R := by
      exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwR⟩⟩
    omega
  have hle : (Finset.univ.filter (fun w : Fin L → Bool => R w ∧ EcHashZero s w)).card
      ≤ (Finset.univ.filter (fun w : Fin L → Bool => R w)).card := by
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.1⟩
  unfold EcRelFiberCount
  exact le_antisymm (hle.trans hR'.le) (Nat.zero_le _)

/-- Every hash zero-fiber count is at most the full relation count. -/
theorem ecRelFiberCount_le {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) :
    EcRelFiberCount R s ≤ EcRelCount R := by
  have hle : (Finset.univ.filter (fun w : Fin L → Bool => R w ∧ EcHashZero s w)).card
      ≤ (Finset.univ.filter (fun w : Fin L → Bool => R w)).card := by
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.1⟩
  unfold EcRelFiberCount EcRelCount
  exact hle

/-- Some seed has scaled zero-fiber count at least the relation count and at most `2 ^ ℓ` times
that count. -/
theorem ecRelFiberCount_best {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ∃ s : EcHashSeed L ℓ,
      EcRelCount R ≤ 2 ^ ℓ * EcRelFiberCount R s ∧
        2 ^ ℓ * EcRelFiberCount R s ≤ 2 ^ ℓ * EcRelCount R := by
  have hne : (Finset.univ.image (fun s : EcHashSeed L ℓ => EcRelFiberCount R s)).Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  have hle : ∀ s : EcHashSeed L ℓ, EcRelFiberCount R s
      ≤ (Finset.univ.image (fun s : EcHashSeed L ℓ => EcRelFiberCount R s)).max' hne := by
    intro s
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
  obtain ⟨s0, hs0⟩ : ∃ s0 : EcHashSeed L ℓ,
      (Finset.univ.image (fun s : EcHashSeed L ℓ => EcRelFiberCount R s)).max' hne
        = EcRelFiberCount R s0 := by
    have hmem := Finset.max'_mem _ hne
    obtain ⟨s0, hs0, hval⟩ := Finset.mem_image.mp hmem
    exact ⟨s0, hval.symm⟩
  have hsum : (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s)
      ≤ Fintype.card (EcHashSeed L ℓ)
          * (Finset.univ.image (fun s : EcHashSeed L ℓ => EcRelFiberCount R s)).max' hne := by
    calc (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s)
        ≤ ∑ s : EcHashSeed L ℓ, (Finset.univ.image
            (fun t : EcHashSeed L ℓ => EcRelFiberCount R t)).max' hne :=
          Finset.sum_le_sum fun s _ => hle s
      _ = Fintype.card (EcHashSeed L ℓ)
          * (Finset.univ.image (fun s : EcHashSeed L ℓ => EcRelFiberCount R s)).max' hne := by
          simp [Finset.sum_const, Finset.card_univ]
  have h1 : EcRelCount R * 2 ^ (ℓ * L)
      ≤ Fintype.card (EcHashSeed L ℓ)
          * (Finset.univ.image (fun s : EcHashSeed L ℓ => EcRelFiberCount R s)).max' hne := by
    rw [← ecRelFiberCount_sum R]
    exact hsum
  rw [Fintype.card_ecHashSeed L ℓ] at h1
  have h2 : EcRelCount R * 2 ^ (ℓ * L) ≤ (2 ^ ℓ * EcRelFiberCount R s0) * 2 ^ (ℓ * L) := by
    rw [show (2 ^ ℓ * EcRelFiberCount R s0) * 2 ^ (ℓ * L)
      = 2 ^ (ℓ * L + ℓ) * EcRelFiberCount R s0 by ring]
    rw [show EcRelFiberCount R s0
      = (Finset.univ.image (fun s : EcHashSeed L ℓ => EcRelFiberCount R s)).max' hne from hs0.symm]
    exact h1
  have h3 : EcRelCount R ≤ 2 ^ ℓ * EcRelFiberCount R s0 := by
    exact Nat.le_of_mul_le_mul_right h2 (by positivity)
  refine ⟨s0, h3, ?_⟩
  have hle' : EcRelFiberCount R s0 ≤ EcRelCount R := ecRelFiberCount_le R s0
  exact Nat.mul_le_mul_left (2 ^ ℓ) hle'

/-- The set of Boolean seeds on which the sampler outputs `y`. -/
def EcSamplerSeedSet {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    Set (Fin L → Bool) := fun r => Sam.O r = y

/-- A sampler's output probability is its matching-seed count divided by `2 ^ L`. -/
theorem ecSamplerProb_count {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    EcSamplerProb Sam y = ((Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card : ℝ)
      / ((2 : ℕ) ^ L : ℝ) := by
  rw [EcSamplerProb, EcSamplerProb_numer]

/-- The relation count of a sampler output's seed set equals its matching-seed cardinality. -/
theorem ecSamplerSeedSet_card {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    EcRelCount (EcSamplerSeedSet Sam y)
      = (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card := by
  unfold EcRelCount EcSamplerSeedSet
  rfl

/-- The sum of sampler-output zero-fiber counts over all seeds equals its matching-seed count
multiplied by `2 ^ (ℓ * L)`. -/
theorem ecSampler_stockmeyer {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) (ℓ : ℕ) :
    ∑ s : EcHashSeed L ℓ, EcRelFiberCount (EcSamplerSeedSet Sam y) s
      = (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card * 2 ^ (ℓ * L) := by
  have h := ecRelFiberCount_sum (L := L) (ℓ := ℓ) (EcSamplerSeedSet Sam y)
  rw [ecSamplerSeedSet_card] at h
  exact h

/-- For every sampler output, some hash seed has scaled zero-fiber count between its
matching-seed count and `2 ^ ℓ` times that count. -/
theorem ecSampler_multiplicative {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out)
    (ℓ : ℕ) :
    ∃ s : EcHashSeed L ℓ,
      (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card
          ≤ 2 ^ ℓ * EcRelFiberCount (EcSamplerSeedSet Sam y) s
        ∧ 2 ^ ℓ * EcRelFiberCount (EcSamplerSeedSet Sam y) s
          ≤ 2 ^ ℓ * (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card := by
  obtain ⟨s, h1, h2⟩ := ecRelFiberCount_best (EcSamplerSeedSet Sam y)
  rw [ecSamplerSeedSet_card] at h1 h2
  exact ⟨s, h1, h2⟩

/-- The number of seeds producing an event equals the sum of output-fiber counts over outputs
satisfying that event. -/
theorem ecSamplerEventCount {L : ℕ} {Out : Type} [Fintype Out] (Sam : EcSampler L Out)
    (Ev : Out → Bool) :
    (∑ r : Fin L → Bool, if Ev (Sam.O r) = true then 1 else 0)
      = ∑ y : Out, if Ev y = true then
          (∑ r : Fin L → Bool, if Sam.O r = y then 1 else 0) else 0 := by
  calc (∑ r : Fin L → Bool, if Ev (Sam.O r) = true then 1 else 0)
      = ∑ r : Fin L → Bool, ∑ y : Out,
          if Sam.O r = y then (if Ev y = true then 1 else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_eq_single (Sam.O r)]
        · simp
        · intro b _ hne
          have hne' : ¬ (Sam.O r = b) := fun h => hne h.symm
          simp [hne']
        · simp
    _ = ∑ y : Out, ∑ r : Fin L → Bool,
          if Sam.O r = y then (if Ev y = true then 1 else 0) else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ y : Out, if Ev y = true then
          (∑ r : Fin L → Bool, if Sam.O r = y then 1 else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hE : Ev y = true
        · simp only [hE, if_pos]
        · simp [hE]

/-- The counts of seeds satisfying an event and its complement sum to the full seed-space
cardinality. -/
theorem ecSamplerBadEventMass {L : ℕ} {Out : Type} [Fintype Out] (Sam : EcSampler L Out)
    (Ev : Out → Bool) :
    (∑ r : Fin L → Bool, if ¬ (Ev (Sam.O r) = true) then 1 else 0)
      + (∑ r : Fin L → Bool, if Ev (Sam.O r) = true then 1 else 0)
        = (Finset.univ : Finset (Fin L → Bool)).card := by
  rw [← Finset.sum_add_distrib]
  calc (∑ r : Fin L → Bool, ((if ¬ (Ev (Sam.O r) = true) then 1 else 0)
      + (if Ev (Sam.O r) = true then 1 else 0)))
      = ∑ r : Fin L → Bool, 1 := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hE : Ev (Sam.O r) = true
        · simp [hE]
        · simp [hE]
    _ = (Finset.univ : Finset (Fin L → Bool)).card := by
        simp [Finset.sum_const, Finset.card_univ]

/-- The effective decision and counting predicates satisfy the displayed witness bridges,
inclusions, hierarchy identities, and query-charge bounds, and the explicit head-bit
language is in effective NP. -/
theorem clause1_complete :
    (∀ (L : List Bool → Prop), EcInNP L → ∃ f : List Bool → ℕ, EcInSharpP f ∧
        ∀ x : List Bool, (L x ↔ 0 < f x))
    ∧ (∀ (f : List Bool → ℕ), EcInSharpP f → ∃ A : List Bool → Bool, EcInSharpPOracle A f)
    ∧ (∀ (L : List Bool → Prop), EcInP L → EcInNP L)
    ∧ (∀ (L : List Bool → Prop), EcInP L → EcInPP L)
    ∧ (∀ (L : List Bool → Prop), EcInPHLevel 1 L ↔ EcInNP L)
    ∧ (∀ (L : List Bool → Prop) (lev : ℕ), EcInPHLevel 0 L → EcInPHLevel lev L)
    ∧ (∀ (q : ℕ) (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool)
        (t : ℕ), 2 * (EcChargeOf P A ρ x t).queries + (EcChargeOf P A ρ x t).queryBits
          ≤ (EcChargeOf P A ρ x t).time)
    ∧ (∀ (q : ℕ) (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool)
        (t : ℕ), 2 * (EcChargeOf P A ρ x t).queries ≤ (EcChargeOf P A ρ x t).time)
    ∧ EcInNP EcBadL
    ∧ (∀ x : List Bool, EcBadL x ↔ (x = [] ∨ x.getD 0 false = true)) := by
  refine ⟨fun L => ecInNP_count_bridge, fun f => ecInSharpP_oracle_transport,
    fun L => ecInP_subset_ecInNP, fun L => ecInP_subset_ecInPP, fun L => ecInPHLevel_one_iff,
    fun L lev => ecInPHLevel_zero_subset, ?_, ?_, ecBadL_in_ecInNP, ecBadL_iff_old⟩
  · intro q P A ρ x t
    exact EcCharge_sound P A ρ x t
  · intro q P A ρ x t
    exact EcCharge_queries_le_half_time P A ρ x t

/-- The affine-hash family has the stated seed cardinalities, exact zero-hash and fiber sums,
and an existing seed with the displayed scaled-fiber bounds; each fiber is bounded by the
relation count and vanishes when that count is zero. -/
theorem clause2_complete :
    (∀ (L ℓ : ℕ) (w : Fin L → Bool),
        (Finset.univ.filter (fun s : EcHashSeed L ℓ => EcHashZero s w)).card = 2 ^ (ℓ * L))
    ∧ (∀ (L ℓ : ℕ) (R : Set (Fin L → Bool)),
        ∑ s : EcHashSeed L ℓ, EcRelFiberCount R s = EcRelCount R * 2 ^ (ℓ * L))
    ∧ (∀ (L ℓ : ℕ) (R : Set (Fin L → Bool)),
        ∃ s : EcHashSeed L ℓ, EcRelCount R ≤ 2 ^ ℓ * EcRelFiberCount R s
          ∧ 2 ^ ℓ * EcRelFiberCount R s ≤ 2 ^ ℓ * EcRelCount R)
    ∧ (∀ (L ℓ : ℕ) (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ),
        EcRelFiberCount R s ≤ EcRelCount R)
    ∧ (∀ (L ℓ : ℕ) (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ),
        EcRelCount R = 0 → EcRelFiberCount R s = 0)
    ∧ (∀ (L ℓ : ℕ), Fintype.card (EcHashSeed L ℓ) = 2 ^ (ℓ * L + ℓ))
    ∧ (∀ (L ℓ : ℕ), Fintype.card (Fin (EcHashSeedBits L ℓ) → Bool) = 2 ^ (ℓ * L + ℓ)) := by
  refine ⟨fun L ℓ w => ecHashZero_seed_count w, fun L ℓ R => ecRelFiberCount_sum R, ?_,
    fun L ℓ R s => ecRelFiberCount_le R s, fun L ℓ R s hR => ecRelFiberCount_zero hR s,
    fun L ℓ => Fintype.card_ecHashSeed L ℓ, fun L ℓ => Fintype.card_ecHashSeedBits L ℓ⟩
  intro L ℓ R
  exact ecRelFiberCount_best R

/-- Finite sampler probabilities are normalized output-fiber counts, and their hash fibers
satisfy the displayed sum and existence bounds. Event counts decompose over outputs, and
complementary event counts partition the seed space. -/
theorem clause3_complete :
    (∀ (L : ℕ) (Out : Type) (Sam : EcSampler L Out) (y : Out),
        EcSamplerProb Sam y
          = ((Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card : ℝ)
            / ((2 : ℕ) ^ L : ℝ))
    ∧ (∀ (L : ℕ) (Out : Type) (Sam : EcSampler L Out) (y : Out) (ℓ : ℕ),
        ∑ s : EcHashSeed L ℓ, EcRelFiberCount (EcSamplerSeedSet Sam y) s
          = (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card * 2 ^ (ℓ * L))
    ∧ (∀ (L : ℕ) (Out : Type) (Sam : EcSampler L Out) (y : Out) (ℓ : ℕ),
        ∃ s : EcHashSeed L ℓ,
          (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card
              ≤ 2 ^ ℓ * EcRelFiberCount (EcSamplerSeedSet Sam y) s
            ∧ 2 ^ ℓ * EcRelFiberCount (EcSamplerSeedSet Sam y) s
              ≤ 2 ^ ℓ * (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card)
    ∧ (∀ (L : ℕ) (Out : Type) [Fintype Out] (Sam : EcSampler L Out) (Ev : Out → Bool),
        (∑ r : Fin L → Bool, if Ev (Sam.O r) = true then 1 else 0)
          = ∑ y : Out, if Ev y = true then
              (∑ r : Fin L → Bool, if Sam.O r = y then 1 else 0) else 0)
    ∧ (∀ (L : ℕ) (Out : Type) [Fintype Out] (Sam : EcSampler L Out) (Ev : Out → Bool),
        (∑ r : Fin L → Bool, if ¬ (Ev (Sam.O r) = true) then 1 else 0)
          + (∑ r : Fin L → Bool, if Ev (Sam.O r) = true then 1 else 0)
            = (Finset.univ : Finset (Fin L → Bool)).card) := by
  refine ⟨fun L Out Sam y => ecSamplerProb_count Sam y,
    fun L Out Sam y ℓ => ecSampler_stockmeyer Sam y ℓ,
    fun L Out Sam y ℓ => ecSampler_multiplicative Sam y ℓ,
    fun L Out inst Sam Ev => ecSamplerEventCount Sam Ev,
    fun L Out inst Sam Ev => ecSamplerBadEventMass Sam Ev⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCounting
