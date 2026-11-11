/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CountingClasses.ClassTransport.CountingComplexityDefs
import Qatlib.Concepts.CountingClasses.ClassTransport.LinearOpticsComplexityModelsDefs
import Qatlib.Concepts.BosonFock.PermAnalysis.BosonDistributionNormalizationThec
import Mathlib.Data.List.GetD

/-!
# Class transport in the counting bit-machine model

This module proves class inclusions, witness-count identities, affine-hash collision counts, and
linear-optics sampling estimates in the `CcProgram` model. `clause1Aux_clause6` constructs a
one-bit output function in `InFBPPNP` from an `InBPP` language by wrapping a decision program.

The model uses tapes filled with false bits beyond the input, so `[]` and `[false]` initialize
identically. The file also proves counterexamples to several proposed transport and
approximate-counting specifications that are sensitive to this input representation.

The mathematical background is described in [KitaevShenVyalyi2002].

## Main statements

* `clause1_clause1`, `clause1_clause3`, and `clause1_clause5`: class inclusions and witness
  counts.
* `clause2_clause2`: the exact collision count for distinct inputs to affine Boolean hashes.
* `clause3_clause4`: sampler witness counts and total-variation estimates.
* `clause1_counter`, `clause2_counter`, and `clause3_counter`: model-specific counterexamples.
* `clause1Aux_clause6`: decision-to-function transport for `InBPP`.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BosonFock.BosonOperators

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.CountingClasses.ClassTransport

open scoped Classical BigOperators Matrix
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib

/-- Running for `t + 1` steps is one machine step applied to the configuration after `t` steps. -/
private lemma ccRun_succ {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) :
    ccRun P A ρ x (t + 1) = ccStep P A ρ (ccRun P A ρ x t) := rfl

/-- The coin-stream index after `t` machine steps is at most `t`. -/
private lemma ccRun_coinIdx_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : (ccRun P A ρ x t).coinIdx ≤ t := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [ccRun_succ]
    cases h : P.states (ccRun P A ρ x n).state <;> simp [ccStep, h] <;> omega

/-- An accepting or rejecting configuration is fixed by `ccStep`. -/
private lemma ccStep_halt {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (c : CcConfig q) (h : P.states c.state = CcAct.accept ∨ P.states c.state = CcAct.reject) :
    ccStep P A ρ c = c := by
  rcases h with h | h <;> simp [ccStep, h]

/-- If the machine is accepting or rejecting after `t` steps, its configuration after `t + k`
steps is unchanged. -/
private lemma ccRun_absorb {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t k : ℕ)
    (h : P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject) :
    ccRun P A ρ x (t + k) = ccRun P A ρ x t := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 from rfl, ccRun_succ, ih, ccStep_halt P A ρ _ h]

/-- A machine result different from `none` implies that the current action is accepting or
rejecting. -/
private lemma result_state {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) (h : ccResult P A ρ x t ≠ none) :
    P.states (ccRun P A ρ x t).state = CcAct.accept ∨
    P.states (ccRun P A ρ x t).state = CcAct.reject := by
  cases hs : P.states (ccRun P A ρ x t).state with
  | accept => exact Or.inl rfl
  | reject => exact Or.inr rfl
  | moveL q' => simp [ccResult, hs] at h
  | moveR q' => simp [ccResult, hs] at h
  | write b q' => simp [ccResult, hs] at h
  | branch qt qf => simp [ccResult, hs] at h
  | coinFlip qt qf => simp [ccResult, hs] at h
  | queryPush q' => simp [ccResult, hs] at h
  | oracleCall qt qf => simp [ccResult, hs] at h

/-- A polynomial-time program is in an accepting or rejecting state at its prescribed polynomial
step bound. -/
private lemma polyTime_haltState {q : ℕ} (P : CcProgram q) (c k : ℕ) (hp : CcPolyTime P c k)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    P.states (ccRun P A ρ x (c * x.length ^ k + c)).state = CcAct.accept ∨
    P.states (ccRun P A ρ x (c * x.length ^ k + c)).state = CcAct.reject :=
  result_state P A ρ x (c * x.length ^ k + c) (hp A ρ x).1

/-- Coin streams agreeing at every index below `t` produce the same configuration after `t`
machine steps. -/
private lemma ccRun_coinPrefix {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ1 ρ2 : ℕ → Bool) (x : List Bool) :
    ∀ t : ℕ, (∀ i, i < t → ρ1 i = ρ2 i) → ccRun P A ρ1 x t = ccRun P A ρ2 x t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
    intro hagr
    have hn : ∀ i, i < n → ρ1 i = ρ2 i := fun i hi => hagr i (by omega)
    have hc := ih hn
    rw [ccRun_succ, ccRun_succ, hc]
    have hle := ccRun_coinIdx_le P A ρ2 x n
    have hcoin : ρ1 (ccRun P A ρ2 x n).coinIdx = ρ2 (ccRun P A ρ2 x n).coinIdx :=
      hagr _ (by omega)
    cases h : P.states (ccRun P A ρ2 x n).state <;> simp [ccStep, h, hcoin]

/-- The empty input and the singleton input `[false]` initialize the same configuration in the
tape model. -/
private lemma ccInit_nil_eq {q : ℕ} : ccInit q [] = ccInit q [false] := by
  have htape : (fun i => ([] : List Bool).getD i false) = (fun i => [false].getD i false) := by
    funext i
    cases i with
    | zero => rfl
    | succ n => rfl
  simp only [ccInit]
  rw [htape]

/-- The empty input and `[false]` give identical runs for every step count, oracle, and coin
stream. -/
private lemma ccRun_nil_false {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool) :
    ∀ t : ℕ, ccRun P A ρ [] t = ccRun P A ρ [false] t := by
  intro t
  induction t with
  | zero => exact ccInit_nil_eq (q := q)
  | succ n ih => rw [ccRun_succ, ccRun_succ, ih]

/-- Restricts a finite bit string to its initial segment of the specified shorter length. -/
private def cutCoins {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) : Fin T0 → Bool :=
  fun i => ω ⟨(i : ℕ), lt_of_lt_of_le i.isLt h⟩

/-- Extracts the suffix remaining after the specified initial segment of a finite bit string. -/
private def tailCoins {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) : Fin (T1 - T0) → Bool :=
  fun j => ω ⟨T0 + (j : ℕ), by omega⟩

/-- Concatenates a finite bit prefix with a suffix to obtain a bit string of the specified total
length. -/
private def padCoins {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool) (u : Fin (T1 - T0) → Bool) :
    Fin T1 → Bool :=
  fun j => if hj : (j : ℕ) < T0 then b ⟨(j : ℕ), hj⟩ else u ⟨(j : ℕ) - T0, by omega⟩

/-- Concatenating the extracted prefix and suffix of a finite bit string recovers the original
string. -/
private lemma pad_cut_tail {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) :
    padCoins h (cutCoins h ω) (tailCoins h ω) = ω := by
  funext j
  have hj1 : (j : ℕ) < T1 := j.isLt
  by_cases hj : (j : ℕ) < T0
  · rw [padCoins, dif_pos hj]
    show ω ⟨(j : ℕ), lt_of_lt_of_le hj h⟩ = ω j
    exact congrArg ω (Fin.ext rfl)
  · rw [padCoins, dif_neg hj]
    have hval : T0 + ((j : ℕ) - T0) < T1 := by omega
    have hval2 : T0 + ((j : ℕ) - T0) = (j : ℕ) := by omega
    show ω (⟨T0 + ((j : ℕ) - T0), hval⟩ : Fin T1) = ω j
    exact congrArg ω (Fin.ext hval2)

/-- Extracting the prefix of a concatenated finite bit string recovers its given prefix. -/
private lemma cut_pad {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool) (u : Fin (T1 - T0) → Bool) :
    cutCoins h (padCoins h b u) = b := by
  funext i
  have hi : (i : ℕ) < T0 := i.isLt
  have hi1 : (i : ℕ) < T1 := lt_of_lt_of_le hi h
  have hd2 : padCoins h b u ⟨(i : ℕ), hi1⟩
      = if hx : (i : ℕ) < T0 then b ⟨(i : ℕ), hx⟩ else u ⟨(i : ℕ) - T0, by omega⟩ := rfl
  show padCoins h b u ⟨(i : ℕ), hi1⟩ = b i
  rw [hd2, dif_pos hi]

/-- Extracting the suffix of a concatenated finite bit string recovers its given suffix. -/
private lemma tail_pad {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool) (u : Fin (T1 - T0) → Bool) :
    tailCoins h (padCoins h b u) = u := by
  funext j
  have hj1 : (j : ℕ) < (T1 - T0) := j.isLt
  have hT : T0 + (j : ℕ) < T1 := by omega
  have hm : T0 + (j : ℕ) - T0 < T1 - T0 := by omega
  have hval2 : T0 + (j : ℕ) - T0 = (j : ℕ) := by omega
  have hd2 : padCoins h b u ⟨T0 + (j : ℕ), hT⟩
      = if hx : (T0 + (j : ℕ)) < T0 then b ⟨T0 + (j : ℕ), hx⟩
        else u ⟨T0 + (j : ℕ) - T0, hm⟩ := rfl
  show padCoins h b u ⟨T0 + (j : ℕ), hT⟩ = u j
  rw [hd2, dif_neg (by omega)]
  exact congrArg u (Fin.ext hval2)

/-- The number of Boolean words of a fixed finite length is two raised to that length. -/
private lemma card_pi_bool (d : ℕ) : Fintype.card (Fin d → Bool) = 2 ^ d := by
  simp [Fintype.card_pi, Finset.prod_const]

/-- The number of longer bit strings satisfying a condition on their prefix is the number of
valid prefixes times `2 ^ (T1 - T0)`. -/
private lemma card_cut_fiber (T0 T1 : ℕ) (h : T0 ≤ T1) (G : (Fin T0 → Bool) → Bool) :
    (Finset.univ.filter (fun ω : Fin T1 → Bool => G (cutCoins h ω))).card =
      (Finset.univ.filter (fun b : Fin T0 → Bool => G b)).card * 2 ^ (T1 - T0) := by
  classical
  have h2 : (2 : ℕ) ^ (T1 - T0) = (Finset.univ : Finset (Fin (T1 - T0) → Bool)).card := by
    rw [Finset.card_univ, card_pi_bool]
  rw [h2, ← Finset.card_product]
  refine Finset.card_nbij' (i := fun ω => (cutCoins h ω, tailCoins h ω))
    (j := fun p => padCoins h p.1 p.2) ?_ ?_ ?_ ?_
  · intro a ha
    have ha1 : G (cutCoins h a) = true := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    apply Finset.mem_coe.mpr
    rw [Finset.mem_product]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
    exact ha1
  · intro p hp
    have hp1 := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    have hp2 := Finset.mem_filter.mp hp1.1
    apply Finset.mem_coe.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [cut_pad]
    exact hp2.2
  · intro a _
    exact pad_cut_tail h a
  · intro p hp
    obtain ⟨b, u⟩ := p
    exact Prod.ext (cut_pad h b u) (tail_pad h b u)

/-- If `n` is within a Boolean list, its prefix of length `n + 1` is its prefix of length `n`
followed by the bit at `n`. -/
private lemma take_succ_getD : ∀ {l : List Bool} {n : ℕ}, n < l.length →
    l.take (n + 1) = l.take n ++ [l.getD n false] := by
  intro l
  induction l with
  | nil => intro n h; simp at h
  | cons a l ih =>
    intro n h
    simp only [List.length_cons] at h
    cases n with
    | zero => rfl
    | succ m =>
      have hm : m < l.length := by omega
      show (a :: l.take (m + 1)) = (a :: l.take m) ++ [l.getD m false]
      rw [ih hm]
      rfl

/-- Every language in `InP` is in `InNP` for the counting bit-machine definitions
[KitaevShenVyalyi2002]. -/
theorem clause1_clause1 : ∀ L : List Bool → Prop, InP L → InNP L := by
  intro L hP
  obtain ⟨q, c, k, M, hpoly, hres⟩ := hP
  refine ⟨q, c, k, 0, M, hpoly, fun x => ?_⟩
  have hlen0 : 0 * x.length ^ 0 + 0 = 0 := by simp
  have hofn : ∀ w : Fin (0 * x.length ^ 0 + 0) → Bool, List.ofFn w = [] := by
    intro w
    have h1 : (List.ofFn w).length = 0 * x.length ^ 0 + 0 := List.length_ofFn
    simp only [Nat.pow_zero] at h1
    exact List.eq_nil_of_length_eq_zero h1
  constructor
  · intro hLx
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    have := hofn (fun i => Fin.elim0 i)
    show decide (ccResult M ccZeroOracle ccDefaultCoin
        (x ++ List.ofFn (fun i : Fin (0 * x.length ^ 0 + 0) => Fin.elim0 i))
        (c * (x ++ List.ofFn (fun i : Fin (0 * x.length ^ 0 + 0) => Fin.elim0 i)).length ^ k + c)
        = some true) = true
    rw [this, List.append_nil]
    rw [hres x]
    simp [hLx]
  · intro ⟨w, hw⟩
    have h2 := hofn w
    rw [h2] at hw
    simp only [ccVerifies, ccAccepts, ccOracleAccepts, List.append_nil] at hw
    rw [hres x] at hw
    simp only [Option.some.injEq, decide_eq_true_eq] at hw
    by_cases hL : L x
    · exact hL
    · simp [hL] at hw

/-- The first level `InPHLevel 1` and `InNP` contain the same languages in this model
[KitaevShenVyalyi2002]. -/
theorem clause1_clause3 : ∀ L : List Bool → Prop,
    (InPHLevel 1 L → InNP L) ∧ (InNP L → InPHLevel 1 L) := by
  intro L
  constructor
  · rintro ⟨q, c, k, p, V, hpoly, hiff⟩
    exact ⟨q, c, k, p, V, hpoly, fun x => hiff x⟩
  · rintro ⟨q, c, k, p, V, hpoly, hiff⟩
    exact ⟨q, c, k, p, V, hpoly, fun x => hiff x⟩

/-- Every `InNP` language is the positivity set of a function in `InSharpP`
[KitaevShenVyalyi2002]. -/
theorem clause1_clause5 : ∀ L : List Bool → Prop, InNP L → ∃ f : List Bool → ℕ,
    InSharpP f ∧ ∀ x : List Bool, (L x ↔ 0 < f x) := by
  intro L hNP
  obtain ⟨q, c, k, p, V, hpoly, hiff⟩ := hNP
  refine ⟨fun x => ccRelCount V c k p x, ⟨q, c, k, p, V, hpoly, fun _ => rfl⟩, fun x => ?_⟩
  rw [hiff x]
  constructor
  · rintro ⟨w, hw⟩
    refine (Finset.card_pos).mpr ⟨w, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
  · intro hpos
    obtain ⟨w, hw⟩ := (Finset.card_pos).mp hpos
    exact ⟨w, (Finset.mem_filter.mp hw).2⟩

/-- Twice the oracle-call count plus the total queried bit count is bounded by the charged
machine time. -/
theorem clause1_clause7 : ∀ (q : ℕ) (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ),
    2 * ccQueries P A ρ x t + ccQueryBits P A ρ x t ≤ ccTime P A ρ x t := by
  intro q P A ρ x t
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

/-- Before state `ℓ`, `ccCallMachine ℓ` pushes the current tape bit to the query and advances to
the next state. -/
private lemma ccCallMachine_states_lt (ℓ : ℕ) (i : Fin (ℓ + 2)) (hi : (i : ℕ) < ℓ) :
    (ccCallMachine ℓ).states i = CcAct.queryPush ⟨(i : ℕ) + 1, by omega⟩ := by
  simp [ccCallMachine, hi]

/-- At state `ℓ`, `ccCallMachine ℓ` calls the oracle and continues to state `ℓ + 1` for either
answer. -/
private lemma ccCallMachine_states_eq (ℓ : ℕ) (i : Fin (ℓ + 2)) (hi : (i : ℕ) = ℓ) :
    (ccCallMachine ℓ).states i = CcAct.oracleCall ⟨ℓ + 1, by omega⟩ ⟨ℓ + 1, by omega⟩ := by
  simp [ccCallMachine, hi]

/-- State `ℓ + 1` of `ccCallMachine ℓ` is accepting. -/
private lemma ccCallMachine_states_top (ℓ : ℕ) :
    (ccCallMachine ℓ).states (⟨ℓ + 1, by omega⟩ : Fin (ℓ + 2)) = CcAct.accept := by
  simp [ccCallMachine]

/-- For an input of length `ℓ` and `t ≤ ℓ`, the call machine is at state and head position `t`,
with query `x.take t`, time `t`, and no oracle calls or coin reads. -/
private lemma ccCallMachine_run (ℓ : ℕ) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (hx : x.length = ℓ) :
    ∀ t, (ht : t ≤ ℓ) →
      ccRun (ccCallMachine ℓ) A ρ x t
        = ({ state := ⟨t, by omega⟩
             tape := fun i => x.getD i false
             head := t
             query := x.take t
             coinIdx := 0
             time := t
             queries := 0
             queryBits := 0
             coins := 0 } : CcConfig (ℓ + 1)) := by
  intro t ht
  induction t with
  | zero =>
    simp [ccRun, ccInit]
  | succ n ih =>
    have hn' : n ≤ ℓ := by omega
    have hlt : n < ℓ := by omega
    rw [ccRun_succ, ih hn']
    have hs := ccCallMachine_states_lt ℓ ⟨n, by omega⟩ hlt
    show ccStep (ccCallMachine ℓ) A ρ
        ({ state := ⟨n, _⟩, tape := fun i => x.getD i false, head := n, query := x.take n,
           coinIdx := 0, time := n, queries := 0, queryBits := 0, coins := 0 } : CcConfig (ℓ + 1))
        = _
    have htake : x.take (n + 1) = x.take n ++ [x.getD n false] :=
      take_succ_getD (l := x) (by omega)
    simp [ccStep, hs, htake]

/-- On a length-`ℓ` input, the call machine accepts after `ℓ + 1` steps with charged time `2 * ℓ
+ 2`, one oracle call, `ℓ` query bits, and no coin reads. -/
theorem clause1_clause8 : ∀ (ℓ : ℕ) (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool),
    x.length = ℓ →
    ccResult (ccCallMachine ℓ) A ρ x (ℓ + 1) = some true
      ∧ ccTime (ccCallMachine ℓ) A ρ x (ℓ + 1) = 2 * ℓ + 2
      ∧ ccQueries (ccCallMachine ℓ) A ρ x (ℓ + 1) = 1
      ∧ ccQueryBits (ccCallMachine ℓ) A ρ x (ℓ + 1) = ℓ
      ∧ ccCoinsRead (ccCallMachine ℓ) A ρ x (ℓ + 1) = 0 := by
  intro ℓ A ρ x hx
  have hrunL := ccCallMachine_run ℓ A ρ x hx ℓ (le_refl ℓ)
  have hs := ccCallMachine_states_eq ℓ ⟨ℓ, by omega⟩ rfl
  have htake : x.take ℓ = x := List.take_of_length_le (by omega)
  have hstep : ccRun (ccCallMachine ℓ) A ρ x (ℓ + 1)
      = ({ state := ⟨ℓ + 1, by omega⟩
           tape := fun i => if i = ℓ then A x else x.getD i false
           head := ℓ
           query := []
           coinIdx := 0
           time := 2 * ℓ + 2
           queries := 1
           queryBits := ℓ
           coins := 0 } : CcConfig (ℓ + 1)) := by
    rw [ccRun_succ, hrunL]
    show ccStep (ccCallMachine ℓ) A ρ
        ({ state := ⟨ℓ, _⟩, tape := fun i => x.getD i false, head := ℓ, query := x.take ℓ,
           coinIdx := 0, time := ℓ, queries := 0, queryBits := 0, coins := 0 } : CcConfig (ℓ + 1))
        = _
    simp [ccStep, hs, htake, hx]
    omega
  have hsacc := ccCallMachine_states_top ℓ
  have hrun1 : (ccRun (ccCallMachine ℓ) A ρ x (ℓ + 1)).state = ⟨ℓ + 1, by omega⟩ := by
    rw [hstep]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [ccResult, hrun1, hsacc]
  · show (ccRun (ccCallMachine ℓ) A ρ x (ℓ + 1)).time = _
    rw [hstep]
  · show (ccRun (ccCallMachine ℓ) A ρ x (ℓ + 1)).queries = _
    rw [hstep]
  · show (ccRun (ccCallMachine ℓ) A ρ x (ℓ + 1)).queryBits = _
    rw [hstep]
  · show (ccRun (ccCallMachine ℓ) A ρ x (ℓ + 1)).coins = _
    rw [hstep]

/-- Every `InSharpP` function belongs to `InSharpPOracle A` for some Boolean oracle `A`. -/
theorem clause1_clause9 : ∀ f : List Bool → ℕ, InSharpP f → ∃ A : List Bool → Bool,
    InSharpPOracle A f := by
  intro f hf
  obtain ⟨q, c, k, p, V, hpoly, heq⟩ := hf
  refine ⟨fun z => ccAccepts V c k z, ⟨p, fun x => ?_⟩⟩
  rw [heq]
  show ccRelCount V c k p x = ccOracleRelCount (fun z => ccAccepts V c k z) p x
  simp [ccRelCount, ccOracleRelCount, ccVerifies, ccAccepts]

/-- The sum of the real indicator of a decidable predicate equals the real-valued cardinality of
its finite truth set. -/
private lemma sum_boole_card {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (∑ a : α, if P a then (1 : ℝ) else 0)
      = ((Finset.univ.filter (fun a => P a)).card : ℝ) := by
  calc (∑ a : α, if P a then (1 : ℝ) else 0)
      = ∑ a ∈ (Finset.univ.filter (fun a => P a)), (1 : ℝ) :=
        (Finset.sum_filter (s := Finset.univ) (p := fun a => P a) (f := fun _ => (1 : ℝ))).symm
    _ = ((Finset.univ.filter (fun a => P a)).card : ℝ) := by
      simp [Finset.sum_const]

/-- A sampler outcome's preimage count equals its probability under `loSamplerDist` multiplied
by `2 ^ Sam.L`. -/
theorem clause3_clause1 : ∀ (m n : ℕ) (Sam : LoSampler m n) (S : FockOccupation m n),
    ((Finset.univ.filter (fun r : Fin Sam.L → Bool => Sam.O r = S)).card : ℝ)
      = loSamplerDist Sam S * ((2 : ℕ) ^ Sam.L : ℝ) := by
  intro m n Sam S
  have h2 : (0 : ℝ) < ((2 : ℕ) ^ Sam.L : ℝ) := by positivity
  simp only [loSamplerDist]
  rw [div_mul_cancel₀ _ (ne_of_gt h2)]
  exact (sum_boole_card (fun r : Fin Sam.L → Bool => Sam.O r = S)).symm

/-- The real cast of the natural absolute value of an integer difference equals the absolute
difference of the real casts. -/
private lemma cast_natAbs_eq_abs (y N : ℕ) :
    (((y : ℤ) - (N : ℤ)).natAbs : ℝ) = |((y : ℕ) : ℝ) - ((N : ℕ) : ℝ)| := by
  rcases le_total y N with h | h
  · have hz : ((y : ℤ) - (N : ℤ)).natAbs = N - y := by omega
    have hy' : (y : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    rw [hz, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hy')]
  · have hz : ((y : ℤ) - (N : ℤ)).natAbs = y - N := by omega
    have hy' : (N : ℝ) ≤ (y : ℝ) := by exact_mod_cast h
    rw [hz, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.2 hy')]

/-- Under the stated relative-error and precision assumptions, dividing the approximate count
`ŷ` by `2 ^ L` approximates `p` within relative error `δ`. -/
theorem clause3_clause2 : ∀ (L N ŷ d : ℕ) (p δ : ℝ), 0 < δ → δ < 1 → 4 ≤ (d + 1) * δ →
    |((N : ℝ) / ((2 : ℕ) ^ L : ℝ)) - p| ≤ δ / 2 * p →
    (d + 1) * ((ŷ : ℤ) - (N : ℤ)).natAbs ≤ N →
    |((ŷ : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p| ≤ δ * p := by
  intro L N ŷ d p δ hδ0 hδ1 h4 hN hy
  have hT : (0 : ℝ) < ((2 : ℕ) ^ L : ℝ) := by positivity
  have hd1 : (0 : ℝ) < ((d : ℝ) + 1) := by
    have hnn : (0:ℝ) ≤ ((d : ℝ)) := Nat.cast_nonneg d
    linarith
  have hyR2 : ((d : ℝ) + 1) * |((ŷ : ℕ) : ℝ) - ((N : ℝ))| ≤ ((N : ℝ)) := by
    have hcast : (((d + 1 : ℕ) : ℝ)) = ((d : ℝ) + 1) := by rw [Nat.cast_add, Nat.cast_one]
    have h1 : (((d + 1 : ℕ) : ℝ) * ((((ŷ : ℤ) - (N : ℤ)).natAbs : ℕ) : ℝ) ≤ ((N : ℝ))) := by
      rw [← Nat.cast_mul, Nat.cast_le]
      exact hy
    have key : (((d + 1 : ℕ) : ℝ) * ((((ŷ : ℤ) - (N : ℤ)).natAbs : ℕ) : ℝ))
        = ((d : ℝ) + 1) * |((ŷ : ℕ) : ℝ) - ((N : ℝ))| := by
      rw [cast_natAbs_eq_abs, hcast]
    rw [← key]
    exact h1
  have hp : 0 ≤ p := by
    have hnn : (0:ℝ) ≤ |((N : ℝ) / ((2 : ℕ) ^ L : ℝ)) - p| := abs_nonneg _
    nlinarith
  have hyN : |((ŷ : ℕ) : ℝ) - ((N : ℝ))| ≤ ((N : ℝ)) / ((d : ℝ) + 1) := by
    rw [le_div_iff₀ hd1, mul_comm]
    exact hyR2
  have hNT : ((N : ℝ)) / ((2 : ℕ) ^ L : ℝ) ≤ p * (1 + δ / 2) := by
    have hle : ((N : ℝ)) / ((2 : ℕ) ^ L : ℝ) - p
        ≤ |((N : ℝ) / ((2 : ℕ) ^ L : ℝ)) - p| := le_abs_self _
    have h1 : ((N : ℝ)) / ((2 : ℕ) ^ L : ℝ) ≤ p + δ / 2 * p := by linarith
    have h2 : p + δ / 2 * p = p * (1 + δ / 2) := by ring
    linarith
  have hsplit : |((ŷ : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p|
      ≤ |((ŷ : ℕ) : ℝ) - ((N : ℝ))| / ((2 : ℕ) ^ L : ℝ) + |((N : ℝ)) / ((2 : ℕ) ^ L : ℝ) - p| := by
    have h1 : ((ŷ : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p
        = (((ŷ : ℕ) : ℝ) - ((N : ℝ))) / ((2 : ℕ) ^ L : ℝ) + (((N : ℝ)) / ((2 : ℕ) ^ L : ℝ) - p) := by
      field_simp
      ring
    rw [h1]
    have h2 := abs_add_le ((((ŷ : ℕ) : ℝ) - ((N : ℝ))) / ((2 : ℕ) ^ L : ℝ))
      (((N : ℝ)) / ((2 : ℕ) ^ L : ℝ) - p)
    have h3 : |(((ŷ : ℕ) : ℝ) - ((N : ℝ))) / ((2 : ℕ) ^ L : ℝ)|
        = |((ŷ : ℕ) : ℝ) - ((N : ℝ))| / ((2 : ℕ) ^ L : ℝ) := by
      rw [abs_div, abs_of_pos hT]
    linarith
  have hmid : |((ŷ : ℕ) : ℝ) - ((N : ℝ))| / ((2 : ℕ) ^ L : ℝ) ≤ δ / 2 * p := by
    have e1 : |((ŷ : ℕ) : ℝ) - ((N : ℝ))| / ((2 : ℕ) ^ L : ℝ)
        ≤ (((N : ℝ)) / ((d : ℝ) + 1)) / ((2 : ℕ) ^ L : ℝ) := by
      rw [div_le_div_iff_of_pos_right hT]
      exact hyN
    have e2 : (((N : ℝ)) / ((d : ℝ) + 1)) / ((2 : ℕ) ^ L : ℝ)
        = (((N : ℝ)) / ((2 : ℕ) ^ L : ℝ)) / ((d : ℝ) + 1) := by field_simp
    have e3 : (((N : ℝ)) / ((2 : ℕ) ^ L : ℝ)) / ((d : ℝ) + 1)
        ≤ p * (1 + δ / 2) / ((d : ℝ) + 1) := by
      rw [div_le_div_iff_of_pos_right hd1]
      exact hNT
    have e4 : p * (1 + δ / 2) / ((d : ℝ) + 1) ≤ δ / 2 * p := by
      rw [div_le_iff₀ hd1]
      have h4' : ((d : ℝ) + 1) * δ ≥ 4 := by exact_mod_cast h4
      nlinarith
    linarith
  linarith

/-- For an isometry and a matching completed-unitary interferometer, the Fock and physical
output distributions agree with the isometry distribution. -/
theorem clause3_clause5 : ∀ (m n : ℕ) (hmn : n ≤ m) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
    ∀ (W : LoCompletedUnitary m n hmn A) (G : loInterferometer m),
      loInterferometerMatrix m G = W.U →
      ∀ S₀ : FockOccupation m n,
        loFockDist m n hmn W.U S₀ = loIsometryDist m n A S₀
          ∧ loPhysicalDist m n hmn G S₀ = loIsometryDist m n A S₀ := by
  intro m n hmn A hA W G hG S₀
  constructor
  · exact loFockDist_eq_of_extendCols W S₀
  · rw [loPhysicalDist_eq_loFockDist, hG]
    exact loFockDist_eq_of_extendCols W S₀

/-- The probabilities of all outcomes of a finite linear-optics sampler sum to one. -/
private lemma sum_loSamplerDist (m n : ℕ) (Sam : LoSampler m n) :
    ∑ S : FockOccupation m n, loSamplerDist Sam S = 1 := by
  have hinner : ∀ r : Fin Sam.L → Bool,
      (∑ S : FockOccupation m n, if Sam.O r = S then (1 : ℝ) else 0) = 1 := by
    intro r
    have hite : (∑ S : FockOccupation m n, if Sam.O r = S then (1 : ℝ) else 0)
        = if Sam.O r ∈ (Finset.univ : Finset (FockOccupation m n)) then (1 : ℝ) else 0 :=
      Finset.sum_ite_eq (s := Finset.univ) (a := Sam.O r) (b := fun _ => (1 : ℝ))
    rw [hite]
    simp
  simp only [loSamplerDist, div_eq_mul_inv]
  rw [← Finset.sum_mul (s := Finset.univ), Finset.sum_comm]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, card_pi_bool]
  field_simp
  rw [nsmul_eq_mul, mul_one, Nat.cast_pow]

/-- The linear-optics distribution associated with an isometry has total mass one. -/
private lemma sum_loIsometryDist (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) (hA : Aᴴ * A = 1) :
    ∑ S : FockOccupation m n, loIsometryDist m n A S = 1 :=
  show ∑ S : FockOccupation m n, bosonWeight A S = 1 from
    Qatlib.Concepts.BosonFock.PermAnalysis.bosonDistributionNormalization m n A hA

/-- A polynomial-time machine recognizing a sampler outcome yields an `InSharpP` witness count
equal to that outcome's scaled probability at empty input. Pointwise and eventwise
differences from an isometry distribution are bounded by twice the total variation and by
the total variation, respectively. -/
theorem clause3_clause4 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
    ∀ (qM cM kM : ℕ) (M : CcProgram qM), CcPolyTime M cM kM →
      ∀ (Sam : LoSampler m n), 0 < Sam.L →
        ∀ S₀ : FockOccupation m n,
          (∀ r : Fin Sam.L → Bool,
            ccAccepts M cM kM (List.ofFn r) = decide (Sam.O r = S₀)) →
          (InSharpP (fun x => ccRelCount M cM kM Sam.L x)
            ∧ ((ccRelCount M cM kM Sam.L [] : ℝ)
                = loSamplerDist Sam S₀ * ((2 : ℕ) ^ Sam.L : ℝ)))
          ∧ (∀ S : FockOccupation m n,
              |loSamplerDist Sam S - loIsometryDist m n A S|
                ≤ 2 * loTvDist (loSamplerDist Sam) (loIsometryDist m n A))
          ∧ (∀ Ev : FockOccupation m n → Bool,
              |(∑ S : FockOccupation m n,
                  if Ev S = true then loSamplerDist Sam S else 0)
                - (∑ S : FockOccupation m n,
                  if Ev S = true then loIsometryDist m n A S else 0)|
                ≤ loTvDist (loSamplerDist Sam) (loIsometryDist m n A)) := by
  intro m n A hA qM cM kM M hpoly Sam hL S₀ hacc
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact ⟨qM, cM, kM, Sam.L, M, hpoly, fun x => rfl⟩
  · have hpow : 0 ^ Sam.L = 0 := Nat.zero_pow (by omega)
    have hplen : Sam.L * 0 ^ Sam.L + Sam.L = Sam.L := by rw [hpow]; omega
    have hcount : ccRelCount M cM kM Sam.L []
        = (Finset.univ.filter (fun r : Fin Sam.L → Bool => Sam.O r = S₀)).card := by
      show (Finset.univ.filter
            (fun w : Fin (Sam.L * 0 ^ Sam.L + Sam.L) → Bool =>
              ccVerifies M cM kM [] (List.ofFn w) = true)).card = _
      rw [hplen]
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hw := hacc w
      show (ccAccepts M cM kM (List.ofFn w) = true) ↔ (Sam.O w = S₀)
      rw [hw, decide_eq_true_eq]
    rw [hcount]
    exact_mod_cast clause3_clause1 m n Sam S₀
  · intro S
    exact loTvDist_apply_le (loSamplerDist Sam) (loIsometryDist m n A) S
  · intro Ev
    set q := loSamplerDist Sam
    set p' := loIsometryDist m n A
    have hsumq : (∑ S : FockOccupation m n, q S) = 1 := sum_loSamplerDist m n Sam
    have hsump : (∑ S : FockOccupation m n, p' S) = 1 := sum_loIsometryDist m n A hA
    have hkey : (∑ S : FockOccupation m n, if Ev S = true then q S else 0)
        - (∑ S : FockOccupation m n, if Ev S = true then p' S else 0)
        = ∑ S : FockOccupation m n, if Ev S = true then (q S - p' S) else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro S _
      by_cases h : Ev S = true <;> simp [h]
    rw [hkey]
    have hsplit : (∑ S : FockOccupation m n, (q S - p' S))
        = (∑ S : FockOccupation m n, if Ev S = true then (q S - p' S) else 0)
          + (∑ S : FockOccupation m n, if Ev S = true then 0 else (q S - p' S)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro S _
      by_cases h : Ev S = true <;> simp [h]
    have hzero : (∑ S : FockOccupation m n, (q S - p' S)) = 0 := by
      rw [Finset.sum_sub_distrib, hsumq, hsump]; ring
    have hA1 : |∑ S : FockOccupation m n, if Ev S = true then (q S - p' S) else 0|
        ≤ ∑ S : FockOccupation m n, |if Ev S = true then (q S - p' S) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    have hA2 : |∑ S : FockOccupation m n, if Ev S = true then 0 else (q S - p' S)|
        ≤ ∑ S : FockOccupation m n, |if Ev S = true then 0 else (q S - p' S)| :=
      Finset.abs_sum_le_sum_abs _ _
    have hsumabs : (∑ S : FockOccupation m n, |if Ev S = true then (q S - p' S) else 0|)
        + (∑ S : FockOccupation m n, |if Ev S = true then 0 else (q S - p' S)|)
        = ∑ S : FockOccupation m n, |(q S - p' S)| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro S _
      by_cases h : Ev S = true <;> simp [h]
    have hBA : |∑ S : FockOccupation m n, if Ev S = true then 0 else (q S - p' S)|
        = |∑ S : FockOccupation m n, if Ev S = true then (q S - p' S) else 0| := by
      have hneg : (∑ S : FockOccupation m n, if Ev S = true then 0 else (q S - p' S))
          = -((∑ S : FockOccupation m n, if Ev S = true then (q S - p' S) else 0)) := by
        linarith
      rw [hneg, abs_neg]
    have h2 : 2 * |∑ S : FockOccupation m n, if Ev S = true then (q S - p' S) else 0|
        ≤ ∑ S : FockOccupation m n, |q S - p' S| := by
      calc 2 * |∑ S : FockOccupation m n, if Ev S = true then (q S - p' S) else 0|
          = |∑ S : FockOccupation m n, if Ev S = true then (q S - p' S) else 0|
            + |∑ S : FockOccupation m n, if Ev S = true then 0 else (q S - p' S)| := by
            rw [hBA]; ring
        _ ≤ (∑ S : FockOccupation m n, |if Ev S = true then (q S - p' S) else 0|)
            + (∑ S : FockOccupation m n, |if Ev S = true then 0 else (q S - p' S)|) :=
            add_le_add hA1 hA2
        _ = ∑ S : FockOccupation m n, |(q S - p' S)| := hsumabs
    simp only [loTvDist]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith

/-- The exclusive-or of a Boolean value with itself is false. -/
private theorem xor_self_f (a : Bool) : (a ^^ a) = false := by cases a <;> rfl

/-- Exclusive-or with false on the right leaves a Boolean value unchanged. -/
private theorem xor_false_r (a : Bool) : (a ^^ false) = a := by cases a <;> rfl

/-- Boolean conjunction on the right distributes over exclusive-or. -/
private theorem and_xor_right (a b c : Bool) : ((a ^^ b) && c) = ((a && c) ^^ (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Equal exclusive-ors with the same right operand have equal left operands. -/
private theorem xor_right_cancel (a b c : Bool) (h : (a ^^ c) = (b ^^ c)) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- The condition that a Boolean hash row has equal parity on `w` and `w'`. -/
private def rowCond {m : ℕ} (w w' : Fin m → Bool) (row : Fin m → Bool) : Prop :=
  (∑ j : Fin m, (row j && w j : Bool)) = (∑ j : Fin m, (row j && w' j : Bool))

/-- The coordinatewise exclusive-or of two Boolean words. -/
private def wdiff {m : ℕ} (w w' : Fin m → Bool) : Fin m → Bool := fun j => (w j ^^ w' j)

/-- The Boolean parity pairing of a row with the word `d`. -/
private def rowT {m : ℕ} (d : Fin m → Bool) (row : Fin m → Bool) : Bool :=
  ∑ j : Fin m, (row j && d j : Bool)

/-- The parity pairing with a fixed word preserves coordinatewise exclusive-or of rows. -/
private theorem rowT_add {m : ℕ} (d : Fin m → Bool) (r1 r2 : Fin m → Bool) :
    rowT d (fun j => (r1 j ^^ r2 j)) = ((rowT d r1) ^^ (rowT d r2)) := by
  unfold rowT
  show (∑ j : Fin m, (((r1 j ^^ r2 j) && d j) : Bool))
      = (∑ j : Fin m, (r1 j && d j : Bool)) + (∑ j : Fin m, (r2 j && d j : Bool))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => and_xor_right (r1 j) (r2 j) (d j))

/-- Equality of a row's parities on two words is equivalent to false parity on their
exclusive-or difference. -/
private theorem rowCond_iff {m : ℕ} (w w' : Fin m → Bool) (row : Fin m → Bool) :
    rowCond w w' row ↔ rowT (wdiff w w') row = false := by
  have key : ∀ j : Fin m, (((row j && w j) + (row j && w' j)) : Bool) = (row j && (w j ^^ w' j)) := by
    intro j
    cases row j <;> cases w j <;> cases w' j <;> rfl
  constructor <;> intro h
  · have hAB : ((∑ j : Fin m, (row j && w j : Bool)) + (∑ j : Fin m, (row j && w' j : Bool))) = false := by
      rw [h]
      exact xor_self_f _
    rw [← Finset.sum_add_distrib] at hAB
    simp_rw [key] at hAB
    exact hAB
  · have hAB : ((∑ j : Fin m, (row j && w j : Bool)) + (∑ j : Fin m, (row j && w' j : Bool))) = false := by
      rw [← Finset.sum_add_distrib]
      simp_rw [key]
      exact h
    have hBB : ((∑ j : Fin m, (row j && w' j : Bool)) + (∑ j : Fin m, (row j && w' j : Bool))) = false :=
      xor_self_f _
    exact add_right_cancel (hAB.trans hBB.symm)

/-- For a nonzero Boolean word of length `m`, exactly `2 ^ (m - 1)` rows have false parity
pairing with it. -/
private theorem card_rowT_false {m : ℕ} (d : Fin m → Bool) (hd : ∃ j : Fin m, d j = true) :
    Fintype.card {row : Fin m → Bool // rowT d row = false} = 2 ^ (m - 1) := by
  obtain ⟨j₀, hj₀⟩ := hd
  let rowStar : Fin m → Bool := fun j => decide (j = j₀)
  have hTstar : rowT d rowStar = true := by
    unfold rowT rowStar
    rw [Finset.sum_eq_single j₀]
    · simp [hj₀]
    · intro b _ hb
      show (((decide (b = j₀) && d b) : Bool)) = 0
      have h1 : decide (b = j₀) = false := decide_eq_false hb
      rw [h1]
      rfl
    · intro hmem
      exact absurd (Finset.mem_univ j₀) hmem
  have hTneg : ∀ row : Fin m → Bool,
      rowT d (fun j => (row j ^^ rowStar j)) = ((rowT d row) ^^ (rowT d rowStar)) :=
    fun row => rowT_add d row rowStar
  have hInv : ∀ row : Fin m → Bool,
      (fun j => ((row j ^^ rowStar j) ^^ rowStar j)) = row := by
    intro row
    funext j
    show ((row j ^^ rowStar j) ^^ rowStar j) = row j
    cases row j <;> cases rowStar j <;> rfl
  let e : {row : Fin m → Bool // rowT d row = true} ≃
      {row : Fin m → Bool // rowT d row = false} :=
    { toFun := fun p => ⟨fun j => (p.1 j ^^ rowStar j), by
        rw [hTneg, p.2, hTstar]
        rfl⟩
      invFun := fun p => ⟨fun j => (p.1 j ^^ rowStar j), by
        have h1 := hTneg p.1
        rw [h1, p.2, hTstar]
        rfl⟩
      left_inv := fun p => Subtype.ext (hInv p.1)
      right_inv := fun p => Subtype.ext (hInv p.1) }
  have hcard_eq : Fintype.card {row : Fin m → Bool // rowT d row = true}
      = Fintype.card {row : Fin m → Bool // rowT d row = false} :=
    Fintype.card_congr e
  have hcompl' := Fintype.card_subtype_compl (α := Fin m → Bool) (p := fun row => rowT d row = true)
  have hc : Fintype.card {row : Fin m → Bool // rowT d row = false}
      = Fintype.card {row : Fin m → Bool // ¬(rowT d row = true)} :=
    Fintype.card_congr
      { toFun := fun p => ⟨p.1, by
          intro h
          have h1 : rowT d p.1 = true := h
          have h2 : rowT d p.1 = false := p.2
          rw [h2] at h1
          simp at h1⟩
        invFun := fun p => ⟨p.1, by
          cases h : rowT d p.1
          · rfl
          · exact absurd h p.2⟩
        left_inv := fun p => Subtype.ext rfl
        right_inv := fun p => Subtype.ext rfl }
  have htot : Fintype.card (Fin m → Bool) = 2 ^ m := by
    rw [Fintype.card_pi]
    simp [Finset.prod_const]
  have hcard : Fintype.card {row : Fin m → Bool // rowT d row = false}
      = Fintype.card (Fin m → Bool) - Fintype.card {row : Fin m → Bool // rowT d row = true} := by
    rw [hc]
    exact hcompl'
  rw [htot] at hcard
  by_cases hm : m = 0
  · subst hm
    exact Fin.elim0 j₀
  · have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have hm1 : m = (m - 1) + 1 := by omega
      conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one, ← hm1]
    have hle : Fintype.card {row : Fin m → Bool // rowT d row = true} ≤ 2 ^ m := by
      have := Nat.sub_le (2 ^ m) (Fintype.card {row : Fin m → Bool // rowT d row = true})
      omega
    have haa : Fintype.card {row : Fin m → Bool // rowT d row = false}
        + Fintype.card {row : Fin m → Bool // rowT d row = false} = 2 ^ m := by
      omega
    omega

/-- For distinct Boolean words of length `m`, exactly `2 ^ m` pairs of a row and an offset bit
satisfy the equal-parity row condition. -/
private theorem card_row_pair {m : ℕ} (w w' : Fin m → Bool)
    (hd : ∃ j : Fin m, wdiff w w' j = true) :
    Fintype.card {p : (Fin m → Bool) × Bool // rowCond w w' p.1} = 2 ^ m := by
  have hrows : Fintype.card {row : Fin m → Bool // rowCond w w' row} = 2 ^ (m - 1) := by
    have h := card_rowT_false (wdiff w w') hd
    refine Fintype.card_congr ?_ |>.trans h
    exact { toFun := fun p => ⟨p.1, (rowCond_iff w w' p.1).mp p.2⟩
            invFun := fun p => ⟨p.1, (rowCond_iff w w' p.1).mpr p.2⟩
            left_inv := fun p => Subtype.ext rfl
            right_inv := fun p => Subtype.ext rfl }
  let e : {p : (Fin m → Bool) × Bool // rowCond w w' p.1} ≃
      ({row : Fin m → Bool // rowCond w w' row} × Bool) :=
    { toFun := fun p => (⟨p.1.1, p.2⟩, p.1.2)
      invFun := fun p => ⟨(p.1.1, p.2), p.1.2⟩
      left_inv := fun p => by rcases p with ⟨⟨r, b⟩, _⟩; rfl
      right_inv := fun p => by rcases p with ⟨⟨r, h⟩, b⟩; rfl }
  have hcard : Fintype.card {p : (Fin m → Bool) × Bool // rowCond w w' p.1}
      = Fintype.card ({row : Fin m → Bool // rowCond w w' row} × Bool) :=
    Fintype.card_congr e
  rw [hcard, Fintype.card_prod, hrows, Fintype.card_bool]
  have hm : 0 < m := by
    by_contra hall
    have hm0 : m = 0 := by omega
    subst hm0
    exact Fin.elim0 (Classical.choose hd)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have hm1 : m = (m - 1) + 1 := by omega
    conv_rhs => rw [mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one, ← hm1]
  omega

/-- For distinct inputs of width `m`, exactly `2 ^ (ℓ * m)` affine Boolean hash parameter pairs
with `ℓ` output bits give equal hash outputs. -/
theorem clause2_clause2 : ∀ (ℓ m : ℕ) (w w' : Fin m → Bool), w ≠ w' →
    (Finset.univ.filter
        (fun Pr : Matrix (Fin ℓ) (Fin m) Bool × (Fin ℓ → Bool) =>
          List.ofFn (ccHash Pr.1 Pr.2 w) = List.ofFn (ccHash Pr.1 Pr.2 w'))).card
      = 2 ^ (ℓ * m) := by
  intro ℓ m w w' hne
  have hd : ∃ j : Fin m, wdiff w w' j = true := by
    by_contra hall
    have hall' : ∀ j : Fin m, ¬(wdiff w w' j = true) := by
      intro j
      exact fun h => hall ⟨j, h⟩
    have hwe : w = w' := by
      funext j
      have := hall' j
      unfold wdiff at this
      cases h1 : w j <;> cases h2 : w' j <;> simp [h1, h2] at this ⊢
    exact hne hwe
  set d := wdiff w w'
  have hrow : ∀ (M : Matrix (Fin ℓ) (Fin m) Bool) (b : Fin ℓ → Bool),
      (List.ofFn (ccHash M b w) = List.ofFn (ccHash M b w'))
        ↔ (∀ i : Fin ℓ, rowCond w w' (fun j => M i j)) := by
    intro M b
    constructor
    · intro h
      have hf : ccHash M b w = ccHash M b w' := List.ofFn_injective h
      intro i
      have hi := congrArg (fun f : Fin ℓ → Bool => f i) hf
      simp only [ccHash] at hi
      have hi2 :
          ((∑ j, (M i j && w j : Bool)) ^^ (b i)) = ((∑ j, (M i j && w' j : Bool)) ^^ (b i)) := hi
      exact xor_right_cancel _ _ (b i) hi2
    · intro h
      have hf : ccHash M b w = ccHash M b w' := by
        funext i
        simp only [ccHash]
        have hi := h i
        rw [hi]
      exact List.ofFn_injective.eq_iff.mpr hf
  let φ : (Matrix (Fin ℓ) (Fin m) Bool × (Fin ℓ → Bool)) ≃
      (Fin ℓ → ((Fin m → Bool) × Bool)) :=
    { toFun := fun Pr i => (fun j => Pr.1 i j, Pr.2 i)
      invFun := fun f => (fun i j => (f i).1 j, fun i => (f i).2)
      left_inv := fun Pr => by rcases Pr with ⟨M, b⟩; rfl
      right_inv := fun f => by
        funext i
        apply Prod.ext
        · funext j; rfl
        · rfl }
  have hpre : (Finset.univ.filter
        (fun Pr : Matrix (Fin ℓ) (Fin m) Bool × (Fin ℓ → Bool) =>
          List.ofFn (ccHash Pr.1 Pr.2 w) = List.ofFn (ccHash Pr.1 Pr.2 w'))).card
      = Fintype.card {Pr : Matrix (Fin ℓ) (Fin m) Bool × (Fin ℓ → Bool) //
          (List.ofFn (ccHash Pr.1 Pr.2 w) = List.ofFn (ccHash Pr.1 Pr.2 w'))} := by
    rw [Fintype.subtype_card]
  have heq : Fintype.card {Pr : Matrix (Fin ℓ) (Fin m) Bool × (Fin ℓ → Bool) //
          (List.ofFn (ccHash Pr.1 Pr.2 w) = List.ofFn (ccHash Pr.1 Pr.2 w'))}
      = Fintype.card (Fin ℓ → {p : (Fin m → Bool) × Bool // rowCond w w' p.1}) := by
    refine Fintype.card_congr ?_
    exact { toFun := fun Pr => fun i =>
          ⟨(fun j => Pr.1.1 i j, Pr.1.2 i), (hrow Pr.1.1 Pr.1.2).mp Pr.2 i⟩
            invFun := fun f => ⟨(fun i j => (f i).1.1 j, fun i => (f i).1.2), by
              have hall : ∀ i : Fin ℓ, rowCond w w' (fun j => (f i).1.1 j) := fun i => (f i).2
              exact (hrow (fun i j => (f i).1.1 j) (fun i => (f i).1.2)).mpr hall⟩
            left_inv := fun Pr => by rcases Pr with ⟨⟨M, b⟩, _⟩; rfl
            right_inv := fun f => by
              funext i
              apply Subtype.ext
              apply Prod.ext
              · rfl
              · rfl }
  rw [hpre, heq, Fintype.card_pi]
  have hrowc : ∀ i : Fin ℓ,
      Fintype.card {p : (Fin m → Bool) × Bool // rowCond w w' p.1} = 2 ^ m :=
    fun _ => card_row_pair w w' hd
  have hprod : (∏ i : Fin ℓ, Fintype.card {p : (Fin m → Bool) × Bool // rowCond w w' p.1})
      = (∏ i : Fin ℓ, (2 ^ m)) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact hrowc i
  rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.pow_mul, Nat.mul_comm]

/-- Running for `t + 1` steps is one machine step applied to the configuration after `t` steps. -/
private lemma ccRun_succ' {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) :
    ccRun P A ρ x (t + 1) = ccStep P A ρ (ccRun P A ρ x t) := rfl

/-- The empty input and the singleton input `[false]` initialize the same configuration in the
tape model. -/
private lemma ccInit_nil_eq' {q : ℕ} : ccInit q [] = ccInit q [false] := by
  have htape : (fun i => ([] : List Bool).getD i false) = (fun i => [false].getD i false) := by
    funext i
    cases i with
    | zero => rfl
    | succ n => rfl
  simp only [ccInit]
  rw [htape]

/-- The empty input and `[false]` give identical runs for every step count, oracle, and coin
stream. -/
private lemma ccRun_nil_false' {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool) :
    ∀ t : ℕ, ccRun P A ρ [] t = ccRun P A ρ [false] t := by
  intro t
  induction t with
  | zero => exact ccInit_nil_eq' (q := q)
  | succ n ih => rw [ccRun_succ', ccRun_succ', ih]

/-- The coin-stream index after `t` machine steps is at most `t`. -/
private lemma ccRun_coinIdx_le' {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : (ccRun P A ρ x t).coinIdx ≤ t := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [ccRun_succ']
    cases h : P.states (ccRun P A ρ x n).state <;> simp [ccStep, h] <;> omega

/-- Coin streams agreeing at every index below `t` produce the same configuration after `t`
machine steps. -/
private lemma ccRun_coinPrefix' {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ1 ρ2 : ℕ → Bool) (x : List Bool) :
    ∀ t : ℕ, (∀ i, i < t → ρ1 i = ρ2 i) → ccRun P A ρ1 x t = ccRun P A ρ2 x t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
    intro hagr
    have hn : ∀ i, i < n → ρ1 i = ρ2 i := fun i hi => hagr i (by omega)
    have hc := ih hn
    rw [ccRun_succ', ccRun_succ', hc]
    have hle := ccRun_coinIdx_le' P A ρ2 x n
    have hcoin : ρ1 (ccRun P A ρ2 x n).coinIdx = ρ2 (ccRun P A ρ2 x n).coinIdx :=
      hagr _ (by omega)
    cases h : P.states (ccRun P A ρ2 x n).state <;> simp [ccStep, h, hcoin]

/-- A machine result different from `none` implies that the current action is accepting or
rejecting. -/
private lemma result_state' {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) (h : ccResult P A ρ x t ≠ none) :
    P.states (ccRun P A ρ x t).state = CcAct.accept ∨
    P.states (ccRun P A ρ x t).state = CcAct.reject := by
  cases hs : P.states (ccRun P A ρ x t).state with
  | accept => exact Or.inl rfl
  | reject => exact Or.inr rfl
  | moveL q' => simp [ccResult, hs] at h
  | moveR q' => simp [ccResult, hs] at h
  | write b q' => simp [ccResult, hs] at h
  | branch qt qf => simp [ccResult, hs] at h
  | coinFlip qt qf => simp [ccResult, hs] at h
  | queryPush q' => simp [ccResult, hs] at h
  | oracleCall qt qf => simp [ccResult, hs] at h

/-- An accepting or rejecting configuration is fixed by `ccStep`. -/
private lemma ccStep_halt' {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (c : CcConfig q) (h : P.states c.state = CcAct.accept ∨ P.states c.state = CcAct.reject) :
    ccStep P A ρ c = c := by
  rcases h with h | h <;> simp [ccStep, h]

/-- If the machine is accepting or rejecting after `t` steps, its configuration after `t + k`
steps is unchanged. -/
private lemma ccRun_absorb' {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t k : ℕ)
    (h : P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject) :
    ccRun P A ρ x (t + k) = ccRun P A ρ x t := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 from rfl, ccRun_succ', ih, ccStep_halt' P A ρ _ h]

/-- The number of Boolean words of a fixed finite length is two raised to that length. -/
private lemma card_pi_bool' (d : ℕ) : Fintype.card (Fin d → Bool) = 2 ^ d := by
  simp [Fintype.card_pi, Finset.prod_const]

/-- Once a run reaches an accepting or rejecting state at time `t`, every later step bound gives
the same configuration. -/
private lemma ccRun_halt_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t t' : ℕ)
    (hhalt : P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject)
    (hle : t ≤ t') : ccRun P A ρ x t' = ccRun P A ρ x t := by
  have h := ccRun_absorb' P A ρ x t (t' - t) hhalt
  rw [Nat.add_sub_cancel' hle] at h
  exact h

/-- Equal run configurations give equal optional machine results for the same program. -/
private lemma ccResult_congr {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ1 ρ2 : ℕ → Bool) (x1 x2 : List Bool) (t1 t2 : ℕ)
    (h : ccRun P A ρ1 x1 t1 = ccRun P A ρ2 x2 t2) :
    ccResult P A ρ1 x1 t1 = ccResult P A ρ2 x2 t2 := by
  simp only [ccResult, h]

/-- Inputs with the same values under `getD` with default `false` initialize identical machine
configurations. -/
theorem ccInit_tape_eq {q : ℕ} (x x' : List Bool) (h : ∀ i, x.getD i false = x'.getD i false) :
    ccInit q x = ccInit q x' := by
  have ht : (fun i => x.getD i false) = (fun i => x'.getD i false) := by
    funext i
    exact h i
  simp only [ccInit]
  rw [ht]

/-- Inputs representing the same tape under `getD` with default `false` produce identical runs
at every step count. -/
theorem ccRun_tape_eq {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x x' : List Bool) (h : ∀ i, x.getD i false = x'.getD i false) :
    ∀ t, ccRun P A ρ x t = ccRun P A ρ x' t := by
  intro t
  induction t with
  | zero => exact ccInit_tape_eq x x' h
  | succ n ih => rw [ccRun_succ', ccRun_succ', ih]

/-- A polynomial-time program has the same acceptance value on inputs representing the same
tape, even when their list lengths differ. -/
theorem ccAccepts_tape_eq {q : ℕ} (V : CcProgram q) (c k : ℕ) (hpoly : CcPolyTime V c k)
    (x x' : List Bool) (h : ∀ i, x.getD i false = x'.getD i false) :
    ccAccepts V c k x = ccAccepts V c k x' := by
  have hall : ccResult V ccZeroOracle ccDefaultCoin x (c * x.length ^ k + c)
      = ccResult V ccZeroOracle ccDefaultCoin x' (c * x'.length ^ k + c) := by
    set b1 : ℕ := c * x.length ^ k + c
    set b2 : ℕ := c * x'.length ^ k + c
    have hrun := ccRun_tape_eq V ccZeroOracle ccDefaultCoin x x' h
    have hresX : ccResult V ccZeroOracle ccDefaultCoin x b1
        = ccResult V ccZeroOracle ccDefaultCoin x' b1 :=
      ccResult_congr V ccZeroOracle ccDefaultCoin ccDefaultCoin x x' b1 b1 (hrun b1)
    rcases le_total b1 b2 with hle | hle
    · have hs1 := result_state' V ccZeroOracle ccDefaultCoin x b1
        (hpoly ccZeroOracle ccDefaultCoin x).1
      have hs1' : V.states (ccRun V ccZeroOracle ccDefaultCoin x' b1).state = CcAct.accept ∨
          V.states (ccRun V ccZeroOracle ccDefaultCoin x' b1).state = CcAct.reject := by
        rw [← hrun b1]
        exact hs1
      have habs := ccRun_halt_le V ccZeroOracle ccDefaultCoin x' b1 b2 hs1' hle
      have hres := ccResult_congr V ccZeroOracle ccDefaultCoin ccDefaultCoin x' x' b2 b1 habs
      exact hresX.trans hres.symm
    · have hs2 := result_state' V ccZeroOracle ccDefaultCoin x' b2
        (hpoly ccZeroOracle ccDefaultCoin x').1
      have habs := ccRun_halt_le V ccZeroOracle ccDefaultCoin x' b2 b1 hs2 hle
      have hres := ccResult_congr V ccZeroOracle ccDefaultCoin ccDefaultCoin x' x' b1 b2 habs
      exact hresX.trans hres
  simp only [ccAccepts, ccOracleAccepts, hall]

/-- Restricts a finite bit string to its initial segment of the specified shorter length. -/
private def cutBits {t1 t2 : ℕ} (h : t1 ≤ t2) (ω : Fin t2 → Bool) : Fin t1 → Bool :=
  fun i => ω ⟨(i : ℕ), lt_of_lt_of_le i.isLt h⟩

/-- Extracts the suffix remaining after the specified initial segment of a finite bit string. -/
private def tailBits {t1 t2 : ℕ} (h : t1 ≤ t2) (ω : Fin t2 → Bool) : Fin (t2 - t1) → Bool :=
  fun j => ω ⟨t1 + (j : ℕ), by omega⟩

/-- Concatenates a finite bit prefix with a suffix to obtain a bit string of the specified total
length. -/
private def padBits {t1 t2 : ℕ} (h : t1 ≤ t2) (b : Fin t1 → Bool) (u : Fin (t2 - t1) → Bool) :
    Fin t2 → Bool :=
  fun j => if hj : (j : ℕ) < t1 then b ⟨(j : ℕ), hj⟩ else u ⟨(j : ℕ) - t1, by omega⟩

/-- Concatenating the extracted prefix and suffix of a finite bit string recovers the original
string. -/
private lemma pad_cut_tail' {t1 t2 : ℕ} (h : t1 ≤ t2) (ω : Fin t2 → Bool) :
    padBits h (cutBits h ω) (tailBits h ω) = ω := by
  funext j
  by_cases hj : (j : ℕ) < t1
  · rw [padBits, dif_pos hj]
    show ω ⟨(j : ℕ), lt_of_lt_of_le hj h⟩ = ω j
    exact congrArg ω (Fin.ext rfl)
  · rw [padBits, dif_neg hj]
    have hval2 : t1 + ((j : ℕ) - t1) = (j : ℕ) := by omega
    show ω (⟨t1 + ((j : ℕ) - t1), _⟩ : Fin t2) = ω j
    exact congrArg ω (Fin.ext hval2)

/-- Extracting the prefix of a concatenated finite bit string recovers its given prefix. -/
private lemma cut_pad' {t1 t2 : ℕ} (h : t1 ≤ t2) (b : Fin t1 → Bool) (u : Fin (t2 - t1) → Bool) :
    cutBits h (padBits h b u) = b := by
  funext i
  have hi : (i : ℕ) < t1 := i.isLt
  have hi1 : (i : ℕ) < t2 := lt_of_lt_of_le hi h
  have hd2 : padBits h b u ⟨(i : ℕ), hi1⟩
      = if hx : (i : ℕ) < t1 then b ⟨(i : ℕ), hx⟩ else u ⟨(i : ℕ) - t1, by omega⟩ := rfl
  show padBits h b u ⟨(i : ℕ), hi1⟩ = b i
  rw [hd2, dif_pos hi]

/-- Extracting the suffix of a concatenated finite bit string recovers its given suffix. -/
private lemma tail_pad' {t1 t2 : ℕ} (h : t1 ≤ t2) (b : Fin t1 → Bool) (u : Fin (t2 - t1) → Bool) :
    tailBits h (padBits h b u) = u := by
  funext j
  have hj : t1 + (j : ℕ) < t2 := by
    have := j.isLt
    omega
  have hval2 : t1 + (j : ℕ) - t1 = (j : ℕ) := by omega
  have hd2 : padBits h b u ⟨t1 + (j : ℕ), hj⟩
      = if hx : (t1 + (j : ℕ)) < t1 then b ⟨t1 + (j : ℕ), hx⟩
        else u ⟨(t1 + (j : ℕ)) - t1, by omega⟩ := rfl
  show padBits h b u ⟨t1 + (j : ℕ), hj⟩ = u j
  rw [hd2, dif_neg (by omega)]
  exact congrArg u (Fin.ext hval2)

/-- A program that branches on the initial tape bit and then accepts if it is true or rejects if
it is false. -/
def clause1BadV : CcProgram 2 where
  states := fun i =>
    match (i : ℕ) with
    | 0 => CcAct.branch ⟨1, by omega⟩ ⟨2, by omega⟩
    | 1 => CcAct.accept
    | _ => CcAct.reject

/-- After one step, `clause1BadV` has branched according to the initial tape bit, leaving the
tape and head unchanged and charging one time unit. -/
private lemma ccRun_clause1BadV_one (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccRun clause1BadV A ρ x 1 =
      ({ state := if x.getD 0 false then (⟨1, by omega⟩ : Fin 3) else ⟨2, by omega⟩
         tape := fun i => x.getD i false
         head := 0
         query := []
         coinIdx := 0
         time := 1
         queries := 0
         queryBits := 0
         coins := 0 } : CcConfig 2) := rfl

/-- The run of `clause1BadV` is unchanged between one and two steps. -/
private lemma ccRun_clause1BadV_two (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccRun clause1BadV A ρ x 2 = ccRun clause1BadV A ρ x 1 := by
  rw [ccRun_succ', ccRun_clause1BadV_one]
  cases x.getD 0 false <;> simp [ccStep, clause1BadV]

/-- After one step, the result of `clause1BadV` is the input's first bit, with default `false`. -/
private lemma clause1BadV_result_one (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccResult clause1BadV A ρ x 1 = some (x.getD 0 false) := by
  simp only [ccResult, ccRun_clause1BadV_one]
  cases x.getD 0 false <;> simp [clause1BadV]

/-- At every step bound at least two, the result of `clause1BadV` is the input's first bit, with
default `false`. -/
lemma clause1BadV_result (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) (t : ℕ)
    (ht : 2 ≤ t) : ccResult clause1BadV A ρ x t = some (x.getD 0 false) := by
  have h2 : ccResult clause1BadV A ρ x 2 = some (x.getD 0 false) := by
    rw [ccResult_congr clause1BadV A ρ ρ x x 2 1 (ccRun_clause1BadV_two A ρ x)]
    exact clause1BadV_result_one A ρ x
  have hhalt := result_state' clause1BadV A ρ x 2 (by rw [h2]; simp)
  have hres :=
      ccResult_congr clause1BadV A ρ ρ x x t 2 (ccRun_halt_le clause1BadV A ρ x 2 t hhalt ht)
  rw [h2] at hres
  exact hres

/-- The first-bit branching program satisfies `CcPolyTime` with coefficient one and exponent
zero. -/
lemma clause1BadV_poly : CcPolyTime clause1BadV 1 0 := by
  intro A ρ x
  have h2 : (1 : ℕ) * x.length ^ 0 + 1 = 2 := by simp
  constructor
  · rw [h2]
    intro hnone
    have hr := clause1BadV_result A ρ x 2 (by omega)
    rw [hr] at hnone
    simp at hnone
  · rw [h2]
    show (ccRun clause1BadV A ρ x 2).time ≤ 2
    rw [ccRun_clause1BadV_two, ccRun_clause1BadV_one]
    simp

/-- The language consisting of the empty list and all Boolean lists whose first bit is true. -/
def clause1BadL : List Bool → Prop := fun x => x = [] ∨ x.getD 0 false = true

/-- The language `clause1BadL` belongs to `InNP` in the specified tape and witness model. -/
theorem clause1BadL_inNP : InNP clause1BadL := by
  refine ⟨2, 1, 0, 1, clause1BadV, clause1BadV_poly, fun x => ?_⟩
  have hver : ∀ (y : List Bool) (w : Fin (1 * y.length ^ 1 + 1) → Bool),
      ccVerifies clause1BadV 1 0 y (List.ofFn w) = ((y ++ List.ofFn w).getD 0 false) := by
    intro y w
    simp [ccVerifies, ccAccepts, ccOracleAccepts, clause1BadV_result]
  constructor
  · intro hx
    cases x with
    | nil =>
      refine ⟨fun _ => true, ?_⟩
      rw [hver]
      have hz : List.ofFn (fun _ : Fin (1 * ([] : List Bool).length ^ 1 + 1) => true)
          = ([true] : List Bool) := by simp
      rw [hz]
      rfl
    | cons a x' =>
      rcases hx with hx | hx
      · cases hx
      · refine ⟨fun _ => false, ?_⟩
        rw [hver]
        exact hx
  · intro hex
    cases x with
    | nil => exact Or.inl rfl
    | cons a x' =>
      obtain ⟨w, hw⟩ := hex
      right
      rw [hver] at hw
      exact hw

/-- The acceptance count on `[false]` at its polynomial budget equals the acceptance count on
`[]` multiplied by the number of additional coin suffixes. -/
private lemma clause1_accScale {q : ℕ} (M : CcProgram q) (c k : ℕ)
    (hpoly : CcPolyTime M c k) :
    ccAcceptCount M ccZeroOracle [false] (c * 1 ^ k + c)
      = ccAcceptCount M ccZeroOracle [] (c * 0 ^ k + c)
          * 2 ^ ((c * 1 ^ k + c) - (c * 0 ^ k + c)) := by
  set t1 : ℕ := c * 0 ^ k + c
  set t2 : ℕ := c * 1 ^ k + c
  have hle : t1 ≤ t2 := by
    by_cases hk : k = 0
    · subst hk; rfl
    · have h0 : 0 ^ k = 0 := Nat.zero_pow (by omega)
      have h1 : 1 ^ k = 1 := Nat.one_pow k
      unfold t1 t2
      rw [h0, h1]
      omega

  have hpoint : ∀ ω : Fin t2 → Bool,
      (ccResult M ccZeroOracle (ccCoinString ω) [false] t2 = some true) ↔
      (ccResult M ccZeroOracle (ccCoinString (cutBits hle ω)) [] t1 = some true) := by
    intro ω
    have hpref : ∀ i, i < t1 →
        ccCoinString ω i = ccCoinString (cutBits hle ω) i := by
      intro i hi
      simp only [ccCoinString, cutBits]
      rw [dif_pos (by omega : i < t2), dif_pos hi]
    have hrun : ccRun M ccZeroOracle (ccCoinString ω) [false] t1
        = ccRun M ccZeroOracle (ccCoinString (cutBits hle ω)) [] t1 := by
      have h1 : ccRun M ccZeroOracle (ccCoinString ω) [false] t1
          = ccRun M ccZeroOracle (ccCoinString ω) [] t1 :=
        (ccRun_nil_false' M ccZeroOracle (ccCoinString ω) t1).symm
      rw [h1]
      exact ccRun_coinPrefix' M ccZeroOracle _ _ [] t1 hpref
    have hres := hpoly ccZeroOracle (ccCoinString (cutBits hle ω)) []
    have hhalt := result_state' M ccZeroOracle (ccCoinString (cutBits hle ω)) [] t1 hres.1
    have habs2 := ccRun_halt_le M ccZeroOracle (ccCoinString (cutBits hle ω)) [] t1 t2 hhalt hle
    have habs1 := ccRun_halt_le M ccZeroOracle (ccCoinString ω) [false] t1 t2
      (by rw [hrun]; exact hhalt) hle
    have hcfg : ccRun M ccZeroOracle (ccCoinString ω) [false] t2
        = ccRun M ccZeroOracle (ccCoinString (cutBits hle ω)) [] t1 := by
      rw [habs1, hrun]
    have hresEq := ccResult_congr M ccZeroOracle (ccCoinString ω) (ccCoinString (cutBits hle ω))
      [false] [] t2 t1 hcfg
    exact ⟨fun h => by rw [← hresEq]; exact h, fun h => by rw [hresEq]; exact h⟩

  have hcount : ccAcceptCount M ccZeroOracle [false] t2
      = ccAcceptCount M ccZeroOracle [] t1 * 2 ^ (t2 - t1) := by
    show (Finset.univ.filter (fun ω : Fin t2 → Bool =>
        ccResult M ccZeroOracle (ccCoinString ω) [false] t2 = some true)).card =
      (Finset.univ.filter (fun ω : Fin t1 → Bool =>
        ccResult M ccZeroOracle (ccCoinString ω) [] t1 = some true)).card * 2 ^ (t2 - t1)
    have h2 : (2 : ℕ) ^ (t2 - t1)
        = (Finset.univ : Finset (Fin (t2 - t1) → Bool)).card := by
      rw [Finset.card_univ, card_pi_bool']
    rw [h2, ← Finset.card_product]
    refine Finset.card_nbij' (i := fun ω : Fin t2 → Bool =>
        (cutBits hle ω, tailBits hle ω))
      (j := fun p : (Fin t1 → Bool) × (Fin (t2 - t1) → Bool) => padBits hle p.1 p.2) ?_ ?_ ?_ ?_
    · intro a ha
      have ha1 : ccResult M ccZeroOracle (ccCoinString a) [false] t2 = some true :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have ha2 := (hpoint a).mp ha1
      apply Finset.mem_coe.mpr
      rw [Finset.mem_product]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha2⟩, Finset.mem_univ _⟩
    · intro p hp
      obtain ⟨b, u⟩ := p
      have hp1 := Finset.mem_product.mp (Finset.mem_coe.mp hp)
      have hp2 := Finset.mem_filter.mp hp1.1
      apply Finset.mem_coe.mpr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hcut : cutBits hle (padBits hle b u) = b := cut_pad' hle b u
      have hgood : ccResult M ccZeroOracle (ccCoinString (cutBits hle (padBits hle b u))) [] t1
          = some true := by
        rw [hcut]
        exact hp2.2
      exact (hpoint (padBits hle b u)).mpr hgood
    · intro a _
      exact pad_cut_tail' hle a
    · intro p hp
      obtain ⟨b, u⟩ := p
      exact Prod.ext (cut_pad' hle b u) (tail_pad' hle b u)
  exact hcount

/-- Strict majority acceptance at the polynomial budget is equivalent on the inputs `[]` and
`[false]`. -/
private lemma clause1_majority_tailFalse {q : ℕ} (M : CcProgram q) (c k : ℕ)
    (hpoly : CcPolyTime M c k) :
    (2 * ccAcceptCount M ccZeroOracle [] (c * 0 ^ k + c) > 2 ^ (c * 0 ^ k + c)) ↔
    (2 * ccAcceptCount M ccZeroOracle [false] (c * 1 ^ k + c) > 2 ^ (c * 1 ^ k + c)) := by
  set t1 : ℕ := c * 0 ^ k + c
  set t2 : ℕ := c * 1 ^ k + c
  have hle : t1 ≤ t2 := by
    by_cases hk : k = 0
    · subst hk; rfl
    · have h0 : 0 ^ k = 0 := Nat.zero_pow (by omega)
      have h1 : 1 ^ k = 1 := Nat.one_pow k
      unfold t1 t2
      rw [h0, h1]
      omega
  have hcount : ccAcceptCount M ccZeroOracle [false] t2
      = ccAcceptCount M ccZeroOracle [] t1 * 2 ^ (t2 - t1) :=
    clause1_accScale M c k hpoly
  have hpow : 2 ^ t2 = 2 ^ t1 * 2 ^ (t2 - t1) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
  have hpos : 0 < 2 ^ (t2 - t1) := Nat.pow_pos (by norm_num)
  constructor <;> intro h
  · have h1 : (2 * ccAcceptCount M ccZeroOracle [] t1) * 2 ^ (t2 - t1)
        = 2 * (ccAcceptCount M ccZeroOracle [] t1 * 2 ^ (t2 - t1)) := by
      ring
    rw [hcount, hpow, ← h1]
    have h2 : 2 ^ t1 < 2 * ccAcceptCount M ccZeroOracle [] t1 := h
    exact Nat.mul_lt_mul_right hpos |>.mpr h2
  · have h1 : (2 * ccAcceptCount M ccZeroOracle [] t1) * 2 ^ (t2 - t1)
        = 2 * (ccAcceptCount M ccZeroOracle [] t1 * 2 ^ (t2 - t1)) := by
      ring
    rw [hcount, hpow, ← h1] at h
    have h2 : 2 ^ t1 < 2 * ccAcceptCount M ccZeroOracle [] t1 :=
      Nat.mul_lt_mul_right hpos |>.mp h
    exact h2

/-- The language `clause1BadL` is outside `InPP` in this tape model, whose runs cannot
distinguish `[]` from `[false]`. -/
theorem clause1BadL_notInPP : ¬ InPP clause1BadL := by
  rintro ⟨q, c, k, M, hpoly, hiff⟩
  have h0 : 2 * ccAcceptCount M ccZeroOracle [] (c * ([] : List Bool).length ^ k + c)
      > 2 ^ (c * ([] : List Bool).length ^ k + c) :=
    (hiff []).mp (Or.inl rfl)
  have hf : ¬ (2 * ccAcceptCount M ccZeroOracle [false] (c * ([false] : List Bool).length ^ k + c)
      > 2 ^ (c * ([false] : List Bool).length ^ k + c)) := by
    intro hgt
    have hL : clause1BadL [false] := (hiff [false]).mpr hgt
    rcases hL with h | h
    · cases h
    · simp at h
  have hkey := clause1_majority_tailFalse M c k hpoly
  exact hf (hkey.mp h0)

/-- The language `clause1BadL` is outside `InBPP` in this tape model, whose runs cannot
distinguish `[]` from `[false]`. -/
theorem clause1BadL_notInBPP : ¬ InBPP clause1BadL := by
  rintro ⟨q, c, k, M, hpoly, hiff⟩
  have h1 : 3 * ccAcceptCount M ccZeroOracle [] (c * 0 ^ k + c)
      ≥ 2 * 2 ^ (c * 0 ^ k + c) := by
    have h := (hiff []).1 (Or.inl rfl)
    exact h
  have h2 : 3 * ccAcceptCount M ccZeroOracle [false] (c * 1 ^ k + c)
      ≤ 2 ^ (c * 1 ^ k + c) := by
    apply (hiff [false]).2
    intro hL
    rcases hL with h | h
    · cases h
    · simp at h
  set t1 : ℕ := c * 0 ^ k + c
  set t2 : ℕ := c * 1 ^ k + c
  have hle : t1 ≤ t2 := by
    by_cases hk : k = 0
    · subst hk; rfl
    · have h0 : 0 ^ k = 0 := Nat.zero_pow (by omega)
      have h1' : 1 ^ k = 1 := Nat.one_pow k
      unfold t1 t2
      rw [h0, h1']
      omega
  have hcount : ccAcceptCount M ccZeroOracle [false] t2
      = ccAcceptCount M ccZeroOracle [] t1 * 2 ^ (t2 - t1) :=
    clause1_accScale M c k hpoly
  have hpow : 2 ^ t2 = 2 ^ t1 * 2 ^ (t2 - t1) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
  have hpos : 0 < 2 ^ (t2 - t1) := Nat.pow_pos (by norm_num)
  have h1' : 2 * 2 ^ t1 ≤ 3 * ccAcceptCount M ccZeroOracle [] t1 := h1
  have h2' : 3 * ccAcceptCount M ccZeroOracle [false] t2 ≤ 2 ^ t2 := h2
  have h2b : 3 * ccAcceptCount M ccZeroOracle [] t1 * 2 ^ (t2 - t1)
      ≤ 2 ^ t1 * 2 ^ (t2 - t1) := by
    rw [hcount, hpow, ← Nat.mul_assoc] at h2'
    exact h2'
  have h3 : 3 * ccAcceptCount M ccZeroOracle [] t1 ≤ 2 ^ t1 :=
    Nat.le_of_mul_le_mul_right h2b hpos
  have h7 : 0 < 2 ^ t1 := Nat.pow_pos (by norm_num)
  omega

/-- The stated conjunction of class-transport and machine-accounting claims is false in this
model, as witnessed by the failure of the proposed `InNP` to `InPP` inclusion. -/
theorem clause1_counter : ¬ (

  (∀ L : List Bool → Prop, InP L → InNP L)

  ∧ (∀ L : List Bool → Prop, InNP L → InPP L)

  ∧ (∀ L : List Bool → Prop,
      (InPHLevel 1 L → InNP L) ∧ (InNP L → InPHLevel 1 L))

  ∧ (∀ (k : ℕ) (L : List Bool → Prop), InPHLevel k L → InPHLevel (k + 1) L)

  ∧ (∀ L : List Bool → Prop, InNP L → ∃ f : List Bool → ℕ,
      InSharpP f ∧ ∀ x : List Bool, (L x ↔ 0 < f x))

  ∧ (∀ L : List Bool → Prop,
      InBPP L → InFBPPNP (fun x => if L x then [true] else [false]))

  ∧ (∀ (q : ℕ) (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
      (x : List Bool) (t : ℕ),
      2 * ccQueries P A ρ x t + ccQueryBits P A ρ x t ≤ ccTime P A ρ x t)

  ∧ (∀ (ℓ : ℕ) (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool),
      x.length = ℓ →
      ccResult (ccCallMachine ℓ) A ρ x (ℓ + 1) = some true
        ∧ ccTime (ccCallMachine ℓ) A ρ x (ℓ + 1) = 2 * ℓ + 2
        ∧ ccQueries (ccCallMachine ℓ) A ρ x (ℓ + 1) = 1
        ∧ ccQueryBits (ccCallMachine ℓ) A ρ x (ℓ + 1) = ℓ
        ∧ ccCoinsRead (ccCallMachine ℓ) A ρ x (ℓ + 1) = 0)

  ∧ (∀ f : List Bool → ℕ, InSharpP f → ∃ A : List Bool → Bool, InSharpPOracle A f)
  ) :=
  fun H => clause1BadL_notInPP (H.2.1 clause1BadL clause1BadL_inNP)

/-- Running for `t + 1` steps is one machine step applied to the configuration after `t` steps. -/
private theorem clause11Aux_ccRun_succ {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) :
    ccRun P A ρ x (t + 1) = ccStep P A ρ (ccRun P A ρ x t) := rfl

/-- The coin-stream index after `t` machine steps is at most `t`. -/
private theorem clause11Aux_ccRun_coinIdx_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) : (ccRun P A ρ x t).coinIdx ≤ t := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [clause11Aux_ccRun_succ]
    cases h : P.states (ccRun P A ρ x n).state <;> simp [ccStep, h] <;> omega

/-- An accepting or rejecting configuration is fixed by `ccStep`. -/
private theorem clause11Aux_ccStep_halt {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (c : CcConfig q) (h : P.states c.state = CcAct.accept ∨ P.states c.state = CcAct.reject) :
    ccStep P A ρ c = c := by
  rcases h with h | h <;> simp [ccStep, h]

/-- If the machine is accepting or rejecting after `t` steps, its configuration after `t + k`
steps is unchanged. -/
private theorem clause11Aux_ccRun_absorb {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t k : ℕ)
    (h : P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject) :
    ccRun P A ρ x (t + k) = ccRun P A ρ x t := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 from rfl, clause11Aux_ccRun_succ, ih,
      clause11Aux_ccStep_halt P A ρ _ h]

/-- A machine result different from `none` implies that the current action is accepting or
rejecting. -/
private theorem clause11Aux_result_state {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) (h : ccResult P A ρ x t ≠ none) :
    P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject := by
  cases hs : P.states (ccRun P A ρ x t).state with
  | accept => exact Or.inl rfl
  | reject => exact Or.inr rfl
  | moveL q' => simp [ccResult, hs] at h
  | moveR q' => simp [ccResult, hs] at h
  | write b q' => simp [ccResult, hs] at h
  | branch qt qf => simp [ccResult, hs] at h
  | coinFlip qt qf => simp [ccResult, hs] at h
  | queryPush q' => simp [ccResult, hs] at h
  | oracleCall qt qf => simp [ccResult, hs] at h

/-- A polynomial-time program is in an accepting or rejecting state at its prescribed polynomial
step bound. -/
private theorem clause11Aux_polyTime_haltState {q : ℕ} (P : CcProgram q) (c k : ℕ)
    (hp : CcPolyTime P c k) (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    P.states (ccRun P A ρ x (c * x.length ^ k + c)).state = CcAct.accept ∨
      P.states (ccRun P A ρ x (c * x.length ^ k + c)).state = CcAct.reject :=
  clause11Aux_result_state P A ρ x (c * x.length ^ k + c) (hp A ρ x).1

/-- Coin streams agreeing at every index below `t` produce the same configuration after `t`
machine steps. -/
private theorem clause11Aux_ccRun_coinPrefix {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ1 ρ2 : ℕ → Bool) (x : List Bool) :
    ∀ t : ℕ, (∀ i, i < t → ρ1 i = ρ2 i) → ccRun P A ρ1 x t = ccRun P A ρ2 x t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
    intro hagr
    have hn : ∀ i, i < n → ρ1 i = ρ2 i := fun i hi => hagr i (by omega)
    have hc := ih hn
    rw [clause11Aux_ccRun_succ, clause11Aux_ccRun_succ, hc]
    have hle := clause11Aux_ccRun_coinIdx_le P A ρ2 x n
    have hcoin : ρ1 (ccRun P A ρ2 x n).coinIdx = ρ2 (ccRun P A ρ2 x n).coinIdx :=
      hagr _ (by omega)
    cases h : P.states (ccRun P A ρ2 x n).state <;> simp [ccStep, h, hcoin]

/-- The empty input and the singleton input `[false]` initialize the same configuration in the
tape model. -/
private theorem clause11Aux_ccInit_nil_eq {q : ℕ} : ccInit q [] = ccInit q [false] := by
  have htape : (fun i => ([] : List Bool).getD i false) = (fun i => [false].getD i false) := by
    funext i
    cases i with
    | zero => rfl
    | succ n => rfl
  simp only [ccInit]
  rw [htape]

/-- The empty input and `[false]` give identical runs for every step count, oracle, and coin
stream. -/
private theorem clause11Aux_ccRun_nil_false {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) : ∀ t : ℕ, ccRun P A ρ [] t = ccRun P A ρ [false] t := by
  intro t
  induction t with
  | zero => exact clause11Aux_ccInit_nil_eq (q := q)
  | succ n ih => rw [clause11Aux_ccRun_succ, clause11Aux_ccRun_succ, ih]

/-- Equal run configurations give equal output bit lists for the same program. -/
private theorem clause11Aux_ccOutput_congr {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ1 ρ2 : ℕ → Bool) (x1 x2 : List Bool) (t1 t2 : ℕ)
    (h : ccRun P A ρ1 x1 t1 = ccRun P A ρ2 x2 t2) :
    ccOutput P A ρ1 x1 t1 = ccOutput P A ρ2 x2 t2 := by
  simp only [ccOutput]
  rw [h]

/-- A verifier that accepts exactly when the initial tape bit is true and otherwise rejects. -/
def clause11Aux_badV : CcProgram 2 where
  states := fun i =>
    match (i : ℕ) with
    | 0 => CcAct.branch ⟨1, by omega⟩ ⟨2, by omega⟩
    | 1 => CcAct.accept
    | _ => CcAct.reject

/-- After one step, `clause11Aux_badV` has selected its accepting or rejecting state from the
first input bit and charged one time unit. -/
private theorem clause11Aux_ccRun_badV_one (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccRun clause11Aux_badV A ρ x 1 =
      ({ state := if x.getD 0 false then (⟨1, by omega⟩ : Fin 3) else ⟨2, by omega⟩
         tape := fun i => x.getD i false
         head := 0
         query := []
         coinIdx := 0
         time := 1
         queries := 0
         queryBits := 0
         coins := 0 } : CcConfig 2) := rfl

/-- The run of `clause11Aux_badV` is unchanged between one and two steps. -/
private theorem clause11Aux_ccRun_badV_two (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccRun clause11Aux_badV A ρ x 2 = ccRun clause11Aux_badV A ρ x 1 := by
  rw [clause11Aux_ccRun_succ, clause11Aux_ccRun_badV_one]
  cases x.getD 0 false <;> simp [ccStep, clause11Aux_badV]

/-- After one step, `clause11Aux_badV` returns the first input bit with default `false`. -/
private theorem clause11Aux_badV_result_one (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccResult clause11Aux_badV A ρ x 1 = some (x.getD 0 false) := by
  simp only [ccResult, clause11Aux_ccRun_badV_one]
  cases x.getD 0 false <;> simp [clause11Aux_badV]

/-- After two steps, `clause11Aux_badV` returns the first input bit with default `false`. -/
private theorem clause11Aux_badV_result_two (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccResult clause11Aux_badV A ρ x 2 = some (x.getD 0 false) := by
  have h := clause11Aux_badV_result_one A ρ x
  have hs : ccResult clause11Aux_badV A ρ x 2 = ccResult clause11Aux_badV A ρ x 1 := by
    simp only [ccResult]
    rw [clause11Aux_ccRun_badV_two]
  rw [hs]
  exact h

/-- The auxiliary first-bit verifier is polynomial-time with coefficient one and exponent zero. -/
theorem clause11Aux_badV_poly : CcPolyTime clause11Aux_badV 1 0 := by
  intro A ρ x
  have h2 : (1 : ℕ) * x.length ^ 0 + 1 = 2 := by simp
  constructor
  · rw [h2]
    intro hnone
    have hr := clause11Aux_badV_result_two A ρ x
    rw [hr] at hnone
    simp at hnone
  · rw [h2]
    show (ccRun clause11Aux_badV A ρ x 2).time ≤ 2
    rw [clause11Aux_ccRun_badV_two, clause11Aux_ccRun_badV_one]
    simp

/-- Verification by `clause11Aux_badV` reads the first bit of the concatenation of input and
witness, with default `false`. -/
private theorem clause11Aux_badV_verifies (x w : List Bool) :
    ccVerifies clause11Aux_badV 1 0 x w = (x ++ w).getD 0 false := by
  simp only [ccVerifies, ccAccepts, ccOracleAccepts]
  have h2 : (1 : ℕ) * (x ++ w).length ^ 0 + 1 = 2 := by simp
  rw [h2, clause11Aux_badV_result_two]
  simp

/-- Restricts a finite bit string to its initial segment of the specified shorter length. -/
private def clause11Aux_cutCoins {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) : Fin T0 → Bool :=
  fun i => ω ⟨(i : ℕ), lt_of_lt_of_le i.isLt h⟩

/-- Extracts the suffix remaining after the specified initial segment of a finite bit string. -/
private def clause11Aux_tailCoins {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) : Fin (T1 - T0) → Bool :=
  fun j => ω ⟨T0 + (j : ℕ), by omega⟩

/-- Concatenates a finite bit prefix with a suffix to obtain a bit string of the specified total
length. -/
private def clause11Aux_padCoins {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool) (u : Fin (T1 - T0) → Bool) :
    Fin T1 → Bool :=
  fun j => if hj : (j : ℕ) < T0 then b ⟨(j : ℕ), hj⟩ else u ⟨(j : ℕ) - T0, by omega⟩

/-- Concatenating the extracted prefix and suffix of a finite bit string recovers the original
string. -/
private theorem clause11Aux_pad_cut_tail {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) :
    clause11Aux_padCoins h (clause11Aux_cutCoins h ω) (clause11Aux_tailCoins h ω) = ω := by
  funext j
  by_cases hj : (j : ℕ) < T0
  · rw [clause11Aux_padCoins, dif_pos hj]
    show ω ⟨(j : ℕ), lt_of_lt_of_le hj h⟩ = ω j
    exact congrArg ω (Fin.ext rfl)
  · rw [clause11Aux_padCoins, dif_neg hj]
    have hval : T0 + ((j : ℕ) - T0) < T1 := by omega
    have hval2 : T0 + ((j : ℕ) - T0) = (j : ℕ) := by omega
    show ω (⟨T0 + ((j : ℕ) - T0), hval⟩ : Fin T1) = ω j
    exact congrArg ω (Fin.ext hval2)

/-- Extracting the prefix of a concatenated finite bit string recovers its given prefix. -/
private theorem clause11Aux_cut_pad {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool)
    (u : Fin (T1 - T0) → Bool) : clause11Aux_cutCoins h (clause11Aux_padCoins h b u) = b := by
  funext i
  have hi : (i : ℕ) < T0 := i.isLt
  have hi1 : (i : ℕ) < T1 := lt_of_lt_of_le hi h
  have hd2 : clause11Aux_padCoins h b u ⟨(i : ℕ), hi1⟩
      = if hx : (i : ℕ) < T0 then b ⟨(i : ℕ), hx⟩ else u ⟨(i : ℕ) - T0, by omega⟩ := rfl
  show clause11Aux_padCoins h b u ⟨(i : ℕ), hi1⟩ = b i
  rw [hd2, dif_pos hi]

/-- Extracting the suffix of a concatenated finite bit string recovers its given suffix. -/
private theorem clause11Aux_tail_pad {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool)
    (u : Fin (T1 - T0) → Bool) : clause11Aux_tailCoins h (clause11Aux_padCoins h b u) = u := by
  funext j
  have hT : T0 + (j : ℕ) < T1 := by omega
  have hm : T0 + (j : ℕ) - T0 < T1 - T0 := by omega
  have hval2 : T0 + (j : ℕ) - T0 = (j : ℕ) := by omega
  have hd2 : clause11Aux_padCoins h b u ⟨T0 + (j : ℕ), hT⟩
      = if hx : (T0 + (j : ℕ)) < T0 then b ⟨T0 + (j : ℕ), hx⟩
        else u ⟨T0 + (j : ℕ) - T0, hm⟩ := rfl
  show clause11Aux_padCoins h b u ⟨T0 + (j : ℕ), hT⟩ = u j
  rw [hd2, dif_neg (by omega)]
  exact congrArg u (Fin.ext hval2)

/-- The number of Boolean words of a fixed finite length is two raised to that length. -/
private theorem clause11Aux_card_pi_bool (d : ℕ) : Fintype.card (Fin d → Bool) = 2 ^ d := by
  simp [Fintype.card_pi, Finset.prod_const]

/-- The number of longer bit strings satisfying a condition on their prefix is the number of
valid prefixes times `2 ^ (T1 - T0)`. -/
private theorem clause11Aux_card_cut_fiber (T0 T1 : ℕ) (h : T0 ≤ T1) (G : (Fin T0 → Bool) → Bool) :
    (Finset.univ.filter (fun ω : Fin T1 → Bool => G (clause11Aux_cutCoins h ω))).card =
      (Finset.univ.filter (fun b : Fin T0 → Bool => G b)).card * 2 ^ (T1 - T0) := by
  classical
  have h2 : (2 : ℕ) ^ (T1 - T0) = (Finset.univ : Finset (Fin (T1 - T0) → Bool)).card := by
    rw [Finset.card_univ, clause11Aux_card_pi_bool]
  rw [h2, ← Finset.card_product]
  refine Finset.card_nbij' (i := fun ω => (clause11Aux_cutCoins h ω, clause11Aux_tailCoins h ω))
    (j := fun p => clause11Aux_padCoins h p.1 p.2) ?_ ?_ ?_ ?_
  · intro a ha
    have ha1 : G (clause11Aux_cutCoins h a) = true :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    apply Finset.mem_coe.mpr
    rw [Finset.mem_product]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
    exact ha1
  · intro p hp
    have hp1 := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    have hp2 := Finset.mem_filter.mp hp1.1
    apply Finset.mem_coe.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [clause11Aux_cut_pad]
    exact hp2.2
  · intro a _
    exact clause11Aux_pad_cut_tail h a
  · intro p _
    obtain ⟨b, u⟩ := p
    exact Prod.ext (clause11Aux_cut_pad h b u) (clause11Aux_tail_pad h b u)

/-- With precision parameter one and target count one, `ccApproxOK` holds exactly for output
count one. -/
theorem clause11Aux_approxOK_one (y : ℕ) : ccApproxOK 1 y 1 = true ↔ y = 1 := by
  simp [ccApproxOK]
  constructor <;> intro h <;> omega

/-- With precision parameter one and target count zero, `ccApproxOK` holds exactly for output
count zero. -/
theorem clause11Aux_approxOK_zero (y : ℕ) : ccApproxOK 1 y 0 = true ↔ y = 0 := by
  simp [ccApproxOK]

/-- The auxiliary verifier's relation count with witness parameter one is one on empty input. -/
theorem clause11Aux_relCount_nil : ccRelCount clause11Aux_badV 1 0 1 [] = 1 := by decide

/-- The auxiliary verifier's relation count with witness parameter one is zero on `[false]`. -/
theorem clause11Aux_relCount_false : ccRelCount clause11Aux_badV 1 0 1 [false] = 0 := by decide

/-- The Boolean predicate reading the first list bit with default `false`. -/
def clause11Aux_predA : List Bool → Bool := fun z => z.getD 0 false

/-- The oracle relation count for `clause11Aux_predA` with witness parameter one is one on empty
input. -/
theorem clause11Aux_oracleRelCount_nil : ccOracleRelCount clause11Aux_predA 1 [] = 1 := by decide

/-- The oracle relation count for `clause11Aux_predA` with witness parameter one is zero on
`[false]`. -/
theorem clause11Aux_oracleRelCount_false : ccOracleRelCount clause11Aux_predA 1 [false] = 0 := by
    decide

/-- The polynomial budget on the empty input is at most the budget on a singleton input. -/
private theorem clause11Aux_budget_le (cE kE : ℕ) : cE * 0 ^ kE + cE ≤ cE * 1 ^ kE + cE := by
  by_cases hk : kE = 0
  · subst hk; norm_num
  · rw [Nat.zero_pow (by omega), Nat.one_pow kE]; omega

/-- For targets with disjoint acceptable estimates, the padded good-estimate count on `[]` plus
the good-estimate count on `[false]` is at most the total number of longer coin strings. -/
private theorem clause11Aux_good_conflict {qE : ℕ} (E : CcProgram qE) (cE kE d N0 N1 : ℕ)
    (hpoly : CcPolyTime E cE kE) (A : List Bool → Bool)
    (hdis : ∀ y : ℕ, ccApproxOK d y N0 = true → ccApproxOK d y N1 = true → False) :
    ccEstGoodCount E A [] (cE * 0 ^ kE + cE) d N0
        * 2 ^ ((cE * 1 ^ kE + cE) - (cE * 0 ^ kE + cE))
        + ccEstGoodCount E A [false] (cE * 1 ^ kE + cE) d N1
      ≤ 2 ^ (cE * 1 ^ kE + cE) := by
  have hle : cE * 0 ^ kE + cE ≤ cE * 1 ^ kE + cE := clause11Aux_budget_le cE kE

  have hpoint : ∀ ω : Fin (cE * 1 ^ kE + cE) → Bool,
      ccOutput E A (ccCoinString ω) [false] (cE * 1 ^ kE + cE)
        = ccOutput E A (ccCoinString (clause11Aux_cutCoins hle ω)) [] (cE * 0 ^ kE + cE) := by
    intro ω
    have hpref : ∀ i : ℕ, i < cE * 0 ^ kE + cE →
        ccCoinString ω i = ccCoinString (clause11Aux_cutCoins hle ω) i := by
      intro i hi
      simp only [ccCoinString]
      rw [dif_pos (show i < cE * 1 ^ kE + cE from by omega), dif_pos hi]
      rfl
    have hrun0 : ccRun E A (ccCoinString ω) [] (cE * 0 ^ kE + cE)
        = ccRun E A (ccCoinString (clause11Aux_cutCoins hle ω)) [] (cE * 0 ^ kE + cE) :=
      clause11Aux_ccRun_coinPrefix E A (ccCoinString ω) (ccCoinString (clause11Aux_cutCoins hle ω)) []
        (cE * 0 ^ kE + cE) hpref
    have hrun1 : ccRun E A (ccCoinString ω) [false] (cE * 0 ^ kE + cE)
        = ccRun E A (ccCoinString ω) [] (cE * 0 ^ kE + cE) :=
      (clause11Aux_ccRun_nil_false E A (ccCoinString ω) (cE * 0 ^ kE + cE)).symm
    have hres0 := hpoly A (ccCoinString (clause11Aux_cutCoins hle ω)) []
    have hres0' : ccResult E A (ccCoinString (clause11Aux_cutCoins hle ω)) []
        (cE * 0 ^ kE + cE) ≠ none := hres0.1
    have hhalt0 := clause11Aux_result_state E A (ccCoinString (clause11Aux_cutCoins hle ω)) []
      (cE * 0 ^ kE + cE) hres0'
    have hhalt1 : E.states (ccRun E A (ccCoinString ω) [false] (cE * 0 ^ kE + cE)).state
        = CcAct.accept ∨
        E.states (ccRun E A (ccCoinString ω) [false] (cE * 0 ^ kE + cE)).state = CcAct.reject := by
      rw [hrun1, hrun0]
      exact hhalt0
    have hab0 : ccRun E A (ccCoinString (clause11Aux_cutCoins hle ω)) [] (cE * 1 ^ kE + cE)
        = ccRun E A (ccCoinString (clause11Aux_cutCoins hle ω)) [] (cE * 0 ^ kE + cE) := by
      have h := clause11Aux_ccRun_absorb E A (ccCoinString (clause11Aux_cutCoins hle ω)) []
        (cE * 0 ^ kE + cE) ((cE * 1 ^ kE + cE) - (cE * 0 ^ kE + cE)) hhalt0
      rw [Nat.add_sub_cancel' hle] at h
      exact h
    have hab1 : ccRun E A (ccCoinString ω) [false] (cE * 1 ^ kE + cE)
        = ccRun E A (ccCoinString ω) [false] (cE * 0 ^ kE + cE) := by
      have h := clause11Aux_ccRun_absorb E A (ccCoinString ω) [false]
        (cE * 0 ^ kE + cE) ((cE * 1 ^ kE + cE) - (cE * 0 ^ kE + cE)) hhalt1
      rw [Nat.add_sub_cancel' hle] at h
      exact h
    have ho1 : ccOutput E A (ccCoinString ω) [false] (cE * 1 ^ kE + cE)
        = ccOutput E A (ccCoinString ω) [false] (cE * 0 ^ kE + cE) :=
      clause11Aux_ccOutput_congr E A (ccCoinString ω) (ccCoinString ω) [false] [false]
        (cE * 1 ^ kE + cE) (cE * 0 ^ kE + cE) hab1
    have ho2 : ccOutput E A (ccCoinString ω) [false] (cE * 0 ^ kE + cE)
        = ccOutput E A (ccCoinString ω) [] (cE * 0 ^ kE + cE) :=
      clause11Aux_ccOutput_congr E A (ccCoinString ω) (ccCoinString ω) [false] []
        (cE * 0 ^ kE + cE) (cE * 0 ^ kE + cE) hrun1
    have ho3 : ccOutput E A (ccCoinString ω) [] (cE * 0 ^ kE + cE)
        = ccOutput E A (ccCoinString (clause11Aux_cutCoins hle ω)) [] (cE * 0 ^ kE + cE) :=
      clause11Aux_ccOutput_congr E A (ccCoinString ω) (ccCoinString (clause11Aux_cutCoins hle ω)) [] []
        (cE * 0 ^ kE + cE) (cE * 0 ^ kE + cE) hrun0
    exact ho1.trans (ho2.trans ho3)

  have hfeq : (Finset.univ.filter (fun ω : Fin (cE * 1 ^ kE + cE) → Bool =>
        ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString ω) [false] (cE * 1 ^ kE + cE))) N1
          = true))
      = (Finset.univ.filter (fun ω : Fin (cE * 1 ^ kE + cE) → Bool =>
        ccApproxOK d
          (ccBitsToNat
            (ccOutput E A (ccCoinString (clause11Aux_cutCoins hle ω)) [] (cE * 0 ^ kE + cE))) N1 = true)) := by
    apply Finset.filter_congr
    intro ω _
    rw [hpoint ω]
  have hgood1 : ccEstGoodCount E A [false] (cE * 1 ^ kE + cE) d N1
      = (Finset.univ.filter (fun ω : Fin (cE * 1 ^ kE + cE) → Bool =>
        ccApproxOK d
          (ccBitsToNat
            (ccOutput E A (ccCoinString (clause11Aux_cutCoins hle ω)) [] (cE * 0 ^ kE + cE))) N1
            = true)).card := congrArg Finset.card hfeq
  have hfib : (Finset.univ.filter (fun ω : Fin (cE * 1 ^ kE + cE) → Bool =>
        ccApproxOK d
          (ccBitsToNat
            (ccOutput E A (ccCoinString (clause11Aux_cutCoins hle ω)) [] (cE * 0 ^ kE + cE))) N1
            = true)).card
      = (Finset.univ.filter (fun b : Fin (cE * 0 ^ kE + cE) → Bool =>
          ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N1
            = true)).card
          * 2 ^ ((cE * 1 ^ kE + cE) - (cE * 0 ^ kE + cE)) :=
    clause11Aux_card_cut_fiber _ _ hle
      (fun b => ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N1)

  have hdisj : Disjoint
      (Finset.univ.filter (fun b : Fin (cE * 0 ^ kE + cE) → Bool =>
        ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N0 = true))
      (Finset.univ.filter (fun b : Fin (cE * 0 ^ kE + cE) → Bool =>
        ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N1
          = true)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    subst heq
    exact hdis _ (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hcu : (Finset.univ : Finset (Fin (cE * 0 ^ kE + cE) → Bool)).card
      = 2 ^ (cE * 0 ^ kE + cE) := by
    rw [Finset.card_univ, clause11Aux_card_pi_bool]
  have hsum : (Finset.univ.filter (fun b : Fin (cE * 0 ^ kE + cE) → Bool =>
        ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N0
          = true)).card
      + (Finset.univ.filter (fun b : Fin (cE * 0 ^ kE + cE) → Bool =>
        ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N1
          = true)).card
      ≤ 2 ^ (cE * 0 ^ kE + cE) := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have hsub : (Finset.univ.filter (fun b : Fin (cE * 0 ^ kE + cE) → Bool =>
          ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N0
            = true))
        ∪ (Finset.univ.filter (fun b : Fin (cE * 0 ^ kE + cE) → Bool =>
          ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N1
            = true)) ⊆ Finset.univ := by
      intro x _
      simp
    calc _ ≤ (Finset.univ : Finset (Fin (cE * 0 ^ kE + cE) → Bool)).card :=
        Finset.card_le_card hsub
      _ = 2 ^ (cE * 0 ^ kE + cE) := hcu

  have hpow : 2 ^ (cE * 1 ^ kE + cE)
      = 2 ^ (cE * 0 ^ kE + cE) * 2 ^ ((cE * 1 ^ kE + cE) - (cE * 0 ^ kE + cE)) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
  have hgood0 : ccEstGoodCount E A [] (cE * 0 ^ kE + cE) d N0
      = (Finset.univ.filter (fun b : Fin (cE * 0 ^ kE + cE) → Bool =>
        ccApproxOK d (ccBitsToNat (ccOutput E A (ccCoinString b) [] (cE * 0 ^ kE + cE))) N0
          = true)).card := rfl
  rw [hgood0, hgood1, hfib, ← Nat.add_mul, hpow]
  exact Nat.mul_le_mul_right _ hsum

/-- Two success counts each at least three quarters of their coin spaces cannot satisfy the
stated disjointness bound after padding to a common length. -/
private theorem clause11Aux_impossible (t0 t1 good0 good1 : ℕ) (hle : t0 ≤ t1)
    (h0 : 4 * good0 ≥ 3 * 2 ^ t0) (h1 : 4 * good1 ≥ 3 * 2 ^ t1)
    (hb : good0 * 2 ^ (t1 - t0) + good1 ≤ 2 ^ t1) : False := by
  have hpow : 2 ^ t1 = 2 ^ t0 * 2 ^ (t1 - t0) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
  have hstep2 : 3 * 2 ^ t1 ≤ 4 * good0 * 2 ^ (t1 - t0) := by
    have h0m : 3 * 2 ^ t0 * 2 ^ (t1 - t0) ≤ 4 * good0 * 2 ^ (t1 - t0) :=
      Nat.mul_le_mul_right _ h0
    have hp : 3 * 2 ^ t0 * 2 ^ (t1 - t0) = 3 * 2 ^ t1 := by
      rw [hpow]; ring
    rw [← hp]; exact h0m
  have hstep3 : 6 * 2 ^ t1 ≤ 4 * good0 * 2 ^ (t1 - t0) + 4 * good1 := by
    have hadd := Nat.add_le_add hstep2 h1
    have hsum3 : 3 * 2 ^ t1 + 3 * 2 ^ t1 = 6 * 2 ^ t1 := by ring
    rw [hsum3] at hadd
    exact hadd
  have hstep4 : 4 * good0 * 2 ^ (t1 - t0) + 4 * good1 ≤ 4 * 2 ^ t1 := by
    have h := Nat.mul_le_mul_left 4 hb
    rw [Nat.mul_add, ← Nat.mul_assoc] at h
    exact h
  have hfin : 6 * 2 ^ t1 ≤ 4 * 2 ^ t1 := le_trans hstep3 hstep4
  have hpos : 0 < 2 ^ t1 := Nat.pow_pos (by norm_num)
  omega

/-- The stated uniform relation-count estimator specification with its hash-witness NP
condition, success bounds, and resource bounds is false in this tape model. -/
theorem clause2_clause1_counter :
    ¬ (∀ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k → ∀ (d s : ℕ),
        ∃ (qE cE kE : ℕ) (E : CcProgram qE),
          CcPolyTime E cE kE
            ∧ CcInNPSet (ccHashWitnessSet V c k p)
            ∧ ∀ x : List Bool,
              2 ^ (s + 1)
                  * ccEstGoodCount E (ccOracleOf (ccHashWitnessSet V c k p)) x
                      (cE * x.length ^ kE + cE) d (ccRelCount V c k p x)
                ≥ (2 ^ (s + 1) - 1) * 2 ^ (cE * x.length ^ kE + cE)
                ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                    ccCoinsRead E (ccOracleOf (ccHashWitnessSet V c k p))
                        (ccCoinString ω) x (cE * x.length ^ kE + cE)
                      ≤ 64 * (d + 1) ^ 4 * (s + 1)
                          * (x.length + (p * x.length ^ p + p) + 2) ^ 4)
                ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                    ccQueries E (ccOracleOf (ccHashWitnessSet V c k p))
                        (ccCoinString ω) x (cE * x.length ^ kE + cE)
                      ≤ 64 * (d + 1) ^ 4 * (s + 1)
                          * (x.length + (p * x.length ^ p + p) + 2))
                ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                    ccTime E (ccOracleOf (ccHashWitnessSet V c k p))
                        (ccCoinString ω) x (cE * x.length ^ kE + cE)
                      ≤ 4096 * (d + 1) ^ 4 * (s + 1)
                          * (x.length + (p * x.length ^ p + p) + 2) ^ 8)) := by
  intro h
  obtain ⟨qE, cE, kE, E, hpoly, _, hgood⟩ := h 2 1 0 1 clause11Aux_badV clause11Aux_badV_poly 1 1
  set A : List Bool → Bool := ccOracleOf (ccHashWitnessSet clause11Aux_badV 1 0 1)
  have hdis : ∀ y : ℕ, ccApproxOK 1 y 1 = true → ccApproxOK 1 y 0 = true → False := by
    intro y ha hb
    have hy1 : y = 1 := (clause11Aux_approxOK_one y).mp ha
    have hy0 : y = 0 := (clause11Aux_approxOK_zero y).mp hb
    omega
  have hconf := clause11Aux_good_conflict E cE kE 1 1 0 hpoly A hdis
  have hg0 := (hgood []).1
  have hg1 := (hgood [false]).1
  have hlen0 : (cE * ([] : List Bool).length ^ kE + cE) = cE * 0 ^ kE + cE := rfl
  have hlen1 : (cE * ([false] : List Bool).length ^ kE + cE) = cE * 1 ^ kE + cE := rfl
  rw [hlen0, clause11Aux_relCount_nil] at hg0
  rw [hlen1, clause11Aux_relCount_false] at hg1
  have h4 : (2:ℕ) ^ (1 + 1) = 4 := rfl
  have h3 : (2:ℕ) ^ (1 + 1) - 1 = 3 := rfl
  rw [h3, h4] at hg0 hg1
  exact clause11Aux_impossible (cE * 0 ^ kE + cE) (cE * 1 ^ kE + cE)
    (ccEstGoodCount E A [] (cE * 0 ^ kE + cE) 1 1)
    (ccEstGoodCount E A [false] (cE * 1 ^ kE + cE) 1 0)
    (clause11Aux_budget_le cE kE) hg0 hg1 hconf

/-- The stated uniform oracle relation-count estimator specification, including the relative NP
hash-witness condition and resource bounds, is false in this tape model. -/
theorem clause2_clause3_counter :
    ¬ (∀ (A : List Bool → Bool) (p d s : ℕ),
        ∃ (qE cE kE : ℕ) (E : CcProgram qE),
          CcPolyTime E cE kE
            ∧ CcInNPOracleSet A (ccHashWitnessOracleSet A p)
            ∧ ∀ x : List Bool,
              2 ^ (s + 1)
                  * ccEstGoodCount E (ccOracleOf (ccHashWitnessOracleSet A p)) x
                      (cE * x.length ^ kE + cE) d (ccOracleRelCount A p x)
                ≥ (2 ^ (s + 1) - 1) * 2 ^ (cE * x.length ^ kE + cE)
                ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                    ccCoinsRead E (ccOracleOf (ccHashWitnessOracleSet A p))
                        (ccCoinString ω) x (cE * x.length ^ kE + cE)
                      ≤ 64 * (d + 1) ^ 4 * (s + 1)
                          * (x.length + (p * x.length ^ p + p) + 2) ^ 4)
                ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                    ccQueries E (ccOracleOf (ccHashWitnessOracleSet A p))
                        (ccCoinString ω) x (cE * x.length ^ kE + cE)
                      ≤ 64 * (d + 1) ^ 4 * (s + 1)
                          * (x.length + (p * x.length ^ p + p) + 2))
                ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                    ccTime E (ccOracleOf (ccHashWitnessOracleSet A p))
                        (ccCoinString ω) x (cE * x.length ^ kE + cE)
                      ≤ 4096 * (d + 1) ^ 4 * (s + 1)
                          * (x.length + (p * x.length ^ p + p) + 2) ^ 8)) := by
  intro h
  obtain ⟨qE, cE, kE, E, hpoly, _, hgood⟩ := h clause11Aux_predA 1 1 1
  set A : List Bool → Bool := ccOracleOf (ccHashWitnessOracleSet clause11Aux_predA 1)
  have hdis : ∀ y : ℕ, ccApproxOK 1 y 1 = true → ccApproxOK 1 y 0 = true → False := by
    intro y ha hb
    have hy1 : y = 1 := (clause11Aux_approxOK_one y).mp ha
    have hy0 : y = 0 := (clause11Aux_approxOK_zero y).mp hb
    omega
  have hconf := clause11Aux_good_conflict E cE kE 1 1 0 hpoly A hdis
  have hg0 := (hgood []).1
  have hg1 := (hgood [false]).1
  have hlen0 : (cE * ([] : List Bool).length ^ kE + cE) = cE * 0 ^ kE + cE := rfl
  have hlen1 : (cE * ([false] : List Bool).length ^ kE + cE) = cE * 1 ^ kE + cE := rfl
  rw [hlen0, clause11Aux_oracleRelCount_nil] at hg0
  rw [hlen1, clause11Aux_oracleRelCount_false] at hg1
  have h4 : (2:ℕ) ^ (1 + 1) = 4 := rfl
  have h3 : (2:ℕ) ^ (1 + 1) - 1 = 3 := rfl
  rw [h3, h4] at hg0 hg1
  exact clause11Aux_impossible (cE * 0 ^ kE + cE) (cE * 1 ^ kE + cE)
    (ccEstGoodCount E A [] (cE * 0 ^ kE + cE) 1 1)
    (ccEstGoodCount E A [false] (cE * 1 ^ kE + cE) 1 0)
    (clause11Aux_budget_le cE kE) hg0 hg1 hconf

/-- Existential quantification over a Boolean word of length zero is equivalent to the predicate
at the unique empty word. -/
theorem exists_fin0_bool {Q : (Fin 0 → Bool) → Prop} :
    (∃ w : Fin 0 → Bool, Q w) ↔ Q (fun i => absurd i.isLt (by omega)) := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := h
    have : w = (fun i : Fin 0 => absurd i.isLt (by omega)) := by
      funext i
      exact absurd i.isLt (by omega)
    rw [← this]
    exact hw
  · intro h
    exact ⟨fun i => absurd i.isLt (by omega), h⟩

/-- Every language in level zero of `InPHLevel` is in level one. -/
theorem clause1_clause4_k0 : ∀ L : List Bool → Prop, InPHLevel 0 L → InPHLevel 1 L := by
  intro L h
  obtain ⟨q, c, k, p, V, hpoly, hL⟩ := h
  refine ⟨q, c, k, 0, V, hpoly, ?_⟩
  intro x
  have hplen : (0 : ℕ) * x.length ^ 0 + 0 = 0 := by
    simp
  have halt : ccAlt true 0 (fun z => ccAccepts V c k z = true) 1 x
      ↔ (ccAccepts V c k x = true) := by
    show (∃ w : Fin 0 → Bool, ccAlt false 0 (fun z => ccAccepts V c k z = true) 0 (x ++ List.ofFn w))
      ↔ (ccAccepts V c k x = true)
    rw [exists_fin0_bool]
    show ccAlt false 0 (fun z => ccAccepts V c k z = true)
        0 (x ++ List.ofFn (fun i : Fin 0 => absurd i.isLt (by omega)))
      ↔ (ccAccepts V c k x = true)
    have hof : List.ofFn (fun i : Fin 0 => absurd i.isLt (by omega)) = ([] : List Bool) := by
      simp [List.ofFn]
    rw [hof, List.append_nil]
    rfl
  rw [hplen, halt]
  exact hL x

/-- Invariance of a language predicate under appending an arbitrary Boolean block of length
`plen`. -/
def RobustAlt (plen : ℕ) (D : List Bool → Prop) : Prop :=
  ∀ (z : List Bool) (w : Fin plen → Bool), D (z ++ List.ofFn w) ↔ D z

/-- For a predicate invariant under appending blocks of width `plen`, adding one alternation
level leaves `ccAlt` unchanged. -/
theorem ccAlt_succ_robust {plen : ℕ} {D : List Bool → Prop} (h : RobustAlt plen D) :
    ∀ (lev : ℕ) (ex : Bool) (z : List Bool),
      ccAlt ex plen D (lev + 1) z ↔ ccAlt ex plen D lev z := by
  intro lev
  induction lev with
  | zero =>
    intro ex z
    unfold ccAlt
    cases ex with
    | true =>
      rw [if_pos rfl]
      show (∃ w : Fin plen → Bool, D (z ++ List.ofFn w)) ↔ D z
      constructor
      · intro hx
        obtain ⟨w, hw⟩ := hx
        exact (h z w).mp hw
      · intro hd
        exact ⟨fun _ => false, (h z _).mpr hd⟩
    | false =>
      rw [if_neg (by decide)]
      show (∀ w : Fin plen → Bool, D (z ++ List.ofFn w)) ↔ D z
      constructor
      · intro hx
        exact (h z (fun _ => false)).mp (hx fun _ => false)
      · intro hd w
        exact (h z w).mpr hd
  | succ k ih =>
    intro ex z
    unfold ccAlt
    cases ex with
    | true =>
      rw [if_pos rfl, if_pos rfl]
      show (∃ w : Fin plen → Bool, ccAlt false plen D (k + 1) (z ++ List.ofFn w))
        ↔ (∃ w : Fin plen → Bool, ccAlt false plen D k (z ++ List.ofFn w))
      constructor
      · intro hx
        obtain ⟨w, hw⟩ := hx
        exact ⟨w, (ih false (z ++ List.ofFn w)).mp hw⟩
      · intro hx
        obtain ⟨w, hw⟩ := hx
        exact ⟨w, (ih false (z ++ List.ofFn w)).mpr hw⟩
    | false =>
      rw [if_neg (by decide), if_neg (by decide)]
      show (∀ w : Fin plen → Bool, ccAlt true plen D (k + 1) (z ++ List.ofFn w))
        ↔ (∀ w : Fin plen → Bool, ccAlt true plen D k (z ++ List.ofFn w))
      constructor
      · intro hx w
        exact (ih true (z ++ List.ofFn w)).mp (hx w)
      · intro hx w
        exact (ih true (z ++ List.ofFn w)).mpr (hx w)

/-- Running for `t + 1` steps is one machine step applied to the configuration after `t` steps. -/
private lemma clause19Aux_ccRun_succ {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) :
    ccRun P A ρ x (t + 1) = ccStep P A ρ (ccRun P A ρ x t) := rfl

/-- Inputs with the same values under `getD` with default `false` initialize identical machine
configurations. -/
private lemma clause19Aux_ccInit_tape {q : ℕ} (x y : List Bool)
    (h : ∀ i, x.getD i false = y.getD i false) : ccInit q x = ccInit q y := by
  have ht : (fun i => x.getD i false) = (fun i => y.getD i false) := funext h
  simp only [ccInit]
  rw [ht]

/-- Inputs representing the same tape under `getD` with default `false` produce identical runs
at every step count. -/
private lemma clause19Aux_ccRun_tape {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x y : List Bool) (h : ∀ i, x.getD i false = y.getD i false) :
    ∀ t, ccRun P A ρ x t = ccRun P A ρ y t := by
  intro t
  induction t with
  | zero => exact clause19Aux_ccInit_tape x y h
  | succ n ih => rw [clause19Aux_ccRun_succ, clause19Aux_ccRun_succ, ih]

/-- A machine result different from `none` implies that the current action is accepting or
rejecting. -/
private lemma clause19Aux_result_state {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) (h : ccResult P A ρ x t ≠ none) :
    P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject := by
  cases hs : P.states (ccRun P A ρ x t).state with
  | accept => exact Or.inl rfl
  | reject => exact Or.inr rfl
  | moveL q' => simp [ccResult, hs] at h
  | moveR q' => simp [ccResult, hs] at h
  | write b q' => simp [ccResult, hs] at h
  | branch qt qf => simp [ccResult, hs] at h
  | coinFlip qt qf => simp [ccResult, hs] at h
  | queryPush q' => simp [ccResult, hs] at h
  | oracleCall qt qf => simp [ccResult, hs] at h

/-- An accepting or rejecting configuration is fixed by `ccStep`. -/
private lemma clause19Aux_ccStep_halt {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (c : CcConfig q) (h : P.states c.state = CcAct.accept ∨ P.states c.state = CcAct.reject) :
    ccStep P A ρ c = c := by
  rcases h with h | h <;> simp [ccStep, h]

/-- If the machine is accepting or rejecting after `t` steps, its configuration after `t + k`
steps is unchanged. -/
private lemma clause19Aux_ccRun_absorb {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t k : ℕ)
    (h : P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject) :
    ccRun P A ρ x (t + k) = ccRun P A ρ x t := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 from rfl, clause19Aux_ccRun_succ, ih, clause19Aux_ccStep_halt P A ρ _ h]

/-- Once a run reaches an accepting or rejecting state at time `t`, every later step bound gives
the same configuration. -/
private lemma clause19Aux_ccRun_halt_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t t' : ℕ)
    (hhalt : P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject)
    (hle : t ≤ t') : ccRun P A ρ x t' = ccRun P A ρ x t := by
  have h := clause19Aux_ccRun_absorb P A ρ x t (t' - t) hhalt
  rw [Nat.add_sub_cancel' hle] at h
  exact h

/-- Raising natural numbers to the same natural exponent preserves their order. -/
private lemma clause19Aux_pow_mono {a b k : ℕ} (h : a ≤ b) : a ^ k ≤ b ^ k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have ha : a ^ (k + 1) = a ^ k * a := rfl
    have hb : b ^ (k + 1) = b ^ k * b := rfl
    rw [ha, hb]
    exact Nat.mul_le_mul ih h

/-- A polynomial-time program has equal acceptance values on two identical represented tapes
when the first input is no longer than the second. -/
private lemma clause19Aux_accepts_mono {q : ℕ} (P : CcProgram q) (c k : ℕ) (hp : CcPolyTime P c k)
    (x y : List Bool) (hgetD : ∀ i, x.getD i false = y.getD i false)
    (hlen : x.length ≤ y.length) : ccAccepts P c k x = ccAccepts P c k y := by
  have hpow : x.length ^ k ≤ y.length ^ k := clause19Aux_pow_mono hlen
  have hle : c * x.length ^ k + c ≤ c * y.length ^ k + c := by
    have h2 : c * x.length ^ k ≤ c * y.length ^ k := Nat.mul_le_mul_left c hpow
    omega
  have hrun : ∀ t, ccRun P ccZeroOracle ccDefaultCoin x t
      = ccRun P ccZeroOracle ccDefaultCoin y t :=
    clause19Aux_ccRun_tape P ccZeroOracle ccDefaultCoin x y hgetD
  have hp1 := hp ccZeroOracle ccDefaultCoin x
  have hhalt := clause19Aux_result_state P ccZeroOracle ccDefaultCoin x
      (c * x.length ^ k + c) hp1.1
  have habs := clause19Aux_ccRun_halt_le P ccZeroOracle ccDefaultCoin x
      (c * x.length ^ k + c) (c * y.length ^ k + c) hhalt hle
  have hy : ccRun P ccZeroOracle ccDefaultCoin y (c * y.length ^ k + c)
      = ccRun P ccZeroOracle ccDefaultCoin x (c * x.length ^ k + c) := by
    rw [← hrun (c * y.length ^ k + c)]
    exact habs
  have key : ccResult P ccZeroOracle ccDefaultCoin x (c * x.length ^ k + c)
      = ccResult P ccZeroOracle ccDefaultCoin y (c * y.length ^ k + c) := by
    simp only [ccResult, hy]
  simp only [ccAccepts, ccOracleAccepts, key]

/-- Appending any number of false bits leaves every list lookup with default `false` unchanged. -/
private lemma clause19Aux_getD_replicate_tail (a : List Bool) (n i : ℕ) :
    (a ++ List.replicate n false).getD i false = a.getD i false := by
  by_cases h : i < a.length
  · exact List.getD_append a (List.replicate n false) false i h
  · have ha : a.getD i false = false :=
      List.getD_eq_default (l := a) (d := false) (by omega)
    have h2 : (a ++ List.replicate n false).getD i false
        = (List.replicate n false).getD (i - a.length) false :=
      List.getD_append_right a (List.replicate n false) false i (by omega)
    rw [h2, ha]
    by_cases h3 : i - a.length < n
    · exact List.getD_replicate (x := false) h3
    · exact List.getD_eq_default (l := List.replicate n false) (d := false)
        (by simp only [List.length_replicate]; omega)

/-- The program whose sole state is accepting. -/
def clause19Aux_Macc : CcProgram 0 where
  states := fun _ => CcAct.accept

/-- The always-accepting program remains in its initial configuration at every step bound. -/
lemma clause19Aux_Macc_run {A : List Bool → Bool} {ρ : ℕ → Bool} {x : List Bool} {t : ℕ} :
    ccRun clause19Aux_Macc A ρ x t = ccInit 0 x := by
  induction t with
  | zero => rfl
  | succ n ih => rw [clause19Aux_ccRun_succ, ih]; rfl

/-- The always-accepting program is polynomial-time with coefficient one and exponent zero. -/
lemma clause19Aux_Macc_poly : CcPolyTime clause19Aux_Macc 1 0 := by
  intro A ρ x
  constructor
  · intro hnone
    have hr : ccResult clause19Aux_Macc A ρ x (1 * x.length ^ 0 + 1) = some true := rfl
    exact Option.some_ne_none true (hr.symm.trans hnone)
  · show (ccRun clause19Aux_Macc A ρ x (1 * x.length ^ 0 + 1)).time ≤ 1 * x.length ^ 0 + 1
    rw [clause19Aux_Macc_run]
    simp [ccInit]

/-- The one-mode, one-particle occupation with occupation number one. -/
def g19r_S₀ : FockOccupation 1 1 := ⟨fun _ => ⟨1, by omega⟩, by simp⟩

/-- Every one-mode, one-particle Fock occupation equals `g19r_S₀`. -/
lemma g19r_S₀_unique : ∀ S : FockOccupation 1 1, S = g19r_S₀ := by
  intro S
  apply Subtype.ext
  funext i
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  have hsum : ∀ T : FockOccupation 1 1, ((T.1 (⟨0, by omega⟩ : Fin 1) : Fin 2) : ℕ) = 1 := by
    intro T
    have h := T.2
    rw [Fin.sum_univ_one] at h
    exact h
  have hval : ((S.1 i : Fin 2) : ℕ) = 1 := by
    rw [show i = (⟨0, by omega⟩ : Fin 1) from Fin.ext hi]
    exact hsum S
  have hfin : (S.1 i : Fin 2) = ⟨1, by omega⟩ := by
    apply Fin.ext
    simpa using hval
  have h0 : (g19r_S₀.1 i : Fin 2) = ⟨1, by omega⟩ := rfl
  rw [hfin, h0]

/-- The type of one-mode, one-particle Fock occupations has cardinality one. -/
lemma clause19Aux_card : Fintype.card (FockOccupation 1 1) = 1 :=
  Fintype.card_eq_one_of_forall_eq g19r_S₀_unique

/-- A one-bit sampler that always outputs the unique one-mode, one-particle occupation. -/
def clause19Aux_Sam : LoSampler 1 1 := ⟨1, fun _ => g19r_S₀⟩

/-- The auxiliary sampler uses a positive number of random bits. -/
lemma clause19Aux_Sam_L : 0 < clause19Aux_Sam.L := by decide

/-- Every occupation in the one-mode, one-particle space has probability one under the auxiliary
sampler. -/
lemma clause19Aux_samplerDist_all (S : FockOccupation 1 1) : loSamplerDist clause19Aux_Sam S = 1 := by
  rw [g19r_S₀_unique S]
  have h : ∀ r : Fin clause19Aux_Sam.L → Bool, clause19Aux_Sam.O r = g19r_S₀ := fun _ => rfl
  simp [loSamplerDist, h]

/-- The one-dimensional identity matrix satisfies the isometry identity `Aᴴ * A = 1`. -/
lemma clause19Aux_hA : ((1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ * 1 = 1 := by
  rw [Matrix.conjTranspose_one, one_mul]

/-- Every one-mode, one-particle occupation has probability one under the identity-isometry
distribution. -/
lemma clause19Aux_isometry_all (S : FockOccupation 1 1) :
    loIsometryDist 1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) S = 1 := by
  have hnorm : ∑ T : FockOccupation 1 1,
      loIsometryDist 1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) T = 1 :=
    show ∑ T : FockOccupation 1 1, bosonWeight (1 : Matrix (Fin 1) (Fin 1) ℂ) T = 1 from
      Qatlib.Concepts.BosonFock.PermAnalysis.bosonDistributionNormalization
        1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) clause19Aux_hA
  have hsum : (∑ T : FockOccupation 1 1,
      loIsometryDist 1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) T)
      = loIsometryDist 1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) S := by
    simp only [g19r_S₀_unique]
    rw [Finset.sum_const, Finset.card_univ, clause19Aux_card]
    simp
  exact hsum.symm.trans hnorm

/-- The auxiliary sampler and the one-dimensional identity-isometry distribution have total
variation distance zero. -/
lemma clause19Aux_tvd : loTvDist (loSamplerDist clause19Aux_Sam)
    (loIsometryDist 1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ)) = 0 := by
  simp only [loTvDist]
  simp_rw [clause19Aux_samplerDist_all, clause19Aux_isometry_all]
  simp

/-- The always-accepting program recognizes the auxiliary sampler's event of outputting
`g19r_S₀` on every one-bit seed. -/
lemma clause19Aux_hacc : ∀ r : Fin 1 → Bool,
    ccAccepts clause19Aux_Macc 1 0 (List.ofFn r) = decide (clause19Aux_Sam.O r = g19r_S₀) := by
  intro r
  have h1 : ccAccepts clause19Aux_Macc 1 0 (List.ofFn r) = true := rfl
  have h2 : clause19Aux_Sam.O r = g19r_S₀ := rfl
  rw [h1, decide_eq_true h2]

/-- The three-bit string `[false, false, false]` decodes as the hash query `(0, 0, [], [])`. -/
lemma clause19Aux_decode_z0 :
    ccDecodeHashQuery [false, false, false] = some (0, 0, [], []) := rfl

/-- Appending any bit word and a final false bit to `[false, false, false]` makes the hash-query
decoder return `none`. -/
lemma clause19Aux_decode_ext (w : List Bool) :
    ccDecodeHashQuery ([false, false, false] ++ w ++ [false]) = none := by
  simp [ccDecodeHashQuery, ccReadUnary, ccReadUnaryAux, List.length_append,
    List.cons_append, List.nil_append]

/-- The three-bit zero string belongs to the auxiliary always-accepting program's hash-witness
set. -/
lemma clause19Aux_z0_mem : ccHashWitnessSet clause19Aux_Macc 1 0 1 [false, false, false] := by
  have hd0 := clause19Aux_decode_z0
  show (match ccDecodeHashQuery [false, false, false] with
    | none => False
    | some (ℓ, n, M, x) =>
        M.length = ℓ * (1 * n ^ 1 + 1) + ℓ ∧
          ∃ w : Fin (1 * n ^ 1 + 1) → Bool,
            ccVerifies clause19Aux_Macc 1 0 x (List.ofFn w) = true ∧
              ∀ i : Fin ℓ, ccHash (ccMatrixFromList ℓ (1 * n ^ 1 + 1) M)
                (ccVectorFromList ℓ (1 * n ^ 1 + 1) M) w i = false)
  rw [hd0]
  show ([] : List Bool).length = 0 * (1 * 0 ^ 1 + 1) + 0 ∧
    ∃ w : Fin (1 * 0 ^ 1 + 1) → Bool,
      ccVerifies clause19Aux_Macc 1 0 ([] : List Bool) (List.ofFn w) = true ∧
        ∀ i : Fin 0, ccHash (ccMatrixFromList 0 (1 * 0 ^ 1 + 1) ([] : List Bool))
          (ccVectorFromList 0 (1 * 0 ^ 1 + 1) ([] : List Bool)) w i = false
  exact ⟨rfl, fun _ => true, rfl, fun i => Fin.elim0 i⟩

/-- No extension of the three-bit zero string by a word and a final false bit belongs to the
auxiliary hash-witness set. -/
lemma clause19Aux_z0_ext_not (w : List Bool) :
    ¬ ccHashWitnessSet clause19Aux_Macc 1 0 1 ([false, false, false] ++ w ++ [false]) := by
  have hd := clause19Aux_decode_ext w
  intro hmem
  change (match ccDecodeHashQuery ([false, false, false] ++ w ++ [false]) with
    | none => False
    | some (ℓ, n, M, x) =>
        M.length = ℓ * (1 * n ^ 1 + 1) + ℓ ∧
          ∃ w' : Fin (1 * n ^ 1 + 1) → Bool,
            ccVerifies clause19Aux_Macc 1 0 x (List.ofFn w') = true ∧
              ∀ i : Fin ℓ, ccHash (ccMatrixFromList ℓ (1 * n ^ 1 + 1) M)
                (ccVectorFromList ℓ (1 * n ^ 1 + 1) M) w' i = false) at hmem
  rw [hd] at hmem
  exact hmem

/-- Appending a false bit and the specified all-false witness block to `a` leaves its
represented tape unchanged. -/
private lemma clause19Aux_attack_getD (p : ℕ) (a : List Bool) :
    ∀ i, ((a ++ [false]) ++ List.ofFn (fun _ => false :
        Fin (p * (a ++ [false]).length ^ p + p) → Bool)).getD i false
      = a.getD i false := by
  intro i
  have key : (a ++ [false]) ++ List.ofFn (fun _ => false :
      Fin (p * (a ++ [false]).length ^ p + p) → Bool)
      = a ++ List.replicate (p * (a ++ [false]).length ^ p + p + 1) false := by
    rw [List.ofFn_const, List.append_assoc]
    rfl
  rw [key]
  exact clause19Aux_getD_replicate_tail a _ i

/-- The list obtained by appending a false bit and the specified witness block is at least as
long as the original list. -/
private lemma clause19Aux_attack_len (p : ℕ) (a : List Bool) :
    a.length ≤ ((a ++ [false]) ++ List.ofFn (fun _ => false :
      Fin (p * (a ++ [false]).length ^ p + p) → Bool)).length := by
  simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  omega

/-- The auxiliary always-accepting program's hash-witness set is outside `InNP` in the specified
tape model. -/
lemma clause19Aux_hashWitnessSet_notInNP :
    ¬ InNP (ccHashWitnessSet clause19Aux_Macc 1 0 1) := by
  rintro ⟨q, c, k, p, V, hpoly, hiff⟩
  obtain ⟨wit, hwit⟩ := (hiff [false, false, false]).mp clause19Aux_z0_mem
  set a : List Bool := [false, false, false] ++ List.ofFn wit with ha
  have hz_not : ¬ ccHashWitnessSet clause19Aux_Macc 1 0 1 (a ++ [false]) := by
    rw [ha]
    exact clause19Aux_z0_ext_not (List.ofFn wit)
  have hver : ccVerifies V c k (a ++ [false])
      (List.ofFn (fun _ => false : Fin (p * (a ++ [false]).length ^ p + p) → Bool)) = true := by
    have h1 : ccVerifies V c k (a ++ [false])
        (List.ofFn (fun _ => false : Fin (p * (a ++ [false]).length ^ p + p) → Bool))
        = ccAccepts V c k ((a ++ [false]) ++
          List.ofFn (fun _ => false : Fin (p * (a ++ [false]).length ^ p + p) → Bool)) := rfl
    have h2 : ccAccepts V c k a = ccAccepts V c k ((a ++ [false]) ++
        List.ofFn (fun _ => false : Fin (p * (a ++ [false]).length ^ p + p) → Bool)) :=
      clause19Aux_accepts_mono V c k hpoly a ((a ++ [false]) ++
        List.ofFn (fun _ => false : Fin (p * (a ++ [false]).length ^ p + p) → Bool))
        (fun i => (clause19Aux_attack_getD p a i).symm) (clause19Aux_attack_len p a)
    have h3 : ccAccepts V c k a = ccVerifies V c k [false, false, false] (List.ofFn wit) := by
      rw [ha]
      rfl
    rw [h1, ← h2, h3]
    exact hwit
  exact hz_not ((hiff (a ++ [false])).2
    ⟨fun _ => false, hver⟩)

/-- The stated linear-optics probability-estimation specification is false in this model, even
with its sampling, relative-error, confidence, and resource assumptions. -/
theorem clause3_clause3_counter :
    ¬ (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
      ∀ (qM cM kM : ℕ) (M : CcProgram qM), CcPolyTime M cM kM →
        ∀ (Sam : LoSampler m n), 0 < Sam.L →
          ∀ S₀ : FockOccupation m n,
            (∀ r : Fin Sam.L → Bool,
              ccAccepts M cM kM (List.ofFn r) = decide (Sam.O r = S₀)) →
            ∀ (ε_s δ : ℝ), 0 < δ → δ < 1 →
              loTvDist (loSamplerDist Sam) (loIsometryDist m n A) ≤ ε_s →
              ε_s ≤ δ / 4 * loIsometryDist m n A S₀ →
              ∀ (d s : ℕ), 4 ≤ (d + 1) * δ →
                ∃ (qE cE kE : ℕ) (E : CcProgram qE),
                  CcPolyTime E cE kE
                    ∧ CcInNPSet (ccHashWitnessSet M cM kM Sam.L)
                    ∧ ((∑ ω : Fin (cE * 0 ^ kE + cE) → Bool,
                          (if
                            |(ccBitsToNat
                                (ccOutput E
                                  (ccOracleOf (ccHashWitnessSet M cM kM Sam.L))
                                  (ccCoinString ω) []
                                  (cE * 0 ^ kE + cE)) : ℝ)
                              / ((2 : ℕ) ^ Sam.L : ℝ)
                              - loIsometryDist m n A S₀|
                            ≤ δ * loIsometryDist m n A S₀
                          then (1 : ℝ) else 0))
                        / ((2 : ℕ) ^ (cE * 0 ^ kE + cE) : ℝ)
                        ≥ 1 - (1 : ℝ) / ((2 : ℕ) ^ (s + 1) : ℝ))
                    ∧ (∀ ω : Fin (cE * 0 ^ kE + cE) → Bool,
                        ccCoinsRead E
                          (ccOracleOf (ccHashWitnessSet M cM kM Sam.L))
                          (ccCoinString ω) [] (cE * 0 ^ kE + cE)
                          ≤ 64 * (d + 1) ^ 4 * (s + 1) * (Sam.L + 2) ^ 4)
                    ∧ (∀ ω : Fin (cE * 0 ^ kE + cE) → Bool,
                        ccQueries E
                          (ccOracleOf (ccHashWitnessSet M cM kM Sam.L))
                          (ccCoinString ω) [] (cE * 0 ^ kE + cE)
                          ≤ 64 * (d + 1) ^ 4 * (s + 1) * (Sam.L + 2))
                    ∧ (∀ ω : Fin (cE * 0 ^ kE + cE) → Bool,
                        ccTime E
                          (ccOracleOf (ccHashWitnessSet M cM kM Sam.L))
                          (ccCoinString ω) [] (cE * 0 ^ kE + cE)
                          ≤ 4096 * (d + 1) ^ 4 * (s + 1) * (Sam.L + 2) ^ 8)) := by
  intro h

  have htv : loTvDist (loSamplerDist clause19Aux_Sam)
      (loIsometryDist 1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ)) ≤ (0 : ℝ) :=
    le_of_eq clause19Aux_tvd
  have hnon : (0 : ℝ) ≤ (1 / 2 : ℝ) / 4 *
      loIsometryDist 1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) g19r_S₀ := by
    rw [clause19Aux_isometry_all]
    norm_num
  have hd : (4 : ℝ) ≤ (8 + 1) * (1 / 2 : ℝ) := by norm_num
  obtain ⟨qE, cE, kE, E, _, hNP, _, _, _, _⟩ :=
    h 1 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) clause19Aux_hA 0 1 0 clause19Aux_Macc clause19Aux_Macc_poly
      clause19Aux_Sam clause19Aux_Sam_L g19r_S₀ clause19Aux_hacc 0 (1 / 2 : ℝ)
      (by norm_num) (by norm_num) htv hnon 8 0 hd
  exact clause19Aux_hashWitnessSet_notInNP hNP

set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 800000

open scoped Classical

/-- Running for `t + 1` steps is one machine step applied to the configuration after `t` steps. -/
private theorem clause1Aux_run_succ {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) :
    ccRun P A ρ x (t + 1) = ccStep P A ρ (ccRun P A ρ x t) := rfl

/-- Looking up a list generated from a finite function returns that function's value within its
domain and `false` beyond its length. -/
theorem clause1Aux_getD_ofFn {m : ℕ} (f : Fin m → Bool) (j : ℕ) :
    (List.ofFn f).getD j false = if h : j < m then f ⟨j, h⟩ else false := by
  simp only [List.getD, List.getElem?_ofFn]
  by_cases h : j < m <;> simp [h]

/-- Within the domain, lookup in `List.ofFn f` returns the corresponding value of `f`. -/
theorem clause1Aux_getD_ofFn_lt {m : ℕ} (f : Fin m → Bool) (j : ℕ) (hj : j < m) :
    (List.ofFn f).getD j false = f ⟨j, hj⟩ := by
  rw [clause1Aux_getD_ofFn f, dif_pos hj]

/-- At or beyond its length, lookup in `List.ofFn f` with default `false` returns `false`. -/
theorem clause1Aux_getD_ofFn_ge {m : ℕ} (f : Fin m → Bool) (j : ℕ) (hj : m ≤ j) :
    (List.ofFn f).getD j false = false := by
  rw [clause1Aux_getD_ofFn f, dif_neg (by omega)]

/-- Every lookup with default `false` in a list of false bits returns `false`. -/
theorem clause1Aux_getD_replicate_false (n j : ℕ) :
    (List.replicate n false).getD j false = (false : Bool) := by
  simp only [List.getD, List.getElem?_replicate]
  by_cases h : j < n <;> simp [h]

/-- Before the end of the left list, lookup in a concatenation equals lookup in the left list. -/
theorem clause1Aux_getD_append_left {z r : List Bool} (i : ℕ) (hi : i < z.length) :
    (z ++ r).getD i false = z.getD i false :=
  List.getD_append z r false i hi

/-- At or beyond the end of the left list, lookup in a concatenation equals lookup in the right
list at the shifted index. -/
theorem clause1Aux_getD_append_right {z r : List Bool} (i : ℕ) (hi : z.length ≤ i) :
    (z ++ r).getD i false = r.getD (i - z.length) false := by
  simp only [List.getD, List.getElem?_append]
  rw [if_neg (by omega : ¬i < z.length)]

/-- Appending a list whose default-false lookups are all false preserves every default-false
lookup in the original list. -/
theorem clause1Aux_getD_append_false {z r : List Bool} (hr : ∀ j, r.getD j false = false) (i : ℕ) :
    (z ++ r).getD i false = z.getD i false := by
  by_cases hi : i < z.length
  · exact clause1Aux_getD_append_left i hi
  · rw [clause1Aux_getD_append_right i (by omega), hr (i - z.length)]
    have hz : z[i]? = none := List.getElem?_eq_none (by omega)
    simp [List.getD, hz]

/-- Appending a block of false bits does not change the acceptance value of a polynomial-time
program in this tape model. -/
theorem clause1Aux_accepts_append_false {q : ℕ} (V : CcProgram q) (c k : ℕ) (hpoly : CcPolyTime V c k)
    (z : List Bool) (d : ℕ) :
    ccAccepts V c k (z ++ List.replicate d false) = ccAccepts V c k z := by
  apply ccAccepts_tape_eq V c k hpoly
  intro i
  exact clause1Aux_getD_append_false (fun j => clause1Aux_getD_replicate_false d j) i

/-- A polynomial-time program accepts an input with an appended all-false block exactly when it
accepts the original input. -/
theorem clause1Aux_accepts_zeroBlock {q : ℕ} (V : CcProgram q) (c k : ℕ) (hpoly : CcPolyTime V c k)
    (z : List Bool) (plen : ℕ) :
    (ccAccepts V c k (z ++ List.ofFn (fun _ : Fin plen => false)) = true) ↔
      (ccAccepts V c k z = true) := by
  have hof : List.ofFn (fun _ : Fin plen => false) = List.replicate plen false :=
    List.ofFn_const _ _
  rw [hof]
  exact ⟨fun h => by rw [← clause1Aux_accepts_append_false V c k hpoly z plen]; exact h,
    fun h => by rw [clause1Aux_accepts_append_false V c k hpoly z plen]; exact h⟩

/-- Unfolds one level of `ccAlt` into an existential or universal Boolean witness block
according to `ex`. -/
theorem clause1Aux_alt_succ {ex : Bool} {plen : ℕ} {D : List Bool → Prop} (m : ℕ) (z : List Bool) :
    ccAlt ex plen D (m + 1) z =
      if ex then ∃ w : Fin plen → Bool, ccAlt false plen D m (z ++ List.ofFn w)
      else ∀ w : Fin plen → Bool, ccAlt true plen D m (z ++ List.ofFn w) := rfl

/-- Zero alternation levels evaluate the underlying predicate directly. -/
theorem clause1Aux_alt_zero {ex : Bool} {plen : ℕ} {D : List Bool → Prop} (z : List Bool) :
    ccAlt ex plen D 0 z = D z := rfl

/-- Extending a finite Boolean word by false entries leaves all lookups in its generated list
unchanged. -/
theorem clause1Aux_getD_ofFn_pad {m d : ℕ} (f : Fin m → Bool) (j : ℕ) :
    (List.ofFn f).getD j false
      = (List.ofFn (fun k : Fin (m + d) =>
          if h : (k : ℕ) < m then f ⟨k, h⟩ else false)).getD j false := by
  by_cases h2 : j < m
  · rw [clause1Aux_getD_ofFn_lt f j h2,
      clause1Aux_getD_ofFn_lt (fun k : Fin (m + d) => if h : (k : ℕ) < m then f ⟨k, h⟩ else false) j
        (lt_of_lt_of_le h2 (Nat.le_add_right m d))]
    show f ⟨j, h2⟩ = (if hlt : j < m then f ⟨j, hlt⟩ else false)
    rw [dif_pos h2]
  · rw [clause1Aux_getD_ofFn_ge f j (by omega)]
    by_cases h3 : j < m + d
    · rw [clause1Aux_getD_ofFn_lt (fun k : Fin (m + d) => if h : (k : ℕ) < m then f ⟨k, h⟩ else false) j h3]
      show (false : Bool) = (if hlt : j < m then f ⟨j, hlt⟩ else false)
      rw [dif_neg h2]
    · rw [clause1Aux_getD_ofFn_ge (fun k : Fin (m + d) => if h : (k : ℕ) < m then f ⟨k, h⟩ else false) j
        (by omega)]

/-- Appending a finite Boolean word or its extension by false entries gives the same represented
tape. -/
theorem clause1Aux_tape_ofFn_pad {m d : ℕ} (f : Fin m → Bool) (z : List Bool) :
    ∀ i, (z ++ List.ofFn f).getD i false
      = (z ++ List.ofFn (fun k : Fin (m + d) =>
          if h : (k : ℕ) < m then f ⟨k, h⟩ else false)).getD i false := by
  intro i
  by_cases h1 : i < z.length
  · rw [clause1Aux_getD_append_left i h1, clause1Aux_getD_append_left i h1]
  · rw [clause1Aux_getD_append_right i (by omega), clause1Aux_getD_append_right i (by omega)]
    exact clause1Aux_getD_ofFn_pad f (i - z.length)

/-- For a predicate depending only on the represented tape, invariance under appending blocks of
length `plen + d` implies invariance for blocks of length `plen`. -/
theorem clause1Aux_robust_amplified {plen d : ℕ} {D : List Bool → Prop}
    (htape : ∀ z z' : List Bool, (∀ i, z.getD i false = z'.getD i false) → (D z ↔ D z'))
    (h : RobustAlt (plen + d) D) : RobustAlt plen D := by
  intro z w
  have h1 : D (z ++ List.ofFn w) ↔ D (z ++ List.ofFn (fun k : Fin (plen + d) =>
      if hlt : (k : ℕ) < plen then w ⟨k, hlt⟩ else false)) :=
    htape _ _ (clause1Aux_tape_ofFn_pad w z)
  have h2 : D (z ++ List.ofFn (fun k : Fin (plen + d) =>
      if hlt : (k : ℕ) < plen then w ⟨k, hlt⟩ else false)) ↔ D z :=
    h z (fun k : Fin (plen + d) => if hlt : (k : ℕ) < plen then w ⟨k, hlt⟩ else false)
  exact h1.trans h2

/-- Tape invariance and robustness for width `plen + d` imply that adding an alternation level
at width `plen` leaves `ccAlt` unchanged. -/
theorem clause1Aux_alt_succ_robust_add {plen d : ℕ} {D : List Bool → Prop}
    (htape : ∀ z z' : List Bool, (∀ i, z.getD i false = z'.getD i false) → (D z ↔ D z'))
    (h : RobustAlt (plen + d) D) :
    ∀ (lev : ℕ) (ex : Bool) (z : List Bool),
      ccAlt ex plen D (lev + 1) z ↔ ccAlt ex plen D lev z :=
  ccAlt_succ_robust (clause1Aux_robust_amplified htape h)

/-- If appending an all-false block preserves `D`, truth at `2 * n` alternation levels beginning
existentially implies truth at `2 * n + 1` levels. -/
theorem clause1Aux_alt_zero_exists {plen : ℕ} {D : List Bool → Prop}
    (hz : ∀ z : List Bool, D (z ++ List.ofFn (fun _ : Fin plen => false)) ↔ D z) :
    ∀ (n : ℕ) (z : List Bool), ccAlt true plen D (2 * n) z → ccAlt true plen D (2 * n + 1) z := by
  intro n
  induction n with
  | zero =>
    intro z
    show ccAlt true plen D 0 z → ccAlt true plen D (0 + 1) z
    intro hD
    rw [clause1Aux_alt_succ (ex := true) 0 z, if_pos rfl]
    exact ⟨fun _ => false, (hz z).mpr hD⟩
  | succ n ih =>
    intro z h
    have hq : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    have hp : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by omega
    rw [hp]
    rw [hq] at h
    rw [clause1Aux_alt_succ (ex := true) (2 * n + 1) z, if_pos rfl] at h
    obtain ⟨w, hw⟩ := h
    rw [show (2 * n + 1) = (2 * n) + 1 from by omega,
      clause1Aux_alt_succ (ex := false) (2 * n) (z ++ List.ofFn w), if_neg (by decide)] at hw
    rw [clause1Aux_alt_succ (ex := true) (2 * n + 2) z, if_pos rfl]
    refine ⟨w, ?_⟩
    rw [show (2 * n + 2) = (2 * n + 1) + 1 from by omega,
      clause1Aux_alt_succ (ex := false) (2 * n + 1) (z ++ List.ofFn w), if_neg (by decide)]
    intro w'
    exact ih ((z ++ List.ofFn w) ++ List.ofFn w') (hw w')

/-- If appending an all-false block preserves `D`, truth at `2 * n + 2` alternation levels
beginning existentially implies truth at `2 * n + 1` levels. -/
theorem clause1Aux_alt_zero_forall {plen : ℕ} {D : List Bool → Prop}
    (hz : ∀ z : List Bool, D (z ++ List.ofFn (fun _ : Fin plen => false)) ↔ D z) :
    ∀ (n : ℕ) (z : List Bool), ccAlt true plen D (2 * n + 2) z → ccAlt true plen D (2 * n + 1) z := by
  intro n
  induction n with
  | zero =>
    intro z
    show ccAlt true plen D (0 + 1 + 1) z → ccAlt true plen D (0 + 1) z
    intro h
    rw [clause1Aux_alt_succ (ex := true) (0 + 1) z, if_pos rfl] at h
    obtain ⟨w, hw⟩ := h
    rw [clause1Aux_alt_succ (ex := false) 0 (z ++ List.ofFn w), if_neg (by decide)] at hw
    rw [clause1Aux_alt_succ (ex := true) 0 z, if_pos rfl]
    refine ⟨w, ?_⟩
    rw [clause1Aux_alt_zero]
    exact (hz (z ++ List.ofFn w)).mp (hw fun _ => false)
  | succ n ih =>
    intro z h
    have hq : 2 * (n + 1) + 2 = (2 * n + 3) + 1 := by omega
    have hp : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by omega
    rw [hp]
    rw [hq] at h
    rw [clause1Aux_alt_succ (ex := true) (2 * n + 3) z, if_pos rfl] at h
    obtain ⟨w, hw⟩ := h
    rw [show (2 * n + 3) = (2 * n + 2) + 1 from by omega,
      clause1Aux_alt_succ (ex := false) (2 * n + 2) (z ++ List.ofFn w), if_neg (by decide)] at hw
    rw [clause1Aux_alt_succ (ex := true) (2 * n + 2) z, if_pos rfl]
    refine ⟨w, ?_⟩
    rw [show (2 * n + 2) = (2 * n + 1) + 1 from by omega,
      clause1Aux_alt_succ (ex := false) (2 * n + 1) (z ++ List.ofFn w), if_neg (by decide)]
    intro w'
    exact ih ((z ++ List.ofFn w) ++ List.ofFn w') (hw w')

set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 800000

open scoped Classical

/-- Running for `t + 1` steps is one machine step applied to the configuration after `t` steps. -/
private theorem clause1Aux_priv_run_succ {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) :
    ccRun P A ρ x (t + 1) = ccStep P A ρ (ccRun P A ρ x t) := rfl

/-- An accepting or rejecting configuration is fixed by `ccStep`. -/
private theorem clause1Aux_priv_step_halt {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig q)
    (h : P.states c.state = CcAct.accept ∨ P.states c.state = CcAct.reject) :
    ccStep P A ρ c = c := by
  rcases h with h | h <;> simp [ccStep, h]

/-- Once a run reaches an accepting or rejecting state at time `t`, every later step bound gives
the same configuration. -/
private theorem clause1Aux_priv_run_halt_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t t' : ℕ)
    (hh : P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject)
    (hle : t ≤ t') : ccRun P A ρ x t' = ccRun P A ρ x t := by
  have h1 : ∀ s, ccRun P A ρ x (t + s) = ccRun P A ρ x t := by
    intro s
    induction s with
    | zero => rfl
    | succ n ih =>
      rw [show t + (n + 1) = (t + n) + 1 from rfl, clause1Aux_priv_run_succ, ih,
        clause1Aux_priv_step_halt P A ρ _ hh]
  have h2 : t + (t' - t) = t' := by omega
  rw [← h2]
  exact h1 (t' - t)

/-- A machine result different from `none` implies that the current action is accepting or
rejecting. -/
private theorem clause1Aux_priv_result_halt {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) (h : ccResult P A ρ x t ≠ none) :
    P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject := by
  cases hs : P.states (ccRun P A ρ x t).state with
  | accept => exact Or.inl rfl
  | reject => exact Or.inr rfl
  | moveL q' => simp [ccResult, hs] at h
  | moveR q' => simp [ccResult, hs] at h
  | write b q' => simp [ccResult, hs] at h
  | branch qt qf => simp [ccResult, hs] at h
  | coinFlip qt qf => simp [ccResult, hs] at h
  | queryPush q' => simp [ccResult, hs] at h
  | oracleCall qt qf => simp [ccResult, hs] at h

/-- The tape head position after `t` machine steps is at most `t`. -/
theorem clause1Aux_head_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : (ccRun P A ρ x t).head ≤ t := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [clause1Aux_priv_run_succ]
    cases hs : P.states (ccRun P A ρ x n).state <;> simp [ccStep, hs] <;> omega

/-- The number of Boolean words of a fixed finite length is two raised to that length. -/
theorem clause1Aux_card_fin_bool (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp [Fintype.card_pi, Finset.prod_const]

/-- With witness width zero, any number of alternation levels is equivalent to the underlying
predicate. -/
theorem clause1Aux_alt_width0 {D : List Bool → Prop} :
    ∀ (lev : ℕ) (ex : Bool) (z : List Bool), ccAlt ex 0 D lev z ↔ D z := by
  intro lev
  induction lev with
  | zero => intro ex z; exact Iff.rfl
  | succ m ih =>
    intro ex z
    have hnil : ∀ w : Fin 0 → Bool, z ++ List.ofFn w = z := by
      intro w
      have h : List.ofFn w = ([] : List Bool) :=
        List.eq_nil_of_length_eq_zero (by simp)
      rw [h, List.append_nil]
    have hw0 : Fin 0 → Bool := fun i => absurd i.isLt (by omega)
    cases ex with
    | true =>
      rw [clause1Aux_alt_succ (ex := true) m z, if_pos rfl]
      constructor
      · rintro ⟨w, hw⟩
        rw [← hnil w]
        exact (ih false (z ++ List.ofFn w)).mp hw
      · intro hD
        refine ⟨hw0, ?_⟩
        rw [hnil hw0]
        exact (ih false z).mpr hD
    | false =>
      rw [clause1Aux_alt_succ (ex := false) m z, if_neg (by decide)]
      constructor
      · intro h
        have h0 := h hw0
        rw [hnil hw0] at h0
        exact (ih true z).mp h0
      · intro hD w
        have hD' : D (z ++ List.ofFn w) := by rw [hnil w]; exact hD
        exact (ih true (z ++ List.ofFn w)).mpr hD'

/-- Every language at level zero of `InPHLevel` belongs to every level of `InPHLevel`. -/
theorem clause1Aux_clause4_from0 : ∀ (k : ℕ) (L : List Bool → Prop), InPHLevel 0 L → InPHLevel k L := by
  intro k L h
  obtain ⟨q, c, κ, p, V, hpoly, hL⟩ := h
  refine ⟨q, c, κ, 0, V, hpoly, ?_⟩
  intro x
  have hplen : (0 : ℕ) * x.length ^ 0 + 0 = 0 := by simp
  rw [hplen, hL x, clause1Aux_alt_zero]
  exact (clause1Aux_alt_width0 (D := fun z => ccAccepts V c κ z = true) k true x).symm

/-- A polynomial-time alternating characterization at level `k` yields membership at level `k +
1` when its acceptance predicate is robust under appending witness blocks. -/
theorem clause1Aux_inPH_succ_robust {k q c κ p : ℕ} {L : List Bool → Prop} (V : CcProgram q)
    (hpoly : CcPolyTime V c κ)
    (hL : ∀ x : List Bool,
      L x ↔ ccAlt true (p * x.length ^ p + p) (fun z => ccAccepts V c κ z = true) k x)
    (hrob : ∀ x : List Bool,
      RobustAlt (p * x.length ^ p + p) (fun z => ccAccepts V c κ z = true)) :
    InPHLevel (k + 1) L := by
  refine ⟨q, c, κ, p, V, hpoly, ?_⟩
  intro x
  rw [hL x]
  exact (ccAlt_succ_robust (hrob x) k true x).symm

/-- A singleton output `[b]` implies that the final head is at position one and tape position
zero contains `b`. -/
theorem clause1Aux_output_shape {q : ℕ} (M : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) (b : Bool) (h : ccOutput M A ρ x t = [b]) :
    (ccRun M A ρ x t).head = 1 ∧ (ccRun M A ρ x t).tape 0 = b := by
  simp only [ccOutput] at h
  have hlen : (List.range (ccRun M A ρ x t).head).length = ([b] : List Bool).length := by
    rw [← h, List.length_map]
  rw [List.length_range, List.length_singleton] at hlen
  have hhead : (ccRun M A ρ x t).head = 1 := hlen
  rw [hhead, List.range_one] at h
  simp at h
  exact ⟨hlen, h⟩

/-- Agreement of all non-tape configuration fields together with agreement of tape cells at
indices below `n`. -/
private def clause1Aux_priv_agree {q : ℕ} (n : ℕ) (c₁ c₂ : CcConfig q) : Prop :=
  c₁.state = c₂.state ∧ c₁.head = c₂.head ∧ c₁.query = c₂.query ∧
    c₁.coinIdx = c₂.coinIdx ∧ c₁.time = c₂.time ∧ c₁.queries = c₂.queries ∧
    c₁.queryBits = c₂.queryBits ∧ c₁.coins = c₂.coins ∧ ∀ i < n, c₁.tape i = c₂.tape i

/-- Inputs agreeing below `n` initialize configurations that agree in every non-tape field and
on tape cells below `n`. -/
private theorem clause1Aux_priv_agree_init {q : ℕ} (x y : List Bool) (n : ℕ)
    (h : ∀ i < n, x.getD i false = y.getD i false) :
    clause1Aux_priv_agree n (ccInit q x) (ccInit q y) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  exact h i hi

/-- Configuration agreement below `n` is preserved by one machine step when the common head
position is below `n`. -/
private theorem clause1Aux_priv_agree_step {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) {n : ℕ} {c₁ c₂ : CcConfig q} (ha : clause1Aux_priv_agree n c₁ c₂) (hh : c₁.head < n) :
    clause1Aux_priv_agree n (ccStep P A ρ c₁) (ccStep P A ρ c₂) := by
  obtain ⟨hstate, hhead, hquery, hcoin, htime, hqueries, hqbits, hcoins, htape⟩ := ha
  have hst : P.states c₂.state = P.states c₁.state := by rw [hstate]
  cases hs : P.states c₁.state with
  | moveL q' =>
    simp only [ccStep, hs, hst]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => htape i hi⟩
    · rw [hhead]
    · rw [hquery]
    · rw [hcoin]
    · rw [htime]
    · rw [hqueries]
    · rw [hqbits]
    · rw [hcoins]
  | moveR q' =>
    simp only [ccStep, hs, hst]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => htape i hi⟩
    · rw [hhead]
    · rw [hquery]
    · rw [hcoin]
    · rw [htime]
    · rw [hqueries]
    · rw [hqbits]
    · rw [hcoins]
  | write b q' =>
    simp only [ccStep, hs, hst]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhead]
    · rw [hquery]
    · rw [hcoin]
    · rw [htime]
    · rw [hqueries]
    · rw [hqbits]
    · rw [hcoins]
    · intro i hi
      show (if i = c₁.head then b else c₁.tape i) = (if i = c₂.head then b else c₂.tape i)
      by_cases hie : i = c₁.head
      · subst hie
        rw [hhead, if_pos rfl, if_pos rfl]
      · have hie2 : ¬i = c₂.head := by rw [← hhead]; exact hie
        rw [if_neg hie, if_neg hie2, htape i hi]
  | branch qt qf =>
    simp only [ccStep, hs, hst]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => htape i hi⟩
    · rw [← hhead, htape c₁.head hh]
    · rw [hhead]
    · rw [hquery]
    · rw [hcoin]
    · rw [htime]
    · rw [hqueries]
    · rw [hqbits]
    · rw [hcoins]
  | coinFlip qt qf =>
    simp only [ccStep, hs, hst]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => htape i hi⟩
    · rw [hcoin]
    · rw [hhead]
    · rw [hquery]
    · rw [hcoin]
    · rw [htime]
    · rw [hqueries]
    · rw [hqbits]
    · rw [hcoins]
  | queryPush q' =>
    simp only [ccStep, hs, hst]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => htape i hi⟩
    · rw [hhead]
    · rw [hquery, ← hhead, htape c₁.head hh]
    · rw [hcoin]
    · rw [htime, hquery]
    · rw [hqueries]
    · rw [hqbits]
    · rw [hcoins]
  | oracleCall qt qf =>
    simp only [ccStep, hs, hst]
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hquery]
    · rw [hhead]
    · rw [hcoin]
    · rw [htime, hquery]
    · rw [hqueries]
    · rw [hqbits, hquery]
    · rw [hcoins]
    · intro i hi
      show (if i = c₁.head then A c₁.query else c₁.tape i)
          = (if i = c₂.head then A c₂.query else c₂.tape i)
      by_cases hie : i = c₁.head
      · subst hie
        rw [hhead, hquery, if_pos rfl, if_pos rfl]
      · have hie2 : ¬i = c₂.head := by rw [← hhead]; exact hie
        rw [if_neg hie, if_neg hie2, htape i hi]
  | accept =>
    simp only [ccStep, hs, hst]
    exact ⟨hstate, hhead, hquery, hcoin, htime, hqueries, hqbits, hcoins, htape⟩
  | reject =>
    simp only [ccStep, hs, hst]
    exact ⟨hstate, hhead, hquery, hcoin, htime, hqueries, hqbits, hcoins, htape⟩

/-- For a polynomial-time program, placing a true bit beyond the empty-input polynomial budget
in an otherwise false tape gives the same result as empty input at every step bound. -/
theorem clause1Aux_result_farTrue {q : ℕ} (P : CcProgram q) (c k : ℕ) (hpoly : CcPolyTime P c k)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (N : ℕ) (hN : c * 0 ^ k + c < N) (t : ℕ) :
    ccResult P A ρ (List.replicate N false ++ [true]) t = ccResult P A ρ [] t := by
  have hinit : ∀ i < N,
      (List.replicate N false ++ [true]).getD i false = ([] : List Bool).getD i false := by
    intro i hi
    have hlenR : (List.replicate N false).length = N := List.length_replicate
    rw [clause1Aux_getD_append_left i (show i < (List.replicate N false).length from by
        rw [hlenR]; exact hi),
      clause1Aux_getD_replicate_false N i]
    rfl
  have hg : ∀ s, s ≤ c * 0 ^ k + c →
      clause1Aux_priv_agree N (ccRun P A ρ (List.replicate N false ++ [true]) s) (ccRun P A ρ [] s) := by
    intro s
    induction s with
    | zero => intro _; exact clause1Aux_priv_agree_init _ _ N hinit
    | succ n ih =>
      intro hle
      have ha := ih (by omega)
      have hhh : (ccRun P A ρ [] n).head < N := by
        have h1 := clause1Aux_head_le P A ρ [] n
        have h2 : (ccRun P A ρ (List.replicate N false ++ [true]) n).head
            = (ccRun P A ρ [] n).head := ha.2.1
        omega
      rw [clause1Aux_priv_run_succ, clause1Aux_priv_run_succ]
      exact clause1Aux_priv_agree_step P A ρ ha (by rw [ha.2.1]; exact hhh)
  have hbg : clause1Aux_priv_agree N
      (ccRun P A ρ (List.replicate N false ++ [true]) (c * 0 ^ k + c))
      (ccRun P A ρ [] (c * 0 ^ k + c)) :=
    hg (c * 0 ^ k + c) (Nat.le_refl _)
  have hhalt := clause1Aux_priv_result_halt P A ρ [] (c * 0 ^ k + c) (hpoly A ρ []).1
  have hhalt' : P.states
      (ccRun P A ρ (List.replicate N false ++ [true]) (c * 0 ^ k + c)).state = CcAct.accept ∨
      P.states
      (ccRun P A ρ (List.replicate N false ++ [true]) (c * 0 ^ k + c)).state = CcAct.reject := by
    rw [hbg.1]
    exact hhalt
  by_cases ht : t ≤ c * 0 ^ k + c
  · have ha := hg t ht
    simp only [ccResult, ha.1]
  · have hlt : c * 0 ^ k + c ≤ t := by omega
    have h1 := clause1Aux_priv_run_halt_le P A ρ [] (c * 0 ^ k + c) t hhalt hlt
    have h2 := clause1Aux_priv_run_halt_le P A ρ (List.replicate N false ++ [true])
      (c * 0 ^ k + c) t hhalt' hlt
    simp only [ccResult, h1, h2, hbg.1]

/-- A polynomial-time program has the same acceptance value on empty input and on an otherwise
false input whose final true bit lies beyond the empty-input polynomial budget. -/
theorem clause1Aux_accepts_farTrue {q : ℕ} (V : CcProgram q) (c k : ℕ) (hpoly : CcPolyTime V c k)
    (N : ℕ) (hN : c * 0 ^ k + c < N) :
    ccAccepts V c k (List.replicate N false ++ [true]) = ccAccepts V c k [] := by
  simp only [ccAccepts, ccOracleAccepts]
  have hlen : ((List.replicate N false ++ [true] : List Bool)).length = N + 1 := by simp
  have hb : c * 0 ^ k + c ≤
      c * ((List.replicate N false ++ [true] : List Bool)).length ^ k + c := by
    rw [hlen]
    by_cases hk : k = 0
    · subst hk; simp
    · have h0 : (0 : ℕ) ^ k = 0 := Nat.zero_pow (by omega)
      have hpow : 0 ≤ (N + 1) ^ k := Nat.zero_le _
      rw [h0]
      have : c * 0 ≤ c * (N + 1) ^ k := Nat.mul_le_mul_left _ hpow
      omega
  have hbig := clause1Aux_result_farTrue V c k hpoly ccZeroOracle ccDefaultCoin N hN
    (c * ((List.replicate N false ++ [true] : List Bool)).length ^ k + c)
  have hhalt := clause1Aux_priv_result_halt V ccZeroOracle ccDefaultCoin [] (c * 0 ^ k + c)
    (hpoly ccZeroOracle ccDefaultCoin []).1
  have hrun := clause1Aux_priv_run_halt_le V ccZeroOracle ccDefaultCoin []
    (c * 0 ^ k + c) (c * ((List.replicate N false ++ [true] : List Bool)).length ^ k + c) hhalt hb
  rw [hbig]
  simp only [ccResult, hrun]
  rfl

/-- A program that writes true and then repeatedly moves left, with the head position truncated
at zero. -/
def clause1Aux_clampProbe : CcProgram 1 where
  states := fun i =>
    match (i : ℕ) with
    | 0 => CcAct.write true ⟨1, by omega⟩
    | _ => CcAct.moveL ⟨1, by omega⟩

/-- Executes two steps of `clause1Aux_clampProbe` with the zero oracle and default coin stream. -/
def clause1Aux_clampRun2 (c : CcConfig 1) : CcConfig 1 :=
  ccStep clause1Aux_clampProbe ccZeroOracle ccDefaultCoin
    (ccStep clause1Aux_clampProbe ccZeroOracle ccDefaultCoin c)

/-- The initial probe configuration with head zero, an all-false tape, and all resource counters
zero. -/
def clause1Aux_clampCfgA : CcConfig 1 where
  state := ⟨0, by omega⟩
  tape := fun _ => false
  head := 0
  query := []
  coinIdx := 0
  time := 0
  queries := 0
  queryBits := 0
  coins := 0

/-- The initial probe configuration with head one, a true bit at position zero, and all resource
counters zero. -/
def clause1Aux_clampCfgB : CcConfig 1 where
  state := ⟨0, by omega⟩
  tape := fun i => if i = 0 then true else false
  head := 1
  query := []
  coinIdx := 0
  time := 0
  queries := 0
  queryBits := 0
  coins := 0

/-- After two probe steps from either specified configuration, the head is at zero and the bit
under it is true. -/
theorem clause1Aux_clamp_falsePos :
    (clause1Aux_clampRun2 clause1Aux_clampCfgA).tape ((clause1Aux_clampRun2 clause1Aux_clampCfgA).head) = true ∧
      (clause1Aux_clampRun2 clause1Aux_clampCfgB).tape ((clause1Aux_clampRun2 clause1Aux_clampCfgB).head) = true ∧
      (clause1Aux_clampRun2 clause1Aux_clampCfgA).head = 0 ∧ (clause1Aux_clampRun2 clause1Aux_clampCfgB).head = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A program that moves right once and then accepts, leaving the input's first bit as its
singleton output. -/
def clause1Aux_outM : CcProgram 1 where
  states := fun i =>
    match (i : ℕ) with
    | 0 => CcAct.moveR ⟨1, by omega⟩
    | _ => CcAct.accept

/-- After one step, `clause1Aux_outM` has head position one and time one, with its original tape
and no queries or coin reads. -/
theorem clause1Aux_outM_run_one (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccRun clause1Aux_outM A ρ x 1 =
      ({ state := (⟨1, by omega⟩ : Fin 2), tape := fun i => x.getD i false,
         head := 1, query := [], coinIdx := 0, time := 1, queries := 0, queryBits := 0,
         coins := 0 } : CcConfig 1) := rfl

/-- The run of `clause1Aux_outM` is unchanged between one and two steps. -/
theorem clause1Aux_outM_run_two (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccRun clause1Aux_outM A ρ x 2 = ccRun clause1Aux_outM A ρ x 1 := by
  rw [clause1Aux_priv_run_succ, clause1Aux_outM_run_one]
  rfl

/-- At every step bound at least two, `clause1Aux_outM` has the same configuration as after two
steps. -/
theorem clause1Aux_outM_halt (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) (t : ℕ)
    (ht : 2 ≤ t) : ccRun clause1Aux_outM A ρ x t = ccRun clause1Aux_outM A ρ x 2 := by
  have hh : clause1Aux_outM.states (ccRun clause1Aux_outM A ρ x 2).state = CcAct.accept := by
    rw [clause1Aux_outM_run_two, clause1Aux_outM_run_one]
    rfl
  exact clause1Aux_priv_run_halt_le clause1Aux_outM A ρ x 2 t (Or.inl hh) ht

/-- At every step bound at least two, `clause1Aux_outM` outputs the singleton containing the
first input bit, with default `false`. -/
theorem clause1Aux_outM_output (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) (t : ℕ)
    (ht : 2 ≤ t) : ccOutput clause1Aux_outM A ρ x t = [x.getD 0 false] := by
  simp only [ccOutput, clause1Aux_outM_halt A ρ x t ht, clause1Aux_outM_run_two,
      clause1Aux_outM_run_one]
  rfl

/-- The singleton-output program is polynomial-time with coefficient two and exponent zero. -/
theorem clause1Aux_outM_poly : CcPolyTime clause1Aux_outM 2 0 := by
  intro A ρ x
  have hb : (2 : ℕ) * x.length ^ 0 + 2 = 4 := by simp
  have hres : ccResult clause1Aux_outM A ρ x 4 = some true := by
    simp only [ccResult, clause1Aux_outM_halt A ρ x 4 (by omega), clause1Aux_outM_run_two,
        clause1Aux_outM_run_one]
    rfl
  constructor
  · rw [hb]
    intro h
    rw [hres] at h
    simp at h
  · rw [hb]
    show (ccRun clause1Aux_outM A ρ x 4).time ≤ 4
    rw [clause1Aux_outM_halt A ρ x 4 (by omega), clause1Aux_outM_run_two, clause1Aux_outM_run_one]
    simp

/-- At step bound `t ≥ 2`, all `2 ^ t` coin strings produce the singleton output determined by
the first input bit. -/
theorem clause1Aux_outM_exactCount (A : List Bool → Bool) (x : List Bool) (t : ℕ) (ht : 2 ≤ t) :
    ccExactOutputCount clause1Aux_outM A x t (if x.getD 0 false then [true] else [false]) = 2 ^ t := by
  show (Finset.univ.filter (fun ω : Fin t → Bool =>
      ccOutput clause1Aux_outM A (ccCoinString ω) x t = (if x.getD 0 false then [true] else [false]))).card
      = 2 ^ t
  have hall : ∀ ω : Fin t → Bool,
      ccOutput clause1Aux_outM A (ccCoinString ω) x t = (if x.getD 0 false then [true] else [false]) := by
    intro ω
    rw [clause1Aux_outM_output A (ccCoinString ω) x t ht]
    cases x.getD 0 false <;> rfl
  have hfilter : (Finset.univ.filter (fun ω : Fin t → Bool =>
      ccOutput clause1Aux_outM A (ccCoinString ω) x t = (if x.getD 0 false then [true] else [false])))
      = Finset.univ := by
    ext ω
    simp [hall ω]
  rw [hfilter, Finset.card_univ]
  exact clause1Aux_card_fin_bool t

/-- The program whose sole state is rejecting. -/
def clause1Aux_rejV : CcProgram 0 where
  states := fun _ => CcAct.reject

/-- The always-rejecting program returns `some false` on every input at every step bound. -/
theorem clause1Aux_rejV_result (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) :
    ccResult clause1Aux_rejV A ρ x t = some false := rfl

/-- The always-rejecting program is polynomial-time with coefficient one and exponent zero. -/
theorem clause1Aux_rejV_poly : CcPolyTime clause1Aux_rejV 1 0 := by
  intro A ρ x
  have hb : (1 : ℕ) * x.length ^ 0 + 1 = 2 := by simp
  have hr : ∀ s, ccRun clause1Aux_rejV A ρ x s = ccInit 0 x := by
    intro s
    induction s with
    | zero => rfl
    | succ n ih => rw [clause1Aux_priv_run_succ, ih]; rfl
  constructor
  · rw [hb]
    intro h
    rw [clause1Aux_rejV_result A ρ x 2] at h
    simp at h
  · rw [hb]
    show (ccRun clause1Aux_rejV A ρ x 2).time ≤ 2
    rw [hr]
    show (0 : ℕ) ≤ 2
    decide

/-- The always-rejecting program rejects every input-witness pair. -/
theorem clause1Aux_rejV_verifies (z w : List Bool) :
    ccVerifies clause1Aux_rejV 1 0 z w = false := rfl

/-- The empty language belongs to `InNP` in the counting bit-machine model. -/
theorem clause1Aux_empty_inNP : InNP (fun _ : List Bool => False) := by
  refine ⟨0, 1, 0, 0, clause1Aux_rejV, clause1Aux_rejV_poly, ?_⟩
  intro x
  constructor
  · intro h
    exact h.elim
  · rintro ⟨w, hw⟩
    rw [clause1Aux_rejV_verifies x (List.ofFn w)] at hw
    simp at hw

/-- The function returning the first input bit as a singleton list belongs to `InFBPPNP`. -/
theorem clause1Aux_clause6_firstBit :
    InFBPPNP (fun x : List Bool => if x.getD 0 false then [true] else [false]) := by
  refine ⟨1, 2, 0, clause1Aux_outM, fun _ => False, clause1Aux_empty_inNP, clause1Aux_outM_poly, ?_⟩
  intro x
  have hb : (2 : ℕ) * x.length ^ 0 + 2 = 4 := by simp
  rw [hb]
  have hcount := clause1Aux_outM_exactCount (ccOracleOf (fun _ => False)) x 4 (by omega)
  rw [hcount]
  norm_num

/-- The language of inputs with true first bit belongs to `InBPP`. -/
theorem clause1Aux_firstBit_inBPP : InBPP (fun x : List Bool => x.getD 0 false = true) := by
  refine ⟨2, 1, 0, clause1BadV, clause1BadV_poly, ?_⟩
  intro x
  have hb : (1 : ℕ) * x.length ^ 0 + 1 = 2 := by simp
  have hpred : ∀ ω : Fin 2 → Bool,
      (ccResult clause1BadV ccZeroOracle (ccCoinString ω) x 2 = some true) ↔ (x.getD 0 false = true) := by
    intro ω
    rw [clause1BadV_result ccZeroOracle (ccCoinString ω) x 2 (by omega)]
    simp
  have hcount : ccAcceptCount clause1BadV ccZeroOracle x 2
      = if x.getD 0 false = true then 4 else 0 := by
    show (Finset.univ.filter (fun ω : Fin 2 → Bool =>
      ccResult clause1BadV ccZeroOracle (ccCoinString ω) x 2 = some true)).card = _
    by_cases hx : x.getD 0 false = true
    · rw [if_pos hx]
      have hfilter : (Finset.univ.filter (fun ω : Fin 2 → Bool =>
          ccResult clause1BadV ccZeroOracle (ccCoinString ω) x 2 = some true)) = Finset.univ := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun _ => trivial, fun _ => (hpred ω).mpr hx⟩
      rw [hfilter, Finset.card_univ]
      exact clause1Aux_card_fin_bool 2
    · rw [if_neg hx]
      have hfilter : (Finset.univ.filter (fun ω : Fin 2 → Bool =>
          ccResult clause1BadV ccZeroOracle (ccCoinString ω) x 2 = some true)) = (∅ : Finset _) := by
        rw [Finset.filter_eq_empty_iff]
        intro ω _
        exact fun h => absurd ((hpred ω).mp h) hx
      rw [hfilter, Finset.card_empty]
  constructor
  · intro hx
    rw [hb, hcount, if_pos hx]
    norm_num
  · intro hx
    rw [hb, hcount, if_neg hx]
    norm_num

/-- The conjunction of the stated relation-count estimator, affine-hash collision, and
oracle-estimator specifications is false in this tape model. -/
theorem clause2_counter : ¬
    (  (∀ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k → ∀ (d s : ℕ),
    ∃ (qE cE kE : ℕ) (E : CcProgram qE),
      CcPolyTime E cE kE
        ∧ CcInNPSet (ccHashWitnessSet V c k p)
        ∧ ∀ x : List Bool,
          2 ^ (s + 1)
              * ccEstGoodCount E (ccOracleOf (ccHashWitnessSet V c k p)) x
                  (cE * x.length ^ kE + cE) d (ccRelCount V c k p x)
            ≥ (2 ^ (s + 1) - 1) * 2 ^ (cE * x.length ^ kE + cE)
            ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                ccCoinsRead E (ccOracleOf (ccHashWitnessSet V c k p))
                    (ccCoinString ω) x (cE * x.length ^ kE + cE)
                  ≤ 64 * (d + 1) ^ 4 * (s + 1)
                      * (x.length + (p * x.length ^ p + p) + 2) ^ 4)
            ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                ccQueries E (ccOracleOf (ccHashWitnessSet V c k p))
                    (ccCoinString ω) x (cE * x.length ^ kE + cE)
                  ≤ 64 * (d + 1) ^ 4 * (s + 1)
                      * (x.length + (p * x.length ^ p + p) + 2))
            ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                ccTime E (ccOracleOf (ccHashWitnessSet V c k p))
                    (ccCoinString ω) x (cE * x.length ^ kE + cE)
                  ≤ 4096 * (d + 1) ^ 4 * (s + 1)
                      * (x.length + (p * x.length ^ p + p) + 2) ^ 8))

  ∧ (∀ (ℓ m : ℕ) (w w' : Fin m → Bool), w ≠ w' →
      (Finset.univ.filter
          (fun Pr : Matrix (Fin ℓ) (Fin m) Bool × (Fin ℓ → Bool) =>
            List.ofFn (ccHash Pr.1 Pr.2 w) = List.ofFn (ccHash Pr.1 Pr.2 w'))).card
        = 2 ^ (ℓ * m))

  ∧ (∀ (A : List Bool → Bool) (p d s : ℕ),
    ∃ (qE cE kE : ℕ) (E : CcProgram qE),
      CcPolyTime E cE kE
        ∧ CcInNPOracleSet A (ccHashWitnessOracleSet A p)
        ∧ ∀ x : List Bool,
          2 ^ (s + 1)
              * ccEstGoodCount E (ccOracleOf (ccHashWitnessOracleSet A p)) x
                  (cE * x.length ^ kE + cE) d (ccOracleRelCount A p x)
            ≥ (2 ^ (s + 1) - 1) * 2 ^ (cE * x.length ^ kE + cE)
            ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                ccCoinsRead E (ccOracleOf (ccHashWitnessOracleSet A p))
                    (ccCoinString ω) x (cE * x.length ^ kE + cE)
                  ≤ 64 * (d + 1) ^ 4 * (s + 1)
                      * (x.length + (p * x.length ^ p + p) + 2) ^ 4)
            ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                ccQueries E (ccOracleOf (ccHashWitnessOracleSet A p))
                    (ccCoinString ω) x (cE * x.length ^ kE + cE)
                  ≤ 64 * (d + 1) ^ 4 * (s + 1)
                      * (x.length + (p * x.length ^ p + p) + 2))
            ∧ (∀ ω : Fin (cE * x.length ^ kE + cE) → Bool,
                ccTime E (ccOracleOf (ccHashWitnessOracleSet A p))
                    (ccCoinString ω) x (cE * x.length ^ kE + cE)
                  ≤ 4096 * (d + 1) ^ 4 * (s + 1)
                      * (x.length + (p * x.length ^ p + p) + 2) ^ 8))) := by
  intro h
  exact clause2_clause1_counter h.1

/-- The conjunction of the stated linear-optics sampler, approximate-counting, and
distribution-transport specifications is false in this tape model. -/
theorem clause3_counter : ¬
    (  (∀ (m n : ℕ) (Sam : LoSampler m n) (S : FockOccupation m n),
    ((Finset.univ.filter (fun r : Fin Sam.L → Bool => Sam.O r = S)).card : ℝ)
      = loSamplerDist Sam S * ((2 : ℕ) ^ Sam.L : ℝ))

  ∧ (∀ (L N ŷ d : ℕ) (p δ : ℝ), 0 < δ → δ < 1 → 4 ≤ (d + 1) * δ →
      |((N : ℝ) / ((2 : ℕ) ^ L : ℝ)) - p| ≤ δ / 2 * p →
      (d + 1) * ((ŷ : ℤ) - (N : ℤ)).natAbs ≤ N →
      |((ŷ : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p| ≤ δ * p)

  ∧ (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
      ∀ (qM cM kM : ℕ) (M : CcProgram qM), CcPolyTime M cM kM →
        ∀ (Sam : LoSampler m n), 0 < Sam.L →
          ∀ S₀ : FockOccupation m n,
            (∀ r : Fin Sam.L → Bool,
              ccAccepts M cM kM (List.ofFn r) = decide (Sam.O r = S₀)) →
            ∀ (ε_s δ : ℝ), 0 < δ → δ < 1 →
              loTvDist (loSamplerDist Sam) (loIsometryDist m n A) ≤ ε_s →
              ε_s ≤ δ / 4 * loIsometryDist m n A S₀ →
              ∀ (d s : ℕ), 4 ≤ (d + 1) * δ →
                ∃ (qE cE kE : ℕ) (E : CcProgram qE),
                  CcPolyTime E cE kE
                    ∧ CcInNPSet (ccHashWitnessSet M cM kM Sam.L)
                    ∧ ((∑ ω : Fin (cE * 0 ^ kE + cE) → Bool,
                          (if
                            |(ccBitsToNat
                                (ccOutput E
                                  (ccOracleOf (ccHashWitnessSet M cM kM Sam.L))
                                  (ccCoinString ω) []
                                  (cE * 0 ^ kE + cE)) : ℝ)
                              / ((2 : ℕ) ^ Sam.L : ℝ)
                              - loIsometryDist m n A S₀|
                            ≤ δ * loIsometryDist m n A S₀
                          then (1 : ℝ) else 0))
                        / ((2 : ℕ) ^ (cE * 0 ^ kE + cE) : ℝ)
                        ≥ 1 - (1 : ℝ) / ((2 : ℕ) ^ (s + 1) : ℝ))
                    ∧ (∀ ω : Fin (cE * 0 ^ kE + cE) → Bool,
                        ccCoinsRead E
                          (ccOracleOf (ccHashWitnessSet M cM kM Sam.L))
                          (ccCoinString ω) [] (cE * 0 ^ kE + cE)
                          ≤ 64 * (d + 1) ^ 4 * (s + 1) * (Sam.L + 2) ^ 4)
                    ∧ (∀ ω : Fin (cE * 0 ^ kE + cE) → Bool,
                        ccQueries E
                          (ccOracleOf (ccHashWitnessSet M cM kM Sam.L))
                          (ccCoinString ω) [] (cE * 0 ^ kE + cE)
                          ≤ 64 * (d + 1) ^ 4 * (s + 1) * (Sam.L + 2))
                    ∧ (∀ ω : Fin (cE * 0 ^ kE + cE) → Bool,
                        ccTime E
                          (ccOracleOf (ccHashWitnessSet M cM kM Sam.L))
                          (ccCoinString ω) [] (cE * 0 ^ kE + cE)
                          ≤ 4096 * (d + 1) ^ 4 * (s + 1) * (Sam.L + 2) ^ 8))

  ∧ (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
      ∀ (qM cM kM : ℕ) (M : CcProgram qM), CcPolyTime M cM kM →
        ∀ (Sam : LoSampler m n), 0 < Sam.L →
          ∀ S₀ : FockOccupation m n,
            (∀ r : Fin Sam.L → Bool,
              ccAccepts M cM kM (List.ofFn r) = decide (Sam.O r = S₀)) →

            (InSharpP (fun x => ccRelCount M cM kM Sam.L x)
              ∧ ((ccRelCount M cM kM Sam.L [] : ℝ)
                  = loSamplerDist Sam S₀ * ((2 : ℕ) ^ Sam.L : ℝ)))
          ∧ (∀ S : FockOccupation m n,

              |loSamplerDist Sam S - loIsometryDist m n A S|
                ≤ 2 * loTvDist (loSamplerDist Sam) (loIsometryDist m n A))
          ∧ (∀ Ev : FockOccupation m n → Bool,

              |(∑ S : FockOccupation m n,
                  if Ev S = true then loSamplerDist Sam S else 0)
                - (∑ S : FockOccupation m n,
                  if Ev S = true then loIsometryDist m n A S else 0)|
                ≤ loTvDist (loSamplerDist Sam) (loIsometryDist m n A)))

  ∧ (∀ (m n : ℕ) (hmn : n ≤ m) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
      ∀ (W : LoCompletedUnitary m n hmn A) (G : loInterferometer m),
        loInterferometerMatrix m G = W.U →
        ∀ S₀ : FockOccupation m n,
          loFockDist m n hmn W.U S₀ = loIsometryDist m n A S₀
            ∧ loPhysicalDist m n hmn G S₀ = loIsometryDist m n A S₀)) := by
  intro h
  exact clause3_clause3_counter h.2.2.1

open Qatlib.Concepts.CountingClasses.ClassTransport

/-- The tape-and-head transformation that writes a local marker pattern to distinguish head
position zero from a positive head position. -/
def clause1Aux_probeCore (tape : ℕ → Bool) (head : ℕ) : (ℕ → Bool) × ℕ :=
  let h1 := head + 1
  let t1 : ℕ → Bool := fun i => if i = h1 then false else tape i
  let h2 := h1 - 1
  let t2 : ℕ → Bool := fun i => if i = h2 then true else t1 i
  let h3 := h2 - 1
  let t3 : ℕ → Bool := fun i => if i = h3 then false else t2 i
  let h4 := h3 + 1
  (t3, h4)

/-- The probe core returns head position one from zero and otherwise preserves the original head
position. -/
theorem clause1Aux_probeCore_head (tape : ℕ → Bool) (head : ℕ) :
    (clause1Aux_probeCore tape head).2 = if head = 0 then 1 else head := by
  simp only [clause1Aux_probeCore]
  by_cases h : head = 0
  · subst h
    simp
  · have e1 : head + 1 - 1 = head := by omega
    have e3 : head - 1 + 1 = head := by omega
    simp [e1, e3, h]

/-- The bit under the head returned by the probe core is true exactly when the original head
position was nonzero. -/
theorem clause1Aux_probeCore_read (tape : ℕ → Bool) (head : ℕ) :
    (clause1Aux_probeCore tape head).1 ((clause1Aux_probeCore tape head).2) = true ↔ head ≠ 0 := by
  simp only [clause1Aux_probeCore]
  by_cases h : head = 0
  · subst h
    simp
  · have e1 : head + 1 - 1 = head := by omega
    have e3 : head - 1 + 1 = head := by omega
    have e4 : head ≠ head - 1 := by omega
    have e5 : head ≠ head + 1 := by omega
    rw [e1, e3]
    simp only [e4, e5]
    simp [h]

/-- A finite program implementing the marker probe and branching to acceptance for positive
initial head position or rejection for initial head position zero. -/
def clause1Aux_zeroProbe : CcProgram 9 where
  states := fun i =>
    match (i : ℕ) with
    | 0 => CcAct.moveR ⟨1, by omega⟩
    | 1 => CcAct.write false ⟨2, by omega⟩
    | 2 => CcAct.moveL ⟨3, by omega⟩
    | 3 => CcAct.write true ⟨4, by omega⟩
    | 4 => CcAct.moveL ⟨5, by omega⟩
    | 5 => CcAct.write false ⟨6, by omega⟩
    | 6 => CcAct.moveR ⟨7, by omega⟩
    | 7 => CcAct.branch ⟨8, by omega⟩ ⟨9, by omega⟩
    | 8 => CcAct.accept
    | _ => CcAct.reject

/-- Executes eight successive machine steps from the given configuration. -/
private def clause1Aux_step8 {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (c : CcConfig q) : CcConfig q :=
  ccStep P A ρ (ccStep P A ρ (ccStep P A ρ (ccStep P A ρ
    (ccStep P A ρ (ccStep P A ρ (ccStep P A ρ (ccStep P A ρ c)))))))

/-- Starting in state zero, eight probe steps move a zero head to one and otherwise preserve its
position. The resulting bit and branch state distinguish zero from positive initial head
position. -/
theorem clause1Aux_zeroProbe_steps (A : List Bool → Bool) (ρ : ℕ → Bool) (c : CcConfig 9)
    (hs : (c.state : ℕ) = 0) :
    let c8 := clause1Aux_step8 clause1Aux_zeroProbe A ρ c
    (c8.head = if c.head = 0 then 1 else c.head) ∧
      ((c8.tape c8.head = true) ↔ (c.head ≠ 0)) ∧
      ((c8.state : ℕ) = if c.head = 0 then 9 else 8) := by
  have hs' : c.state = (⟨0, by omega⟩ : Fin 10) := Fin.ext hs
  simp only [clause1Aux_step8, ccStep, clause1Aux_zeroProbe, hs']
  by_cases h : c.head = 0
  · rw [h]
    simp
  · have e1 : c.head + 1 - 1 = c.head := by omega
    have e3 : c.head - 1 + 1 = c.head := by omega
    have e4 : ¬(c.head = c.head - 1) := by omega
    have e5 : ¬(c.head = c.head + 1) := by omega
    rw [e1, e3, if_neg e4, if_neg e5, if_pos rfl, if_pos rfl]
    simp [h]

/-- A final head at position one and tape bit `b` at position zero imply singleton output `[b]`. -/
theorem clause1Aux_output_of_head {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) (b : Bool) (hhead : (ccRun P A ρ x t).head = 1)
    (htape : (ccRun P A ρ x t).tape 0 = b) :
    ccOutput P A ρ x t = [b] := by
  simp [ccOutput, hhead, htape]

/-- An acceptance fraction at least two thirds remains at least two thirds after extending every
coin string by all possible suffixes. -/
theorem clause1Aux_count_transfer_pos {acc t t' : ℕ} (hle : t ≤ t')
    (h : 2 * 2 ^ t ≤ 3 * acc) : 2 * 2 ^ t' ≤ 3 * (acc * 2 ^ (t' - t)) := by
  have hmul : 2 ^ t * 2 ^ (t' - t) = 2 ^ t' := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
  calc 2 * 2 ^ t' = 2 * (2 ^ t * 2 ^ (t' - t)) := by rw [hmul]
    _ = (2 * 2 ^ t) * 2 ^ (t' - t) := by ring
    _ ≤ (3 * acc) * 2 ^ (t' - t) := Nat.mul_le_mul_right _ h
    _ = 3 * (acc * 2 ^ (t' - t)) := by ring

/-- If the acceptance fraction is at most one third, the rejection count remains at least two
thirds of the coin space after padding to a longer length. -/
theorem clause1Aux_count_transfer_neg {acc t t' : ℕ} (hle : t ≤ t')
    (h : 3 * acc ≤ 2 ^ t) : 2 * 2 ^ t' ≤ 3 * ((2 ^ t - acc) * 2 ^ (t' - t)) := by
  have hmul : 2 ^ t * 2 ^ (t' - t) = 2 ^ t' := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
  have hcore : 2 * 2 ^ t ≤ 3 * (2 ^ t - acc) := by
    have h1 : 3 * (2 ^ t - acc) = 3 * 2 ^ t - 3 * acc := Nat.mul_sub _ _ _
    have h2 : 2 * 2 ^ t ≤ 3 * 2 ^ t - 3 * acc := by
      set X := 2 ^ t
      omega
    omega
  calc 2 * 2 ^ t' = 2 * (2 ^ t * 2 ^ (t' - t)) := by rw [hmul]
    _ = (2 * 2 ^ t) * 2 ^ (t' - t) := by ring
    _ ≤ (3 * (2 ^ t - acc)) * 2 ^ (t' - t) := Nat.mul_le_mul_right _ hcore
    _ = 3 * ((2 ^ t - acc) * 2 ^ (t' - t)) := by ring

/-- A wrapper preserving accepting and rejecting branch counts up to coin-padding factors
transports an `InBPP` language's singleton decision-bit function into `InFBPPNP`. -/
theorem clause1Aux_clause6_of_wrap (L : List Bool → Prop) (hin : InBPP L)
    (hwrap : ∀ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k →
      (∀ x : List Bool,
        (L x → 3 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
            ≥ 2 * 2 ^ (c * x.length ^ k + c)) ∧
        (¬L x → 3 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
            ≤ 2 ^ (c * x.length ^ k + c))) →
      ∃ (q' c' k' : ℕ) (W : CcProgram q') (B : List Bool → Prop),
        CcInNPSet B ∧ CcPolyTime W c' k' ∧
        (∀ x : List Bool, c * x.length ^ k + c ≤ c' * x.length ^ k' + c') ∧
        (∀ x : List Bool,
          ccExactOutputCount W (ccOracleOf B) x (c' * x.length ^ k' + c') [true]
            = ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
                * 2 ^ ((c' * x.length ^ k' + c') - (c * x.length ^ k + c)) ∧
          ccExactOutputCount W (ccOracleOf B) x (c' * x.length ^ k' + c') [false]
            = (2 ^ (c * x.length ^ k + c)
                - ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c))
                * 2 ^ ((c' * x.length ^ k' + c') - (c * x.length ^ k + c)))) :
    InFBPPNP (fun x => if L x then [true] else [false]) := by
  obtain ⟨q, c, k, M, hpoly, hbnd⟩ := hin
  obtain ⟨q', c', k', W, B, hnp, hwpoly, hgap, hcount⟩ :=
    hwrap q c k M hpoly (fun x => hbnd x)
  refine ⟨q', c', k', W, B, hnp, hwpoly, ?_⟩
  intro x
  have hcnt := hcount x
  have hg := hgap x
  by_cases hx : L x
  · have hF : (fun x => if L x then [true] else [false]) x = [true] := if_pos hx
    rw [hF, hcnt.1]
    exact clause1Aux_count_transfer_pos hg ((hbnd x).1 hx)
  · have hF : (fun x => if L x then [true] else [false]) x = [false] := if_neg hx
    rw [hF, hcnt.2]
    exact clause1Aux_count_transfer_neg hg ((hbnd x).2 hx)

open scoped Classical BigOperators

/-- The Boolean oracle of the empty language is `ccZeroOracle`. -/
theorem clause1Aux_wrap_oracle_empty :
    (ccOracleOf (fun _ : List Bool => False)) = ccZeroOracle := by
  funext z
  simp [ccOracleOf, ccZeroOracle]

/-- Tests whether a machine action is accepting or rejecting. -/
private def clause1Aux_wrap_isHalt {q : ℕ} (a : CcAct q) : Bool :=
  match a with
  | CcAct.accept => true
  | CcAct.reject => true
  | _ => false

/-- Embeds an original state index into the wrapper's larger state space without changing its
numeric value. -/
private def clause1Aux_wrap_upFin {q : ℕ} (i : Fin (q + 1)) : Fin ((q + 26) + 1) :=
  ⟨(i : ℕ), by omega⟩

/-- Lifts machine actions to the wrapper state space, redirecting acceptance and rejection to
the corresponding output gadgets. -/
private def clause1Aux_wrap_liftAct {q : ℕ} (a : CcAct (q + 1)) : CcAct ((q + 26) + 1) :=
  match a with
  | CcAct.moveL j => CcAct.moveL (clause1Aux_wrap_upFin j)
  | CcAct.moveR j => CcAct.moveR (clause1Aux_wrap_upFin j)
  | CcAct.write b j => CcAct.write b (clause1Aux_wrap_upFin j)
  | CcAct.branch jt jf => CcAct.branch (clause1Aux_wrap_upFin jt) (clause1Aux_wrap_upFin jf)
  | CcAct.coinFlip jt jf => CcAct.coinFlip (clause1Aux_wrap_upFin jt) (clause1Aux_wrap_upFin jf)
  | CcAct.queryPush j => CcAct.queryPush (clause1Aux_wrap_upFin j)
  | CcAct.oracleCall jt jf => CcAct.oracleCall (clause1Aux_wrap_upFin jt) (clause1Aux_wrap_upFin jf)
  | CcAct.accept => CcAct.branch ⟨q + 14, by omega⟩ ⟨q + 14, by omega⟩
  | CcAct.reject => CcAct.branch ⟨q + 1, by omega⟩ ⟨q + 1, by omega⟩

/-- The state table for a gadget that locates the tape boundary, writes the prescribed Boolean
output, and accepts. -/
private def clause1Aux_gadStates {Q : ℕ} (base : ℕ) (b : Bool) (hbase : base + 12 < Q) :
    ℕ → CcAct Q
  | 0 => CcAct.moveR ⟨base + 1, by omega⟩
  | 1 => CcAct.write false ⟨base + 2, by omega⟩
  | 2 => CcAct.moveL ⟨base + 3, by omega⟩
  | 3 => CcAct.write true ⟨base + 4, by omega⟩
  | 4 => CcAct.moveL ⟨base + 5, by omega⟩
  | 5 => CcAct.write false ⟨base + 6, by omega⟩
  | 6 => CcAct.moveR ⟨base + 7, by omega⟩
  | 7 => CcAct.branch ⟨base + 8, by omega⟩ ⟨base + 9, by omega⟩
  | 8 => CcAct.moveL ⟨base + 0, by omega⟩
  | 9 => CcAct.moveL ⟨base + 10, by omega⟩
  | 10 => CcAct.write b ⟨base + 11, by omega⟩
  | 11 => CcAct.moveR ⟨base + 12, by omega⟩
  | _ => CcAct.accept

/-- The wrapper state table combining lifted original actions with separate false-output and
true-output gadgets. -/
private def clause1Aux_wrapStates {q : ℕ} (M : CcProgram q) (i : Fin ((q + 26) + 1)) :
    CcAct ((q + 26) + 1) :=
  if h : (i : ℕ) ≤ q then
    clause1Aux_wrap_liftAct (M.states ⟨(i : ℕ), by omega⟩)
  else if h2 : (i : ℕ) < q + 14 then
    clause1Aux_gadStates (base := q + 1) (b := false) (by omega) ((i : ℕ) - (q + 1))
  else
    clause1Aux_gadStates (base := q + 14) (b := true) (by omega) ((i : ℕ) - (q + 14))

/-- The program obtained by adding two output gadgets to `M`, converting its decision into a
singleton Boolean output. -/
def clause1Aux_wrapProg {q : ℕ} (M : CcProgram q) : CcProgram (q + 26) where
  states := clause1Aux_wrapStates M

/-- Embeds a configuration into the wrapper state space while preserving its tape, head, query,
coin index, and resource counters. -/
private def clause1Aux_wrap_upCfg {q : ℕ} (c : CcConfig q) : CcConfig (q + 26) where
  state := clause1Aux_wrap_upFin c.state
  tape := c.tape
  head := c.head
  query := c.query
  coinIdx := c.coinIdx
  time := c.time
  queries := c.queries
  queryBits := c.queryBits
  coins := c.coins

/-- Running for `t + 1` steps is one machine step applied to the configuration after `t` steps. -/
private lemma clause1Aux_wrap_run_succ {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) :
    ccRun P A ρ x (t + 1) = ccStep P A ρ (ccRun P A ρ x t) := rfl

/-- Executes a specified number of machine steps starting from an arbitrary configuration. -/
private def clause1Aux_wrap_runN {Q : ℕ} (P : CcProgram Q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (c : CcConfig Q) : ℕ → CcConfig Q
  | 0 => c
  | n + 1 => ccStep P A ρ (clause1Aux_wrap_runN P A ρ c n)

/-- Executing `n + 1` steps from a configuration is one machine step after executing `n` steps. -/
private lemma clause1Aux_wrap_runN_succ {Q : ℕ} (P : CcProgram Q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig Q) (n : ℕ) :
    clause1Aux_wrap_runN P A ρ c (n + 1) = ccStep P A ρ (clause1Aux_wrap_runN P A ρ c n) := rfl

/-- Execution for `m + n` steps factors into execution for `m` steps followed by execution for
`n` steps. -/
private lemma clause1Aux_wrap_runN_add {Q : ℕ} (P : CcProgram Q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig Q) (m n : ℕ) :
    clause1Aux_wrap_runN P A ρ c (m + n) = clause1Aux_wrap_runN P A ρ (clause1Aux_wrap_runN P A ρ c m) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show m + (n + 1) = (m + n) + 1 from rfl, clause1Aux_wrap_runN_succ, ih,
      clause1Aux_wrap_runN_succ]

/-- A run for `s + n` steps is obtained by executing `n` further steps from the configuration
after `s` steps. -/
private lemma clause1Aux_wrap_runN_run {Q : ℕ} (P : CcProgram Q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (s n : ℕ) :
    ccRun P A ρ x (s + n) = clause1Aux_wrap_runN P A ρ (ccRun P A ρ x s) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show s + (n + 1) = (s + n) + 1 from rfl, clause1Aux_wrap_run_succ, ih,
      clause1Aux_wrap_runN_succ]

/-- At an embedded original state, the wrapper's action is the lifted action of the original
program. -/
private lemma clause1Aux_wrap_states_sim {q : ℕ} (M : CcProgram q) (i : Fin (q + 1)) :
    (clause1Aux_wrapProg M).states (clause1Aux_wrap_upFin i) = clause1Aux_wrap_liftAct (M.states i) := by
  have hlt : (i : ℕ) < q + 1 := i.isLt
  have hle : (clause1Aux_wrap_upFin i : ℕ) ≤ q := by
    have h : (clause1Aux_wrap_upFin i : ℕ) = (i : ℕ) := rfl
    omega
  show clause1Aux_wrapStates M (clause1Aux_wrap_upFin i) = _
  simp only [clause1Aux_wrapStates]
  rw [dif_pos hle]
  rfl

/-- Embedding an original initial configuration gives the wrapper's initial configuration on the
same input. -/
private lemma clause1Aux_wrap_upCfg_init {q : ℕ} (x : List Bool) :
    clause1Aux_wrap_upCfg (ccInit q x) = ccInit (q + 26) x := rfl

/-- One wrapper step from an embedded configuration simulates an original step whenever the
original action is nonhalting. -/
private lemma clause1Aux_wrap_sim_step {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig q) (hn : clause1Aux_wrap_isHalt (M.states c.state) = false) :
    ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c) = clause1Aux_wrap_upCfg (ccStep M A ρ c) := by
  have hst : (clause1Aux_wrapProg M).states (clause1Aux_wrap_upCfg c).state
      = clause1Aux_wrap_liftAct (M.states c.state) := by
    have h1 : (clause1Aux_wrap_upCfg c).state = clause1Aux_wrap_upFin c.state := rfl
    rw [h1, clause1Aux_wrap_states_sim]
  cases hs : M.states c.state with
  | accept => simp [clause1Aux_wrap_isHalt, hs] at hn
  | reject => simp [clause1Aux_wrap_isHalt, hs] at hn
  | moveL j =>
    simp only [ccStep]; rw [hst, hs]; simp [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg,
        clause1Aux_wrap_upFin]
  | moveR j =>
    simp only [ccStep]; rw [hst, hs]; simp [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg,
        clause1Aux_wrap_upFin]
  | write b j =>
    simp only [ccStep]; rw [hst, hs]; simp [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg,
        clause1Aux_wrap_upFin]
  | branch jt jf =>
    simp only [ccStep]; rw [hst, hs]
    simp only [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg, clause1Aux_wrap_upFin]
    split_ifs <;> rfl
  | coinFlip jt jf =>
    simp only [ccStep]; rw [hst, hs]
    simp only [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg, clause1Aux_wrap_upFin]
    split_ifs <;> rfl
  | queryPush j =>
    simp only [ccStep]; rw [hst, hs]; simp [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg,
        clause1Aux_wrap_upFin]
  | oracleCall jt jf =>
    simp only [ccStep]; rw [hst, hs]
    simp only [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg, clause1Aux_wrap_upFin]
    split_ifs <;> rfl

/-- The wrapper run equals the embedded original run through step `j` if the original run has no
halting action at any earlier step. -/
private lemma clause1Aux_wrap_sim_run {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) :
    ∀ j : ℕ, (∀ i < j, clause1Aux_wrap_isHalt (M.states (ccRun M A ρ x i).state) = false) →
      ccRun (clause1Aux_wrapProg M) A ρ x j = clause1Aux_wrap_upCfg (ccRun M A ρ x j) := by
  intro j
  induction j with
  | zero => intro _; exact (clause1Aux_wrap_upCfg_init x).symm
  | succ n ih =>
    intro hn
    have hn' : ∀ i < n, clause1Aux_wrap_isHalt (M.states (ccRun M A ρ x i).state) = false :=
      fun i hi => hn i (by omega)
    have hnn : clause1Aux_wrap_isHalt (M.states (ccRun M A ρ x n).state) = false := hn n (by omega)
    rw [clause1Aux_wrap_run_succ, clause1Aux_wrap_run_succ, ih hn',
      clause1Aux_wrap_sim_step M A ρ (ccRun M A ρ x n) hnn]

/-- An accepting or rejecting configuration is fixed by `ccStep`. -/
private lemma clause1Aux_wrap_step_halt {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig q)
    (h : P.states c.state = CcAct.accept ∨ P.states c.state = CcAct.reject) :
    ccStep P A ρ c = c := by
  rcases h with h | h <;> simp [ccStep, h]

/-- Once a run reaches an accepting or rejecting state at time `t`, every later step bound gives
the same configuration. -/
private lemma clause1Aux_wrap_run_halt_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t t' : ℕ)
    (hh : P.states (ccRun P A ρ x t).state = CcAct.accept ∨
      P.states (ccRun P A ρ x t).state = CcAct.reject)
    (hle : t ≤ t') : ccRun P A ρ x t' = ccRun P A ρ x t := by
  have h1 : ∀ s, ccRun P A ρ x (t + s) = ccRun P A ρ x t := by
    intro s
    induction s with
    | zero => rfl
    | succ n ih =>
      rw [show t + (n + 1) = (t + n) + 1 from rfl, clause1Aux_wrap_run_succ, ih,
        clause1Aux_wrap_step_halt P A ρ _ hh]
  have h2 : t + (t' - t) = t' := by omega
  rw [← h2]
  exact h1 (t' - t)

/-- Executes eight successive steps from an arbitrary configuration for the wrapper analysis. -/
private def clause1Aux_wrap_step8 {Q : ℕ} (P : CcProgram Q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (c : CcConfig Q) : CcConfig Q :=
  ccStep P A ρ (ccStep P A ρ (ccStep P A ρ (ccStep P A ρ
    (ccStep P A ρ (ccStep P A ρ (ccStep P A ρ (ccStep P A ρ c)))))))

/-- Iterating the machine step eight times agrees with the explicit eight-step expression. -/
private lemma clause1Aux_wrap_runN_8 {Q : ℕ} (P : CcProgram Q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig Q) :
    clause1Aux_wrap_runN P A ρ c 8 = clause1Aux_wrap_step8 P A ρ c := rfl

/-- The wrapper states at offsets zero through twelve from `q + 1` implement the false-output
gadget. -/
private lemma clause1Aux_wrap_gadStates_false {q : ℕ} (M : CcProgram q) (d : ℕ) (hd : d ≤ 12) :
    (clause1Aux_wrapProg M).states (⟨q + 1 + d, by omega⟩ : Fin (q + 27))
      = clause1Aux_gadStates (base := q + 1) (b := false) (by omega) d := by
  show clause1Aux_wrapStates M ⟨q + 1 + d, by omega⟩ = _
  simp only [clause1Aux_wrapStates]
  rw [dif_neg (by omega : ¬(q + 1 + d ≤ q)), dif_pos (by omega : q + 1 + d < q + 14)]
  have hsub : q + 1 + d - (q + 1) = d := by omega
  rw [hsub]

/-- The wrapper states at offsets zero through twelve from `q + 14` implement the true-output
gadget. -/
private lemma clause1Aux_wrap_gadStates_true {q : ℕ} (M : CcProgram q) (d : ℕ) (hd : d ≤ 12) :
    (clause1Aux_wrapProg M).states (⟨q + 14 + d, by omega⟩ : Fin (q + 27))
      = clause1Aux_gadStates (base := q + 14) (b := true) (by omega) d := by
  show clause1Aux_wrapStates M ⟨q + 14 + d, by omega⟩ = _
  simp only [clause1Aux_wrapStates]
  rw [dif_neg (by omega : ¬(q + 14 + d ≤ q)),
    dif_neg (by omega : ¬(q + 14 + d < q + 14))]
  have hsub : q + 14 + d - (q + 14) = d := by omega
  rw [hsub]

/-- After eight steps in a matching output gadget, the head and branch state distinguish zero
from positive initial head position, and the charged time increases by eight. -/
private lemma clause1Aux_wrap_probeCore {Q : ℕ} (P : CcProgram Q) (base : ℕ) (b : Bool)
    (hbase : base + 12 < Q + 1)
    (hact : ∀ (d : ℕ) (_hd : d ≤ 12),
      P.states (⟨base + d, by omega⟩ : Fin (Q + 1))
        = clause1Aux_gadStates (base := base) (b := b) hbase d)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (c : CcConfig Q)
    (hs : c.state = (⟨base, by omega⟩ : Fin (Q + 1))) :
    (clause1Aux_wrap_runN P A ρ c 8).head = (if c.head = 0 then 1 else c.head) ∧
      ((clause1Aux_wrap_runN P A ρ c 8).state : ℕ)
        = (if c.head = 0 then base + 9 else base + 8) ∧
      (clause1Aux_wrap_runN P A ρ c 8).time = c.time + 8 := by
  have ha0 : P.states (⟨base, by omega⟩ : Fin (Q + 1))
      = clause1Aux_gadStates (base := base) (b := b) hbase 0 := by
    simpa using hact 0 (by omega)
  have ha1 : P.states (⟨base + 1, by omega⟩ : Fin (Q + 1))
      = clause1Aux_gadStates (base := base) (b := b) hbase 1 := by
    simpa using hact 1 (by omega)
  have ha2 : P.states (⟨base + 2, by omega⟩ : Fin (Q + 1))
      = clause1Aux_gadStates (base := base) (b := b) hbase 2 := by
    simpa using hact 2 (by omega)
  have ha3 : P.states (⟨base + 3, by omega⟩ : Fin (Q + 1))
      = clause1Aux_gadStates (base := base) (b := b) hbase 3 := by
    simpa using hact 3 (by omega)
  have ha4 : P.states (⟨base + 4, by omega⟩ : Fin (Q + 1))
      = clause1Aux_gadStates (base := base) (b := b) hbase 4 := by
    simpa using hact 4 (by omega)
  have ha5 : P.states (⟨base + 5, by omega⟩ : Fin (Q + 1))
      = clause1Aux_gadStates (base := base) (b := b) hbase 5 := by
    simpa using hact 5 (by omega)
  have ha6 : P.states (⟨base + 6, by omega⟩ : Fin (Q + 1))
      = clause1Aux_gadStates (base := base) (b := b) hbase 6 := by
    simpa using hact 6 (by omega)
  have ha7 : P.states (⟨base + 7, by omega⟩ : Fin (Q + 1))
      = clause1Aux_gadStates (base := base) (b := b) hbase 7 := by
    simpa using hact 7 (by omega)
  have ga0 : clause1Aux_gadStates (base := base) (b := b) hbase 0
      = CcAct.moveR ⟨base + 1, by omega⟩ := rfl
  have ga1 : clause1Aux_gadStates (base := base) (b := b) hbase 1
      = CcAct.write false ⟨base + 2, by omega⟩ := rfl
  have ga2 : clause1Aux_gadStates (base := base) (b := b) hbase 2
      = CcAct.moveL ⟨base + 3, by omega⟩ := rfl
  have ga3 : clause1Aux_gadStates (base := base) (b := b) hbase 3
      = CcAct.write true ⟨base + 4, by omega⟩ := rfl
  have ga4 : clause1Aux_gadStates (base := base) (b := b) hbase 4
      = CcAct.moveL ⟨base + 5, by omega⟩ := rfl
  have ga5 : clause1Aux_gadStates (base := base) (b := b) hbase 5
      = CcAct.write false ⟨base + 6, by omega⟩ := rfl
  have ga6 : clause1Aux_gadStates (base := base) (b := b) hbase 6
      = CcAct.moveR ⟨base + 7, by omega⟩ := rfl
  have ga7 : clause1Aux_gadStates (base := base) (b := b) hbase 7
      = CcAct.branch ⟨base + 8, by omega⟩ ⟨base + 9, by omega⟩ := rfl
  rw [clause1Aux_wrap_runN_8]
  simp only [clause1Aux_wrap_step8, ccStep, hs, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
    ga0, ga1, ga2, ga3, ga4, ga5, ga6, ga7]
  by_cases h : c.head = 0
  · rw [h]
    simp
  · have e1 : c.head + 1 - 1 = c.head := by omega
    have e3 : c.head - 1 + 1 = c.head := by omega
    have e4 : ¬(c.head = c.head - 1) := by omega
    have e5 : ¬(c.head = c.head + 1) := by omega
    rw [e1, e3, if_neg e4, if_neg e5, if_pos rfl, if_pos rfl]
    simp [h]

/-- A matching output gadget starting at head position `h` reaches its final state after `9 * h
+ 12` steps, with head one, output bit `b` at position zero, and charged-time increase at
most that bound. -/
private lemma clause1Aux_wrap_gadCore {Q : ℕ} (P : CcProgram Q) (base : ℕ) (b : Bool)
    (hbase : base + 12 < Q + 1)
    (hact : ∀ (d : ℕ) (_hd : d ≤ 12),
      P.states (⟨base + d, by omega⟩ : Fin (Q + 1))
        = clause1Aux_gadStates (base := base) (b := b) hbase d)
    (A : List Bool → Bool) (ρ : ℕ → Bool) :
    ∀ (c : CcConfig Q) (h : ℕ), c.state = (⟨base, by omega⟩ : Fin (Q + 1)) → c.head = h →
      (clause1Aux_wrap_runN P A ρ c (9 * h + 12)).state = (⟨base + 12, by omega⟩ : Fin (Q + 1)) ∧
        (clause1Aux_wrap_runN P A ρ c (9 * h + 12)).head = 1 ∧
        (clause1Aux_wrap_runN P A ρ c (9 * h + 12)).tape 0 = b ∧
        (clause1Aux_wrap_runN P A ρ c (9 * h + 12)).time ≤ c.time + (9 * h + 12) := by
  intro c h
  induction h generalizing c with
  | zero =>
    intro hs hh
    have h0 : c.head = 0 := by omega
    have hp := clause1Aux_wrap_probeCore P base b hbase hact A ρ c hs
    have hp1 : (clause1Aux_wrap_runN P A ρ c 8).head = 1 := by
      rw [hp.1, if_pos h0]
    have hp2 : ((clause1Aux_wrap_runN P A ρ c 8).state : ℕ) = base + 9 := by
      rw [hp.2.1, if_pos h0]
    have hp3 : (clause1Aux_wrap_runN P A ρ c 8).time = c.time + 8 := hp.2.2
    have hst9 : (clause1Aux_wrap_runN P A ρ c 8).state = (⟨base + 9, by omega⟩ : Fin (Q + 1)) :=
      Fin.ext (by rw [hp2])
    have ha9 : P.states (⟨base + 9, by omega⟩ : Fin (Q + 1))
        = clause1Aux_gadStates (base := base) (b := b) hbase 9 := by
      simpa using hact 9 (by omega)
    have ha10 : P.states (⟨base + 10, by omega⟩ : Fin (Q + 1))
        = clause1Aux_gadStates (base := base) (b := b) hbase 10 := by
      simpa using hact 10 (by omega)
    have ha11 : P.states (⟨base + 11, by omega⟩ : Fin (Q + 1))
        = clause1Aux_gadStates (base := base) (b := b) hbase 11 := by
      simpa using hact 11 (by omega)
    have ha12 : P.states (⟨base + 12, by omega⟩ : Fin (Q + 1))
        = clause1Aux_gadStates (base := base) (b := b) hbase 12 := by
      simpa using hact 12 (by omega)
    have ga9 : clause1Aux_gadStates (base := base) (b := b) hbase 9
        = CcAct.moveL ⟨base + 10, by omega⟩ := rfl
    have ga10 : clause1Aux_gadStates (base := base) (b := b) hbase 10
        = CcAct.write b ⟨base + 11, by omega⟩ := rfl
    have ga11 : clause1Aux_gadStates (base := base) (b := b) hbase 11
        = CcAct.moveR ⟨base + 12, by omega⟩ := rfl
    have ga12 : clause1Aux_gadStates (base := base) (b := b) hbase 12
        = CcAct.accept := rfl
    have h9state : (clause1Aux_wrap_runN P A ρ c 9).state
        = (⟨base + 10, by omega⟩ : Fin (Q + 1)) := by
      rw [show (9 : ℕ) = 8 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, hst9, ha9, ga9]
    have h9head : (clause1Aux_wrap_runN P A ρ c 9).head = 0 := by
      rw [show (9 : ℕ) = 8 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, hst9, ha9, ga9, hp1]
    have h9time : (clause1Aux_wrap_runN P A ρ c 9).time = c.time + 9 := by
      rw [show (9 : ℕ) = 8 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, hst9, ha9, ga9, hp3]
    have h10state : (clause1Aux_wrap_runN P A ρ c 10).state
        = (⟨base + 11, by omega⟩ : Fin (Q + 1)) := by
      rw [show (10 : ℕ) = 9 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, h9state, ha10, ga10]
    have h10tape : ∀ i, (clause1Aux_wrap_runN P A ρ c 10).tape i
        = if i = (clause1Aux_wrap_runN P A ρ c 9).head then b else (clause1Aux_wrap_runN P A ρ c 9).tape i := by
      intro i
      rw [show (10 : ℕ) = 9 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, h9state, ha10, ga10]
    have h10head : (clause1Aux_wrap_runN P A ρ c 10).head = (clause1Aux_wrap_runN P A ρ c 9).head := by
      rw [show (10 : ℕ) = 9 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, h9state, ha10, ga10]
    have h10time : (clause1Aux_wrap_runN P A ρ c 10).time = (clause1Aux_wrap_runN P A ρ c 9).time + 1 := by
      rw [show (10 : ℕ) = 9 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, h9state, ha10, ga10]
    have h11state : (clause1Aux_wrap_runN P A ρ c 11).state
        = (⟨base + 12, by omega⟩ : Fin (Q + 1)) := by
      rw [show (11 : ℕ) = 10 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, h10state, ha11, ga11]
    have h11head : (clause1Aux_wrap_runN P A ρ c 11).head = 1 := by
      rw [show (11 : ℕ) = 10 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, h10state, ha11, ga11, h10head, h9head]
    have h11tape : ∀ i, (clause1Aux_wrap_runN P A ρ c 11).tape i
        = (clause1Aux_wrap_runN P A ρ c 10).tape i := by
      intro i
      rw [show (11 : ℕ) = 10 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, h10state, ha11, ga11]
    have h11time : (clause1Aux_wrap_runN P A ρ c 11).time = (clause1Aux_wrap_runN P A ρ c 10).time + 1 := by
      rw [show (11 : ℕ) = 10 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, h10state, ha11, ga11]
    have h12eq : clause1Aux_wrap_runN P A ρ c 12 = clause1Aux_wrap_runN P A ρ c 11 := by
      rw [show (12 : ℕ) = 11 + 1 from rfl, clause1Aux_wrap_runN_succ]
      have halt : P.states (clause1Aux_wrap_runN P A ρ c 11).state = CcAct.accept := by
        rw [h11state, ha12, ga12]
      exact clause1Aux_wrap_step_halt P A ρ _ (Or.inl halt)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show (9 * 0 + 12 : ℕ) = 12 by omega, h12eq, h11state]
    · rw [show (9 * 0 + 12 : ℕ) = 12 by omega, h12eq, h11head]
    · rw [show (9 * 0 + 12 : ℕ) = 12 by omega, h12eq, h11tape 0, h10tape, h9head]
      rfl
    · rw [show (9 * 0 + 12 : ℕ) = 12 by omega, h12eq, h11time, h10time, h9time]
      omega
  | succ n ih =>
    intro hs hh
    have hpos : c.head ≠ 0 := by omega
    have hp := clause1Aux_wrap_probeCore P base b hbase hact A ρ c hs
    have hp1 : (clause1Aux_wrap_runN P A ρ c 8).head = c.head := by
      rw [hp.1, if_neg hpos]
    have hp2 : ((clause1Aux_wrap_runN P A ρ c 8).state : ℕ) = base + 8 := by
      rw [hp.2.1, if_neg hpos]
    have hp3 : (clause1Aux_wrap_runN P A ρ c 8).time = c.time + 8 := hp.2.2
    have hst8 : (clause1Aux_wrap_runN P A ρ c 8).state = (⟨base + 8, by omega⟩ : Fin (Q + 1)) :=
      Fin.ext (by rw [hp2])
    have ha8 : P.states (⟨base + 8, by omega⟩ : Fin (Q + 1))
        = clause1Aux_gadStates (base := base) (b := b) hbase 8 := by
      simpa using hact 8 (by omega)
    have ga8 : clause1Aux_gadStates (base := base) (b := b) hbase 8
        = CcAct.moveL ⟨base + 0, by omega⟩ := rfl
    have h9state : (clause1Aux_wrap_runN P A ρ c 9).state
        = (⟨base + 0, by omega⟩ : Fin (Q + 1)) := by
      rw [show (9 : ℕ) = 8 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, hst8, ha8, ga8]
    have h9head : (clause1Aux_wrap_runN P A ρ c 9).head = n := by
      rw [show (9 : ℕ) = 8 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, hst8, ha8, ga8, hp1, hh]
      omega
    have h9time : (clause1Aux_wrap_runN P A ρ c 9).time = c.time + 9 := by
      rw [show (9 : ℕ) = 8 + 1 from rfl, clause1Aux_wrap_runN_succ]
      simp only [ccStep, hst8, ha8, ga8, hp3]
    have hrec : clause1Aux_wrap_runN P A ρ c (9 * n.succ + 12)
        = clause1Aux_wrap_runN P A ρ (clause1Aux_wrap_runN P A ρ c 9) (9 * n + 12) := by
      have h : 9 * n.succ + 12 = 9 + (9 * n + 12) := by omega
      rw [h, clause1Aux_wrap_runN_add]
    have hcfg : (clause1Aux_wrap_runN P A ρ c 9).state = (⟨base, by omega⟩ : Fin (Q + 1)) := by
      rw [h9state]
      rfl
    have hih := ih (clause1Aux_wrap_runN P A ρ c 9) hcfg h9head
    obtain ⟨hstate, hfin, htape, htle⟩ := hih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrec]
      exact hstate
    · rw [hrec]
      exact hfin
    · rw [hrec]
      exact htape
    · rw [hrec]
      calc (clause1Aux_wrap_runN P A ρ (clause1Aux_wrap_runN P A ρ c 9) (9 * n + 12)).time
          ≤ (clause1Aux_wrap_runN P A ρ c 9).time + (9 * n + 12) := htle
        _ ≤ c.time + (9 * n.succ + 12) := by rw [h9time]; omega

/-- The coin-stream index after `t` machine steps is at most `t`. -/
private lemma clause1Aux_wrap_coinIdx_le {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) : (ccRun P A ρ x t).coinIdx ≤ t := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [clause1Aux_wrap_run_succ]
    cases h : P.states (ccRun P A ρ x n).state <;> simp [ccStep, h] <;> omega

/-- Coin streams agreeing at every index below `t` produce the same configuration after `t`
machine steps. -/
private lemma clause1Aux_wrap_coinPrefix {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ1 ρ2 : ℕ → Bool) (x : List Bool) :
    ∀ t : ℕ, (∀ i, i < t → ρ1 i = ρ2 i) → ccRun P A ρ1 x t = ccRun P A ρ2 x t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
    intro hagr
    have hn : ∀ i, i < n → ρ1 i = ρ2 i := fun i hi => hagr i (by omega)
    have hc := ih hn
    rw [clause1Aux_wrap_run_succ, clause1Aux_wrap_run_succ, hc]
    have hle := clause1Aux_wrap_coinIdx_le P A ρ2 x n
    have hcoin : ρ1 (ccRun P A ρ2 x n).coinIdx = ρ2 (ccRun P A ρ2 x n).coinIdx :=
      hagr _ (by omega)
    cases h : P.states (ccRun P A ρ2 x n).state <;> simp [ccStep, h, hcoin]

/-- The halting test is true exactly for accepting or rejecting actions. -/
private lemma clause1Aux_wrap_isHalt_iff {q : ℕ} (a : CcAct q) :
    clause1Aux_wrap_isHalt a = true ↔ (a = CcAct.accept ∨ a = CcAct.reject) := by
  cases a <;> simp [clause1Aux_wrap_isHalt]

/-- The proposition that the original program's action after `j` steps is accepting or
rejecting. -/
private def clause1Aux_wrap_haltPred {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (j : ℕ) : Prop :=
  clause1Aux_wrap_isHalt (M.states (ccRun M A ρ x j).state) = true

/-- A machine result different from `none` implies that the current action is accepting or
rejecting. -/
private lemma clause1Aux_wrap_result_halt {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) (h : ccResult P A ρ x t ≠ none) :
    clause1Aux_wrap_haltPred P A ρ x t := by
  cases hs : P.states (ccRun P A ρ x t).state with
  | accept => simp [clause1Aux_wrap_haltPred, hs, clause1Aux_wrap_isHalt]
  | reject => simp [clause1Aux_wrap_haltPred, hs, clause1Aux_wrap_isHalt]
  | moveL j => simp [ccResult, hs] at h
  | moveR j => simp [ccResult, hs] at h
  | write b j => simp [ccResult, hs] at h
  | branch jt jf => simp [ccResult, hs] at h
  | coinFlip jt jf => simp [ccResult, hs] at h
  | queryPush j => simp [ccResult, hs] at h
  | oracleCall jt jf => simp [ccResult, hs] at h

/-- From an embedded accepting configuration, the wrapper enters the true-output gadget at state
`q + 14`, preserving tape and head and increasing charged time by one. -/
private lemma clause1Aux_wrap_intercept_true {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig q) (hacc : M.states c.state = CcAct.accept) :
    ((ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c)).state : ℕ) = q + 14 ∧
      (ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c)).head = c.head ∧
      (ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c)).tape = c.tape ∧
      (ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c)).time = c.time + 1 := by
  have hst : (clause1Aux_wrapProg M).states (clause1Aux_wrap_upCfg c).state
      = clause1Aux_wrap_liftAct (M.states c.state) := by
    have h1 : (clause1Aux_wrap_upCfg c).state = clause1Aux_wrap_upFin c.state := rfl
    rw [h1, clause1Aux_wrap_states_sim]
  simp only [ccStep]
  rw [hst, hacc]
  simp [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg, clause1Aux_wrap_upFin]

/-- From an embedded rejecting configuration, the wrapper enters the false-output gadget at
state `q + 1`, preserving tape and head and increasing charged time by one. -/
private lemma clause1Aux_wrap_intercept_false {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig q) (hrej : M.states c.state = CcAct.reject) :
    ((ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c)).state : ℕ) = q + 1 ∧
      (ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c)).head = c.head ∧
      (ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c)).tape = c.tape ∧
      (ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg c)).time = c.time + 1 := by
  have hst : (clause1Aux_wrapProg M).states (clause1Aux_wrap_upCfg c).state
      = clause1Aux_wrap_liftAct (M.states c.state) := by
    have h1 : (clause1Aux_wrap_upCfg c).state = clause1Aux_wrap_upFin c.state := rfl
    rw [h1, clause1Aux_wrap_states_sim]
  simp only [ccStep]
  rw [hst, hrej]
  simp [clause1Aux_wrap_liftAct, clause1Aux_wrap_upCfg, clause1Aux_wrap_upFin]

/-- Starting at the false-output gadget with head `h`, after `9 * h + 12` steps the wrapper is
accepting at state `q + 13`, has head one and false at tape position zero, and satisfies the
stated time bound. -/
private lemma clause1Aux_wrap_gadW_false {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig (q + 26)) (h : ℕ)
    (hstate : c.state = (⟨q + 1, by omega⟩ : Fin (q + 27))) (hhead : c.head = h) :
    (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).state
        = (⟨q + 13, by omega⟩ : Fin (q + 27)) ∧
      (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).head = 1 ∧
      (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).tape 0 = false ∧
      (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).time ≤ c.time + (9 * h + 12) ∧
      (clause1Aux_wrapProg M).states
          (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).state = CcAct.accept := by
  have hact : ∀ (d : ℕ) (_hd : d ≤ 12),
      (clause1Aux_wrapProg M).states (⟨q + 1 + d, by omega⟩ : Fin (q + 27))
        = clause1Aux_gadStates (base := q + 1) (b := false) (by omega) d := by
    intro d hd
    exact clause1Aux_wrap_gadStates_false M d hd
  have hg :=
      clause1Aux_wrap_gadCore (clause1Aux_wrapProg M) (q + 1) false
      (by omega) hact A ρ c h hstate hhead
  obtain ⟨hst, hfin, htape, htle⟩ := hg
  refine ⟨?_, hfin, htape, htle, ?_⟩
  · rw [hst]
  · rw [hst, clause1Aux_wrap_gadStates_false M 12 (by omega)]
    rfl

/-- Starting at the true-output gadget with head `h`, after `9 * h + 12` steps the wrapper is
accepting at state `q + 26`, has head one and true at tape position zero, and satisfies the
stated time bound. -/
private lemma clause1Aux_wrap_gadW_true {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (c : CcConfig (q + 26)) (h : ℕ)
    (hstate : c.state = (⟨q + 14, by omega⟩ : Fin (q + 27))) (hhead : c.head = h) :
    (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).state
        = (⟨q + 26, by omega⟩ : Fin (q + 27)) ∧
      (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).head = 1 ∧
      (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).tape 0 = true ∧
      (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).time ≤ c.time + (9 * h + 12) ∧
      (clause1Aux_wrapProg M).states
          (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ c (9 * h + 12)).state = CcAct.accept := by
  have hact : ∀ (d : ℕ) (_hd : d ≤ 12),
      (clause1Aux_wrapProg M).states (⟨q + 14 + d, by omega⟩ : Fin (q + 27))
        = clause1Aux_gadStates (base := q + 14) (b := true) (by omega) d := by
    intro d hd
    exact clause1Aux_wrap_gadStates_true M d hd
  have hg :=
      clause1Aux_wrap_gadCore (clause1Aux_wrapProg M) (q + 14) true
      (by omega) hact A ρ c h hstate hhead
  obtain ⟨hst, hfin, htape, htle⟩ := hg
  refine ⟨?_, hfin, htape, htle, ?_⟩
  · rw [hst]
  · rw [hst, clause1Aux_wrap_gadStates_true M 12 (by omega)]
    rfl

/-- At any step bound `t' ≥ 10 * t + 13`, where `t` is the original polynomial budget, the
wrapper accepts and outputs the original decision as a singleton bit, with charged time at
most `t'`. -/
private lemma clause1Aux_wrap_main {q c k : ℕ} (M : CcProgram q) (hp : CcPolyTime M c k)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) (t t' : ℕ)
    (ht : t = c * x.length ^ k + c) (hgap : 10 * t + 13 ≤ t') :
    ccOutput (clause1Aux_wrapProg M) A ρ x t'
      = (if ccResult M A ρ x t = some true then [true] else [false]) ∧
      ccResult (clause1Aux_wrapProg M) A ρ x t' = some true ∧
      ccTime (clause1Aux_wrapProg M) A ρ x t' ≤ t' := by
  have hp' := hp A ρ x
  have hres : ccResult M A ρ x t ≠ none := by
    rw [ht]
    exact hp'.1
  have htm : ccTime M A ρ x t ≤ t := by
    rw [ht]
    exact hp'.2
  have hex : ∃ j, clause1Aux_wrap_haltPred M A ρ x j :=
    ⟨t, clause1Aux_wrap_result_halt M A ρ x t hres⟩
  have hs_spec : clause1Aux_wrap_haltPred M A ρ x (Nat.find hex) := Nat.find_spec hex
  have hs_min : ∀ i < Nat.find hex, clause1Aux_wrap_haltPred M A ρ x i → False :=
    fun i hi => Nat.find_min hex hi
  have hs_le : Nat.find hex ≤ t :=
    not_lt.mp (fun hlt => Nat.find_min hex hlt (clause1Aux_wrap_result_halt M A ρ x t hres))
  have hno : ∀ i < Nat.find hex,
      clause1Aux_wrap_isHalt (M.states (ccRun M A ρ x i).state) = false := by
    intro i hi
    exact Bool.eq_false_iff.mpr (hs_min i hi)
  have hsim : ∀ j ≤ Nat.find hex,
      ccRun (clause1Aux_wrapProg M) A ρ x j = clause1Aux_wrap_upCfg (ccRun M A ρ x j) := by
    intro j hj
    exact clause1Aux_wrap_sim_run M A ρ x j (fun i hi => hno i (by omega))
  have hhalt' : M.states (ccRun M A ρ x (Nat.find hex)).state = CcAct.accept ∨
      M.states (ccRun M A ρ x (Nat.find hex)).state = CcAct.reject :=
    (clause1Aux_wrap_isHalt_iff _).mp hs_spec
  have hmabs : ccRun M A ρ x t = ccRun M A ρ x (Nat.find hex) :=
    clause1Aux_wrap_run_halt_le M A ρ x (Nat.find hex) t hhalt' hs_le
  have hmt : (ccRun M A ρ x (Nat.find hex)).time ≤ t := by
    rw [← hmabs]
    exact htm
  have hhead : (ccRun M A ρ x (Nat.find hex)).head ≤ Nat.find hex :=
    clause1Aux_head_le M A ρ x (Nat.find hex)
  rcases hhalt' with hacc | hrej
  · have hws : ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex)
        = clause1Aux_wrap_upCfg (ccRun M A ρ x (Nat.find hex)) :=
      hsim (Nat.find hex) (le_refl _)
    have hs1 : ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)
        = ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg (ccRun M A ρ x (Nat.find hex))) := by
      rw [clause1Aux_wrap_run_succ, hws]
    have hi := clause1Aux_wrap_intercept_true M A ρ (ccRun M A ρ x (Nat.find hex)) hacc
    have hcfg1 : (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)).state
        = (⟨q + 14, by omega⟩ : Fin (q + 27)) := by
      rw [hs1]
      exact Fin.ext hi.1
    have hhd1 : (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)).head
        = (ccRun M A ρ x (Nat.find hex)).head := by
      rw [hs1]
      exact hi.2.1
    set h := (ccRun M A ρ x (Nat.find hex)).head with hhdef
    have hg := clause1Aux_wrap_gadW_true M A ρ (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1))
      h hcfg1 hhd1
    obtain ⟨hstate, hfin, htape, htle, haccW⟩ := hg
    have hrun : ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1 + (9 * h + 12))
        = clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ
            (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)) (9 * h + 12) :=
      clause1Aux_wrap_runN_run (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1) (9 * h + 12)
    have hS : Nat.find hex + 1 + (9 * h + 12) ≤ t' := by
      rw [hhdef]
      omega
    have htimeS : (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ
          (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)) (9 * h + 12)).time ≤ t' := by
      have h1 : (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)).time
          = (ccRun M A ρ x (Nat.find hex)).time + 1 := by
        rw [hs1]
        exact hi.2.2.2
      rw [hhdef] at htle ⊢
      omega
    have habs : ccRun (clause1Aux_wrapProg M) A ρ x t'
        = ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1 + (9 * h + 12)) :=
      clause1Aux_wrap_run_halt_le (clause1Aux_wrapProg M) A ρ x
        (Nat.find hex + 1 + (9 * h + 12)) t'
        (by rw [hrun]; exact Or.inl haccW) hS
    refine ⟨?_, ?_, ?_⟩
    · have hh' : (ccRun (clause1Aux_wrapProg M) A ρ x t').head = 1 := by
        rw [habs, hrun]
        exact hfin
      have htt' : (ccRun (clause1Aux_wrapProg M) A ρ x t').tape 0 = true := by
        rw [habs, hrun]
        exact htape
      have hres : ccResult M A ρ x t = some true := by
        simp [ccResult, hmabs, hacc]
      rw [hres]
      exact clause1Aux_output_of_head (clause1Aux_wrapProg M) A ρ x t' true hh' htt'
    · simp only [ccResult]
      rw [habs, hrun]
      simp [haccW]
    · simp only [ccTime]
      rw [habs, hrun]
      exact htimeS
  · have hws : ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex)
        = clause1Aux_wrap_upCfg (ccRun M A ρ x (Nat.find hex)) :=
      hsim (Nat.find hex) (le_refl _)
    have hs1 : ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)
        = ccStep (clause1Aux_wrapProg M) A ρ (clause1Aux_wrap_upCfg (ccRun M A ρ x (Nat.find hex))) := by
      rw [clause1Aux_wrap_run_succ, hws]
    have hi := clause1Aux_wrap_intercept_false M A ρ (ccRun M A ρ x (Nat.find hex)) hrej
    have hcfg1 : (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)).state
        = (⟨q + 1, by omega⟩ : Fin (q + 27)) := by
      rw [hs1]
      exact Fin.ext hi.1
    have hhd1 : (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)).head
        = (ccRun M A ρ x (Nat.find hex)).head := by
      rw [hs1]
      exact hi.2.1
    set h := (ccRun M A ρ x (Nat.find hex)).head with hhdef
    have hg := clause1Aux_wrap_gadW_false M A ρ (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1))
      h hcfg1 hhd1
    obtain ⟨hstate, hfin, htape, htle, haccW⟩ := hg
    have hrun : ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1 + (9 * h + 12))
        = clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ
            (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)) (9 * h + 12) :=
      clause1Aux_wrap_runN_run (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1) (9 * h + 12)
    have hS : Nat.find hex + 1 + (9 * h + 12) ≤ t' := by
      rw [hhdef]
      omega
    have htimeS : (clause1Aux_wrap_runN (clause1Aux_wrapProg M) A ρ
          (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)) (9 * h + 12)).time ≤ t' := by
      have h1 : (ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1)).time
          = (ccRun M A ρ x (Nat.find hex)).time + 1 := by
        rw [hs1]
        exact hi.2.2.2
      rw [hhdef] at htle ⊢
      omega
    have habs : ccRun (clause1Aux_wrapProg M) A ρ x t'
        = ccRun (clause1Aux_wrapProg M) A ρ x (Nat.find hex + 1 + (9 * h + 12)) :=
      clause1Aux_wrap_run_halt_le (clause1Aux_wrapProg M) A ρ x
        (Nat.find hex + 1 + (9 * h + 12)) t'
        (by rw [hrun]; exact Or.inl haccW) hS
    refine ⟨?_, ?_, ?_⟩
    · have hh' : (ccRun (clause1Aux_wrapProg M) A ρ x t').head = 1 := by
        rw [habs, hrun]
        exact hfin
      have htt' : (ccRun (clause1Aux_wrapProg M) A ρ x t').tape 0 = false := by
        rw [habs, hrun]
        exact htape
      have hres : ccResult M A ρ x t = some false := by
        simp [ccResult, hmabs, hrej]
      rw [hres]
      exact clause1Aux_output_of_head (clause1Aux_wrapProg M) A ρ x t' false hh' htt'
    · simp only [ccResult]
      rw [habs, hrun]
      simp [haccW]
    · simp only [ccTime]
      rw [habs, hrun]
      exact htimeS

/-- Restricts a finite bit string to its initial segment of the specified shorter length. -/
private def clause1Aux_wrap_cut {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) : Fin T0 → Bool :=
  fun i => ω ⟨(i : ℕ), lt_of_lt_of_le i.isLt h⟩

/-- Extracts the suffix remaining after the specified initial segment of a finite bit string. -/
private def clause1Aux_wrap_tail {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) : Fin (T1 - T0) → Bool :=
  fun j => ω ⟨T0 + (j : ℕ), by omega⟩

/-- Concatenates a finite bit prefix with a suffix to obtain a bit string of the specified total
length. -/
private def clause1Aux_wrap_pad {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool)
    (u : Fin (T1 - T0) → Bool) : Fin T1 → Bool :=
  fun j => if hj : (j : ℕ) < T0 then b ⟨(j : ℕ), hj⟩ else u ⟨(j : ℕ) - T0, by omega⟩

/-- Concatenating the extracted prefix and suffix of a finite bit string recovers the original
string. -/
private lemma clause1Aux_wrap_pad_cut_tail {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) :
    clause1Aux_wrap_pad h (clause1Aux_wrap_cut h ω) (clause1Aux_wrap_tail h ω) = ω := by
  funext j
  have hj1 : (j : ℕ) < T1 := j.isLt
  by_cases hj : (j : ℕ) < T0
  · rw [clause1Aux_wrap_pad, dif_pos hj]
    show ω ⟨(j : ℕ), lt_of_lt_of_le hj h⟩ = ω j
    exact congrArg ω (Fin.ext rfl)
  · rw [clause1Aux_wrap_pad, dif_neg hj]
    have hval : T0 + ((j : ℕ) - T0) < T1 := by omega
    have hval2 : T0 + ((j : ℕ) - T0) = (j : ℕ) := by omega
    show ω (⟨T0 + ((j : ℕ) - T0), hval⟩ : Fin T1) = ω j
    exact congrArg ω (Fin.ext hval2)

/-- Extracting the prefix of a concatenated finite bit string recovers its given prefix. -/
private lemma clause1Aux_wrap_cut_pad {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool)
    (u : Fin (T1 - T0) → Bool) : clause1Aux_wrap_cut h (clause1Aux_wrap_pad h b u) = b := by
  funext i
  have hi : (i : ℕ) < T0 := i.isLt
  have hi1 : (i : ℕ) < T1 := lt_of_lt_of_le hi h
  have hd2 : clause1Aux_wrap_pad h b u ⟨(i : ℕ), hi1⟩
      = if hx : (i : ℕ) < T0 then b ⟨(i : ℕ), hx⟩ else u ⟨(i : ℕ) - T0, by omega⟩ := rfl
  show clause1Aux_wrap_pad h b u ⟨(i : ℕ), hi1⟩ = b i
  rw [hd2, dif_pos hi]

/-- Extracting the suffix of a concatenated finite bit string recovers its given suffix. -/
private lemma clause1Aux_wrap_tail_pad {T0 T1 : ℕ} (h : T0 ≤ T1) (b : Fin T0 → Bool)
    (u : Fin (T1 - T0) → Bool) : clause1Aux_wrap_tail h (clause1Aux_wrap_pad h b u) = u := by
  funext j
  have hj1 : (j : ℕ) < (T1 - T0) := j.isLt
  have hT : T0 + (j : ℕ) < T1 := by omega
  have hm : T0 + (j : ℕ) - T0 < T1 - T0 := by omega
  have hval2 : T0 + (j : ℕ) - T0 = (j : ℕ) := by omega
  have hd2 : clause1Aux_wrap_pad h b u ⟨T0 + (j : ℕ), hT⟩
      = if hx : (T0 + (j : ℕ)) < T0 then b ⟨T0 + (j : ℕ), hx⟩
        else u ⟨T0 + (j : ℕ) - T0, hm⟩ := rfl
  show clause1Aux_wrap_pad h b u ⟨T0 + (j : ℕ), hT⟩ = u j
  rw [hd2, dif_neg (by omega)]
  exact congrArg u (Fin.ext hval2)

/-- The number of longer bit strings satisfying a condition on their prefix is the number of
valid prefixes times `2 ^ (T1 - T0)`. -/
private lemma clause1Aux_wrap_card_fiber {T0 T1 : ℕ} (h : T0 ≤ T1)
    (P : (Fin T0 → Bool) → Prop) [DecidablePred P]
    [DecidablePred (fun ω : Fin T1 → Bool => P (clause1Aux_wrap_cut h ω))] :
    (Finset.univ.filter (fun ω : Fin T1 → Bool => P (clause1Aux_wrap_cut h ω))).card =
      (Finset.univ.filter (fun b : Fin T0 → Bool => P b)).card * 2 ^ (T1 - T0) := by
  classical
  have h2 : (2 : ℕ) ^ (T1 - T0) = (Finset.univ : Finset (Fin (T1 - T0) → Bool)).card := by
    rw [Finset.card_univ, clause1Aux_card_fin_bool]
  rw [h2, ← Finset.card_product]
  refine Finset.card_nbij' (i := fun ω => (clause1Aux_wrap_cut h ω, clause1Aux_wrap_tail h ω))
    (j := fun p => clause1Aux_wrap_pad h p.1 p.2) ?_ ?_ ?_ ?_
  · intro a ha
    apply Finset.mem_coe.mpr
    rw [Finset.mem_product]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
    exact (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
  · intro p hp
    have hp1 := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    have hp2 := Finset.mem_filter.mp hp1.1
    apply Finset.mem_coe.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [clause1Aux_wrap_cut_pad]
    exact hp2.2
  · intro a _
    exact clause1Aux_wrap_pad_cut_tail h a
  · intro p _
    obtain ⟨b, u⟩ := p
    exact Prod.ext (clause1Aux_wrap_cut_pad h b u) (clause1Aux_wrap_tail_pad h b u)

/-- A finite coin string and its prefix induce equal infinite coin-stream values at indices
within the prefix. -/
private lemma clause1Aux_wrap_coinString_cut {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool)
    (i : ℕ) (hi : i < T0) : ccCoinString ω i = ccCoinString (clause1Aux_wrap_cut h ω) i := by
  simp [ccCoinString, clause1Aux_wrap_cut, hi, lt_of_lt_of_le hi h]

/-- A run for `T0` steps is unchanged when a length-`T1` finite coin string is replaced by its
length-`T0` prefix. -/
private lemma clause1Aux_wrap_run_cut {q : ℕ} (M : CcProgram q) (A : List Bool → Bool)
    (x : List Bool) {T0 T1 : ℕ} (h : T0 ≤ T1) (ω : Fin T1 → Bool) :
    ccRun M A (ccCoinString ω) x T0 = ccRun M A (ccCoinString (clause1Aux_wrap_cut h ω)) x T0 := by
  apply clause1Aux_wrap_coinPrefix
  intro i hi
  exact clause1Aux_wrap_coinString_cut h ω i hi

/-- The polynomial budget with coefficient `10 * c + 13` bounds ten times the original budget
plus thirteen. -/
private lemma clause1Aux_wrap_budget_gap (c m : ℕ) :
    10 * (c * m + c) + 13 ≤ (10 * c + 13) * m + (10 * c + 13) := by
  have h1 : 10 * (c * m + c) + 13 + 13 * m = (10 * c + 13) * m + (10 * c + 13) := by ring
  have h2 : 10 * (c * m + c) + 13 ≤ 10 * (c * m + c) + 13 + 13 * m := Nat.le_add_right _ _
  rw [← h1]
  exact h2

/-- Replacing coefficient `c` by `10 * c + 13` increases the polynomial budget. -/
private lemma clause1Aux_wrap_budget_mono (c m : ℕ) :
    c * m + c ≤ (10 * c + 13) * m + (10 * c + 13) := by
  have h1 : c * m + c + (9 * (c * m) + 13 * m + 9 * c + 13)
      = (10 * c + 13) * m + (10 * c + 13) := by ring
  have h2 : c * m + c ≤ c * m + c + (9 * (c * m) + 13 * m + 9 * c + 13) :=
    Nat.le_add_right _ _
  rw [← h1]
  exact h2

/-- A polynomial-time bounded-error decision program has a polynomial-time output wrapper with
an NP oracle language, a larger budget, and exact true- and false-output counts equal to the
original branch counts times the coin-padding factor. -/
theorem clause1Aux_hwrap (L : List Bool → Prop) :
    ∀ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k →
      (∀ x : List Bool,
        (L x → 3 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
            ≥ 2 * 2 ^ (c * x.length ^ k + c)) ∧
        (¬L x → 3 * ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
            ≤ 2 ^ (c * x.length ^ k + c))) →
      ∃ (q' c' k' : ℕ) (W : CcProgram q') (B : List Bool → Prop),
        CcInNPSet B ∧ CcPolyTime W c' k' ∧
        (∀ x : List Bool, c * x.length ^ k + c ≤ c' * x.length ^ k' + c') ∧
        (∀ x : List Bool,
          ccExactOutputCount W (ccOracleOf B) x (c' * x.length ^ k' + c') [true]
            = ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c)
                * 2 ^ ((c' * x.length ^ k' + c') - (c * x.length ^ k + c)) ∧
          ccExactOutputCount W (ccOracleOf B) x (c' * x.length ^ k' + c') [false]
            = (2 ^ (c * x.length ^ k + c)
                - ccAcceptCount M ccZeroOracle x (c * x.length ^ k + c))
                * 2 ^ ((c' * x.length ^ k' + c') - (c * x.length ^ k + c))) := by
  intro q c k M hpoly _hbnd
  refine ⟨q + 26, 10 * c + 13, k, clause1Aux_wrapProg M, fun _ => False,
    clause1Aux_empty_inNP, ?_, ?_, ?_⟩
  · intro A ρ x
    have hg := clause1Aux_wrap_budget_gap c (x.length ^ k)
    have hm := clause1Aux_wrap_main M hpoly A ρ x
      (c * x.length ^ k + c) ((10 * c + 13) * x.length ^ k + (10 * c + 13)) rfl hg
    have hne : ccResult (clause1Aux_wrapProg M) A ρ x
        ((10 * c + 13) * x.length ^ k + (10 * c + 13)) ≠ none := by
      rw [hm.2.1]
      exact Option.some_ne_none true
    exact ⟨hne, hm.2.2⟩
  · intro x
    exact clause1Aux_wrap_budget_mono c (x.length ^ k)
  · intro x
    rw [clause1Aux_wrap_oracle_empty]
    set t := c * x.length ^ k + c with ht0
    set t' := (10 * c + 13) * x.length ^ k + (10 * c + 13) with ht0'
    have hle : t ≤ t' := by
      rw [ht0, ht0']
      exact clause1Aux_wrap_budget_mono c (x.length ^ k)
    have hgap : 10 * t + 13 ≤ t' := by
      rw [ht0, ht0']
      exact clause1Aux_wrap_budget_gap c (x.length ^ k)
    have hout : ∀ ω : Fin t' → Bool,
        ccOutput (clause1Aux_wrapProg M) ccZeroOracle (ccCoinString ω) x t'
          = (if ccResult M ccZeroOracle (ccCoinString ω) x t = some true
              then [true] else [false]) := by
      intro ω
      exact (clause1Aux_wrap_main M hpoly ccZeroOracle (ccCoinString ω) x t t' ht0 hgap).1
    have hcut : ∀ ω : Fin t' → Bool,
        ccResult M ccZeroOracle (ccCoinString ω) x t
          = ccResult M ccZeroOracle (ccCoinString (clause1Aux_wrap_cut hle ω)) x t := by
      intro ω
      have hr := clause1Aux_wrap_run_cut M ccZeroOracle x hle ω
      simp [ccResult, hr]
    refine ⟨?_, ?_⟩
    · show (Finset.univ.filter (fun ω : Fin t' → Bool =>
        ccOutput (clause1Aux_wrapProg M) ccZeroOracle (ccCoinString ω) x t' = [true])).card = _
      have hfeq : (Finset.univ.filter (fun ω : Fin t' → Bool =>
          ccOutput (clause1Aux_wrapProg M) ccZeroOracle (ccCoinString ω) x t' = [true]))
          = Finset.univ.filter (fun ω : Fin t' → Bool =>
            ccResult M ccZeroOracle (ccCoinString (clause1Aux_wrap_cut hle ω)) x t = some true) := by
        refine Finset.filter_congr (fun ω _ => ?_)
        rw [hout ω, hcut ω]
        by_cases hc : ccResult M ccZeroOracle
            (ccCoinString (clause1Aux_wrap_cut hle ω)) x t = some true
        · rw [if_pos hc]
          simp [hc]
        · rw [if_neg hc]
          simp [hc]
      rw [hfeq]
      exact clause1Aux_wrap_card_fiber (T0 := t) (T1 := t') hle
        (fun b : Fin t → Bool => ccResult M ccZeroOracle (ccCoinString b) x t = some true)
    · show (Finset.univ.filter (fun ω : Fin t' → Bool =>
        ccOutput (clause1Aux_wrapProg M) ccZeroOracle (ccCoinString ω) x t' = [false])).card = _
      have hfeq : (Finset.univ.filter (fun ω : Fin t' → Bool =>
          ccOutput (clause1Aux_wrapProg M) ccZeroOracle (ccCoinString ω) x t' = [false]))
          = Finset.univ.filter (fun ω : Fin t' → Bool =>
            ¬(ccResult M ccZeroOracle (ccCoinString (clause1Aux_wrap_cut hle ω)) x t = some true)) := by
        refine Finset.filter_congr (fun ω _ => ?_)
        rw [hout ω, hcut ω]
        by_cases hc : ccResult M ccZeroOracle
            (ccCoinString (clause1Aux_wrap_cut hle ω)) x t = some true
        · rw [if_pos hc]
          simp [hc]
        · rw [if_neg hc]
          simp [hc]
      rw [hfeq]
      have hcomp : (Finset.univ.filter (fun b : Fin t → Bool =>
          ¬(ccResult M ccZeroOracle (ccCoinString b) x t = some true))).card
          = 2 ^ t - ccAcceptCount M ccZeroOracle x t := by
        have h1 := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin t → Bool)))
          (fun ω : Fin t → Bool => ccResult M ccZeroOracle (ccCoinString ω) x t = some true)
        rw [Finset.card_univ, clause1Aux_card_fin_bool] at h1
        have h2 : (Finset.univ.filter (fun ω : Fin t → Bool =>
            ccResult M ccZeroOracle (ccCoinString ω) x t = some true)).card
            = ccAcceptCount M ccZeroOracle x t := rfl
        omega
      have hfib := clause1Aux_wrap_card_fiber (T0 := t) (T1 := t') hle
        (fun b : Fin t → Bool => ¬(ccResult M ccZeroOracle (ccCoinString b) x t = some true))
      refine hfib.trans ?_
      rw [hcomp]

/-- Every `InBPP` language has its singleton decision-bit function in `InFBPPNP` for the
counting bit-machine definitions [KitaevShenVyalyi2002]. -/
theorem clause1Aux_clause6 : ∀ L : List Bool → Prop, InBPP L →
    InFBPPNP (fun x => if L x then [true] else [false]) := by
  intro L hin
  exact clause1Aux_clause6_of_wrap L hin (clause1Aux_hwrap L)

end Qatlib.Concepts.CountingClasses.ClassTransport
