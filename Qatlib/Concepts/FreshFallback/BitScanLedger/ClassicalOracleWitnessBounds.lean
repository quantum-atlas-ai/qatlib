/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshFallback.BitScanLedger.ClassicalOracleWitnessBoundsDefs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Qatlib.Concepts.QmaCompleteness.WitnessSampler.Theorem62CumulativeSamplerSepa

/-!
# Classical oracle witness bounds

This module proves resource bounds for sampler prefixes, phase-oracle padding, and bounded
searches for unused binary strings. It also establishes weighted sampling estimates, protected
diagonal lengths, and tensor-state occupation inequalities in the finite oracle-circuit setting
of [KitaevShenVyalyi2002].

`classifier_strong_sampling_lower` transfers classifier acceptance and rejection hypotheses to a
lower bound for cumulative sampling. The tensor lemmas express normalization, permutation
symmetry, and occupation-event bounds using the state and measurement conventions of
[Watrous2018].

## Main statements

* `paddedSamplerPrefix_resources`: gives exact padded query counts and a word-length bound.
* `classifier_strong_sampling_lower`: derives a strong-average lower bound for cumulative
  sampling success.
* `occupied_born_le_moment`: bounds an occupation event by a Born-weighted occupation moment.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.FreshFallback.BitScanLedger

open Qatlib
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025
open scoped BigOperators

/-- The number of sampler prefixes equals the number of `S` queries in the circuit. -/
theorem samplerPrefixes_length {I : Type} (D : Matrix I I ℂ) (C : TOCircuit I) :
    (samplerPrefixes D C).length = TOQueryCountS C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp [samplerPrefixes, TOQueryCountS, ih, Nat.add_comm]

/-- Running the extracted sampler prefixes produces the list of `S`-query states with earlier
`S` queries replaced by `D`. -/
theorem samplerPrefixes_run {I : Type} [Fintype I] [DecidableEq I]
    (D S U : Matrix I I ℂ) (C : TOCircuit I) (ψ : QState I) :
    ((samplerPrefixes D C).map (fun P => TORun S U P ψ)) = sQueryStates D U C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp [samplerPrefixes, sQueryStates, List.map_map, Function.comp_def, TORun, ih]

/-- Each sampler prefix has no `S` queries, no more `U` queries than the original circuit, and
no greater length. -/
theorem samplerPrefixes_resources {I : Type} (D : Matrix I I ℂ) (C P : TOCircuit I)
    (hP : P ∈ samplerPrefixes D C) :
    TOQueryCountS P = 0 ∧ TOQueryCountU P ≤ TOQueryCountU C ∧ P.length ≤ C.length := by
  induction C generalizing P with
  | nil => simp [samplerPrefixes] at hP
  | cons s C ih =>
    cases s with
    | gate G =>
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
      obtain ⟨hS, hU, hlen⟩ := ih Q hQ
      exact ⟨hS, hU, Nat.succ_le_succ hlen⟩
    | queryU =>
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
      obtain ⟨hS, hU, hlen⟩ := ih Q hQ
      exact ⟨hS, Nat.add_le_add_right hU 1, Nat.succ_le_succ hlen⟩
    | queryS =>
      simp only [samplerPrefixes, List.mem_cons] at hP
      rcases hP with rfl | hP
      · exact ⟨rfl, Nat.zero_le _, Nat.zero_le _⟩
      · obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
        obtain ⟨hS, hU, hlen⟩ := ih Q hQ
        exact ⟨hS, hU, Nat.succ_le_succ hlen⟩

/-- The binary alphabet list on `n` bits has length `2^n`. -/
theorem binaryAlphabet_length (n : ℕ) : (binaryAlphabet n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binaryAlphabet, ih, pow_succ, Nat.mul_two]

/-- Every `n`-bit register configuration occurs in the binary alphabet list. -/
theorem mem_binaryAlphabet (n : ℕ) (x : Reg n) : x ∈ binaryAlphabet n := by
  induction n with
  | zero =>
    have hx : x = (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    simp [binaryAlphabet, hx]
  | succ n ih =>
    have hx : Fin.cons (x 0) (fun i => x i.succ) = x := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    have hm := ih (fun i => x i.succ)
    cases hb : x 0
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨_, hm, by simpa [hb] using! hx⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨_, hm, by simpa [hb] using! hx⟩

/-- The full fresh-string search returns `none` exactly when every `n`-bit string occurs in the
history. -/
theorem firstFresh_eq_none_iff (n : ℕ) (hist : List (Reg n)) :
    firstFresh n hist = none ↔ ∀ x : Reg n, x ∈ hist := by
  simp only [firstFresh, List.find?_eq_none, Bool.not_eq_true, decide_eq_false_iff_not,
    not_not]
  exact ⟨fun h x => h x (mem_binaryAlphabet n x), fun h x _ => h x⟩

/-- Every string returned by the sampler fallback is absent from the history. -/
theorem samplerFallback_fresh (n : ℕ) (hist : List (Reg n)) (x y : Reg n)
    (h : samplerFallback n hist x = some y) : y ∉ hist := by
  unfold samplerFallback at h
  split at h
  · exact of_decide_eq_true (List.find?_some (p := fun z => decide (z ∉ hist)) h)
  · cases h
    assumption

/-- The sampler fallback returns its input string when that string is absent from the history. -/
theorem samplerFallback_direct (n : ℕ) (hist : List (Reg n)) (x : Reg n)
    (hx : x ∉ hist) : samplerFallback n hist x = some x := by
  simp [samplerFallback, hx]

/-- If the prefix has at most `t` `U` queries, padding preserves its `S` query count, raises its
`U` query count to `t`, and adds exactly `t - TOQueryCountU P` steps. -/
theorem paddedPrefix_resources {I : Type} (t : ℕ) (P : TOCircuit I)
    (hP : TOQueryCountU P ≤ t) :
    TOQueryCountS (paddedPrefix t P) = TOQueryCountS P ∧
    TOQueryCountU (paddedPrefix t P) = t ∧
    (paddedPrefix t P).length = P.length + (t - TOQueryCountU P) := by
  have hS : ∀ (A B : TOCircuit I), TOQueryCountS (A ++ B) = TOQueryCountS A + TOQueryCountS B := by
    intro A B
    induction A with
    | nil => simp [TOQueryCountS]
    | cons s A ih => cases s <;> simp [TOQueryCountS, ih, Nat.add_comm, Nat.add_left_comm]
  have hU : ∀ (A B : TOCircuit I), TOQueryCountU (A ++ B) = TOQueryCountU A + TOQueryCountU B := by
    intro A B
    induction A with
    | nil => simp [TOQueryCountU]
    | cons s A ih => cases s <;> simp [TOQueryCountU, ih, Nat.add_comm, Nat.add_left_comm]
  have hrep (k : ℕ) :
      TOQueryCountS (List.replicate k (TOStep.queryU : TOStep I)) = 0 ∧
      TOQueryCountU (List.replicate k (TOStep.queryU : TOStep I)) = k := by
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih => simp [List.replicate_succ, TOQueryCountS, TOQueryCountU, ih.1, ih.2]
  simp only [paddedPrefix, hS, hU, (hrep _).1, (hrep _).2, Nat.add_zero,
    Nat.add_sub_of_le hP, List.length_append, List.length_replicate, and_self]

/-- The value component of the counted binary-prefix generator is the first `k` entries of the
binary alphabet. -/
theorem binaryPrefixCounted_value (n k : ℕ) :
    (binaryPrefixCounted n k).1 = (binaryAlphabet n).take k := by
  induction n generalizing k with
  | zero => cases k <;> simp [binaryPrefixCounted, binaryAlphabet]
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [binaryPrefixCounted, ih, binaryAlphabet, List.take_append,
        List.length_map, binaryAlphabet_length, ← List.map_take]
      congr 1
      congr 1
      simpa only [binaryAlphabet_length] using!
        (List.take_eq_take_min (l := binaryAlphabet n) (i := k + 1)).symm

/-- The counted binary-prefix generator uses at most `(2 * n + 1) * k + 1` recursive visits. -/
theorem binaryPrefixCounted_visits (n k : ℕ) :
    (binaryPrefixCounted n k).2 ≤ (2 * n + 1) * k + 1 := by
  induction n generalizing k with
  | zero => cases k <;> simp [binaryPrefixCounted]
  | succ n ih =>
    cases k with
    | zero => simp [binaryPrefixCounted]
    | succ k =>
      have hlo := ih (min (k + 1) (2 ^ n))
      have hhi := ih ((k + 1) - 2 ^ n)
      have hsum : min (k + 1) (2 ^ n) + ((k + 1) - 2 ^ n) = k + 1 := by omega
      simp only [binaryPrefixCounted]
      calc
        _ ≤ 1 + ((2*n+1) * min (k+1) (2^n) + 1) +
            ((2*n+1) * ((k+1)-2^n) + 1) := Nat.add_le_add (Nat.add_le_add_left hlo 1) hhi
        _ = (2*n+1) * (min (k+1) (2^n) + ((k+1)-2^n)) + 3 := by ring
        _ = (2*n+1) * (k+1) + 3 := by rw [hsum]
        _ ≤ (2*(n+1)+1) * (k+1) + 1 := by nlinarith

/-- The binary alphabet list has no repeated entries. -/
theorem binaryAlphabet_nodup (n : ℕ) : (binaryAlphabet n).Nodup := by
  induction n with
  | zero => simp [binaryAlphabet]
  | succ n ih =>
    rw [binaryAlphabet, List.nodup_append]
    refine ⟨ih.map (Fin.cons_right_injective (α := fun _ : Fin (n+1) => Bool) false),
      ih.map (Fin.cons_right_injective (α := fun _ : Fin (n+1) => Bool) true), ?_⟩
    intro a ha b hb hab
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    have h := congrFun hab 0
    simp at h

/-- The bounded fresh-string search returns `none` exactly when the history contains every
`n`-bit string. -/
theorem firstFreshBounded_eq_none_iff (n : ℕ) (hist : List (Reg n)) :
    firstFreshBounded n hist = none ↔ ∀ x : Reg n, x ∈ hist := by
  simp only [firstFreshBounded, binaryPrefixCounted_value, List.find?_eq_none,
    Bool.not_eq_true, decide_eq_false_iff_not, not_not]
  constructor
  · intro h x
    by_cases hlen : (binaryAlphabet n).length ≤ hist.length + 1
    · exact h x (by simpa [List.take_of_length_le hlen] using! mem_binaryAlphabet n x)
    · have hsub : (binaryAlphabet n).take (hist.length + 1) ⊆ hist := h
      have hnd : ((binaryAlphabet n).take (hist.length + 1)).Nodup :=
        (binaryAlphabet_nodup n).take
      have hcard := (hnd.subperm hsub).length_le
      rw [List.length_take, min_eq_left (by omega)] at hcard
      omega
  · intro h x _
    exact h x

/-- The bounded fresh-string search agrees with the full binary-alphabet search. -/
theorem firstFreshBounded_eq_firstFresh (n : ℕ) (hist : List (Reg n)) :
    firstFreshBounded n hist = firstFresh n hist := by
  cases h : firstFreshBounded n hist with
  | none =>
    exact ((firstFresh_eq_none_iff n hist).mpr
      ((firstFreshBounded_eq_none_iff n hist).mp h)).symm
  | some x =>
    have ht : ((binaryAlphabet n).take (hist.length + 1)).find?
        (fun z => decide (z ∉ hist)) = some x := by
      simpa only [firstFreshBounded, binaryPrefixCounted_value] using! h
    exact ((List.take_prefix (hist.length + 1) (binaryAlphabet n)).find?_eq_some ht).symm

/-- Appending copies of a phase oracle at the end of a prefix preserves every
computational-basis event probability. -/
theorem paddedPrefix_phase_readout {I : Type} [Fintype I] [DecidableEq I]
    (f : I → Bool) (S : Matrix I I ℂ) (P : TOCircuit I) (t : ℕ)
    (ψ : QState I) (E : Finset I) :
    MeasureProb (TORun S (PhaseOracle f) (paddedPrefix t P) ψ) E =
      MeasureProb (TORun S (PhaseOracle f) P ψ) E := by
  have happ : ∀ (A B : TOCircuit I) (φ : QState I),
      TORun S (PhaseOracle f) (A ++ B) φ =
      TORun S (PhaseOracle f) B (TORun S (PhaseOracle f) A φ) := by
    intro A B φ
    induction A generalizing φ with
    | nil => rfl
    | cons s A ih => cases s <;> simp only [List.cons_append, TORun, ih]
  have hrep (k : ℕ) (φ : QState I) :
      MeasureProb (TORun S (PhaseOracle f) (List.replicate k TOStep.queryU) φ) E =
        MeasureProb φ E := by
    induction k generalizing φ with
    | zero => rfl
    | succ k ih =>
      simp only [List.replicate_succ, TORun, ih]
      unfold MeasureProb
      apply Finset.sum_congr rfl
      intro i _
      unfold BornProb
      rw [applyGate_phaseOracle]
      split_ifs <;> simp
  exact (congrArg (fun φ => MeasureProb φ E) (happ P _ ψ)).trans (hrep _ _)

/-- The `U` forrelation phase oracle is the diagonal phase oracle for the predicate combining
its control bit with `U`. -/
theorem forrPhaseOracleU_diagonal (n : ℕ) (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    forrPhaseOracleU n U W = PhaseOracle (fun p : ForrSpace n W => p.2.1.2 && U p.2.1.1) := by
  simp only [forrPhaseOracleU, TensorGate, PhaseOracle, ← Matrix.diagonal_one,
    Matrix.diagonal_kronecker_diagonal, one_mul, mul_one]

/-- A sampler prefix padded to a circuit-wide `U` query bound has zero `S` queries, exactly `t`
`U` queries, and length at most `C.length + t`. -/
theorem paddedSamplerPrefix_resources {I : Type} (D : Matrix I I ℂ)
    (C P : TOCircuit I) (t : ℕ) (hP : P ∈ samplerPrefixes D C) (hC : TOQueryCountU C ≤ t) :
    TOQueryCountS (paddedPrefix t P) = 0 ∧
    TOQueryCountU (paddedPrefix t P) = t ∧
    (paddedPrefix t P).length ≤ C.length + t := by
  obtain ⟨hS, hU, hlen⟩ := samplerPrefixes_resources D C P hP
  obtain ⟨hSp, hUp, hlenp⟩ := paddedPrefix_resources t P (hU.trans hC)
  refine ⟨hSp.trans hS, hUp, ?_⟩
  rw [hlenp]
  omega

/-- Flattening words with zero `S` queries, exactly `t` `U` queries, and length at most `L`
yields the corresponding counts and length bound multiplied by the number of words. -/
theorem cumulativeWords_resources {I : Type} (words : List (TOCircuit I)) (t L : ℕ)
    (hwords : ∀ P ∈ words, TOQueryCountS P = 0 ∧ TOQueryCountU P = t ∧ P.length ≤ L) :
    TOQueryCountS words.flatten = 0 ∧
    TOQueryCountU words.flatten = words.length * t ∧
    words.flatten.length ≤ words.length * L := by
  have hS : ∀ (A B : TOCircuit I), TOQueryCountS (A ++ B) = TOQueryCountS A + TOQueryCountS B := by
    intro A B
    induction A with
    | nil => simp [TOQueryCountS]
    | cons s A ih => cases s <;> simp [TOQueryCountS, ih, Nat.add_comm, Nat.add_left_comm]
  have hU : ∀ (A B : TOCircuit I), TOQueryCountU (A ++ B) = TOQueryCountU A + TOQueryCountU B := by
    intro A B
    induction A with
    | nil => simp [TOQueryCountU]
    | cons s A ih => cases s <;> simp [TOQueryCountU, ih, Nat.add_comm, Nat.add_left_comm]
  induction words with
  | nil => simp [TOQueryCountS, TOQueryCountU]
  | cons P words ih =>
    obtain ⟨hPS, hPU, hPL⟩ := hwords P List.mem_cons_self
    obtain ⟨hiS, hiU, hiL⟩ := ih (fun Q hQ => hwords Q (List.mem_cons_of_mem P hQ))
    simp only [List.flatten_cons, hS, hU, hPS, hPU, hiS, hiU, Nat.zero_add,
      List.length_cons, Nat.succ_mul, List.length_append]
    exact ⟨trivial, Nat.add_comm _ _, (add_le_add hPL hiL).trans_eq (Nat.add_comm _ _)⟩

/-- For every fixed sample tuple, the strong Bernoulli weights sum to one over all Boolean
oracles. -/
theorem strongWeight_sum (n ℓ : ℕ) (κ : ℝ) (s : Fin ℓ → Reg n) :
    ∑ U : Reg n → Bool, strongBernoulliWeight n ℓ κ s U = 1 := by
  classical
  let factor : Reg n → Bool → ℝ := fun y b =>
    if y = ZeroStr n then (if b then 0 else 1)
    else if b then 1 - Real.exp (-κ * gammaOfMultiset n ℓ s y) / 2
      else Real.exp (-κ * gammaOfMultiset n ℓ s y) / 2
  have heq (U : Reg n → Bool) : strongBernoulliWeight n ℓ κ s U = ∏ y, factor y (U y) := by
    unfold strongBernoulliWeight
    split
    · rename_i hU
      exact (Finset.prod_eq_zero (Finset.mem_univ (ZeroStr n)) (by simp [factor, hU])).symm
    · rename_i hU
      apply Finset.prod_congr rfl
      intro y _
      by_cases hy : y = ZeroStr n
      · subst y; simp [factor, hU]
      · simp only [factor, if_neg hy]
  simp_rw [heq]
  have hsum : (∑ U : Reg n → Bool, ∏ y, factor y (U y)) =
      ∏ y : Reg n, ∑ b : Bool, factor y b := by
    simpa using! (Finset.prod_univ_sum
      (t := fun _ : Reg n => (Finset.univ : Finset Bool)) (f := factor)).symm
  rw [hsum]
  have hf (y : Reg n) : ∑ b : Bool, factor y b = 1 := by
    by_cases hy : y = ZeroStr n <;> simp [factor, hy]
  simp only [hf, Finset.prod_const_one]

/-- The strong weighted average of the constant function one is one. -/
theorem strongAverage_one (n ℓ : ℕ) (κ : ℝ) : strongAverage n ℓ κ (fun _ _ => 1) = 1 := by
  simp [strongAverage, strongWeight_sum]

/-- For nonnegative `κ`, the strong weighted average preserves pointwise inequalities. -/
theorem strongAverage_mono (n ℓ : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (f g : (Fin ℓ → Reg n) → (Reg n → Bool) → ℝ) (hfg : ∀ s U, f s U ≤ g s U) :
    strongAverage n ℓ κ f ≤ strongAverage n ℓ κ g := by
  unfold strongAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun U _ =>
    mul_le_mul_of_nonneg_left (hfg s U) (strongBernoulliWeight_nonneg n ℓ κ hκ s U)

/-- For nonnegative `κ`, a nonnegative function bounded below by `L` on strong yes instances has
strong average at least `(1 - strongFailProb) * L`. -/
theorem strongAverage_lower_of_good (n ℓ v : ℕ) (κ t1 t2 L : ℝ) (hκ : 0 ≤ κ)
    (f : (Fin ℓ → Reg n) → (Reg n → Bool) → ℝ)
    (hf : ∀ s U, 0 ≤ f s U)
    (hgood : ∀ s U, IsStrongYes t1 t2 v (multisetInd s) U → L ≤ f s U) :
    (1 - strongFailProb n ℓ κ t1 t2 v) * L ≤ strongAverage n ℓ κ f := by
  classical
  let good : (Fin ℓ → Reg n) → (Reg n → Bool) → ℝ :=
    fun s U => if IsStrongYes t1 t2 v (multisetInd s) U then L else 0
  have hmono := strongAverage_mono n ℓ κ hκ good f (by
    intro s U
    dsimp [good]
    split
    · exact hgood s U ‹_›
    · exact hf s U)
  have hpartition : strongAverage n ℓ κ good + strongFailProb n ℓ κ t1 t2 v * L = L := by
    calc
      _ = strongAverage n ℓ κ (fun _ _ => 1) * L := by
        unfold strongAverage strongFailProb
        simp only [mul_assoc, Finset.sum_mul]
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro U _
        dsimp [good]
        split_ifs <;> ring
      _ = L := by rw [strongAverage_one, one_mul]
  nlinarith only [hmono, hpartition]

/-- A query to the packed bit oracle uses the tag bit to select `S` or `U` and XORs the selected
oracle value into the answer bit. -/
theorem packedOracle_query (S U : ∀ n, Reg n → Bool) (n : ℕ) (tag : Bool)
    (x : Reg n) (b : Bool) :
    ApplyGate (BitOracleOn (packedOracle S U (n+1))) (Ket (Fin.cons tag x, b)) =
      Ket (Fin.cons tag x, b ^^ (if tag then U n x else S n x)) := by
  rw [applyGate_bitOracleOn_ket]
  rfl

/-- The false-tag and true-tag restrictions of the packed oracle recover `S` and `U`,
respectively. -/
theorem packedOracle_restrictions (S U : ∀ n, Reg n → Bool) (n : ℕ) (x : Reg n) :
    packedOracle S U (n+1) (Fin.cons false x) = S n x ∧
    packedOracle S U (n+1) (Fin.cons true x) = U n x := ⟨rfl, rfl⟩

/-- The diagonal length sequence is strictly increasing. -/
theorem diagonalLengths_strictMono (threshold : ℕ → ℕ) (window : ℕ → ℕ → ℕ) :
    StrictMono (diagonalLengths threshold window) := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [diagonalLengths]
  omega

/-- Every diagonal length exceeds its threshold, and each later length exceeds the query window
associated with each earlier stage. -/
theorem diagonalLengths_protection (threshold : ℕ → ℕ) (window : ℕ → ℕ → ℕ) :
    (∀ k, threshold k < diagonalLengths threshold window k) ∧
    (∀ k j, k < j → window k (diagonalLengths threshold window k) <
      diagonalLengths threshold window j) := by
  constructor
  · intro k
    cases k with
    | zero => exact Nat.lt_succ_self _
    | succ k =>
      simp only [diagonalLengths]
      omega
  · intro k j hkj
    have hnext : window k (diagonalLengths threshold window k) <
        diagonalLengths threshold window (k+1) := by
      simp only [diagonalLengths]
      omega
    exact hnext.trans_le ((diagonalLengths_strictMono threshold window).monotone (by omega))

/-- The cumulative sampler success quantity is nonnegative. -/
theorem cumulativeSamplerSuccess_nonneg (n q : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool) (C : TOCircuit (ForrSpace n W))
    (ψfam : (Fin q → Bool) → QState (ForrSpace n W)) (v : ℕ) :
    0 ≤ cumulativeSamplerSuccess n q W S U C ψfam v := by
  classical
  have htransition (ψ : QState (ForrSpace n W)) (hist : List (Reg n)) (x : Reg n) :
      0 ≤ directTransitionMass n W S U C ψ hist x := by
    unfold directTransitionMass
    apply mul_nonneg (by positivity)
    apply List.sum_nonneg
    intro z hz
    obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hz
    exact Finset.sum_nonneg fun i _ => sq_nonneg ‖φ i‖
  have hcum (ψ : QState (ForrSpace n W)) (m : ℕ) (hist : List (Reg n)) :
      0 ≤ cumDirectSuccess n W S U C ψ m hist := by
    induction m generalizing hist with
    | zero => exact zero_le_one
    | succ m ih =>
      apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg _ (ih _)
      split_ifs
      · exact htransition ψ hist x
      · exact le_refl 0
  unfold cumulativeSamplerSuccess
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => hcum (ψfam w) v [])

/-- Under the unitary classifier, normalization, query-budget, and acceptance-gap hypotheses,
the strong average of cumulative sampling success is at least `(1 - strongFailProb) * ((1 /
2^q) * (1 / (36 * t²)))^v`. -/
theorem classifier_strong_sampling_lower (n ℓ q t v : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (W : Type) [Fintype W] [DecidableEq W]
    (C : TOCircuit (ForrSpace n W))
    (ψfam : (Fin q → Bool) → QState (ForrSpace n W)) (E : Finset (ForrSpace n W))
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w))
    (hS : TOQueryCountS C ≤ t) (hU : TOQueryCountU C ≤ t)
    (hyes : ∀ S U : Reg n → Bool, (59 / 100 : ℝ) ≤ spectralForrelation n S U →
      ∃ w, (2 / 3 : ℝ) ≤ MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E)
    (hno : ∀ S U : Reg n → Bool, spectralForrelation n S U ≤ (57 / 100 : ℝ) →
      ∀ w, MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E ≤ (1 / 3 : ℝ)) :
    (1 - strongFailProb n ℓ κ (57/100) (59/100) v) *
        ((1 / (2 ^ q : ℝ)) * (1 / (36 * (t : ℝ) ^ 2)) ^ v) ≤
      strongAverage n ℓ κ (fun s U =>
        cumulativeSamplerSuccess n q W (multisetInd s) U C ψfam v) := by
  classical
  apply strongAverage_lower_of_good n ℓ v κ (57/100) (59/100) _ hκ
  · intro s U
    exact cumulativeSamplerSuccess_nonneg n q W (multisetInd s) U C ψfam v
  · intro s U hstrong
    apply (theorem6_2CumulativeSampler n q t v W (multisetInd s) U C ψfam E hC hnorm hS hU
      ?_ (hyes _ _ hstrong.1)).1
    intro hist _ hsub hlen w
    apply hno _ U (hstrong.2 _ ?_ ?_) w
    · intro x hx
      exact hsub x (of_decide_eq_true hx)
    · have heq : supportCard (regOfList n hist) = hist.toFinset.card := by
        unfold supportCard
        congr 1
        ext x
        simp [regOfList]
      rw [heq]
      exact hist.toFinset_card_le.trans hlen

/-- The inner product of two `ℓ`-fold condensate tensors is the `ℓ`-th power of the underlying
state inner product. -/
theorem condensateTensor_inner {I : Type} [Fintype I] [DecidableEq I]
    (ℓ : ℕ) (φ ψ : QState I) :
    Inner (condensateTensor ℓ φ) (condensateTensor ℓ ψ) = (Inner φ ψ) ^ ℓ := by
  classical
  simp only [inner_apply, condensateTensor, map_prod, ← Finset.prod_mul_distrib]
  have hsum : (∑ s : Fin ℓ → I, ∏ j, (starRingEnd ℂ) (φ (s j)) * ψ (s j)) =
      ∏ _j : Fin ℓ, ∑ i : I, (starRingEnd ℂ) (φ i) * ψ i := by
    simpa using! (Finset.prod_univ_sum (t := fun _ : Fin ℓ => (Finset.univ : Finset I))
      (f := fun _j i => (starRingEnd ℂ) (φ i) * ψ i)).symm
  rw [hsum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A condensate tensor of a normalized state is normalized. -/
theorem condensateTensor_normalized {I : Type} [Fintype I] [DecidableEq I]
    (ℓ : ℕ) (φ : QState I) (hφ : Normalized φ) : Normalized (condensateTensor ℓ φ) := by
  rw [normalized_iff_inner_self, condensateTensor_inner,
    (normalized_iff_inner_self φ).mp hφ, one_pow]

/-- A condensate tensor is invariant under permutations of its tensor coordinates. -/
theorem condensateTensor_symmetric {I : Type} (ℓ : ℕ) (φ : QState I)
    (π : Equiv.Perm (Fin ℓ)) (s : Fin ℓ → I) :
    condensateTensor ℓ φ (s ∘ π) = condensateTensor ℓ φ s := by
  unfold condensateTensor
  exact Equiv.prod_comp π (fun j => φ (s j))

/-- Permuting the sample coordinates preserves each occupation count. -/
theorem occupationCount_permutation {I : Type} [DecidableEq I] {ℓ : ℕ}
    (x : I) (s : Fin ℓ → I) (π : Equiv.Perm (Fin ℓ)) :
    occupationCount x (s ∘ π) = occupationCount x s := by
  unfold occupationCount
  apply Finset.card_equiv π
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]

/-- The indicator that all guessed values occur is bounded by the product of their occupation
counts. -/
theorem occupied_indicator_le_moment {I : Type} [DecidableEq I] {ℓ v : ℕ}
    (guesses : Fin v → I) (s : Fin ℓ → I) :
    (if allOccupied guesses s then 1 else 0) ≤ occupationMoment guesses s := by
  classical
  split_ifs with h
  · apply Finset.one_le_prod₀
    intro a _
    obtain ⟨j, hj⟩ := h a
    exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨j, by simp [hj]⟩)
  · exact Nat.zero_le _

/-- The Born mass that all guessed values occur is bounded by the Born-weighted sum of their
occupation-count product. -/
theorem occupied_born_le_moment {I : Type} [Fintype I] [DecidableEq I] {ℓ v : ℕ}
    (guesses : Fin v → I) (φ : QState (Fin ℓ → I)) :
    MeasureProb φ (Finset.univ.filter fun s => allOccupied guesses s) ≤
      ∑ s : Fin ℓ → I, BornProb φ s * (occupationMoment guesses s : ℝ) := by
  classical
  unfold MeasureProb
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro s _
  have hnn : 0 ≤ BornProb φ s := sq_nonneg ‖φ s‖
  have hbound := occupied_indicator_le_moment guesses s
  by_cases h : allOccupied guesses s
  · rw [if_pos h] at hbound ⊢
    have hreal : (1 : ℝ) ≤ (occupationMoment guesses s : ℝ) := by exact_mod_cast hbound
    exact (mul_one (BornProb φ s)).symm.trans_le (mul_le_mul_of_nonneg_left hreal hnn)
  · rw [if_neg h]
    exact mul_nonneg hnn (Nat.cast_nonneg _)

end Qatlib.Concepts.FreshFallback.BitScanLedger
