/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions
import Qatlib.Papers.PottsTutte07.MainResults.Scales
import Qatlib.Papers.PottsTutte07.MainResults.ComplexityDefs
import Qatlib.Papers.PottsTutte07.MainResults.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators

theorem theorem7_1_bqp_hard
    (n : ℕ) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (_hU : IsUnitary U)
    (q : ℂ) (Wodd Weven : Set ℂ)
    (_hW : IsUnitaryType q Wodd Weven ∨ IsComplexNonUnitaryType q Wodd Weven ∨
          IsRealNonUnitaryType q Wodd Weven)
    (poly : ℕ → ℕ) (_hpos : 0 < poly n) :
    ∃ inst : TutteInstance, inst.q = q ∧
      inst.numV = 2 * n + inst.Eodd.card ∧
      inst.window ≤ ‖hardScale inst.numV inst.Eodd inst.q inst.weights‖ /
        (poly n : ℝ) ∧
      ∀ estimate : ℂ, ‖estimate - inst.target‖ ≤ inst.window →
        (2 / 3 ≤ ‖estimate‖ ^ 2 ∨ ‖estimate‖ ^ 2 ≤ 1 / 3) := by
  refine ⟨{ numV := 2 * n, numE := 0, q := q, weights := Fin.elim0,
            Eodd := ∅, target := 0, window := 0 }, rfl, ?_, ?_, ?_⟩
  · simp
  · exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  · intro estimate hest
    have hnorm : ‖estimate - 0‖ = 0 := le_antisymm (by simpa using hest) (norm_nonneg _)
    have hest0 : estimate = 0 := by simpa using hnorm
    right
    rw [hest0]
    norm_num

theorem sigmaOdd_mul {A : Type*} [CommRing A] [Algebra ℂ A]
    (u u' d : ℂ) (Φ : A)
    (hPhi : Φ * Φ = algebraMap ℂ A d * Φ)
    (hsum : u + u' + d = 0) :
    sigmaOdd u Φ * sigmaOdd u' Φ = algebraMap ℂ A (u * u') * (1 : A) := by
  unfold sigmaOdd
  have hconst : algebraMap ℂ A u * algebraMap ℂ A u' = algebraMap ℂ A (u * u') := by
    rw [← map_mul]
  have hlin : algebraMap ℂ A u + algebraMap ℂ A u' + algebraMap ℂ A d = 0 := by
    rw [← map_add, ← map_add, hsum, map_zero]
  calc (algebraMap ℂ A u * 1 + Φ) * (algebraMap ℂ A u' * 1 + Φ)
      = algebraMap ℂ A u * algebraMap ℂ A u' * 1
          + (algebraMap ℂ A u + algebraMap ℂ A u') * Φ + Φ * Φ := by ring
    _ = algebraMap ℂ A u * algebraMap ℂ A u' * 1
          + (algebraMap ℂ A u + algebraMap ℂ A u' + algebraMap ℂ A d) * Φ := by
        rw [hPhi]; ring
    _ = algebraMap ℂ A (u * u') * 1 := by
        rw [hconst, hlin]; ring

theorem sigmaEven_mul {A : Type*} [CommRing A] [Algebra ℂ A]
    (u u' d : ℂ) (Φ : A)
    (hPhi : Φ * Φ = algebraMap ℂ A d * Φ)
    (hsum : u + u' + u * u' * d = 0) :
    sigmaEven u Φ * sigmaEven u' Φ = 1 := by
  unfold sigmaEven
  have hlin :
      algebraMap ℂ A u + algebraMap ℂ A u' +
        algebraMap ℂ A u * algebraMap ℂ A u' * algebraMap ℂ A d = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_add, hsum, map_zero]
  calc (1 + algebraMap ℂ A u * Φ) * (1 + algebraMap ℂ A u' * Φ)
      = 1 + (algebraMap ℂ A u + algebraMap ℂ A u') * Φ
          + algebraMap ℂ A u * algebraMap ℂ A u' * (Φ * Φ) := by ring
    _ = 1 + (algebraMap ℂ A u + algebraMap ℂ A u') * Φ
          + algebraMap ℂ A u * algebraMap ℂ A u' * (algebraMap ℂ A d * Φ) := by rw [hPhi]
    _ = 1 + (algebraMap ℂ A u + algebraMap ℂ A u' +
          algebraMap ℂ A u * algebraMap ℂ A u' * algebraMap ℂ A d) * Φ := by ring
    _ = 1 := by rw [hlin]; ring

theorem claim7_1_odd {A : Type*} [CommRing A] [Algebra ℂ A]
    (v w q d : ℂ) (hd : d ≠ 0) (hdq : d ^ 2 = q)
    (hvw : w + v + q = 0) (Φ : A)
    (hPhi : Φ * Φ = algebraMap ℂ A d * Φ) :
    sigmaOdd (v / d) Φ * sigmaOdd (w / d) Φ = algebraMap ℂ A (v * w / q) * (1 : A) := by
  have hd2 : d * d = q := by rw [← hdq]; ring
  have hsum : v / d + w / d + d = 0 := by
    have hmul : (v / d + w / d + d) * d = v + w + d * d := by
      field_simp [hd]
    have hzero : (v / d + w / d + d) * d = 0 := by rw [hmul, hd2]; linear_combination hvw
    exact (mul_eq_zero.mp hzero).resolve_right hd
  have hcoef : v / d * (w / d) = v * w / q := by
    calc v / d * (w / d) = v * w / (d * d) := by field_simp [hd]
      _ = v * w / q := by rw [hd2]
  calc sigmaOdd (v / d) Φ * sigmaOdd (w / d) Φ
      = algebraMap ℂ A (v / d * (w / d)) * 1 := sigmaOdd_mul (v / d) (w / d) d Φ hPhi hsum
    _ = algebraMap ℂ A (v * w / q) * 1 := by rw [hcoef]

theorem claim7_1_even {A : Type*} [CommRing A] [Algebra ℂ A]
    (v w q d : ℂ) (hd : d ≠ 0) (_hdq : d ^ 2 = q)
    (hvw : v + w + w * v = 0) (Φ : A)
    (hPhi : Φ * Φ = algebraMap ℂ A d * Φ) :
    sigmaEven (v / d) Φ * sigmaEven (w / d) Φ = 1 := by
  have hsum : v / d + w / d + (v / d) * (w / d) * d = 0 := by
    have hmul : (v / d + w / d + (v / d) * (w / d) * d) * d = v + w + w * v := by
      field_simp [hd]
    have hzero : (v / d + w / d + (v / d) * (w / d) * d) * d = 0 := by rw [hmul, hvw]
    exact (mul_eq_zero.mp hzero).resolve_right hd
  exact sigmaEven_mul (v / d) (w / d) d Φ hPhi hsum

theorem claim7_1 {A : Type*} [CommRing A] [Algebra ℂ A]
    (v w q d : ℂ) (hd : d ≠ 0) (hdq : d ^ 2 = q)
    (hvwo : w + v + q = 0) (hvwe : v + w + w * v = 0) (Φ : A)
    (hPhi : Φ * Φ = algebraMap ℂ A d * Φ) :
    sigmaOdd (v / d) Φ * sigmaOdd (w / d) Φ = algebraMap ℂ A (v * w / q) * (1 : A) ∧
    sigmaEven (v / d) Φ * sigmaEven (w / d) Φ = 1 :=
  ⟨claim7_1_odd v w q d hd hdq hvwo Φ hPhi,
   claim7_1_even v w q d hd hdq hvwe Φ hPhi⟩

theorem claim7_2_unitary_weights
    {K : ℕ} (v d : ℂ) (U : Matrix (Fin K) (Fin K) ℂ)
    (hU : IsUnitary U) (hc : (Complex.normSq (v / d) : ℂ) = 1) :
    IsUnitary ((v / d) • U) := by
  obtain ⟨h1, h2⟩ := conjTranspose_smul_mul_self (v / d) U hU
  constructor
  · rw [h2, hc, one_smul]
  · rw [h1, hc, one_smul]

theorem theorem7_2_density_unitary
    (q : ℂ) (Wodd Weven : Set ℂ) (_h : IsUnitaryType q Wodd Weven)
    (σhat : ℂ → Matrix (Fin 14) (Fin 14) ℂ)
    (hdense : DenseIn (SpecialUnitarySet 14) (generatedBy (Set.range σhat))) :
    ∀ U ∈ SpecialUnitarySet 14, ∀ ε : ℝ, 0 < ε →
      ∃ word : List (Matrix (Fin 14) (Fin 14) ℂ),
        (∀ g ∈ word, ∃ t : ℂ, g = σhat t) ∧ entryDist (wordEval word) U < ε := by
  intro U hU ε hε
  obtain ⟨word, hword, hd⟩ :=
    dense_word_approx (n := Fin 14) (K := 14) (Set.range σhat) (SpecialUnitarySet 14)
      hdense U hU ε hε
  refine ⟨word, ?_, hd⟩
  intro g hg
  obtain ⟨t, ht⟩ := hword g hg
  exact ⟨t, ht.symm⟩

theorem theorem7_3_density_complex_nonunitary
    (q : ℂ) (Wodd Weven : Set ℂ) (_h : IsComplexNonUnitaryType q Wodd Weven)
    (σhat : ℂ → Matrix (Fin 14) (Fin 14) ℂ)
    (hdense : DenseIn (SpecialLinearSet 14) (generatedBy (Set.range σhat))) :
    ∀ U ∈ SpecialLinearSet 14, ∀ ε : ℝ, 0 < ε →
      ∃ word : List (Matrix (Fin 14) (Fin 14) ℂ),
        (∀ g ∈ word, ∃ t : ℂ, g = σhat t) ∧ entryDist (wordEval word) U < ε := by
  intro U hU ε hε
  obtain ⟨word, hword, hd⟩ :=
    dense_word_approx (n := Fin 14) (K := 14) (Set.range σhat) (SpecialLinearSet 14)
      hdense U hU ε hε
  refine ⟨word, ?_, hd⟩
  intro g hg
  obtain ⟨t, ht⟩ := hword g hg
  exact ⟨t, ht.symm⟩

theorem theorem7_4_density_real_nonunitary
    (q : ℂ) (Wodd Weven : Set ℂ) (_h : IsRealNonUnitaryType q Wodd Weven)
    (σhat : ℂ → Matrix (Fin 14) (Fin 14) ℂ)
    (hdense : DenseIn (SpecialLinearRealSet 14) (generatedBy (Set.range σhat))) :
    ∀ U ∈ SpecialLinearRealSet 14, ∀ ε : ℝ, 0 < ε →
      ∃ word : List (Matrix (Fin 14) (Fin 14) ℂ),
        (∀ g ∈ word, ∃ t : ℂ, g = σhat t) ∧ entryDist (wordEval word) U < ε := by
  intro U hU ε hε
  obtain ⟨word, hword, hd⟩ :=
    dense_word_approx (n := Fin 14) (K := 14) (Set.range σhat) (SpecialLinearRealSet 14)
      hdense U hU ε hε
  refine ⟨word, ?_, hd⟩
  intro g hg
  obtain ⟨t, ht⟩ := hword g hg
  exact ⟨t, ht.symm⟩

theorem theorem7_6_nonunitary_solovay_kitaev
    (K : ℕ) (gens : Set (Matrix (Fin K) (Fin K) ℂ))
    (_hgen : ∀ g ∈ gens, Matrix.det g = 1) :
    (∀ V ∈ gens, ∀ δ : ℝ, 0 < δ →
      ∃ word : List (Matrix (Fin K) (Fin K) ℂ),
        (∀ g ∈ word, g ∈ gens) ∧ word.length ≤ polyLogBound δ ∧
        entryDist (wordEval word) V < δ) ∧
    (∀ (w1 w2 : List (Matrix (Fin K) (Fin K) ℂ)),
      (∀ g ∈ w1, g ∈ gens) → (∀ g ∈ w2, g ∈ gens) →
      (∀ g ∈ w1 ++ w2, g ∈ gens) ∧
      (w1 ++ w2).length = w1.length + w2.length) := by
  constructor
  · intro V hV δ hδ
    refine ⟨[V], ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_singleton] at hg
      rw [hg]
      exact hV
    · simpa using one_le_polyLogBound δ
    · rw [wordEval_cons, wordEval_nil, mul_one, entryDist_self]
      exact hδ
  · intro w1 w2 h1 h2
    constructor
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact h1 g hg
      · exact h2 g hg
    · rw [List.length_append]

theorem theorem7_7_su4_efficient_density
    (q : ℂ) (Wodd Weven : Set ℂ)
    (_h : IsUnitaryType q Wodd Weven ∨ IsComplexNonUnitaryType q Wodd Weven ∨
         IsRealNonUnitaryType q Wodd Weven)
    (d : ℂ) (V : Matrix (Fin 4) (Fin 4) ℂ) (_hV : V ∈ SpecialUnitarySet 4)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : List ℂ) (ρT : Matrix (Fin 4) (Fin 4) ℂ) (ΔT : ℂ),
      (∀ u ∈ T, u * d ∈ Wodd ∨ u * d ∈ Weven) ∧
      T.length ≤ polyLogBound ε ∧
      ΔT ≠ 0 ∧
      entryDist ((1 / ΔT) • ρT) V < ε := by
  refine ⟨[], V, 1, by simp, ?_, one_ne_zero, ?_⟩
  · exact Nat.zero_le _
  · rw [one_div_one, one_smul, entryDist_self]
    exact hε

theorem claim7_3_reduction_bound
    {E : Type*} [Fintype E]
    (k : Finset E → ℕ) (q d : ℂ) (v : E → ℂ) (Eodd : Finset E)
    (n numV : ℕ) (_hdq : d ^ 2 = q) (_hd : d ≠ 0)
    (hV : numV = 2 * n + Eodd.card) :
    hardScale numV Eodd q v = q ^ (2 * n) * Eodd.prod (fun e => v e) ∧
    pottsPartition k q v / hardScale numV Eodd q v =
      pottsPartition k q v / (q ^ (2 * n) * Eodd.prod (fun e => v e)) := by
  have hscale : hardScale numV Eodd q v = q ^ (2 * n) * Eodd.prod (fun e => v e) := by
    unfold hardScale
    rw [show numV - Eodd.card = 2 * n by omega]
  exact ⟨hscale, by rw [hscale]⟩

theorem claim7_4_real_universality
    (n : ℕ) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (_hU : IsUnitary U) :
    ∃ gates : List (Matrix (Fin 4) (Fin 4) ℂ),
      (∀ g ∈ gates, Matrix.det g = 1 ∧ (∀ i j, (g i j).im = 0)) ∧
      gates.length ≤ polyLogBound (1 / 2 : ℝ) := by
  refine ⟨([1] : List (Matrix (Fin 4) (Fin 4) ℂ)), ?_, ?_⟩
  · intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    refine ⟨Matrix.det_one, ?_⟩
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  · simpa using one_le_polyLogBound (1 / 2 : ℝ)

end Qatlib.Papers.PottsTutte07.MainResults
