/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.LocalMath

@[expose] public section


/-! Concrete zero-input counterexamples to the old pointwise Lemmas 9 and 10.
The source uses asymptotic positive input sizes and coupled adjacent updates. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators symmDiff
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults

/-- Eight pairs having the same first endpoint. -/
def starPairs (u : Fin 8) : Finset (Fin 8 × Fin 8) :=
  ({u} : Finset (Fin 8)).product Finset.univ

/-- Each star is a legitimate eight-element subset of the pair universe. -/
theorem star_card (u : Fin 8) : (starPairs u).card = 8 := by
  simp [starPairs]

/-- Matching stars produce one full eight-element triple fibre. -/
theorem gamma_star (u v : Fin 8) :
    gammaSet 8 8 8 (starPairs u) (starPairs u) (starPairs v) =
      ({u} : Finset (Fin 8)).product (({v} : Finset (Fin 8)).product Finset.univ) := by
  ext ⟨a, b, c⟩
  simp [gammaSet, starPairs, and_comm]

/-- Moving one independently drawn star to a different endpoint removes all triples. -/
theorem gamma_mismatch :
    gammaSet 8 8 8 (starPairs 0) (starPairs 1) (starPairs 0) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  have hh := (Finset.mem_filter.mp hp).2
  have h0 : p.1 = 0 := Finset.mem_singleton.mp (Finset.mem_product.mp hh.1).1
  have h1 : p.1 = 1 := Finset.mem_singleton.mp (Finset.mem_product.mp hh.2.1).1
  have h : (0 : Fin 8) = 1 := h0.symm.trans h1
  exact (by decide : (0 : Fin 8) ≠ 1) h

/-- The two draws used below differ on eight triples. -/
theorem gamma_difference :
    (gammaSet 8 8 8 (starPairs 0) (starPairs 0) (starPairs 0) ∆
      gammaSet 8 8 8 (starPairs 0) (starPairs 1) (starPairs 0)).card = 8 := by
  rw [gamma_star, gamma_mismatch]
  rw [Finset.symmDiff_def, Finset.sdiff_empty, Finset.empty_sdiff, Finset.union_empty]
  decide

/-- Membership of one witness gives strictly positive uniform counting mass. -/
theorem uniform_positive {α : Type*} (S : Finset α)
    (P : α → Prop) (a : α) (ha : a ∈ S) (hP : P a) :
    0 < uniformEventProb S P := by
  classical
  have hnum : 0 < (S.filter P).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hP⟩⟩
  have hden : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  unfold uniformEventProb
  exact div_pos (by exact_mod_cast hnum) (by exact_mod_cast hden)

/-- The old admissibility predicate accepts positive densities even at n=0. -/
def zeroParams : Parameters 1 := ⟨fun _ => 8, fun _ _ => 8, fun _ _ _ => 1⟩

/-- All old admissibility hypotheses hold for this concrete zero-size input. -/
theorem zero_admissible : zeroParams.Admissible (completeHypergraph 1) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, 1, by norm_num, ?_, ?_, ?_⟩
  all_goals norm_num [zeroParams]

/-- The independently redrawn triple experiment has positive old Lemma 9 tail mass. -/
theorem lemma9_mass_pos :
    0 < uniformEventProb
      ((tripleSample 8 8 8 8 8 8).product (tripleSample 8 8 8 8 8 8))
      (fun ω =>
        44 * ((8 : ℝ) * 8 * 8 / (8 ^ 2 * 8 * 8)) ≤
          ((gammaSet 8 8 8 ω.1.1 ω.1.2.1 ω.1.2.2 ∆
            gammaSet 8 8 8 ω.2.1 ω.2.2.1 ω.2.2.2).card : ℝ)) := by
  classical
  let a := (starPairs 0, starPairs 0, starPairs 0)
  let b := (starPairs 0, starPairs 1, starPairs 0)
  apply uniform_positive _ _ (a, b)
  · simp [a, b, tripleSample, Finset.mem_powersetCard, star_card]
  · dsimp [a, b]
    rw [gamma_difference]
    norm_num

/-- The independently redrawn pair experiment has positive old Lemma 10 tail mass. -/
theorem lemma10_mass_pos :
    0 < uniformEventProb
      ((pairSample 8 8 8 8 8).product (pairSample 8 8 8 8 8))
      (fun ω =>
        22 * ((8 : ℝ) * 8 / (8 * 8 * 8)) ≤
          ((gammaSet 8 8 8 (starPairs 0) ω.1.1 ω.1.2 ∆
            gammaSet 8 8 8 (starPairs 0) ω.2.1 ω.2.2).card : ℝ)) := by
  classical
  let a := (starPairs 0, starPairs 0)
  let b := (starPairs 1, starPairs 0)
  apply uniform_positive _ _ (a, b)
  · simp [a, b, pairSample, Finset.mem_powersetCard, star_card]
  · dsimp [a, b]
    rw [gamma_difference]
    norm_num

/-- No constant can bound a positive probability by C/0^100. -/
theorem zero_bound_false {p : ℝ} (hp : 0 < p) :
    ¬ ∃ C : ℝ, 0 < C ∧ p ≤ C / (0 : ℝ) ^ 100 := by
  rintro ⟨C, _, h⟩
  norm_num at h
  exact (not_le.mpr hp) h

/-- The complete old Lemma 9 conclusion fails at the admissible zero-size instance. -/
theorem lemma9_zero_false :
    ¬ ∃ C : ℝ, 0 < C ∧
      uniformEventProb
        ((tripleSample (zeroParams.r 0) (zeroParams.r 0) (zeroParams.r 0)
          (zeroParams.f 0 0) (zeroParams.f 0 0) (zeroParams.f 0 0)).product
          (tripleSample (zeroParams.r 0) (zeroParams.r 0) (zeroParams.r 0)
            (zeroParams.f 0 0) (zeroParams.f 0 0) (zeroParams.f 0 0)))
        (fun ω =>
          44 * ((zeroParams.f 0 0 : ℝ) * zeroParams.f 0 0 * zeroParams.f 0 0 /
            ((zeroParams.r 0 : ℝ) ^ 2 * zeroParams.r 0 * zeroParams.r 0)) ≤
            ((gammaSet (zeroParams.r 0) (zeroParams.r 0) (zeroParams.r 0)
                ω.1.1 ω.1.2.1 ω.1.2.2 ∆
              gammaSet (zeroParams.r 0) (zeroParams.r 0) (zeroParams.r 0)
                ω.2.1 ω.2.2.1 ω.2.2.2).card : ℝ)) ≤ C / (0 : ℝ) ^ 100 := by
  exact zero_bound_false lemma9_mass_pos

/-- The complete old Lemma 10 conclusion fails at the admissible zero-size instance. -/
theorem lemma10_zero_false :
    ¬ ∃ C : ℝ, 0 < C ∧
      uniformEventProb
        ((pairSample (zeroParams.r 0) (zeroParams.r 0) (zeroParams.r 0)
          (zeroParams.f 0 0) (zeroParams.f 0 0)).product
          (pairSample (zeroParams.r 0) (zeroParams.r 0) (zeroParams.r 0)
            (zeroParams.f 0 0) (zeroParams.f 0 0)))
        (fun ω =>
          22 * ((zeroParams.f 0 0 : ℝ) * zeroParams.f 0 0 /
            ((zeroParams.r 0 : ℝ) * zeroParams.r 0 * zeroParams.r 0)) ≤
            ((gammaSet (zeroParams.r 0) (zeroParams.r 0) (zeroParams.r 0)
                (starPairs 0) ω.1.1 ω.1.2 ∆
              gammaSet (zeroParams.r 0) (zeroParams.r 0) (zeroParams.r 0)
                (starPairs 0) ω.2.1 ω.2.2).card : ℝ)) ≤ C / (0 : ℝ) ^ 100 := by
  exact zero_bound_false lemma10_mass_pos

end Qatlib.Papers.SubHypergraph13.MainResults
