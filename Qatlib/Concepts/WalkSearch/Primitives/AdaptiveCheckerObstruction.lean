/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.CheckerAmplificationObstruction

/-!
# Adaptive checker counterexamples

Constructs bounded-error primitive implementations that refute the local adaptive checker and
corrected walk contracts. Explicit disjoint seed boxes give a lower bound on rejection events;
the examples clarify composition requirements in the bounded-error search setting of
[HoyerMoscaDeWolf2003].

## Main statements

* `triCheckSpecCorrected_adaptive_obstruction`: The corrected checker specification fails on the
  three-vertex triangle for `oneBadCollisionSolver`, `failingTestNoisySearch`, and four
  amplification trials, for every `r'`.
* `theorem4WalkCorrected_adaptive_obstruction`: The universally quantified corrected walk-search
  proposition `theorem4WalkCorrected` is false.

## References

* [Hoyer, Mosca and de Wolf, 2003][HoyerMoscaDeWolf2003]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

/-- A zero-cost noisy-search implementation that preferentially selects a marked vertex whose
test is false, and otherwise selects any marked vertex. -/
def failingTestNoisySearch : NoisySearch where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 4
  κ := 1
  run := fun {_N} marked test _tcost _floor _ρ =>
    if h : ∃ v, marked v = true ∧ test v = false then some (Classical.choose h)
    else if h : ∃ v, marked v = true then some (Classical.choose h) else none
  cost := fun {_N} _marked _test _tcost _floor _ρ => 0
  sound := by
    intro N marked test tcost floor ρ v ht
    split at ht
    · rename_i h
      cases ht
      exact (Classical.choose_spec h).1
    · split at ht
      · rename_i h
        cases ht
        exact Classical.choose_spec h
      · cases ht
  reject := by
    intro N marked test tcost floor ρ hR
    have hn : ¬∃ v, marked v = true := by
      rintro ⟨v, hv⟩; rw [hR v] at hv; cases hv
    have hn' : ¬∃ v, marked v = true ∧ test v = false := by
      rintro ⟨v, hv, _⟩; exact hn ⟨v, hv⟩
    simp [hn, hn']
  finds := by
    intro N marked test tcost floor hR _
    by_cases hbad : ∃ v, marked v = true ∧ test v = false
    · simp [hbad]
    · simp [hbad, hR]
  charges := by intros; simp

/-- If all collision-solver trials fail the Boolean adjacency test, `triCheckAmpExtract` returns
no witness. -/
theorem triCheckAmpExtract_none_of_any_false {n m : ℕ}
    (adj : Fin n → Fin n → Bool) (e : Fin m → Fin n) (kcs : KCollisionSolver)
    (r' : ℕ) (subR : (Fin 2 → Fin m) → Bool) (v : Fin n) (c₀ : ℕ)
    (stape : ℕ → kcs.seed)
    (htest : ((List.range c₀).any fun i =>
      match kcs.run r' subR r' 1 0 (stape (v.val*c₀+i)) with
      | some t => adj v (e (t 0)) && adj v (e (t 1))
      | none => false) = false) :
    (triCheckAmpExtract adj e kcs r' subR v c₀ stape).1 = none := by
  let step := fun (acc : Option (Fin 2 → Fin m) × ℕ) (i : ℕ) =>
    match acc with
    | (some t, q) => (some t, q)
    | (none, q) =>
        let qi := kcs.cost r' subR r' 1 0 (stape (v.val*c₀+i))
        match kcs.run r' subR r' 1 0 (stape (v.val*c₀+i)) with
        | some t => if adj v (e (t 0)) && adj v (e (t 1)) then
            (some t, q+qi) else (none, q+qi)
        | none => (none, q+qi)
  have hscan : ∀ l : List ℕ, ∀ q : ℕ,
      (∀ i ∈ l, (match kcs.run r' subR r' 1 0 (stape (v.val*c₀+i)) with
        | some t => adj v (e (t 0)) && adj v (e (t 1))
        | none => false) = false) → (l.foldl step (none,q)).1 = none := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro q h
      have hi := h i (by simp)
      have hl : ∀ j ∈ l, (match kcs.run r' subR r' 1 0 (stape (v.val*c₀+j)) with
          | some t => adj v (e (t 0)) && adj v (e (t 1))
          | none => false) = false := fun j hj => h j (by simp [hj])
      cases he : kcs.run r' subR r' 1 0 (stape (v.val*c₀+i)) with
      | none =>
        simpa only [List.foldl_cons, step, he] using
          ih (q+kcs.cost r' subR r' 1 0 (stape (v.val*c₀+i))) hl
      | some t =>
        simp only [he] at hi
        simpa only [List.foldl_cons, step, he, hi, Bool.false_eq_true, ↓reduceIte]
          using ih (q+kcs.cost r' subR r' 1 0 (stape (v.val*c₀+i))) hl
  apply hscan (List.range c₀) 0
  simpa only [List.any_eq_false, Bool.not_eq_true] using htest

/-- If some truly marked vertex has no successful collision-solver trial on its assigned seed
block, the amplified checker using `failingTestNoisySearch` returns no witness. -/
theorem adaptive_checker_rejects {n : ℕ} (adj : Fin n → Fin n → Bool)
    (U : Finset (Fin n)) (kcs : KCollisionSolver) (r' c₀ : ℕ) (stape : ℕ → kcs.seed)
    (hbad : ∃ v : Fin n,
      (decide (∃ u₁ ∈ U, ∃ u₂ ∈ U, u₁ ≠ u₂ ∧ adj v u₁ ∧ adj v u₂ ∧ adj u₁ u₂) : Bool) = true ∧
      ((List.range c₀).any fun i =>
        match kcs.run r'
          (fun t : Fin 2 → Fin (Fintype.card ↥U) => decide
            (t 0 ≠ t 1 ∧ adj v (((Fintype.equivFin ↥U).symm (t 0)) : Fin n) ∧
              adj v (((Fintype.equivFin ↥U).symm (t 1)) : Fin n) ∧
              adj (((Fintype.equivFin ↥U).symm (t 0)) : Fin n)
                (((Fintype.equivFin ↥U).symm (t 1)) : Fin n))) r' 1 0
          (stape (v.val*c₀+i)) with
        | some t => adj v (((Fintype.equivFin ↥U).symm (t 0)) : Fin n) &&
            adj v (((Fintype.equivFin ↥U).symm (t 1)) : Fin n)
        | none => false) = false) :
    (triCheckAmp adj U kcs failingTestNoisySearch r' c₀ stape ()).1 = none := by
  simp only [triCheckAmp, failingTestNoisySearch]
  split_ifs with hb hm
  · have he := triCheckAmpExtract_none_of_any_false adj
      (fun i => ((Fintype.equivFin ↥U).symm i : Fin n)) kcs r'
      (fun t => decide (t 0 ≠ t 1 ∧
        adj (Classical.choose hb) (((Fintype.equivFin ↥U).symm (t 0)) : Fin n) ∧
        adj (Classical.choose hb) (((Fintype.equivFin ↥U).symm (t 1)) : Fin n) ∧
        adj (((Fintype.equivFin ↥U).symm (t 0)) : Fin n)
          (((Fintype.equivFin ↥U).symm (t 1)) : Fin n)))
      (Classical.choose hb) c₀ stape (Classical.choose_spec hb).2
    simp only [he]
  · exfalso
    apply hb
    convert hbad using 1; congr!
    funext motive x h₁ h₂
    cases x <;> rfl
  · exfalso
    apply hb
    convert hbad using 1; congr!
    funext motive x h₁ h₂
    cases x <;> rfl

/-- The finite seed box with the selected vertex's four-trial block fixed to zero and earlier
block-start coordinates constrained to be nonzero. -/
@[irreducible] def adaptiveBadBox (v : Fin 3) : Finset (Fin 13 → Fin 4) :=
  Fintype.piFinset fun i =>
    if v.val*4 ≤ i.val ∧ i.val < v.val*4+4 then {0}
    else if i.val < v.val*4 ∧ i.val % 4 = 0 then Finset.univ.erase 0
    else Finset.univ

/-- The seed box for vertex zero contains `4 ^ 9` tapes. -/
theorem adaptiveBadBox_card_zero : (adaptiveBadBox 0).card = 4^9 := by
  rw [adaptiveBadBox, Fintype.card_piFinset]
  decide

/-- The seed box for vertex one contains `3 * 4 ^ 8` tapes. -/
theorem adaptiveBadBox_card_one : (adaptiveBadBox 1).card = 3*4^8 := by
  rw [adaptiveBadBox, Fintype.card_piFinset]
  decide

/-- The seed box for vertex two contains `9 * 4 ^ 7` tapes. -/
theorem adaptiveBadBox_card_two : (adaptiveBadBox 2).card = 9*4^7 := by
  rw [adaptiveBadBox, Fintype.card_piFinset]
  decide

/-- Every seed in the selected four-trial vertex block is zero for tapes belonging to
`adaptiveBadBox v`. -/
theorem adaptiveBadBox_block_zero (v : Fin 3) (τ : Fin 13 → Fin 4)
    (hτ : τ ∈ adaptiveBadBox v) (i : ℕ) (hi : i < 4) :
    @extSeed 13 (Fin 4) inferInstance τ (v.val*4+i) = 0 := by
  have hbound : v.val*4+i < 13 := by have := v.isLt; omega
  unfold adaptiveBadBox at hτ
  have ht := Fintype.mem_piFinset.mp hτ ⟨v.val*4+i, hbound⟩
  have hrange : v.val*4 ≤ v.val*4+i ∧ v.val*4+i < v.val*4+4 := by omega
  simpa [hrange, extSeed, hbound] using ht

/-- Every tape in `adaptiveBadBox v` makes the amplified checker reject the three-vertex
triangle for the supplied primitive implementations. -/
theorem adaptiveBadBox_rejects (r' : ℕ) (v : Fin 3) (τ : Fin 13 → Fin 4)
    (hτ : τ ∈ adaptiveBadBox v) :
    (triCheckAmp threeVertexTriangle Finset.univ oneBadCollisionSolver failingTestNoisySearch
      r' 4 (@extSeed 13 (Fin 4) inferInstance τ) ()).1 = none := by
  apply adaptive_checker_rejects
  refine ⟨v, ?_, ?_⟩
  · fin_cases v <;> decide
  · apply List.any_eq_false.mpr
    intro i hi
    have hib : i < 4 := List.mem_range.mp hi
    have hz := adaptiveBadBox_block_zero v τ hτ i hib
    simp only [oneBadCollisionSolver, Fintype.card_coe, Finset.card_univ, Fintype.card_fin,
      show (3 : ℕ) ≤ 3 by decide, hz, true_and, ↓reduceIte]
    simp

/-- The adaptive bad seed boxes for strictly ordered vertices are disjoint. -/
theorem adaptiveBadBox_disjoint (v w : Fin 3) (hvw : v < w) :
    Disjoint (adaptiveBadBox v) (adaptiveBadBox w) := by
  apply Finset.disjoint_left.mpr
  intro τ hv hw
  unfold adaptiveBadBox at hv hw
  have hbound : v.val*4 < 13 := by have := v.isLt; omega
  have hv0 := Fintype.mem_piFinset.mp hv ⟨v.val*4,hbound⟩
  have hw0 := Fintype.mem_piFinset.mp hw ⟨v.val*4,hbound⟩
  have hvR : v.val*4 ≤ v.val*4 ∧ v.val*4 < v.val*4+4 := by omega
  have hwR : ¬(w.val*4 ≤ v.val*4 ∧ v.val*4 < w.val*4+4) := by
    have : v.val < w.val := hvw
    omega
  have hwE : v.val*4 < w.val*4 ∧ v.val*4 % 4 = 0 := by
    constructor
    · have : v.val < w.val := hvw; omega
    · omega
  simp [hvR] at hv0
  simp only [hwR, ↓reduceIte, hwE, Finset.mem_erase, Finset.mem_univ, and_true] at hw0
  exact hw0 hv0

/-- The union of the three adaptive bad seed boxes has cardinality `37 * 4 ^ 7`. -/
theorem adaptiveBadBoxes_card :
    ((adaptiveBadBox 0 ∪ adaptiveBadBox 1) ∪ adaptiveBadBox 2).card = 37*4^7 := by
  have h01 := adaptiveBadBox_disjoint 0 1 (by decide)
  have h02 := adaptiveBadBox_disjoint 0 2 (by decide)
  have h12 := adaptiveBadBox_disjoint 1 2 (by decide)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
    Finset.card_union_of_disjoint h01, adaptiveBadBox_card_zero,
    adaptiveBadBox_card_one, adaptiveBadBox_card_two]
  norm_num

/-- If every element of `S` satisfies `F` after pairing with the unique unit value, then
`S.card` is at most the cardinality of the full event defined by `F`. -/
theorem unit_failure_card_ge {α : Type} [Fintype α] (S : Finset α)
    (F : Unit × α → Prop) [DecidablePred F] (hF : ∀ x ∈ S, F ((),x)) :
    S.card ≤ (Finset.univ.filter F).card := by
  have hsub : S.image (fun x => ((),x)) ⊆ Finset.univ.filter F := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hF x hx⟩
  have hi : Function.Injective (fun x : α => ((),x)) := by
    intro x y hxy
    exact congrArg Prod.snd hxy
  simpa only [Finset.card_image_of_injective S hi] using Finset.card_le_card hsub

/-- If every element of `S`, paired with the unique unit value, belongs to `E`, then `S.card ≤
E.card`. -/
theorem unit_event_card_ge {α : Type} (S : Finset α) (E : Finset (Unit × α))
    (hE : ∀ x ∈ S, ((),x) ∈ E) : S.card ≤ E.card := by
  have hsub : S.image (fun x => ((),x)) ⊆ E := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact hE x hx
  have hi : Function.Injective (fun x : α => ((),x)) := by
    intro x y hxy
    exact congrArg Prod.snd hxy
  simpa only [Finset.card_image_of_injective S hi] using Finset.card_le_card hsub

/-- The corrected checker specification fails on the three-vertex triangle for
`oneBadCollisionSolver`, `failingTestNoisySearch`, and four amplification trials, for every
`r'`. -/
theorem triCheckSpecCorrected_adaptive_obstruction (r' : ℕ) :
    ¬triCheckSpecCorrected threeVertexTriangle Finset.univ
      oneBadCollisionSolver failingTestNoisySearch r' 4 := by
  intro h
  have htriangle : ∃ v : Fin 3, ∃ u₁ ∈ (Finset.univ : Finset (Fin 3)),
      ∃ u₂ ∈ Finset.univ, u₁ ≠ u₂ ∧ threeVertexTriangle v u₁ = true ∧
        threeVertexTriangle v u₂ = true ∧ threeVertexTriangle u₁ u₂ = true := by
    decide
  let boxes := (adaptiveBadBox 0 ∪ adaptiveBadBox 1) ∪ adaptiveBadBox 2
  have hl : boxes.card ≤
      (Finset.univ.filter fun ρ : Unit × (Fin 13 → Fin 4) =>
        (triCheckAmp threeVertexTriangle Finset.univ oneBadCollisionSolver failingTestNoisySearch
          r' 4 (@extSeed 13 (Fin 4) inferInstance ρ.2) ρ.1).1 = none).card := by
    apply unit_event_card_ge
    intro τ hτ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [boxes, Finset.mem_union] at hτ
    rcases hτ with (h0 | h1) | h2
    · exact adaptiveBadBox_rejects r' 0 τ h0
    · exact adaptiveBadBox_rejects r' 1 τ h1
    · exact adaptiveBadBox_rejects r' 2 τ h2
  rw [show boxes.card = 37*4^7 from adaptiveBadBoxes_card] at hl
  have hb := (h (by decide) (by decide)).2.1 htriangle
  change _ ≤ _ at hb
  have hseed : @Fintype.card failingTestNoisySearch.seed failingTestNoisySearch.seedFin = 1 := rfl
  have hseed4 : @Fintype.card oneBadCollisionSolver.seed oneBadCollisionSolver.seedFin = 4 := rfl
  simp only [Fintype.card_fun, Fintype.card_fin, hseed, hseed4,
    Finset.card_univ, show oneBadCollisionSolver.cExp = 1 by rfl,
    show failingTestNoisySearch.cExp = 4 by rfl, mul_one, min_self] at hb
  have hcontra := (Nat.mul_le_mul_right (4^4) hl).trans hb
  norm_num at hcontra

/-- A zero-cost `SafeGrover` implementation with `κ = 1` and `cExp = 0` that always returns no
result. -/
def positiveNullGrover : SafeGrover where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 0
  κ := 1
  run := fun {_N} _marked _check _floor _ρ => none
  cost := fun {_N} _marked _check _floor _ρ => 0
  sound := by intros; contradiction
  reject := by intros; rfl
  finds := by intros; simp
  charges := by intros; simp

/-- The universally quantified corrected walk-search proposition `theorem4WalkCorrected` is
false. -/
theorem theorem4WalkCorrected_adaptive_obstruction : ¬theorem4WalkCorrected := by
  intro h
  obtain ⟨r, r', _, _, _, _, _, _, hcheck, _⟩ :=
    h 3 (by decide) threeVertexTriangle threeVertexTriangle_symm threeVertexTriangle_loopless
      oneBadCollisionSolver failingTestNoisySearch positiveNullGrover
      (by decide) (by decide) (by decide)
  exact triCheckSpecCorrected_adaptive_obstruction r' hcheck

end Qatlib.Concepts.WalkSearch.Primitives
