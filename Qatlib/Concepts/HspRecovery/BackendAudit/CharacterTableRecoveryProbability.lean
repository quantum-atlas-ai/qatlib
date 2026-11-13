/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.BackendAudit.CountedCharacterTableDecoder
import Qatlib.Concepts.HspRecovery.Distinguisher.BooleanSamplingProbability

/-!
# Recovery probabilities for character table decoding

This module bounds the probability that an element outside a hidden subgroup survives
`tableKernelDecode`. Uniform sampling from the annihilator gives survival probability at most
`2⁻ᵐ` for each false candidate, and a union bound gives exact subgroup recovery probability at
least `1 - card G * 2⁻ᵐ`. The budget `tableRecoverySamples` makes the failure bound at most
`2⁻ᵏ`. [Lomont2004]

## Main statements

* `character_table_false_candidate_fresh_probability`: bounds survival of each element outside
  the hidden subgroup.
* `character_table_actual_subgroup_recovery_probability`: proves the subgroup recovery
  probability bound.
* `character_table_computed_sample_budget`: verifies the budget `k + Nat.clog 2 N`.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option autoImplicit false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree

open Qatlib.Concepts.HspRecovery.Distinguisher

namespace Qatlib.Concepts.HspRecovery.BackendAudit

open scoped Classical

variable {G R : Type}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- A predicate holds for every element of `List.ofFn xs` exactly when it holds at every index
of `xs`. -/
private theorem forall_mem_ofFn {α : Type} {n : ℕ} (xs : Fin n → α) (P : α → Prop) :
    (∀ a ∈ List.ofFn xs, P a) ↔ ∀ i, P (xs i) := by
  constructor
  · intro h i
    have hmem : xs i ∈ List.ofFn xs := by
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    exact h (xs i) hmem
  · intro h a ha
    obtain ⟨i, hi⟩ : ∃ i, xs i = a := by
      rw [List.mem_ofFn] at ha
      exact ha
    rw [← hi]
    exact h i

/-- The cardinality of a filtered finite universe equals the cardinality of the corresponding
subtype. -/
private theorem card_filter_eq_card_subtype {X : Type} [Fintype X] [DecidableEq X]
    (Q : X → Prop) [DecidablePred Q] :
    (Finset.univ.filter Q).card = Fintype.card {x // Q x} :=
  (Fintype.card_subtype Q).symm

/-- Summing a constant `c` on the elements satisfying a predicate and zero elsewhere gives the
number of such elements times `c`. -/
private theorem sum_ite_filter_card {X : Type} [Fintype X] [DecidableEq X]
    (Q : X → Prop) [DecidablePred Q] (c : ℝ) :
    (∑ x : X, if Q x then c else 0) = (Finset.univ.filter Q).card * c := by
  calc
    (∑ x : X, if Q x then c else 0)
        = (Finset.univ : Finset X).sum (fun y => if Q y then c else 0) := rfl
    _ = (Finset.univ.filter Q).sum (fun _ => c) := by rw [Finset.sum_filter]
    _ = (Finset.univ.filter Q).card * c := by rw [Finset.sum_const, nsmul_eq_mul]

/-- For independent samples from a finite distribution, inclusion of events implies the
corresponding probability inequality. -/
theorem probEvent_mono {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (E F : (Fin L → X) → Prop) [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω → F ω) : p.probEvent E ≤ p.probEvent F := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hEF ω hω
  · intro ω _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg (ω i)

/-- The probability of the union of two independent sample events is at most the sum of their
probabilities. -/
theorem probEvent_union_le {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (E F : (Fin L → X) → Prop) [DecidablePred E] [DecidablePred F] :
    p.probEvent (fun ω => E ω ∨ F ω) ≤ p.probEvent E + p.probEvent F := by
  classical
  have hs : (Finset.univ.filter (fun ω : Fin L → X => E ω ∨ F ω))
      = (Finset.univ.filter E) ∪ (Finset.univ.filter fun ω => ¬ E ω ∧ F ω) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  have hdisj : Disjoint (Finset.univ.filter E)
      (Finset.univ.filter fun ω : Fin L → X => ¬ E ω ∧ F ω) := by
    rw [Finset.disjoint_left]
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [Finset.mem_filter]
    intro hmem
    exact hmem.2.1 hω.2
  have hsplit : (Finset.univ.filter (fun ω : Fin L → X => E ω ∨ F ω)).sum p.probOf
      = (Finset.univ.filter E).sum p.probOf
        + (Finset.univ.filter fun ω => ¬ E ω ∧ F ω).sum p.probOf := by
    rw [hs, Finset.sum_union hdisj]
  have hle : (Finset.univ.filter fun ω : Fin L → X => ¬ E ω ∧ F ω).sum p.probOf
      ≤ (Finset.univ.filter F).sum p.probOf :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun ω hω => by
        rw [Finset.mem_filter] at hω
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hω.2.2⟩)
      (fun ω _ _ => Finset.prod_nonneg fun i _ => p.nonneg (ω i))
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  calc
    _ = _ + _ := hsplit
    _ ≤ _ + _ := add_le_add_right hle _

/-- The probability that some event in a finite indexed family occurs is at most the sum of the
individual event probabilities. -/
private theorem probEvent_exists_le {X I : Type} [Fintype X] [DecidableEq X] [Fintype I]
    {L : ℕ} (p : FinDist X) (Ev : I → (Fin L → X) → Prop) [∀ i, DecidablePred (Ev i)]
    [DecidablePred (fun ω : Fin L → X => ∃ i, Ev i ω)] :
    p.probEvent (fun ω => ∃ i, Ev i ω) ≤ ∑ i, p.probEvent (Ev i) := by
  classical
  let eqv := Fintype.equivFin I
  have hpred : ∀ ω : Fin L → X,
      (∃ i : I, Ev i ω) ↔ ∃ j : Fin (Fintype.card I), Ev (eqv.symm j) ω := by
    intro ω
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨eqv i, by simpa using hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨eqv.symm j, hj⟩
  have hrewrite : p.probEvent (fun ω : Fin L → X => ∃ i : I, Ev i ω)
      = p.probEvent (fun ω : Fin L → X => ∃ j, Ev (eqv.symm j) ω) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    apply Finset.sum_congr
    · ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpred ω
    · intro ω _
      rfl
  calc
    p.probEvent (fun ω => ∃ i : I, Ev i ω)
      = p.probEvent (fun ω => ∃ j : Fin (Fintype.card I), Ev (eqv.symm j) ω) := hrewrite
    _ ≤ ∑ j : Fin (Fintype.card I), p.probEvent (Ev (eqv.symm j)) :=
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.union_bound p (fun j : Fin (Fintype.card I) => Ev (eqv.symm j))
    _ = ∑ i : I, p.probEvent (Ev i) :=
      eqv.symm.sum_comp (fun i : I => p.probEvent (Ev i))

/-- With a correct character kernel table, an element survives decoding exactly when every
sampled character evaluates to one on it. -/
theorem tableCandidate_mem_iff {m : ℕ} (tab : G → G → Bool) (e : G ≃ AddChar G ℂ)
    (htab : ∀ a y, tab a y = true ↔ e a y = 1) (xs : Fin m → G) (x : G) :
    x ∈ (tableKernelDecode tab (List.ofFn xs)).1 ↔ ∀ i, e (xs i) x = 1 := by
  rw [mem_tableKernelDecode, forall_mem_ofFn]
  constructor
  · intro h i
    exact (htab (xs i) x).1 (h i)
  · intro h i
    exact (htab (xs i) x).2 (h i)

/-- If every sampled character annihilates `H`, every element of `H` survives decoding with a
correct character kernel table. -/
theorem tableCandidate_contains_of_supported {m : ℕ} (tab : G → G → Bool)
    (e : G ≃ AddChar G ℂ) (htab : ∀ a y, tab a y = true ↔ e a y = 1) (xs : Fin m → G)
    (H : AddSubgroup G) (hsupported : ∀ i, e (xs i) ∈ characterAnnihilator H) (x : G)
    (hx : x ∈ H) : x ∈ (tableKernelDecode tab (List.ofFn xs)).1 := by
  rw [tableCandidate_mem_iff tab e htab xs x]
  intro i
  exact (mem_characterAnnihilator H (e (xs i))).1 (hsupported i) ⟨x, hx⟩

/-- For an oracle hiding `H`, the probability that any independent Fourier record labels a
character outside the annihilator of `H` is zero. -/
theorem tableGroupRecordDist_unsupported_eq_zero {m : ℕ} (f : G → R) (e : G ≃ AddChar G ℂ)
    (H : AddSubgroup G) (hf : HidesSubgroup f H) :
    (tableGroupRecordDist f e).probEvent
      (fun xs : Fin m → G => ∃ i, e (xs i) ∉ characterAnnihilator H) = 0 := by
  classical
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  apply Finset.sum_eq_zero
  intro xs hxs
  have hex : ∃ i, e (xs i) ∉ characterAnnihilator H := by
    rw [Finset.mem_filter] at hxs
    exact hxs.2
  obtain ⟨i, hi⟩ := hex
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf,
      Finset.prod_eq_zero (Finset.mem_univ i)]
  have hz : (tableGroupRecordDist f e).prob (xs i) = 0 := by
    show (hiddenSubgroupSampleDist f e).prob (e (xs i)) = 0
    rw [hiddenSubgroupSampleDist_prob f H hf e, ite_eq_right hi]
  simp [hz]

omit [DecidableEq G] in

/-- Every element outside `H` is separated from `H` by a character that annihilates `H` but does
not take value one on that element. -/
private theorem exists_annihilator_not_killing (H : AddSubgroup G) (x : G) (hx : x ∉ H) :
    ∃ χ : AddChar G ℂ, χ ∈ characterAnnihilator H ∧ χ x ≠ 1 := by
  classical
  have h1 : AddChar.doubleDualEmb x ∉ characterAnnihilator (characterAnnihilator H) := by
    intro hmem
    exact hx ((doubleDualEmb_mem_characterAnnihilator_characterAnnihilator_iff H x).mp hmem)
  by_contra hcon
  refine h1 ((mem_characterAnnihilator (characterAnnihilator H)
    (AddChar.doubleDualEmb x)).2 ?_)
  intro χ
  rw [AddChar.doubleDualEmb_apply]
  have h3 : ¬ ((χ : AddChar G ℂ) x ≠ 1) := fun h => hcon ⟨χ, χ.property, h⟩
  exact Classical.byContradiction fun h => h3 h

/-- For an element outside `H`, at most half of the characters in the annihilator of `H` take
value one on that element. -/
private theorem card_killers_le_half (H : AddSubgroup G) (x : G) (hx : x ∉ H) :
    2 * (Finset.univ.filter fun χ : AddChar G ℂ =>
      χ ∈ characterAnnihilator H ∧ χ x = 1).card ≤ Fintype.card (characterAnnihilator H) := by
  classical
  obtain ⟨χ₀, hχ₀, hχ₀x⟩ := exists_annihilator_not_killing H x hx
  set S : Finset (AddChar G ℂ) := Finset.univ.filter fun χ =>
    χ ∈ characterAnnihilator H ∧ χ x = 1 with hSdef
  set T : Finset (AddChar G ℂ) := Finset.univ.filter fun χ =>
    χ ∈ characterAnnihilator H ∧ χ x ≠ 1 with hTdef
  have hmemT : ∀ χ ∈ S, χ₀ * χ ∈ T := by
    intro χ hχ
    rw [Finset.mem_filter] at hχ ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [mem_characterAnnihilator]
      intro y
      rw [AddChar.mul_apply, (mem_characterAnnihilator H χ₀).1 hχ₀ y,
        (mem_characterAnnihilator H χ).1 hχ.2.1 y, mul_one]
    · intro hcon
      have h2 : χ₀ x * χ x = 1 := hcon
      rw [hχ.2.2, mul_one] at h2
      exact hχ₀x h2
  have hinj : Function.Injective (fun χ : AddChar G ℂ => χ₀ * χ) := by
    intro c d hcd
    exact mul_left_cancel hcd
  have hsplit : S ∪ T = Finset.univ.filter fun χ : AddChar G ℂ =>
      χ ∈ characterAnnihilator H := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hSdef, hTdef]
    tauto
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro χ hχS
    rw [Finset.mem_filter] at hχS
    rw [Finset.mem_filter]
    intro hmem
    exact hmem.2.2 hχS.2.2
  have hcardST : S.card + T.card = Fintype.card (characterAnnihilator H) := by
    have h1 : S.card + T.card = (S ∪ T).card := (Finset.card_union_of_disjoint hdisj).symm
    rw [h1, hsplit]
    exact card_filter_eq_card_subtype (fun χ : AddChar G ℂ => χ ∈ characterAnnihilator H)
  have hcardImg : (S.image fun χ : AddChar G ℂ => χ₀ * χ).card = S.card :=
    Finset.card_image_of_injective S hinj
  have hsub : S.image (fun χ : AddChar G ℂ => χ₀ * χ) ⊆ T := by
    intro χ hχ
    rw [Finset.mem_image] at hχ
    obtain ⟨c, hc1, hc2⟩ := hχ
    rw [← hc2]
    exact hmemT c hc1
  have hle : S.card ≤ T.card := by
    rw [← hcardImg]
    exact Finset.card_le_card hsub
  omega

/-- For an oracle hiding `H`, the probability that a sampled character takes value one on a
fixed element outside `H` is at most one half. -/
private theorem killer_mass_le_half (f : G → R) (e : G ≃ AddChar G ℂ) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (x : G) (hx : x ∉ H) :
    (∑ χ : AddChar G ℂ,
      (hiddenSubgroupSampleDist f e).prob χ * (if χ x = 1 then (1 : ℝ) else 0))
      ≤ (2 : ℝ)⁻¹ := by
  classical
  have hsum : (∑ χ : AddChar G ℂ,
        (hiddenSubgroupSampleDist f e).prob χ * (if χ x = 1 then (1 : ℝ) else 0))
      = (Finset.univ.filter fun χ : AddChar G ℂ => χ ∈ characterAnnihilator H ∧ χ x = 1).card
        * (1 / (Fintype.card (characterAnnihilator H) : ℝ)) := by
    have h1 : (∑ χ : AddChar G ℂ,
          (hiddenSubgroupSampleDist f e).prob χ * (if χ x = 1 then (1 : ℝ) else 0))
        = (Finset.univ.filter fun χ : AddChar G ℂ =>
          χ ∈ characterAnnihilator H ∧ χ x = 1).sum
            (fun _ => (1 / (Fintype.card (characterAnnihilator H) : ℝ))) := by
      calc
        _ = ∑ χ : AddChar G ℂ,
            (if χ ∈ characterAnnihilator H ∧ χ x = 1
              then (1 / (Fintype.card (characterAnnihilator H) : ℝ)) else (0 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro χ _
            rw [hiddenSubgroupSampleDist_prob f H hf e]
            by_cases h1' : χ ∈ characterAnnihilator H
            · by_cases h2' : χ x = 1 <;> simp [h1', h2']
            · simp [h1']
        _ = _ := (Finset.sum_filter (fun χ : AddChar G ℂ =>
            χ ∈ characterAnnihilator H ∧ χ x = 1)
            (fun _ => (1 / (Fintype.card (characterAnnihilator H) : ℝ)))).symm
    rw [h1, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hhalf := card_killers_le_half H x hx
  have hreal : 2 * ((Finset.univ.filter
      (fun χ : AddChar G ℂ => χ ∈ characterAnnihilator H ∧ χ x = 1)).card : ℝ)
      ≤ (Fintype.card (characterAnnihilator H) : ℝ) := by
    exact_mod_cast hhalf
  have hpos : (0 : ℝ) < (Fintype.card (characterAnnihilator H) : ℝ) := by
    exact_mod_cast (Fintype.card_pos)
  have hdiv : ((Finset.univ.filter
      (fun χ : AddChar G ℂ => χ ∈ characterAnnihilator H ∧ χ x = 1)).card : ℝ) *
      (1 / (Fintype.card (characterAnnihilator H) : ℝ)) ≤ (1 / 2 : ℝ) := by
    rw [one_div]
    exact (div_le_iff₀ hpos).2 (by linarith)
  have hone : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [hone]
  exact hdiv

/-- The sample budget `k + Nat.clog 2 N` for reducing the union bound over `N` candidates to
`2⁻ᵏ`. -/
def tableRecoverySamples (N k : ℕ) : ℕ := k + Nat.clog 2 N

end Qatlib.Concepts.HspRecovery.BackendAudit

namespace Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open Matrix
open scoped Classical

variable {G R : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- For a correct character table and oracle hiding `H`, a fixed element outside `H` survives
decoding `m` independent Fourier records with probability at most `2⁻ᵐ`. -/
theorem character_table_false_candidate_fresh_probability (f : G → R) (e : G ≃ AddChar G ℂ)
    (tab : G → G → Bool) (H : AddSubgroup G) (m : ℕ) (x : G) (hf : HidesSubgroup f H)
    (htab : ∀ a y, tab a y = true ↔ e a y = 1) (hx : x ∉ H) :
    (tableGroupRecordDist f e).probEvent
        (fun xs : Fin m → G => x ∈ (tableKernelDecode tab (List.ofFn xs)).1) ≤ ((2 : ℝ)⁻¹)^m := by
  classical
  have hset : (Finset.univ.filter
        (fun xs : Fin m → G => x ∈ (tableKernelDecode tab (List.ofFn xs)).1))
      = Finset.univ.filter (fun xs : Fin m → G => ∀ i, e (xs i) x = 1) := by
    ext xs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [tableCandidate_mem_iff tab e htab xs x]
  have hrewrite : (tableGroupRecordDist f e).probEvent
        (fun xs : Fin m → G => x ∈ (tableKernelDecode tab (List.ofFn xs)).1)
      = ∑ xs ∈ Finset.univ.filter (fun xs : Fin m → G => ∀ i, e (xs i) x = 1),
          (tableGroupRecordDist f e).probOf xs := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    rw [hset]
  rw [hrewrite]
  have hprod := Qatlib.Concepts.HspRecovery.Distinguisher.FinDist.sum_probOf_forall_eq_pow (tableGroupRecordDist f e)
    (fun a : G => e a x = 1) m
  rw [hprod]
  have hfilter : (∑ a ∈ Finset.univ.filter (fun a : G => e a x = 1),
        (tableGroupRecordDist f e).prob a)
      = ∑ a : G, (tableGroupRecordDist f e).prob a * (if e a x = 1 then (1 : ℝ) else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : e a x = 1 <;> simp [h]
  have hrelabel : (∑ a : G, (tableGroupRecordDist f e).prob a *
        (if e a x = 1 then (1 : ℝ) else 0))
      = ∑ χ : AddChar G ℂ,
        (hiddenSubgroupSampleDist f e).prob χ * (if χ x = 1 then (1 : ℝ) else 0) := by
    exact e.sum_comp (fun χ => (hiddenSubgroupSampleDist f e).prob χ *
      (if χ x = 1 then (1 : ℝ) else 0))
  rw [hfilter, hrelabel]
  have hnonneg : 0 ≤ ∑ χ : AddChar G ℂ,
      (hiddenSubgroupSampleDist f e).prob χ * (if χ x = 1 then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun χ _ => by
      by_cases h : χ x = 1
      · rw [ite_eq_left h]
        exact mul_nonneg ((hiddenSubgroupSampleDist f e).nonneg χ) (by norm_num)
      · rw [ite_eq_right h]
        exact mul_nonneg ((hiddenSubgroupSampleDist f e).nonneg χ) (by norm_num)
  exact pow_le_pow_left₀ hnonneg (killer_mass_le_half f e H hf x hx) m

/-- For a correct character kernel table and an oracle hiding `H`, decoding `m` independent
Fourier records recovers `H` with probability at least `1 - card G * 2⁻ᵐ` [Lomont2004]. -/
theorem character_table_actual_subgroup_recovery_probability (f : G → R)
    (e : G ≃ AddChar G ℂ) (tab : G → G → Bool) (H : AddSubgroup G) (m : ℕ)
    (hf : HidesSubgroup f H) (htab : ∀ a y, tab a y = true ↔ e a y = 1) :
    1 - (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹)^m ≤
      (tableGroupRecordDist f e).probEvent (fun xs : Fin m → G =>
        ((tableKernelDecode tab (List.ofFn xs)).1 : Set G) = (H : Set G)) := by
  classical
  set p := tableGroupRecordDist f e with hp
  set ok : (Fin m → G) → Prop := fun xs =>
    ((tableKernelDecode tab (List.ofFn xs)).1 : Set G) = (H : Set G) with hok
  have htot : p.probEvent ok + p.probEvent (fun xs : Fin m → G => ¬ ok xs) = 1 := by
    have hsplit : p.probEvent ok + p.probEvent (fun xs : Fin m → G => ¬ ok xs)
        = ∑ xs : Fin m → G, p.probOf xs := by
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
      rw [Finset.sum_filter_add_sum_filter_not]
    rw [hsplit]
    exact Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf p m
  have hcover : ∀ xs : Fin m → G, ¬ ok xs →
      (∃ x : G, x ∉ H ∧ x ∈ (tableKernelDecode tab (List.ofFn xs)).1) ∨
        (∃ i, e (xs i) ∉ characterAnnihilator H) := by
    intro xs hxs
    by_cases hex : ∃ i, e (xs i) ∉ characterAnnihilator H
    · exact Or.inr hex
    · have hsupported : ∀ i, e (xs i) ∈ characterAnnihilator H := by
        intro i
        by_contra hcon
        exact hex ⟨i, hcon⟩
      have hle : ∀ x, x ∈ H → x ∈ (tableKernelDecode tab (List.ofFn xs)).1 :=
        fun x hx => tableCandidate_contains_of_supported tab e htab xs H hsupported x hx
      by_cases hEq : ((tableKernelDecode tab (List.ofFn xs)).1 : Set G) = (H : Set G)
      · exact (hxs hEq).elim
      · refine Or.inl ?_
        have hex : ∃ x : G, x ∈ (tableKernelDecode tab (List.ofFn xs)).1 ∧ x ∉ H := by
          by_contra hcon
          have hsub : ∀ y : G, y ∈ (tableKernelDecode tab (List.ofFn xs)).1 → y ∈ H := by
            intro y hy
            by_contra hyH
            exact hcon ⟨y, hy, hyH⟩
          exact hEq (Set.ext_iff.mpr fun y => ⟨hsub y, fun hyH => hle y hyH⟩)
        obtain ⟨x, hx1, hx2⟩ := hex
        exact ⟨x, hx2, hx1⟩
  have hfail : p.probEvent (fun xs : Fin m → G => ¬ ok xs)
      ≤ (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹)^m := by
    have hmono : p.probEvent (fun xs : Fin m → G => ¬ ok xs) ≤
        p.probEvent (fun xs : Fin m → G =>
          (∃ x : G, x ∉ H ∧ x ∈ (tableKernelDecode tab (List.ofFn xs)).1) ∨
            (∃ i, e (xs i) ∉ characterAnnihilator H)) :=
      probEvent_mono p (fun xs : Fin m → G => ¬ ok xs)
        (fun xs : Fin m → G =>
          (∃ x : G, x ∉ H ∧ x ∈ (tableKernelDecode tab (List.ofFn xs)).1) ∨
            (∃ i, e (xs i) ∉ characterAnnihilator H))
        fun xs hxs => hcover xs hxs
    have hsub := probEvent_union_le p
      (fun xs : Fin m → G => ∃ x : G, x ∉ H ∧ x ∈ (tableKernelDecode tab (List.ofFn xs)).1)
      (fun xs : Fin m → G => ∃ i, e (xs i) ∉ characterAnnihilator H)
    have hnul : p.probEvent (fun xs : Fin m → G => ∃ i, e (xs i) ∉ characterAnnihilator H) = 0 :=
      tableGroupRecordDist_unsupported_eq_zero f e H hf
    have hrewrite : p.probEvent (fun xs : Fin m → G =>
          ∃ x : G, x ∉ H ∧ x ∈ (tableKernelDecode tab (List.ofFn xs)).1)
        = p.probEvent (fun xs : Fin m → G =>
          ∃ x : {x : G // x ∉ H}, x.1 ∈ (tableKernelDecode tab (List.ofFn xs)).1) := by
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
      apply Finset.sum_congr
      · ext xs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, hx, hxc⟩
          exact ⟨⟨x, hx⟩, hxc⟩
        · rintro ⟨x, hxc⟩
          exact ⟨x.1, x.2, hxc⟩
      · intro xs _
        rfl
    have hunion := probEvent_exists_le p
      (fun x : {x : G // x ∉ H} => fun xs : Fin m → G =>
        x.1 ∈ (tableKernelDecode tab (List.ofFn xs)).1)
    have hterm : ∀ x : {x : G // x ∉ H},
        p.probEvent (fun xs : Fin m → G => x.1 ∈ (tableKernelDecode tab (List.ofFn xs)).1)
          ≤ ((2 : ℝ)⁻¹)^m := by
      intro x
      exact character_table_false_candidate_fresh_probability f e tab H m x.1 hf htab x.2
    have hsumle : (∑ x : {x : G // x ∉ H},
          p.probEvent (fun xs : Fin m → G =>
            x.1 ∈ (tableKernelDecode tab (List.ofFn xs)).1))
        ≤ (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹)^m := by
      calc
        (∑ x : {x : G // x ∉ H}, p.probEvent (fun xs : Fin m → G =>
            x.1 ∈ (tableKernelDecode tab (List.ofFn xs)).1))
            ≤ ∑ _x : {x : G // x ∉ H}, ((2 : ℝ)⁻¹)^m := Finset.sum_le_sum fun x _ => hterm x
        _ = (Fintype.card {x : G // x ∉ H} : ℝ) * ((2 : ℝ)⁻¹)^m := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹)^m := by
          refine mul_le_mul_of_nonneg_right (by
            exact_mod_cast (Fintype.card_le_of_injective
              (fun x : {x : G // x ∉ H} => x.1) fun a b hab => Subtype.ext hab)) (by positivity)
    calc
      p.probEvent (fun xs : Fin m → G => ¬ ok xs)
          ≤ p.probEvent (fun xs : Fin m → G =>
            (∃ x : G, x ∉ H ∧ x ∈ (tableKernelDecode tab (List.ofFn xs)).1) ∨
              (∃ i, e (xs i) ∉ characterAnnihilator H)) := hmono
      _ ≤ p.probEvent (fun xs : Fin m → G =>
            ∃ x : G, x ∉ H ∧ x ∈ (tableKernelDecode tab (List.ofFn xs)).1) +
          p.probEvent (fun xs : Fin m → G => ∃ i, e (xs i) ∉ characterAnnihilator H) := hsub
      _ = p.probEvent (fun xs : Fin m → G =>
            ∃ x : G, x ∉ H ∧ x ∈ (tableKernelDecode tab (List.ofFn xs)).1) := by
        rw [hnul, add_zero]
      _ = p.probEvent (fun xs : Fin m → G =>
            ∃ x : {x : G // x ∉ H}, x.1 ∈ (tableKernelDecode tab (List.ofFn xs)).1) := hrewrite
      _ ≤ ∑ x : {x : G // x ∉ H}, p.probEvent (fun xs : Fin m → G =>
          x.1 ∈ (tableKernelDecode tab (List.ofFn xs)).1) := hunion
      _ ≤ (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹)^m := hsumle
  calc
    1 - (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹)^m
        ≤ 1 - p.probEvent (fun xs : Fin m → G => ¬ ok xs) := by linarith
    _ = p.probEvent ok := by linarith

/-- The computed sample budget is `k + Nat.clog 2 N`; for positive `N`, it satisfies `(N : ℝ) *
(1 / 2) ^ tableRecoverySamples N k ≤ (1 / 2) ^ k` [Lomont2004]. -/
theorem character_table_computed_sample_budget (N k : ℕ) :
    tableRecoverySamples N k = k + Nat.clog 2 N ∧
      (0 < N → (N : ℝ) * ((2 : ℝ)⁻¹)^(tableRecoverySamples N k) ≤ ((2 : ℝ)⁻¹)^k) := by
  constructor
  · rfl
  · intro hN
    have hclog : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (b := 2) (by norm_num) N
    have hreal : (N : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 N := by exact_mod_cast hclog
    have hpos : (0 : ℝ) < (2 : ℝ) ^ Nat.clog 2 N := by positivity
    have hdiv : (N : ℝ) / (2 : ℝ) ^ Nat.clog 2 N ≤ 1 :=
      (div_le_iff₀ hpos).2 (by simpa using hreal)
    have hmain : (N : ℝ) * ((2 : ℝ)⁻¹)^Nat.clog 2 N ≤ 1 := by
      have h1 : (N : ℝ) * ((2 : ℝ)⁻¹)^Nat.clog 2 N
          = (N : ℝ) / (2 : ℝ) ^ Nat.clog 2 N := by
        rw [div_eq_mul_inv, inv_pow]
      rw [h1]
      exact hdiv
    have hkey : (N : ℝ) * ((2 : ℝ)⁻¹)^k * ((2 : ℝ)⁻¹)^Nat.clog 2 N ≤ ((2 : ℝ)⁻¹)^k := by
      calc
        (N : ℝ) * ((2 : ℝ)⁻¹)^k * ((2 : ℝ)⁻¹)^Nat.clog 2 N
            = ((N : ℝ) * ((2 : ℝ)⁻¹)^Nat.clog 2 N) * ((2 : ℝ)⁻¹)^k := by ring
        _ ≤ 1 * ((2 : ℝ)⁻¹)^k := mul_le_mul_of_nonneg_right hmain (by positivity)
        _ = ((2 : ℝ)⁻¹)^k := one_mul _
    rw [tableRecoverySamples, pow_add]
    simpa [mul_assoc] using hkey

end Qatlib.Concepts.HspRecovery.BackendAudit
