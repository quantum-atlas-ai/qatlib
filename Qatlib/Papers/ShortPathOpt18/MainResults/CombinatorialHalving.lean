/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Qatlib.Papers.ShortPathOpt18.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Combinatorial and Diagonal-Hamiltonian Ground-State Degeneracy Halving

This module formalizes Appendix A (Lemmas 13 and 14) of Hastings on slicing any finite
configuration set `S ⊆ {0, 1}^N` (`|S| > 1`) by a single coordinate sign to at most half
its size, iterating at most `⌊log₂ |S|⌋` times to reach a singleton, and lifting the
halving chain to a sparse `{-1, 0, 1}` single-qubit `Z` perturbation isolating a unique
ground state of any integer-spectrum diagonal Hamiltonian.

## Main definitions

* `halveStep`: one coordinate-halving step on `Finset (Config N)`.
* `zOf`, `zPerturbation`, `perturbedEnergy`, `IsGroundSet`: diagonal `Z`-perturbation model.

## Main statements

* `source_lemma13`, `source_lemma13_slice_exists`: Lemma 13, existence of a non-empty half-size coordinate slice.
* `source_lemma14_halving`: Lemma 14 (combinatorial form), logarithmic-length halving chain to a singleton.
* `source_lemma14_hamiltonian`: Lemma 14 (Hamiltonian form), unique ground state via `≤ log₂ |S|` `Z`-terms.

## References

* [Hastings, 2018][Hastings2018ShortPath], Appendix A, Lemmas 13 and 14, pp. 21--22.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ShortPathOpt18.MainResults

/- ## Lemma 13 -/

/-- Source Lemma 13, p. 21: for any `S` of basis states with `1 < |S|` there is
a coordinate `i : Fin N` and a sign `σ : Bool` such that the slice
`T = {v ∈ S | v i = σ}` is nonempty and has at most half the cardinality of
`S`.  (The paper writes `{−1,+1}^N`; here `true`/`false` are the two signs.) -/
theorem source_lemma13 {N : ℕ} (S : Finset (Config N)) (hS : 1 < S.card) :
    ∃ (i : Fin N) (σ : Bool),
      1 ≤ (S.filter fun v => v i = σ).card ∧
        (S.filter fun v => v i = σ).card ≤ S.card / 2 := by
  classical
  by_contra h
  push Not at h
  -- For every coordinate, one of the two sign slices is empty.
  have hstep : ∀ i : Fin N,
      (S.filter fun v => v i = true).card = 0 ∨
        (S.filter fun v => v i = false).card = 0 := by
    intro i
    have hsum : (S.filter fun v => v i = true).card +
        (S.filter fun v => v i = false).card = S.card := by
      have h' := Finset.card_filter_add_card_filter_not (s := S)
        (p := fun v : Config N => v i = true)
      simpa using h'
    by_cases ha : 1 ≤ (S.filter fun v => v i = true).card
    · have ha' : S.card / 2 < (S.filter fun v => v i = true).card :=
        h i true ha
      by_cases hb : 1 ≤ (S.filter fun v => v i = false).card
      · have hb' : S.card / 2 < (S.filter fun v => v i = false).card :=
          h i false hb
        have hm := Nat.div_add_mod S.card 2
        omega
      · right
        omega
    · left
      omega
  -- A slice that is empty gives a fixed value of the coordinate on all of `S`.
  have hz : ∀ (p : Config N → Prop) [DecidablePred p], (S.filter p).card = 0 →
      ∀ v ∈ S, ¬ p v := by
    intro p _ h0 v hv hp
    have hmem : v ∈ S.filter p := Finset.mem_filter.mpr ⟨hv, hp⟩
    rw [Finset.card_eq_zero.mp h0] at hmem
    exact absurd hmem (Finset.notMem_empty v)
  obtain ⟨v0, hv0⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  -- Hence all elements of `S` agree with `v0` in every coordinate.
  have hconst : ∀ v ∈ S, v = v0 := by
    intro v hv
    funext i
    rcases hstep i with h0 | h0
    · have hv' : v i = false := by
        cases hvi : v i
        · rfl
        · exact absurd hvi (hz (p := fun v => v i = true) h0 v hv)
      have hv0' : v0 i = false := by
        cases hvi : v0 i
        · rfl
        · exact absurd hvi (hz (p := fun v => v i = true) h0 v0 hv0)
      rw [hv', hv0']
    · have hv' : v i = true := by
        cases hvi : v i
        · exact absurd hvi (hz (p := fun v => v i = false) h0 v hv)
        · rfl
      have hv0' : v0 i = true := by
        cases hvi : v0 i
        · exact absurd hvi (hz (p := fun v => v i = false) h0 v0 hv0)
        · rfl
      rw [hv', hv0']
  have hcard : S.card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => by rw [hconst a ha, hconst b hb])
  omega

/-- Slice form of Lemma 13: the slice itself is a subset of `S` with the two
cardinality bounds.  This is only a repackaging of `source_lemma13` and is the
form used to build the halving chain of Lemma 14. -/
theorem source_lemma13_slice_exists {N : ℕ} (S : Finset (Config N))
    (hS : 1 < S.card) :
    ∃ T : Finset (Config N), T ⊆ S ∧ 1 ≤ T.card ∧ T.card ≤ S.card / 2 := by
  obtain ⟨i, σ, h1, h2⟩ := source_lemma13 S hS
  exact ⟨S.filter (fun v => v i = σ), Finset.filter_subset _ _, h1, h2⟩

/- ## Lemma 14 (combinatorial core) -/

/-- One halving step: if `S` has more than one element, replace it by the slice
given by Lemma 13; otherwise keep `S`. -/
def halveStep {N : ℕ} (S : Finset (Config N)) : Finset (Config N) :=
  if h : 1 < S.card then Classical.choose (source_lemma13_slice_exists S h) else S

/-- The halving step is monotone: it returns a subset. -/
theorem halveStep_subset {N : ℕ} (S : Finset (Config N)) : halveStep S ⊆ S := by
  classical
  unfold halveStep
  by_cases h : 1 < S.card
  · simpa [h] using (Classical.choose_spec (source_lemma13_slice_exists S h)).1
  · simp [h]

/-- The halving step at least halves the cardinality when the set has more than
one element. -/
theorem halveStep_card_le {N : ℕ} (S : Finset (Config N)) (h : 1 < S.card) :
    (halveStep S).card ≤ S.card / 2 := by
  classical
  unfold halveStep
  simpa [h] using (Classical.choose_spec (source_lemma13_slice_exists S h)).2.2

/-- The halving step preserves nonemptiness. -/
theorem halveStep_nonempty {N : ℕ} (S : Finset (Config N)) (h : S.Nonempty) :
    (halveStep S).Nonempty := by
  classical
  unfold halveStep
  by_cases hh : 1 < S.card
  · have h1 : 1 ≤ (Classical.choose (source_lemma13_slice_exists S hh)).card :=
      (Classical.choose_spec (source_lemma13_slice_exists S hh)).2.1
    simpa [hh] using Finset.card_pos.mp (by omega :
      0 < (Classical.choose (source_lemma13_slice_exists S hh)).card)
  · simpa [hh] using h

/-- When `S` is already a singleton the halving step does nothing. -/
theorem halveStep_eq_self {N : ℕ} (S : Finset (Config N)) (h : ¬ 1 < S.card) :
    halveStep S = S := by
  unfold halveStep
  simp [h]

/-- Source Lemma 14 (combinatorial form), p. 21: from any nonempty set `S` of
basis states one can choose a sequence `Sseq 0 = S, Sseq 1, …, Sseq m` such that
`m ≤ log₂ |S|`, `|Sseq m| = 1`, and for every `a < m` the next set is a
nonempty subset of the previous one with at most half its cardinality:
`1 ≤ |Sseq (a+1)| ≤ |Sseq a| / 2`.

This is the counting content of Lemma 14; the paper realises each slice as the
ground-state set of `H^(a+1) = H^(a) − σ Z_i`, which is stated separately in
`source_lemma14_hamiltonian`. -/
theorem source_lemma14_halving {N : ℕ} (S : Finset (Config N)) (hS : S.Nonempty) :
    ∃ (m : ℕ) (Sseq : ℕ → Finset (Config N)),
      m ≤ Nat.log2 S.card ∧ Sseq 0 = S ∧ (Sseq m).card = 1 ∧
        ∀ a, a < m → Sseq (a + 1) ⊆ Sseq a ∧
          (Sseq (a + 1)).Nonempty ∧ (Sseq (a + 1)).card ≤ (Sseq a).card / 2 := by
  classical
  let Sseq : ℕ → Finset (Config N) :=
    fun a => Nat.rec S (fun _ T => halveStep T) a
  have hSseq_zero : Sseq 0 = S := rfl
  have hSseq_succ : ∀ a, Sseq (a + 1) = halveStep (Sseq a) := fun _ => rfl
  have hne : ∀ a, (Sseq a).Nonempty := by
    intro a
    induction a with
    | zero => exact hS
    | succ k ih => exact halveStep_nonempty (Sseq k) ih
  -- Cardinality bound: after `a` steps the size is at most `|S| / 2^a`.
  have hbound : ∀ a, a ≤ Nat.log2 S.card → (Sseq a).card ≤ S.card / 2 ^ a := by
    intro a
    induction a with
    | zero =>
        intro _
        rw [hSseq_zero]
        simp
    | succ k ih =>
        intro hk
        have hk' : k ≤ Nat.log2 S.card := by omega
        have hprev := ih hk'
        rw [hSseq_succ k]
        by_cases hbig : 1 < (Sseq k).card
        · calc (halveStep (Sseq k)).card ≤ (Sseq k).card / 2 := halveStep_card_le _ hbig
            _ ≤ (S.card / 2 ^ k) / 2 := Nat.div_le_div_right hprev
            _ = S.card / 2 ^ (k + 1) := by
                rw [Nat.div_div_eq_div_mul, pow_succ]
        · rw [halveStep_eq_self _ hbig]
          have hcard1 : (Sseq k).card = 1 := by
            have := (hne k).card_pos
            omega
          rw [hcard1]
          have hpow : 2 ^ (k + 1) ≤ S.card := by
            have h1 : 2 ^ (k + 1) ≤ 2 ^ Nat.log2 S.card :=
              Nat.pow_le_pow_right (by norm_num) hk
            have h2 : 2 ^ Nat.log2 S.card ≤ S.card := by
              have := Nat.pow_log_le_self 2 (by have := hS.card_pos; omega : S.card ≠ 0)
              simpa [Nat.log2_eq_log_two] using this
            omega
          exact (Nat.one_le_div_iff (by positivity : 0 < 2 ^ (k + 1))).mpr hpow
  -- At `a = log₂ |S|` the bound reads `|Sseq a| ≤ 1`.
  have hlog : (Sseq (Nat.log2 S.card)).card ≤ 1 := by
    have hb := hbound (Nat.log2 S.card) le_rfl
    have hdiv : S.card / 2 ^ Nat.log2 S.card = 1 := by
      refine Nat.div_eq_of_lt_le (k := 1) (n := 2 ^ Nat.log2 S.card) (m := S.card) ?_ ?_
      · have := Nat.pow_log_le_self 2 (by have := hS.card_pos; omega : S.card ≠ 0)
        simpa [Nat.log2_eq_log_two] using this
      · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) S.card
        have heq : (1 + 1) * 2 ^ Nat.log2 S.card = 2 ^ (Nat.log 2 S.card).succ := by
          rw [Nat.log2_eq_log_two, pow_succ]
          ring
        rw [heq]
        exact h
    rw [hdiv] at hb
    exact hb
  have hex : ∃ a, (Sseq a).card = 1 := by
    refine ⟨Nat.log2 S.card, le_antisymm hlog ?_⟩
    have := (hne (Nat.log2 S.card)).card_pos
    omega
  let m := Nat.find hex
  have hpos : 1 ≤ (Sseq (Nat.log2 S.card)).card := by
    have := (hne (Nat.log2 S.card)).card_pos
    omega
  have hm_le : m ≤ Nat.log2 S.card :=
    Nat.find_min' hex (le_antisymm hlog hpos)
  have hm_card : (Sseq m).card = 1 := Nat.find_spec hex
  refine ⟨m, Sseq, hm_le, hSseq_zero, hm_card, ?_⟩
  intro a ha
  have hne1 : ¬ (Sseq a).card = 1 := Nat.find_min hex ha
  have hbig : 1 < (Sseq a).card := by
    have := (hne a).card_pos
    omega
  rw [hSseq_succ a]
  exact ⟨halveStep_subset _, halveStep_nonempty _ (hne a), halveStep_card_le _ hbig⟩

/- ## Lemma 14 (Hamiltonian form) -/

/-- The diagonal `Z`-perturbation `∑ᵢ hᵢ Zᵢ` evaluated on a basis state, with
`hᵢ ∈ {−1,0,1}`.  The paper writes `vᵢ ∈ {−1,+1}`; here `zOf b = 1` for
`true` and `−1` for `false`. -/
def zOf (b : Bool) : ℝ := if b then 1 else -1

/-- Value of `∑ᵢ hᵢ Zᵢ` on the basis state `v`. -/
def zPerturbation {N : ℕ} (h : Fin N → ℝ) (v : Config N) : ℝ :=
  ∑ i, h i * zOf (v i)

/-- The modified diagonal Hamiltonian `H_Z + ∑ᵢ hᵢ Zᵢ` evaluated on `v`. -/
def perturbedEnergy {N : ℕ} (energy : Config N → ℝ) (h : Fin N → ℝ)
    (v : Config N) : ℝ :=
  energy v + zPerturbation h v

/-- `S` is precisely the ground-state set of `H_Z` with ground energy `E0`. -/
def IsGroundSet {N : ℕ} (energy : Config N → ℝ) (E0 : ℝ) (S : Finset (Config N)) :
    Prop :=
  (∀ v, v ∈ S ↔ energy v = E0) ∧ ∀ v, E0 ≤ energy v

/-- Repeated coordinate slices isolate one configuration with logarithmically many signs. -/
private theorem isolating_coordinates {N : ℕ} (T : Finset (Config N))
    (hT : T.Nonempty) :
    ∃ (I : Finset (Fin N)) (σ : Fin N → Bool) (v : Config N),
      I.card ≤ Nat.log2 T.card ∧
        (∀ w : Config N, (w ∈ T ∧ ∀ i ∈ I, w i = σ i) ↔ w = v) ∧
          ∀ i ∈ I, v i = σ i := by
  classical
  induction hcard : T.card using Nat.strongRecOn generalizing T with
  | ind n ih =>
    by_cases hbig : 1 < T.card
    · obtain ⟨i₀, σ₀, hpos, hhalf⟩ := source_lemma13 T hbig
      let T₁ := T.filter fun w => w i₀ = σ₀
      change 1 ≤ T₁.card at hpos
      change T₁.card ≤ T.card / 2 at hhalf
      have hT₁ : T₁.Nonempty := Finset.card_pos.mp (by omega)
      have hlt : T₁.card < T.card :=
        lt_of_le_of_lt hhalf (Nat.div_lt_self (by omega) (by decide))
      obtain ⟨I₁, σ₁, v, hI₁, hisolate, hsign⟩ :=
        ih T₁.card (by omega) T₁ hT₁ rfl
      have hv := (hisolate v).mpr rfl
      have hv₀ : v i₀ = σ₀ := (Finset.mem_filter.mp hv.1).2
      let σ := Function.update σ₁ i₀ σ₀
      have hσ₀ : σ i₀ = σ₀ := by simp [σ]
      have hσ₁ : ∀ i ∈ I₁, σ i = σ₁ i := by
        intro i hi
        by_cases heq : i = i₀
        · subst i
          rw [hσ₀, ← hsign i₀ hi, hv₀]
        · simp [σ, heq]
      refine ⟨insert i₀ I₁, σ, v, ?_, ?_, ?_⟩
      · have hlog : Nat.log2 T₁.card + 1 ≤ Nat.log2 T.card := by
          apply (Nat.le_log2 (by omega : T.card ≠ 0)).mpr
          calc
            2 ^ (Nat.log2 T₁.card + 1) = 2 ^ Nat.log2 T₁.card * 2 := pow_succ _ _
            _ ≤ T₁.card * 2 := Nat.mul_le_mul_right 2
              (Nat.log2_self_le (by have := hT₁.card_pos; omega))
            _ ≤ T.card := by omega
        rw [hcard] at hlog
        exact (Finset.card_insert_le _ _).trans ((Nat.add_le_add_right hI₁ 1).trans hlog)
      · intro w
        constructor
        · rintro ⟨hw, hmatch⟩
          apply (hisolate w).mp
          refine ⟨Finset.mem_filter.mpr ⟨hw, ?_⟩, ?_⟩
          · simpa only [hσ₀] using hmatch i₀ (Finset.mem_insert_self _ _)
          · intro i hi
            rw [← hσ₁ i hi]
            exact hmatch i (Finset.mem_insert_of_mem hi)
        · intro hw
          subst w
          refine ⟨Finset.mem_of_mem_filter v hv.1, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hv₀.trans hσ₀.symm
          · exact (hsign i hi).trans (hσ₁ i hi).symm
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hv₀.trans hσ₀.symm
        · exact (hsign i hi).trans (hσ₁ i hi).symm
    · have hone : T.card = 1 := by have := hT.card_pos; omega
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      exact ⟨∅, fun _ => true, v, by simp, by simp, by simp⟩

/-- Source Lemma 14 (Hamiltonian form), p. 21: if `H_Z` has integer energies,
ground energy `E0` and ground-state set `S` of cardinality `ngs`, then there is
`h : Fin N → {−1,0,1}` supported on at most `log₂ ngs` coordinates such that
`H_Z + ∑ᵢ hᵢ Zᵢ` has a unique ground state, and that ground state is also a
ground state of `H_Z`.

Repeated applications of Lemma 13 select coordinates and signs isolating one
element of `S`.  Set `hᵢ = −zOf σᵢ` on those coordinates and zero elsewhere.
The selected element attains the minimum of every perturbation term.  Any
other element of `S` has a strictly larger term, while integer energies put
every element outside `S` at least one unit above `E0`. -/
theorem source_lemma14_hamiltonian {N : ℕ} (energy : Config N → ℝ) (E0 : ℝ)
    (S : Finset (Config N)) (hint : ∀ v, ∃ k : ℤ, energy v = k)
    (hground : IsGroundSet energy E0 S) (hne : S.Nonempty) :
    ∃ h : Fin N → ℝ,
      (∀ i, h i = -1 ∨ h i = 0 ∨ h i = 1) ∧
        Fintype.card {i : Fin N // h i ≠ 0} ≤ Nat.log2 S.card ∧
          ∃ v : Config N,
            v ∈ S ∧
              (∀ w, perturbedEnergy energy h v ≤ perturbedEnergy energy h w) ∧
                ∀ w, perturbedEnergy energy h w = perturbedEnergy energy h v → w = v := by
  classical
  obtain ⟨I, σ, v, hI, hisolate, hsign⟩ := isolating_coordinates S hne
  have hv : v ∈ S := ((hisolate v).mpr rfl).1
  have hev : energy v = E0 := (hground.1 v).mp hv
  obtain ⟨k₀, hk₀⟩ := hint v
  have hgap : ∀ w, w ∉ S → E0 + 1 ≤ energy w := by
    intro w hw
    obtain ⟨k, hk⟩ := hint w
    have hlt : E0 < energy w :=
      lt_of_le_of_ne (hground.2 w) (fun heq => hw ((hground.1 w).mpr heq.symm))
    have hcast : (k₀ : ℝ) < (k : ℝ) := by rw [← hk₀, ← hk]; linarith
    have hklt : k₀ < k := by exact_mod_cast hcast
    have hkstep : k₀ + 1 ≤ k := by omega
    have hcaststep : (k₀ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkstep
    rw [hk]
    linarith
  let h : Fin N → ℝ := fun i => if i ∈ I then -zOf (σ i) else 0
  have hsupport : ∀ i, h i ≠ 0 ↔ i ∈ I := by
    intro i
    by_cases hi : i ∈ I <;> cases hσ : σ i <;> simp [h, hi, hσ, zOf]
  have hpert : ∀ w, zPerturbation h w = ∑ i ∈ I, -zOf (σ i) * zOf (w i) := by
    intro w
    simp [zPerturbation, h, ite_mul]
  have hterm : ∀ (w : Config N) i, (-1 : ℝ) ≤ -zOf (σ i) * zOf (w i) := by
    intro w i
    cases σ i <;> cases w i <;> norm_num [zOf]
  have hsum : (∑ _i ∈ I, (-1 : ℝ)) = -(I.card : ℝ) := by simp
  have hlow : ∀ w, -(I.card : ℝ) ≤ zPerturbation h w := by
    intro w
    rw [hpert, ← hsum]
    exact Finset.sum_le_sum fun i _ => hterm w i
  have hpv : zPerturbation h v = -(I.card : ℝ) := by
    rw [hpert, ← hsum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsign i hi]
    cases σ i <;> norm_num [zOf]
  have hstrict : ∀ w, w ≠ v → perturbedEnergy energy h v < perturbedEnergy energy h w := by
    intro w hw
    by_cases hwS : w ∈ S
    · have hmismatch : ∃ i ∈ I, w i ≠ σ i := by
        by_contra hmatch
        push Not at hmatch
        exact hw ((hisolate w).mp ⟨hwS, hmatch⟩)
      have hplt : -(I.card : ℝ) < zPerturbation h w := by
        rw [hpert, ← hsum]
        apply Finset.sum_lt_sum (fun i _ => hterm w i)
        obtain ⟨i, hi, hne⟩ := hmismatch
        refine ⟨i, hi, ?_⟩
        cases hσ : σ i <;> cases hwi : w i <;> norm_num [zOf] at hne ⊢
        all_goals exact (hne (hwi.trans hσ.symm)).elim
      have hew : energy w = E0 := (hground.1 w).mp hwS
      simp only [perturbedEnergy, hev, hew, hpv]
      linarith
    · have hgw := hgap w hwS
      have hpw := hlow w
      simp only [perturbedEnergy, hev, hpv]
      linarith
  refine ⟨h, ?_, ?_, v, hv, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ I <;> cases hσ : σ i <;> simp [h, hi, hσ, zOf]
  · have hcard : Fintype.card {i : Fin N // h i ≠ 0} = I.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext i
      simp [hsupport]
    exact hcard.le.trans hI
  · intro w
    by_cases hw : w = v
    · subst w
      exact le_rfl
    · exact (hstrict w hw).le
  · intro w heq
    by_contra hw
    exact (ne_of_lt (hstrict w hw)) heq.symm

end Qatlib.Papers.ShortPathOpt18.MainResults
