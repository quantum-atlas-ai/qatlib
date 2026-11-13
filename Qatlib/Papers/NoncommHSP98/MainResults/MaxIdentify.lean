/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoncommHSP98.MainResults.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.CastCard

/-!
# Identification by maximal sampled statistics

This module derives exponential tail estimates for bounded statistics and combines them with
finite union bounds. If one canonical candidate has expectation at least one half and every
other candidate has expectation zero, `max_identifies` shows that sufficiently many independent
samples make it the unique maximizing candidate. `theorem5_holds` specializes this result to the
dihedral cosine statistics. This development accompanies [EttingerHoyer1999].

## Main statements

* `tail_lower` and `tail_upper`: exponential bounds at the threshold `m / 4`.
* `max_identifies`: unique maximization with probability at least `1 - 1 / (2 * N)`.
* `theorem5_holds`: the dihedral cosine identification statement.

## References

* [Ettinger and Hoyer, 1999][EttingerHoyer1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

namespace Qatlib.Papers.NoncommHSP98.MainResults

/-- The mass of an event under a finite distribution, using classical decidability for the event
predicate. -/
noncomputable def evMass {X : Type*} [Fintype X] (p : FinDist X) (E : X → Prop) : ℝ :=
  @eventMass X _ p E (Classical.decPred E)

/-- The probability of a tuple event is independent of the chosen decision procedure for its
predicate. -/
theorem probEvent_inst_eq {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    {m : ℕ} (E : (Fin m → X) → Prop) (i1 i2 : DecidablePred E) :
    @probEvent X _ m p E i1 = @probEvent X _ m p E i2 := by
  have hi : i1 = i2 := funext fun x => Subsingleton.elim _ _
  exact congrArg (fun i => @probEvent X _ m p E i) hi

/-- Inclusion of events implies monotonicity of `eventMass` with the supplied decision
procedures. -/
theorem em_mono {X : Type*} [Fintype X] (p : FinDist X) {E F : X → Prop}
    (hE : DecidablePred E) (hF : DecidablePred F) (h : ∀ x, E x → F x) :
    @eventMass X _ p E hE ≤ @eventMass X _ p F hF := by
  classical
  unfold eventMass
  have hsub : Finset.univ.filter E ⊆ Finset.univ.filter F := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => p.nonneg x)

/-- The mass of the union of two events is at most the sum of their masses. -/
theorem em_or_le {X : Type*} [Fintype X] (p : FinDist X) (E F : X → Prop)
    (hE : DecidablePred E) (hF : DecidablePred F) (hEF : DecidablePred (fun x => E x ∨ F x)) :
    @eventMass X _ p (fun x => E x ∨ F x) hEF ≤ @eventMass X _ p E hE + @eventMass X _ p F hF := by
  classical
  unfold eventMass
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf]
  linarith [p.nonneg x]

/-- The mass of the complement of an event is one minus its mass. -/
theorem em_compl {X : Type*} [Fintype X] (p : FinDist X) (E : X → Prop)
    (hE : DecidablePred E) (hNE : DecidablePred (fun x => ¬ E x)) :
    @eventMass X _ p (fun x => ¬ E x) hNE = 1 - @eventMass X _ p E hE := by
  classical
  unfold eventMass
  have hsplit :=
      Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset X)) (p := E) (f := p.prob)
  rw [p.sum_one] at hsplit
  linarith

/-- The classical event mass of a complement is one minus the original event mass. -/
theorem evMass_compl {X : Type*} [Fintype X] (p : FinDist X) (E : X → Prop) :
    evMass p (fun x => ¬ E x) = 1 - evMass p E := by
  unfold evMass
  exact em_compl p E (Classical.decPred E) (Classical.decPred (fun x => ¬ E x))

/-- Classical event mass is monotone under event inclusion. -/
theorem evMass_mono {X : Type*} [Fintype X] (p : FinDist X) {E F : X → Prop}
    (h : ∀ x, E x → F x) : evMass p E ≤ evMass p F := by
  unfold evMass
  exact em_mono p (Classical.decPred E) (Classical.decPred F) h

/-- The classical mass of a union of two events is at most the sum of their masses. -/
theorem evMass_or_le {X : Type*} [Fintype X] (p : FinDist X) (E F : X → Prop) :
    evMass p (fun x => E x ∨ F x) ≤ evMass p E + evMass p F := by
  unfold evMass
  exact em_or_le p E F (Classical.decPred E) (Classical.decPred F)
    (Classical.decPred (fun x => E x ∨ F x))

/-- The mass of a union indexed by a finite set is at most the sum of its event masses. -/
theorem evMass_exists_le_sum_finset {X : Type*} [Fintype X] (p : FinDist X)
    {ι : Type*} (K : Finset ι) (E : ι → X → Prop) :
    evMass p (fun x => ∃ i ∈ K, E i x) ≤ ∑ i ∈ K, evMass p (E i) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
      unfold evMass
      simp [eventMass]
  | insert a K ha ih =>
      have hpred : (fun x => ∃ i ∈ insert a K, E i x)
          = (fun x => E a x ∨ ∃ i ∈ K, E i x) := by
        funext x
        apply propext
        constructor
        · rintro ⟨i, hi, hEi⟩
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · exact Or.inl hEi
          · exact Or.inr ⟨i, hi, hEi⟩
        · rintro (h | ⟨i, hi, hEi⟩)
          · exact ⟨a, Finset.mem_insert_self a K, h⟩
          · exact ⟨i, Finset.mem_insert_of_mem hi, hEi⟩
      unfold evMass
      rw [hpred, Finset.sum_insert ha]
      refine le_trans (em_or_le p (E a) (fun x => ∃ i ∈ K, E i x)
        (Classical.decPred (E a))
        (Classical.decPred (fun x => ∃ i ∈ K, E i x))
        (Classical.decPred (fun x => E a x ∨ ∃ i ∈ K, E i x))) ?_
      exact add_le_add_right ih _

/-- For positive `m`, independent samples of a statistic in `[-1, 1]` with mean at least one
half have sum at most `m / 4` with probability at most `exp (-m / 32)`. -/
theorem tail_lower {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) (hmean : (1 : ℝ) / 2 ≤ p.expect f) :
    probEvent (L := m) p (fun ω : Fin m → X => ∑ i, f (ω i) ≤ (m : ℝ) / 4)
      ≤ Real.exp (-(m : ℝ) / 32) := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmeanprod : (independent (fun _ : Fin m => p)).expect
      (weightedSum (fun _ : Fin m => (1 : ℝ)) (fun (_ : Fin m) (x : X) => f x))
      = (m : ℝ) * p.expect f := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hS : (0 : ℝ) < ∑ _ : Fin m, (1 : ℝ) ^ 2 * ((1 : ℝ) - (-1)) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    norm_num
    positivity
  have hH := independent_weighted_hoeffding_signed
    (fun _ : Fin m => p) (fun _ : Fin m => (1 : ℝ))
    (fun (_ : Fin m) (x : X) => f x)
    (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ((m : ℝ) / 4) (-1)
    (fun _ => by norm_num) (fun _ x => hf x) (by positivity) (by norm_num) hS
  have himp : ∀ ω : Fin m → X,
      (∑ i, f (ω i) ≤ (m : ℝ) / 4) →
      ((m : ℝ) / 4 ≤ (-1 : ℝ) *
        (weightedSum (fun _ : Fin m => (1 : ℝ))
          (fun (_ : Fin m) (x : X) => f x) ω
         - (independent (fun _ : Fin m => p)).expect
            (weightedSum (fun _ : Fin m => (1 : ℝ))
              (fun (_ : Fin m) (x : X) => f x)))) := by
    intro ω hω
    have hW : weightedSum (fun _ : Fin m => (1 : ℝ))
        (fun (_ : Fin m) (x : X) => f x) ω = ∑ i, f (ω i) := by
      simp [weightedSum]
    have hmul : (m : ℝ) * (1 / 2) ≤ (m : ℝ) * p.expect f :=
      mul_le_mul_of_nonneg_left hmean hmpos.le
    rw [hW, hmeanprod]
    linarith
  rw [probEvent_eq_eventMass_independent p
    (fun ω : Fin m → X => ∑ i, f (ω i) ≤ (m : ℝ) / 4)]
  refine le_trans (le_trans (eventMass_mono _ himp) hH) (le_of_eq ?_)
  congr 1
  rw [show (∑ _ : Fin m, (1 : ℝ) ^ 2 * ((1 : ℝ) - (-1)) ^ 2) = 4 * (m : ℝ) from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring]
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  field_simp
  ring

/-- For positive `m`, independent samples of a statistic in `[-1, 1]` with mean zero have sum at
least `m / 4` with probability at most `exp (-m / 32)`. -/
theorem tail_upper {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) (hmean : p.expect f = 0) :
    probEvent (L := m) p (fun ω : Fin m → X => (m : ℝ) / 4 ≤ ∑ i, f (ω i))
      ≤ Real.exp (-(m : ℝ) / 32) := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmeanprod : (independent (fun _ : Fin m => p)).expect
      (weightedSum (fun _ : Fin m => (1 : ℝ)) (fun (_ : Fin m) (x : X) => f x)) = 0 := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    simp [hmean]
  have hS : (0 : ℝ) < ∑ _ : Fin m, (1 : ℝ) ^ 2 * ((1 : ℝ) - (-1)) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    norm_num
    positivity
  have hH := independent_weighted_hoeffding_signed
    (fun _ : Fin m => p) (fun _ : Fin m => (1 : ℝ))
    (fun (_ : Fin m) (x : X) => f x)
    (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ((m : ℝ) / 4) 1
    (fun _ => by norm_num) (fun _ x => hf x) (by positivity) (by norm_num) hS
  have hEv : eventMass (independent (fun _ : Fin m => p))
      (fun ω : Fin m → X => (m : ℝ) / 4 ≤ ∑ i, f (ω i))
      = eventMass (independent (fun _ : Fin m => p))
        (fun ω : Fin m → X => (m : ℝ) / 4 ≤ (1 : ℝ) *
          (weightedSum (fun _ : Fin m => (1 : ℝ))
            (fun (_ : Fin m) (x : X) => f x) ω
           - (independent (fun _ : Fin m => p)).expect
              (weightedSum (fun _ : Fin m => (1 : ℝ))
                (fun (_ : Fin m) (x : X) => f x)))) := by
    apply eventMass_congr
    intro ω
    have hW : weightedSum (fun _ : Fin m => (1 : ℝ))
        (fun (_ : Fin m) (x : X) => f x) ω = ∑ i, f (ω i) := by
      simp [weightedSum]
    rw [hW, hmeanprod]
    simp
  rw [probEvent_eq_eventMass_independent p
    (fun ω : Fin m → X => (m : ℝ) / 4 ≤ ∑ i, f (ω i)), hEv]
  refine le_trans hH (le_of_eq ?_)
  congr 1
  rw [show (∑ _ : Fin m, (1 : ℝ) ^ 2 * ((1 : ℝ) - (-1)) ^ 2) = 4 * (m : ℝ) from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring]
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  field_simp
  ring

/-- The canonical signed representative of `k0` is either `k0` or `-k0`. -/
theorem kRep_eq_or (N : ℕ) [NeZero N] (k0 : ZMod N) :
    kRep N k0 = k0 ∨ kRep N k0 = -k0 := by
  unfold kRep
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The canonical signed representative of a nonzero residue is nonzero. -/
theorem kRep_ne_zero {N : ℕ} [NeZero N] {k0 : ZMod N} (hk0 : k0 ≠ 0) :
    kRep N k0 ≠ 0 := by
  rcases kRep_eq_or N k0 with h | h
  · rw [h]; exact hk0
  · rw [h]; exact neg_ne_zero.mpr hk0

/-- The canonical signed representative of a nonzero residue belongs to `Candidates N`. -/
theorem kRep_mem_Candidates {N : ℕ} [NeZero N] {k0 : ZMod N} (hk0 : k0 ≠ 0) :
    kRep N k0 ∈ Candidates N := by
  classical
  unfold Candidates
  rw [Finset.mem_filter]
  constructor
  · exact Finset.mem_univ _
  · unfold kRep
    by_cases hle : k0.val ≤ N / 2
    · rw [if_pos hle]
      exact ⟨ZMod.val_pos.mpr hk0, hle⟩
    · rw [if_neg hle]
      haveI : NeZero k0 := ⟨hk0⟩
      rw [ZMod.val_neg_of_ne_zero (a := k0)]
      have hlt : k0.val < N := ZMod.val_lt k0
      constructor
      · omega
      · omega

/-- Every candidate residue is nonzero. -/
theorem candidate_ne_zero {N : ℕ} [NeZero N] {k : ZMod N}
    (hk : k ∈ Candidates N) : k ≠ 0 := by
  classical
  unfold Candidates at hk
  rw [Finset.mem_filter] at hk
  intro h
  have hv : k.val = 0 := by rw [h]; exact ZMod.val_zero
  omega

/-- A candidate different from `kRep N k0` is also different from `k0`. -/
theorem candidate_ne_kRep {N : ℕ} [NeZero N] {k0 k : ZMod N} (_hk0 : k0 ≠ 0)
    (hk : k ∈ Candidates N) (hne : k ≠ kRep N k0) :
    k ≠ k0 := by
  classical
  intro h
  have hC := hk
  unfold Candidates at hC
  rw [Finset.mem_filter] at hC
  have hkval : k0.val ≤ N / 2 := by rw [← h]; exact hC.2.2
  unfold kRep at hne
  rw [if_pos hkval] at hne
  exact hne h

/-- A candidate different from `kRep N k0` is also different from `-k0`, provided `k0` is
nonzero. -/
theorem candidate_ne_neg_kRep {N : ℕ} [NeZero N] {k0 k : ZMod N} (hk0 : k0 ≠ 0)
    (hk : k ∈ Candidates N) (hne : k ≠ kRep N k0) :
    k ≠ -k0 := by
  classical
  intro h
  have hC := hk
  unfold Candidates at hC
  rw [Finset.mem_filter] at hC
  have hkval : k.val ≤ N / 2 := hC.2.2
  by_cases hle : k0.val ≤ N / 2
  · have hr : kRep N k0 = k0 := by unfold kRep; rw [if_pos hle]
    rw [hr] at hne
    haveI : NeZero k0 := ⟨hk0⟩
    have hnegval : (-k0).val = N - k0.val := ZMod.val_neg_of_ne_zero (a := k0)
    have hval : k.val = N - k0.val := by rw [h, hnegval]
    have hkey : N - k0.val ≤ N / 2 := by rw [← hval]; exact hkval
    have hlt : k0.val < N := ZMod.val_lt k0
    have hcancel : N - k0.val = N / 2 := by omega
    have hveq : (-k0).val = k0.val := by
      rw [hnegval, hcancel]
      omega
    have heq : -k0 = k0 := ZMod.val_injective N hveq
    exact hne (by rw [h, heq])
  · have hr : kRep N k0 = -k0 := by unfold kRep; rw [if_neg hle]
    exact hne (by rw [h, hr])

/-- There are at most `N / 2` candidate residues. -/
theorem Candidates_card_le (N : ℕ) [NeZero N] :
    (Candidates N).card ≤ N / 2 := by
  classical
  have hinj : Function.Injective (fun k : ZMod N => k.val) := ZMod.val_injective N
  have hsub : (Candidates N).image (fun k : ZMod N => k.val) ⊆ Finset.Icc 1 (N / 2) := by
    intro v hv
    obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp hv
    rw [← hkv]
    unfold Candidates at hk
    rw [Finset.mem_filter] at hk
    exact Finset.mem_Icc.mpr ⟨hk.2.1, hk.2.2⟩
  calc (Candidates N).card = ((Candidates N).image (fun k : ZMod N => k.val)).card := by
        rw [Finset.card_image_of_injective _ hinj]
    _ ≤ (Finset.Icc 1 (N / 2)).card := Finset.card_le_card hsub
    _ = N / 2 := by
        rw [Nat.card_Icc]
        omega

/-- For `N ≥ 2`, nonzero `k0`, and positive `m ≥ 64 * log N`, bounded candidate statistics with
mean at least one half at `kRep N k0` and mean zero elsewhere have a unique sample-sum
maximum there with probability at least `1 - 1 / (2 * N)`. This is the probabilistic
identification step for Theorem 5 of [EttingerHoyer1999]. -/
theorem max_identifies {X : Type*} [Fintype X] [DecidableEq X]
    (N : ℕ) [NeZero N] (k0 : ZMod N) (hk0 : k0 ≠ 0)
    (p : FinDist X) (stat : ZMod N → X → ℝ)
    (hstat : ∀ k x, stat k x ∈ Set.Icc (-1 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) (h2N : 2 ≤ N) (hm64 : 64 * Real.log N ≤ (m : ℝ))
    (hgood : (1 : ℝ) / 2 ≤ p.expect (stat (kRep N k0)))
    (hbad : ∀ k, k ∈ Candidates N → k ≠ kRep N k0 → p.expect (stat k) = 0) :
    1 - 1 / (2 * (N : ℝ)) ≤ evMass (independent (fun _ : Fin m => p))
      (fun ω : Fin m → X =>
        ∀ k ∈ Candidates N, k ≠ kRep N k0 →
          ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i)) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h2N)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast h2N)
  have hrC : kRep N k0 ∈ Candidates N := kRep_mem_Candidates hk0

  have hexp : Real.exp (-(m : ℝ) / 32) ≤ 1 / ((N : ℝ) ^ 2) := by
    have hm32 : (2 : ℝ) * Real.log N ≤ (m : ℝ) / 32 := by linarith
    have h1 : Real.exp (-(m : ℝ) / 32) ≤ Real.exp (-(2 * Real.log N)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h2 : Real.exp (-(2 * Real.log N)) = 1 / ((N : ℝ) ^ 2) := by
      have hsq : Real.exp (-(2 * Real.log N)) = Real.exp (-(Real.log N)) ^ 2 := by
        rw [show -(2 * Real.log N) = ((2 : ℕ) : ℝ) * (-(Real.log N)) from by
          push_cast
          ring]
        exact Real.exp_nat_mul (-(Real.log N)) 2
      rw [hsq, Real.exp_neg, Real.exp_log hNpos, inv_pow, one_div]
    rwa [h2] at h1
  have hexp_nonneg : 0 ≤ Real.exp (-(m : ℝ) / 32) := (Real.exp_pos _).le

  have hcard : ((Candidates N).card : ℝ) ≤ (N : ℝ) / 2 := by
    have h1 : ((Candidates N).card : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
      exact_mod_cast Candidates_card_le N
    have h2 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
    linarith

  let q : FinDist (Fin m → X) := independent (fun _ : Fin m => p)
  let A : (Fin m → X) → Prop := fun ω => ∑ i, stat (kRep N k0) (ω i) ≤ (m : ℝ) / 4
  let B : ZMod N → (Fin m → X) → Prop := fun k ω =>
      (m : ℝ) / 4 ≤ ∑ i, stat k (ω i)
  have hfail : ∀ ω : Fin m → X,
      ¬ (∀ k ∈ Candidates N, k ≠ kRep N k0 →
          ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i)) →
      A ω ∨ ∃ k ∈ (Candidates N).erase (kRep N k0), B k ω := by
    intro ω hω
    by_contra hcon
    push Not at hcon
    apply hω
    intro k hkC hkr
    have hkK : k ∈ (Candidates N).erase (kRep N k0) := by
      rw [Finset.mem_erase]
      exact ⟨hkr, hkC⟩
    have hBk : ¬ B k ω := hcon.2 k hkK
    have hltk : ∑ i, stat k (ω i) < (m : ℝ) / 4 := lt_of_not_ge hBk
    have hAr : ¬ A ω := hcon.1
    have hgtr : (m : ℝ) / 4 < ∑ i, stat (kRep N k0) (ω i) := lt_of_not_ge hAr
    linarith

  have hA : evMass q A ≤ Real.exp (-(m : ℝ) / 32) := by
    have h := tail_lower p (stat (kRep N k0)) (fun x => hstat (kRep N k0) x) hm hgood
    have hbridge : probEvent (L := m) p
        (fun ω : Fin m → X => ∑ i, stat (kRep N k0) (ω i) ≤ (m : ℝ) / 4)
        = evMass (independent (fun _ : Fin m => p))
            (fun ω : Fin m → X => ∑ i, stat (kRep N k0) (ω i) ≤ (m : ℝ) / 4) := by
      unfold evMass
      exact probEvent_eq_eventMass_independent p _
    rw [hbridge] at h
    exact h
  have hBk : ∀ k ∈ (Candidates N).erase (kRep N k0),
      evMass q (B k) ≤ Real.exp (-(m : ℝ) / 32) := by
    intro k hk
    rw [Finset.mem_erase] at hk
    have hkr : k ≠ kRep N k0 := hk.1
    have hkC : k ∈ Candidates N := hk.2
    have h := tail_upper p (stat k) (fun x => hstat k x) hm (hbad k hkC hkr)
    have hbridge : probEvent (L := m) p
        (fun ω : Fin m → X => (m : ℝ) / 4 ≤ ∑ i, stat k (ω i))
        = evMass (independent (fun _ : Fin m => p))
            (fun ω : Fin m → X => (m : ℝ) / 4 ≤ ∑ i, stat k (ω i)) := by
      unfold evMass
      exact probEvent_eq_eventMass_independent p _
    rw [hbridge] at h
    exact h

  have hb : evMass q (fun ω => ∃ k ∈ (Candidates N).erase (kRep N k0), B k ω)
      ≤ ((Candidates N).card : ℝ) * Real.exp (-(m : ℝ) / 32) - Real.exp (-(m : ℝ) / 32) := by
    refine le_trans (evMass_exists_le_sum_finset q ((Candidates N).erase (kRep N k0)) B) ?_
    calc (∑ k ∈ (Candidates N).erase (kRep N k0), evMass q (B k))
        ≤ ∑ k ∈ (Candidates N).erase (kRep N k0), Real.exp (-(m : ℝ) / 32) := by
          apply Finset.sum_le_sum
          exact hBk
      _ = (((Candidates N).erase (kRep N k0)).card : ℝ) * Real.exp (-(m : ℝ) / 32) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((Candidates N).card : ℝ) * Real.exp (-(m : ℝ) / 32)
            - Real.exp (-(m : ℝ) / 32) := by
          rw [Finset.cast_card_erase_of_mem hrC]
          ring

  have hfailbound : evMass q (fun ω => ¬ (∀ k ∈ Candidates N, k ≠ kRep N k0 →
      ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i))) ≤ 1 / (2 * (N : ℝ)) := by
    have hmono : evMass q (fun ω => ¬ (∀ k ∈ Candidates N, k ≠ kRep N k0 →
          ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i)))
        ≤ evMass q (fun ω => A ω ∨ ∃ k ∈ (Candidates N).erase (kRep N k0), B k ω) :=
      evMass_mono q (fun ω hω => hfail ω hω)
    have hor : evMass q (fun ω => A ω ∨ ∃ k ∈ (Candidates N).erase (kRep N k0), B k ω)
        ≤ evMass q A
          + evMass q (fun ω => ∃ k ∈ (Candidates N).erase (kRep N k0), B k ω) :=
      evMass_or_le q A (fun ω => ∃ k ∈ (Candidates N).erase (kRep N k0), B k ω)
    calc evMass q (fun ω => ¬ (∀ k ∈ Candidates N, k ≠ kRep N k0 →
          ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i)))
        ≤ evMass q A
            + evMass q (fun ω => ∃ k ∈ (Candidates N).erase (kRep N k0), B k ω) :=
          le_trans hmono hor
      _ ≤ Real.exp (-(m : ℝ) / 32)
            + (((Candidates N).card : ℝ) * Real.exp (-(m : ℝ) / 32)
              - Real.exp (-(m : ℝ) / 32)) := add_le_add hA hb
      _ = ((Candidates N).card : ℝ) * Real.exp (-(m : ℝ) / 32) := by ring
      _ ≤ ((N : ℝ) / 2) * (1 / ((N : ℝ) ^ 2)) := by
          apply mul_le_mul hcard hexp hexp_nonneg (by positivity)
      _ = 1 / (2 * (N : ℝ)) := by
          field_simp

  have hcompl : evMass q (fun ω => ∀ k ∈ Candidates N, k ≠ kRep N k0 →
        ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i))
      = 1 - evMass q (fun ω => ¬ (∀ k ∈ Candidates N, k ≠ kRep N k0 →
          ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i))) := by
    unfold evMass
    have h := em_compl q (fun ω => ∀ k ∈ Candidates N, k ≠ kRep N k0 →
          ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i))
      (Classical.decPred _) (Classical.decPred _)
    linarith
  have hgoal : 1 - 1 / (2 * (N : ℝ)) ≤ evMass q (fun ω => ∀ k ∈ Candidates N,
      k ≠ kRep N k0 → ∑ i, stat k (ω i) < ∑ i, stat (kRep N k0) (ω i)) := by
    rw [hcompl]
    linarith [hfailbound]
  exact hgoal

/-- The cosine statistic at `kRep N k0` strictly exceeds every other candidate statistic with
the probability and sample bound encoded by `Theorem5Statement`. See Theorem 5 of
[EttingerHoyer1999]. -/
theorem theorem5_holds : Theorem5Statement := by
  intro N _ h2N k0 hk0 m hm64
  have hmpos : 0 < m := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h2N)
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast h2N)
    have hpos : (0 : ℝ) < 64 * Real.log N := by positivity
    have : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hpos hm64
    exact_mod_cast this
  let pred : (Fin m → ZMod N) → Prop := fun ω =>
    ∀ k ∈ Candidates N, k ≠ kRep N k0 →
      ∑ i, cosPhase N k (ω i) < ∑ i, cosPhase N (kRep N k0) (ω i)
  have hmain : 1 - 1 / (2 * (N : ℝ)) ≤
      evMass (independent (fun _ : Fin m => zLaw N k0)) pred := by
    refine max_identifies N k0 hk0 (zLaw N k0) (cosPhase N)
      (fun k x => cosPhase_mem_Icc (N := N) k x) hmpos h2N hm64 ?_ ?_
    · show (1 : ℝ) / 2 ≤ ∑ z : ZMod N, zMass N k0 z * cosPhase N (kRep N k0) z
      exact expect_cosPhase_ge_half hk0 (kRep_eq_or N k0)
    · intro k hkC hne
      have hk0' : k ≠ 0 := candidate_ne_zero hkC
      have hkp : k ≠ k0 := candidate_ne_kRep hk0 hkC hne
      have hkm : k ≠ -k0 := candidate_ne_neg_kRep hk0 hkC hne
      show ∑ z : ZMod N, zMass N k0 z * cosPhase N k z = 0
      exact expect_cosPhase_eq_zero hk0' hkp hkm
  calc 1 - 1 / (2 * (N : ℝ))
      ≤ evMass (independent (fun _ : Fin m => zLaw N k0)) pred := hmain
    _ = @probEvent (ZMod N) _ m (zLaw N k0) pred (Classical.decPred pred) := by
        unfold evMass
        exact (@probEvent_eq_eventMass_independent (ZMod N) _ _ (zLaw N k0) m pred
          (Classical.decPred pred)).symm
    _ = probEvent (zLaw N k0) pred :=
        probEvent_inst_eq (zLaw N k0) pred (Classical.decPred pred) _

end Qatlib.Papers.NoncommHSP98.MainResults
