/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.PairImageRetry
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.DistinctImageTable
variable {X R : Type} [Fintype X] [Nonempty X] [Nonempty R] [DecidableEq R]

structure Records (F : X → R) (n : ℕ) where
  entries : List (X × R)
  length_eq : entries.length = n
  distinct : (entries.map Prod.snd).Nodup
  accurate : ∀ p ∈ entries, p.2 = F p.1

def values {F : X → R} {n : ℕ} (s : Records F n) : Finset R :=
  (s.entries.map Prod.snd).toFinset

omit [Fintype X] [Nonempty X] [Nonempty R] in

theorem values_card {F : X → R} {n : ℕ} (s : Records F n) : (values s).card = n := by
  rw [values, List.toFinset_card_of_nodup s.distinct, List.length_map, s.length_eq]

omit [Nonempty X] [Nonempty R] in

theorem values_subset {F : X → R} {n : ℕ} (s : Records F n) :
    values s ⊆ Finset.univ.image F := by
  intro z hz
  obtain ⟨p, hp, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
  exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, he ▸ s.accurate p hp |>.symm⟩

def empty (F : X → R) : Records F 0 :=
  ⟨[], rfl, List.nodup_nil, by simp⟩

def insert {F : X → R} {n : ℕ} (s : Records F n) (p : X × R)
    (hp : PairImageRetry.Valid F (values s) p) : Records F (n+1) where
  entries := p :: s.entries
  length_eq := by simp [s.length_eq]
  distinct := List.nodup_cons.mpr ⟨by simpa [values] using hp.2, s.distinct⟩
  accurate := by
    intro q hq
    rcases List.mem_cons.mp hq with he | hq
    · simpa only [he] using hp.1
    · exact s.accurate q hq

def stageMean (F : X → R) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((Finset.univ.image F).card : ℝ) /
    (((Finset.univ.image F).card - n : ℕ) : ℝ))

def extend (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    {n : ℕ} (hhalf : 2*n ≤ (Finset.univ.image F).card) (s : Records F n) :
    CostedLaw (Records F (n+1)) :=
  ReturningStages.relabelSupported (PairImageRetry.returning F (values s)) fun z hz =>
    insert s z.1 (PairImageRetry.returning_valid F r hr hF (values s) (values_subset s)
      (by simpa only [values_card] using hhalf) z.1 z.2 hz)

theorem extend_expected (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    {n : ℕ} (hhalf : 2*n ≤ (Finset.univ.image F).card) (s : Records F n) :
    expectedCost (extend F r hr hF hhalf s) = stageMean F n ∧
      expectedCost (extend F r hr hF hhalf s) ≤ 2 := by
  rw [extend, ReturningStages.relabelSupported_expectedCost]
  simpa only [stageMean, values_card] using
    PairImageRetry.returning_expected F r hr hF (values s) (values_subset s)
      (by simpa only [values_card] using hhalf)

theorem extend_support (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    {n : ℕ} (hhalf : 2*n ≤ (Finset.univ.image F).card) (s : Records F n)
    (t : Records F (n+1)) (c : ℕ) (hm : extend F r hr hF hhalf s (t,c) ≠ 0) :
    ∃ p, PairImageRetry.returning F (values s) (p,c) ≠ 0 ∧
      t.entries = p :: s.entries := by
  obtain ⟨z, hz, ht, hc⟩ := ReturningStages.relabelSupported_support _ _ t c hm
  refine ⟨z.1, ?_, ?_⟩
  · simpa only [hc] using! hz
  · rw [ht]
    rfl

def build (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r) :
    (n : ℕ) → 2*n ≤ (Finset.univ.image F).card → CostedLaw (Records F n)
  | 0, _ => CostedLaw.ret (empty F)
  | n+1, hn => CostedLaw.bind (build F r hr hF n (by omega))
      (extend F r hr hF (by omega))

theorem build_expected (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    (n : ℕ) (hn : 2*n ≤ (Finset.univ.image F).card) :
    expectedCost (build F r hr hF n hn) = ∑ j ∈ Finset.range n, stageMean F j := by
  induction n with
  | zero => simp [build]
  | succ n ih =>
    rw [build, expectedCost_bind, ih, Finset.sum_range_succ]
    congr 1
    have he : (fun z : Records F n × ℕ => expectedCost
        (extend F r hr hF (by omega) z.1)) = fun _ => stageMean F n := by
      funext z
      exact (extend_expected F r hr hF (by omega) z.1).1
    rw [he, expectation_const]

omit [Nonempty R] in

theorem stageMean_bounds (F : X → R) (n : ℕ)
    (hn : 2*n ≤ (Finset.univ.image F).card) : 1 ≤ stageMean F n ∧ stageMean F n ≤ 2 := by
  let m := (Finset.univ.image F).card
  have hm : 0 < m := Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hnm : n ≤ m := by dsimp [m]; omega
  have hgap : 0 < m-n := by omega
  have hgR : (0:ℝ) < (m-n:ℕ) := by exact_mod_cast hgap
  have hhalfR : (2:ℝ)*n ≤ m := by exact_mod_cast hn
  have hdiv : (1:ℝ) ≤ (m:ℝ)/((m-n:ℕ):ℝ) ∧ (m:ℝ)/((m-n:ℕ):ℝ) ≤ 2 := by
    constructor
    · apply (le_div_iff₀ hgR).mpr
      rw [Nat.cast_sub hnm]
      simp only [one_mul]
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · apply (div_le_iff₀ hgR).mpr
      rw [Nat.cast_sub hnm]
      linarith
  constructor
  · simpa only [stageMean, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hdiv.1
  · simpa only [stageMean, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hdiv.2

theorem build_query_bounds (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    (k : ℕ) (hk : 2*k ≤ (Finset.univ.image F).card) :
    (k : ℝ≥0∞) ≤ expectedCost (build F r hr hF k hk) ∧
      expectedCost (build F r hr hF k hk) ≤ 2*k := by
  rw [build_expected]
  constructor
  · calc
      (k : ℝ≥0∞) = ∑ _j ∈ Finset.range k, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ j ∈ Finset.range k, stageMean F j := by
        apply Finset.sum_le_sum
        intro j hj
        exact (stageMean_bounds F j (by have := Finset.mem_range.mp hj; omega)).1
  · calc
      (∑ j ∈ Finset.range k, stageMean F j) ≤ ∑ _j ∈ Finset.range k, (2 : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (stageMean_bounds F j (by have := Finset.mem_range.mp hj; omega)).2
      _ = 2*k := by simp [mul_comm]

theorem build_records (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    (k : ℕ) (hk : 2*k ≤ (Finset.univ.image F).card)
    (s : Records F k) (c : ℕ) (_hm : build F r hr hF k hk (s,c) ≠ 0) :
    s.entries.length = k ∧ (s.entries.map Prod.snd).Nodup ∧
      (∀ p ∈ s.entries, p.2 = F p.1) ∧ (values s).card = k :=
  ⟨s.length_eq, s.distinct, s.accurate, values_card s⟩

end Qatlib.Papers.CollisionProb97.MainResults.DistinctImageTable
