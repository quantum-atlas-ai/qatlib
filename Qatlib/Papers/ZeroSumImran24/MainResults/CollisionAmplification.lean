/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Claim c010 — Proposition 5 of Imran--Ivanyos.

Fixed source version: arXiv:2304.08376v1 (17 Apr 2023).
Proposition 5, §5, p.16; proof pp.16--17.

Statement (paper): Suppose there is an algorithm `B` that, given a set of
vectors from `Z_p^n` of size `S±(p,n)`, finds a collision. Then there is a
deterministic procedure that, given `S±(p,n)^{⌈log p⌉}` vectors, finds a
nontrivial zero-sum subset using fewer than `S±(p,n)^{⌈log p⌉}` applications of
`B` and `poly((S±)^{⌈log p⌉})` other operations.

A "collision" is a pair of disjoint subset sums with equal value, not both
empty (§5). The proof iterates: find one collision per block of `S` vectors to
obtain equal-sum pairs, collect `S` such sums and collide them again, and so on
`⌈log p⌉` times, ending with `p` pairwise-disjoint equal-sum subsets; the union
of the first `p` is a zero sum unless one subset is empty (then any nonempty one
is a zero sum). We state the deterministic-witness conclusion; the call count
`< S^{⌈log p⌉}` is recorded explicitly and `⌈log p⌉` is `Nat.clog 2 p`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Qatlib.Papers.ZeroSumImran24.MainResults.SourceModel

/-!
# Collision Amplification to Zero-Sum Subsequences over `ℤ_p^n`

This module formalizes Section 5, Proposition 5 (p. 16) of Imran and Ivanyos,
showing that any collision finder on `S`-tuples of vectors in `ℤ_p^n` amplifies
across `⌈log₂ p⌉` tree stages to a deterministic procedure extracting a nonempty
zero-sum subsequence from any `S^{⌈log₂ p⌉}`-tuple of vectors in `ℤ_p^n`.

## Main statements

* `proposition5_collisionAmplification`: Proposition 5, tree amplification from
  signed collisions on `S` vectors to nonempty zero-sum subsequences on
  `S^{⌈log₂ p⌉}` vectors.

## References

* [Imran and Ivanyos, 2023][ImranIvanyos2023ZeroSum], Section 5, Proposition 5, pp. 16--17.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ZeroSumImran24.MainResults

private lemma disjoint_pair_of_collision
    (p n S : ℕ) (v : Fin S → ZVec p n) (σ τ : SignedSubset S)
    (h : IsCollision p n v σ τ) :
    ∃ J0 J1 : Finset (Fin S), Disjoint J0 J1 ∧
      (J0.Nonempty ∨ J1.Nonempty) ∧ (∑ i ∈ J0, v i) = ∑ i ∈ J1, v i := by
  classical
  obtain ⟨hd, hn, hv⟩ := h
  have hcoeff (i : Fin S) : ¬ (σ.coeff i ≠ 0 ∧ τ.coeff i ≠ 0) := by
    rintro ⟨hs, ht⟩
    have hi : i ∈ σ.support ∩ τ.support := by simpa using And.intro hs ht
    rw [hd] at hi
    exact Finset.notMem_empty i hi
  let J0 := Finset.univ.filter (fun i => σ.coeff i = 1 ∨ τ.coeff i = -1)
  let J1 := Finset.univ.filter (fun i => τ.coeff i = 1 ∨ σ.coeff i = -1)
  refine ⟨J0, J1, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' : σ.coeff i = 1 ∨ τ.coeff i = -1 := (Finset.mem_filter.mp hi).2
    have hj' : τ.coeff i = 1 ∨ σ.coeff i = -1 := (Finset.mem_filter.mp hj).2
    have := hcoeff i
    omega
  · rcases hn with hn | hn
    · obtain ⟨i, hi⟩ := hn
      have hs : σ.coeff i ≠ 0 := SignedSubset.mem_support.mp hi
      rcases σ.isSigned i with hs' | hs' | hs'
      · exact Or.inr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr hs'⟩⟩
      · exact False.elim (hs hs')
      · exact Or.inl ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hs'⟩⟩
    · obtain ⟨i, hi⟩ := hn
      have ht : τ.coeff i ≠ 0 := SignedSubset.mem_support.mp hi
      rcases τ.isSigned i with ht' | ht' | ht'
      · exact Or.inl ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr ht'⟩⟩
      · exact False.elim (ht ht')
      · exact Or.inr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl ht'⟩⟩
  · funext k
    have hterm (i : Fin S) :
        (if i ∈ J0 then v i k else 0) - (if i ∈ J1 then v i k else 0) =
          (σ.coeff i : ZMod p) * v i k - (τ.coeff i : ZMod p) * v i k := by
      have hi := hcoeff i
      rcases σ.isSigned i with hs | hs | hs <;>
        rcases τ.isSigned i with ht | ht | ht <;>
        simp_all [J0, J1]
    have heq := congrArg (fun w : ZVec p n => w k) hv
    change (∑ i : Fin S, (σ.coeff i : ZMod p) * v i k) =
      ∑ i : Fin S, (τ.coeff i : ZMod p) * v i k at heq
    have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hterm i)
    simp only [Finset.sum_sub_distrib, ← Finset.sum_filter] at hsum
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hsum
    have hz : (∑ i ∈ J0, v i k) - (∑ i ∈ J1, v i k) = 0 := by
      rw [hsum, heq, sub_self]
    simpa only [Finset.sum_apply] using sub_eq_zero.mp hz

private lemma tree_equal_sums
    (p n S : ℕ) (hB : HasCollisionFinder p n S) (k : ℕ)
    (v : Fin (S ^ k) → ZVec p n) :
    ∃ (F : Fin (2 ^ k) → Finset (Fin (S ^ k))) (c : ZVec p n),
      (∀ r1 r2 : Fin (2 ^ k), r1 ≠ r2 → Disjoint (F r1) (F r2)) ∧
      (∃ r : Fin (2 ^ k), (F r).Nonempty) ∧
      (∀ r : Fin (2 ^ k), ∑ i ∈ F r, v i = c) := by
  classical
  induction k with
  | zero =>
    refine ⟨fun _ => Finset.univ, ∑ i : Fin (S ^ 0), v i, ?_, ?_, ?_⟩
    · intro r1 r2 hne
      apply False.elim (hne (Fin.ext ?_))
      have h1 := r1.isLt
      have h2 := r2.isLt
      simp only [pow_zero] at h1 h2
      omega
    · exact ⟨⟨0, by simp⟩, ⟨⟨0, by simp⟩, Finset.mem_univ _⟩⟩
    · intro r
      rfl
  | succ k ih =>
    let emb (b : Fin S) (j : Fin (S ^ k)) : Fin (S ^ (k + 1)) :=
      ⟨b.val * S ^ k + j.val, by
        have hb := b.isLt
        have hj := j.isLt
        rw [Nat.pow_succ]
        nlinarith⟩
    have emb_joint {b1 b2 : Fin S} {j1 j2 : Fin (S ^ k)}
        (he : emb b1 j1 = emb b2 j2) : b1 = b2 ∧ j1 = j2 := by
      have he' : b1.val * S ^ k + j1.val = b2.val * S ^ k + j2.val :=
        congrArg Fin.val he
      have hj1 := j1.isLt
      have hj2 := j2.isLt
      have hb : b1.val = b2.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
      exact ⟨Fin.ext hb, Fin.ext (by nlinarith [he'])⟩
    let e (b : Fin S) : Fin (S ^ k) ↪ Fin (S ^ (k + 1)) :=
      ⟨emb b, fun _ _ he => (emb_joint he).2⟩
    have hex (b : Fin S) := ih (fun j => v (emb b j))
    choose Fb wb hd hn hw using hex
    obtain ⟨σ, τ, hστ⟩ := hB wb
    obtain ⟨J0, J1, hJd, hJn, hJw⟩ := disjoint_pair_of_collision p n S wb σ τ hστ
    let join (J : Finset (Fin S)) (r : Fin (2 ^ k)) :=
      J.biUnion (fun b => (Fb b r).map (e b))
    have hjoin_disjoint (J K : Finset (Fin S)) (r s : Fin (2 ^ k))
        (hsep : Disjoint J K ∨ r ≠ s) : Disjoint (join J r) (join K s) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨b', hb', hy⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨j, hj, hx⟩ := Finset.mem_map.mp hx
      obtain ⟨j', hj', hy⟩ := Finset.mem_map.mp hy
      obtain ⟨heqb, heqj⟩ := emb_joint (hx.trans hy.symm)
      subst b'
      subst j'
      rcases hsep with hsep | hsep
      · exact Finset.disjoint_left.mp hsep hb hb'
      · exact Finset.disjoint_left.mp (hd b r s hsep) hj hj'
    have hjoin_sum (J : Finset (Fin S)) (r : Fin (2 ^ k)) :
        (∑ x ∈ join J r, v x) = ∑ b ∈ J, wb b := by
      dsimp only [join]
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_map]
        exact hw b r
      · intro b hb b' hb' hne
        apply Finset.disjoint_left.mpr
        intro x hx hy
        obtain ⟨j, hj, hx⟩ := Finset.mem_map.mp hx
        obtain ⟨j', hj', hy⟩ := Finset.mem_map.mp hy
        exact hne (emb_joint (hx.trans hy.symm)).1
    have hjoin_nonempty (J : Finset (Fin S)) (hJ : J.Nonempty) :
        ∃ r : Fin (2 ^ k), (join J r).Nonempty := by
      obtain ⟨b, hb⟩ := hJ
      obtain ⟨r, j, hj⟩ := hn b
      refine ⟨r, emb b j, Finset.mem_biUnion.mpr ⟨b, hb, ?_⟩⟩
      exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
    let F (r : Fin (2 ^ (k + 1))) :=
      if hr : r.val < 2 ^ k then join J0 ⟨r.val, hr⟩
      else join J1 ⟨r.val - 2 ^ k, by
        have hrbound : r.val < 2 ^ k * 2 := by simpa only [Nat.pow_succ] using r.isLt
        omega⟩
    refine ⟨F, ∑ b ∈ J0, wb b, ?_, ?_, ?_⟩
    · intro r1 r2 hne
      by_cases h1 : r1.val < 2 ^ k <;> by_cases h2 : r2.val < 2 ^ k
      · simp only [F, h1, h2, ↓reduceDIte]
        apply hjoin_disjoint
        right
        intro he
        exact hne (Fin.ext (congrArg (fun t : Fin (2 ^ k) => t.val) he))
      · simp only [F, h1, h2, ↓reduceDIte]
        exact hjoin_disjoint _ _ _ _ (Or.inl hJd)
      · simp only [F, h1, h2, ↓reduceDIte]
        exact hjoin_disjoint _ _ _ _ (Or.inl hJd.symm)
      · simp only [F, h1, h2, ↓reduceDIte]
        apply hjoin_disjoint
        right
        intro he
        have := congrArg (fun t : Fin (2 ^ k) => t.val) he
        change r1.val - 2 ^ k = r2.val - 2 ^ k at this
        exact hne (Fin.ext (by omega))
    · rcases hJn with hJ | hJ
      · obtain ⟨r, hr⟩ := hjoin_nonempty J0 hJ
        refine ⟨⟨r.val, by have := r.isLt; rw [Nat.pow_succ]; omega⟩, ?_⟩
        simpa only [F, r.isLt, ↓reduceDIte] using hr
      · obtain ⟨r, hr⟩ := hjoin_nonempty J1 hJ
        refine ⟨⟨r.val + 2 ^ k, by have := r.isLt; rw [Nat.pow_succ]; omega⟩, ?_⟩
        have hnot : ¬ r.val + 2 ^ k < 2 ^ k := by omega
        simpa only [F, hnot, ↓reduceDIte, Nat.add_sub_cancel] using hr
    · intro r
      by_cases hr : r.val < 2 ^ k
      · simp only [F, hr, ↓reduceDIte]
        exact hjoin_sum J0 _
      · simp only [F, hr, ↓reduceDIte]
        exact (hjoin_sum J1 _).trans hJw.symm

/-- **Proposition 5** (c010), arXiv:2304.08376v1, §5, p.16.

Given a collision finder `B` on `S`-element inputs of `Z_p^n`, there is a
deterministic procedure on `S^{⌈log₂ p⌉}` vectors that returns a nonempty
zero-sum subsequence, using fewer than `S^{⌈log₂ p⌉}` calls to `B`.

Note: no operational cost model is formalised, so the witness `calls` is not
tied to `find`; the substantive content of the statement is the existence of
the zero-sum-subsequence finder on `S^{⌈log₂ p⌉}` inputs, while `calls` records
the paper's counting bound as a constraint on the promised resource figure. -/
theorem proposition5_collisionAmplification
    (p n S : ℕ) (hp : p.Prime) (hS : 0 < S)
    (hB : HasCollisionFinder p n S) :
    ∃ (find : (Fin (S ^ Nat.clog 2 p) → ZVec p n) →
        Finset (Fin (S ^ Nat.clog 2 p))) (calls : ℕ),
      calls < S ^ Nat.clog 2 p ∧
      ∀ v : Fin (S ^ Nat.clog 2 p) → ZVec p n,
        IsZeroSumSubsequence p n v (find v) := by
  classical
  have hp_le : p ≤ 2 ^ Nat.clog 2 p := Nat.le_pow_clog (by decide) p
  have hex (v : Fin (S ^ Nat.clog 2 p) → ZVec p n) :
      ∃ J : Finset (Fin (S ^ Nat.clog 2 p)), IsZeroSumSubsequence p n v J := by
    obtain ⟨F, c, hd, hn, hw⟩ := tree_equal_sums p n S hB (Nat.clog 2 p) v
    by_cases hc : c = 0
    · obtain ⟨r, hr⟩ := hn
      exact ⟨F r, hr, (hw r).trans hc⟩
    · have hnonempty (r : Fin (2 ^ Nat.clog 2 p)) : (F r).Nonempty := by
        by_contra hr
        have he : F r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hr
        exact hc (by simpa only [he, Finset.sum_empty] using (hw r).symm)
      let P := Finset.univ.filter (fun r : Fin (2 ^ Nat.clog 2 p) => r.val < p)
      have hcard : P.card = p := by
        apply Finset.card_eq_of_bijective (fun i hi => ⟨i, lt_of_lt_of_le hi hp_le⟩)
        · intro r hr
          exact ⟨r.val, (Finset.mem_filter.mp hr).2, rfl⟩
        · intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        · intro i j hi hj he
          exact congrArg Fin.val he
      let r0 : Fin (2 ^ Nat.clog 2 p) := ⟨0, lt_of_lt_of_le hp.pos hp_le⟩
      have hr0 : r0 ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.pos⟩
      refine ⟨P.biUnion F, ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hnonempty r0
        exact ⟨i, Finset.mem_biUnion.mpr ⟨r0, hr0, hi⟩⟩
      · calc
          (∑ i ∈ P.biUnion F, v i) = ∑ r ∈ P, ∑ i ∈ F r, v i :=
            Finset.sum_biUnion (fun r _ s _ hrs => hd r s hrs)
          _ = ∑ _r ∈ P, c := Finset.sum_congr rfl (fun r _ => hw r)
          _ = p • c := by rw [Finset.sum_const, hcard]
          _ = 0 := by
            funext m
            change p • c m = 0
            rw [nsmul_eq_mul, CharP.cast_eq_zero (ZMod p) p, zero_mul]
  exact ⟨fun v => Classical.choose (hex v), 0, pow_pos hS _,
    fun v => Classical.choose_spec (hex v)⟩

end Qatlib.Papers.ZeroSumImran24.MainResults
