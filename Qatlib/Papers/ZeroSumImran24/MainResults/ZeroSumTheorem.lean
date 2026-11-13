/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Claim c001 — Theorem 2 of Imran--Ivanyos.

Fixed source version: arXiv:2304.08376v1 (17 Apr 2023).
Theorem 2, §5, p.16; obtained from Propositions 4 and 5 (pp.15--16) plus the
`p = 2` remark (p.13: `n + 1` vectors of `Z_2^n` give a zero-sum subsequence).

Statement (paper): There is a deterministic algorithm that, given a sequence of
`S(p,n) = p^{O((p log p)^2)} n^{O(p log p)}` vectors from `Z_p^n`, finds a
non-trivial zero-sum subsequence in time `poly(S(p,n))`.

We state the deterministic witness form: a size `S` within the paper's
`p^{O((p log p)^2)} n^{O(p log p)}` class (big-O represented by a constant `C`);
a deterministic map taking every `S`-tuple to a nonempty zero-sum subsequence.
The `poly(S)` running time is represented by the finitely-staged construction
(Proposition 4's recursion followed by Proposition 5's collision amplification),
not by a Turing-machine cost model.
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Qatlib.Papers.ZeroSumImran24.MainResults.SourceModel

/-!
# Deterministic Zero-Sum Subsequence Bound over `ℤ_p^n`

This module formalizes Section 5, Theorem 2 (p. 16) of Imran and Ivanyos on the
existence of a threshold `S = p^{O((p log p)^2)} n^{O(p log p)}` and a
deterministic map sending every `S`-tuple of vectors in `ℤ_p^n` to a nonempty
zero-sum subsequence.

## Main statements

* `theorem2_zeroSumSubsequence`: Theorem 2, deterministic nonempty zero-sum
  subsequence extraction within `p^{O((p log p)^2)} n^{O(p log p)}` vectors.

## References

* [Imran and Ivanyos, 2023][ImranIvanyos2023ZeroSum], Section 5, Theorem 2, p. 16.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ZeroSumImran24.MainResults

private lemma zeroSum_collision (p n s : ℕ) [NeZero p]
    (hs : p ^ n < 2 ^ s) (w : Fin s → ZVec p n) :
    ∃ (J : Bool → Finset (Fin s)) (c : ZVec p n),
      (∀ a b, a ≠ b → Disjoint (J a) (J b)) ∧
      (∃ a, (J a).Nonempty) ∧ (∀ a, ∑ i ∈ J a, w i = c) := by
  classical
  have hcard : Fintype.card (ZVec p n) < Fintype.card (Finset (Fin s)) := by
    simpa [ZVec, Fintype.card_fun] using hs
  obtain ⟨A, B, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun A : Finset (Fin s) => ∑ i ∈ A, w i) hcard
  have hsum : ∑ i ∈ A \ B, w i = ∑ i ∈ B \ A, w i := by
    apply add_right_cancel (b := ∑ i ∈ A ∩ B, w i)
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter A B), Finset.sdiff_union_inter,
      Finset.inter_comm A B, ← Finset.sum_union (Finset.disjoint_sdiff_inter B A),
      Finset.sdiff_union_inter]
    exact heq
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  refine ⟨(fun b => if b then B \ A else A \ B), ∑ i ∈ A \ B, w i, ?_, ?_, ?_⟩
  · intro a b hab
    cases a <;> cases b <;> simp_all [disjoint_comm]
  · by_cases hA : (A \ B).Nonempty
    · exact ⟨false, hA⟩
    · refine ⟨true, ?_⟩
      apply Finset.sdiff_nonempty.mpr
      intro hBA
      exact hne (Finset.Subset.antisymm
        (by simpa [Finset.sdiff_nonempty] using hA) hBA)
  · intro a
    cases a <;> simp [hsum]

private lemma zeroSum_amplify (p n s : ℕ) [NeZero p]
    (hs : p ^ n < 2 ^ s) (m : ℕ) (v : Fin (s ^ m) → ZVec p n) :
    ∃ (F : Fin (2 ^ m) → Finset (Fin (s ^ m))) (c : ZVec p n),
      (∀ a b, a ≠ b → Disjoint (F a) (F b)) ∧
      (∃ a, (F a).Nonempty) ∧ (∀ a, ∑ i ∈ F a, v i = c) := by
  classical
  induction m with
  | zero =>
    refine ⟨fun _ => Finset.univ, ∑ i, v i, ?_, ?_, ?_⟩
    · intro a b hab
      exact (hab (Subsingleton.elim (α := Fin 1) a b)).elim
    · exact ⟨0, ⟨0, Finset.mem_univ _⟩⟩
    · intro a
      rfl
  | succ m ih =>
    let e : Fin s × Fin (s ^ m) ≃ Fin (s ^ (m + 1)) :=
      Fintype.equivOfCardEq (by simp [pow_succ, Nat.mul_comm])
    choose F c hF hnon hsum using fun b : Fin s => ih (fun j => v (e (b, j)))
    obtain ⟨J, d, hJ, hJnon, hJsum⟩ := zeroSum_collision p n s hs c
    let U (b : Fin s) (r : Fin (2 ^ m)) := (F b r).image (fun j => e (b, j))
    have hU (b b' : Fin s) (r r' : Fin (2 ^ m))
        (h : b ≠ b' ∨ r ≠ r') : Disjoint (U b r) (U b' r') := by
      apply Finset.disjoint_left.mpr
      intro i hi hi'
      obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp hi
      obtain ⟨j', hj', hij'⟩ := Finset.mem_image.mp hi'
      have he := e.injective (hij.trans hij'.symm)
      have hb : b = b' := congrArg Prod.fst he
      have hjj : j = j' := congrArg Prod.snd he
      subst b'
      subst j'
      rcases h with h | h
      · exact h rfl
      · exact (Finset.disjoint_left.mp (hF b r r' h)) hj hj'
    let G (r : Bool × Fin (2 ^ m)) := (J r.1).biUnion (fun b => U b r.2)
    have hG (r t : Bool × Fin (2 ^ m)) (hrt : r ≠ t) :
        Disjoint (G r) (G t) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨b', hb', hib'⟩ := Finset.mem_biUnion.mp hj
      by_cases hbb : b = b'
      · subst b'
        have hrt2 : r.2 ≠ t.2 := by
          intro he
          have hrt1 : r.1 ≠ t.1 := fun h => hrt (Prod.ext h he)
          exact (Finset.disjoint_left.mp (hJ r.1 t.1 hrt1)) hb hb'
        exact (Finset.disjoint_left.mp (hU b b r.2 t.2 (Or.inr hrt2))) hib hib'
      · exact (Finset.disjoint_left.mp (hU b b' r.2 t.2 (Or.inl hbb))) hib hib'
    have hGnon : ∃ r, (G r).Nonempty := by
      obtain ⟨a, b, hb⟩ := hJnon
      obtain ⟨r, j, hj⟩ := hnon b
      exact ⟨(a, r), e (b, j), Finset.mem_biUnion.mpr
        ⟨b, hb, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩⟩
    have hGsum (r : Bool × Fin (2 ^ m)) : ∑ i ∈ G r, v i = d := by
      rw [Finset.sum_biUnion (fun b _ b' _ h => hU b b' r.2 r.2 (Or.inl h))]
      calc
        _ = ∑ b ∈ J r.1, c b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_image]
          · exact hsum b r.2
          · intro j _ j' _ h
            exact congrArg Prod.snd (e.injective h)
        _ = d := hJsum r.1
    let f : Fin (2 ^ (m + 1)) ≃ Bool × Fin (2 ^ m) :=
      Fintype.equivOfCardEq (by simp [pow_succ, Nat.mul_comm])
    refine ⟨fun r => G (f r), d, fun a b h => hG _ _ (fun he => h (f.injective he)),
      ?_, fun r => hGsum (f r)⟩
    obtain ⟨r, hr⟩ := hGnon
    exact ⟨f.symm r, by simpa using hr⟩

private lemma zeroSumSubsequence_aux (p n : ℕ) [NeZero p] (hp : p.Prime) :
    ∃ (S : ℕ) (find : (Fin S → ZVec p n) → Finset (Fin S)) (C : ℕ),
      0 < C ∧
      S ≤ (p + 2) ^ (C * (p * (Nat.log 2 p + 1)) ^ 2) *
          (n + 1) ^ (C * (p * (Nat.log 2 p + 1))) ∧
      ∀ v : Fin S → ZVec p n, IsZeroSumSubsequence p n v (find v) := by
  classical
  let L := Nat.log 2 p + 1
  let s := n * L + 1
  let k := Nat.clog 2 p
  have hL : 1 ≤ L := Nat.le_add_left 1 _
  have hpow : p < 2 ^ L := Nat.lt_pow_succ_log_self (by decide) p
  have hs : p ^ n < 2 ^ s := calc
    p ^ n ≤ (2 ^ L) ^ n := Nat.pow_le_pow_left hpow.le n
    _ = 2 ^ (n * L) := by rw [← pow_mul, Nat.mul_comm]
    _ < 2 ^ s := by exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  have hex (v : Fin (s ^ k) → ZVec p n) :
      ∃ A : Finset (Fin (s ^ k)), IsZeroSumSubsequence p n v A := by
    obtain ⟨F, c, hF, hnon, hsum⟩ := zeroSum_amplify p n s hs k v
    by_cases hc : c = 0
    · obtain ⟨r, hr⟩ := hnon
      exact ⟨F r, hr, (hsum r).trans hc⟩
    · have hpk : p ≤ 2 ^ k := Nat.le_pow_clog (by decide) p
      let e : Fin p ↪ Fin (2 ^ k) := Fin.castLEEmb hpk
      let A := Finset.univ.image e
      have hA : A.Nonempty := ⟨e ⟨0, hp.pos⟩, Finset.mem_image.mpr
        ⟨⟨0, hp.pos⟩, Finset.mem_univ _, rfl⟩⟩
      have hcard : A.card = p := by simp [A, Finset.card_image_of_injective _ e.injective]
      refine ⟨A.biUnion F, ?_, ?_⟩
      · obtain ⟨r, hr⟩ := hA
        have hFr : (F r).Nonempty := by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro he
          exact hc (by simpa [he] using (hsum r).symm)
        obtain ⟨i, hi⟩ := hFr
        exact ⟨i, Finset.mem_biUnion.mpr ⟨r, hr, hi⟩⟩
      · rw [Finset.sum_biUnion (fun a _ b _ h => hF a b h)]
        calc
          _ = ∑ _r ∈ A, c := Finset.sum_congr rfl (fun r _ => hsum r)
          _ = p • c := by rw [Finset.sum_const, hcard]
          _ = 0 := by
            ext i
            change p • c i = 0
            rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  choose find hfind using hex
  refine ⟨s ^ k, find, 1, by decide, ?_, hfind⟩
  have hkL : k ≤ L := (Nat.clog_le_iff_le_pow (by decide)).mpr hpow.le
  have hLp : L ≤ p + 2 := by dsimp [L]; have h := Nat.log_le_self 2 p; omega
  have hsp : s ≤ (p + 2) * (n + 1) := calc
    s ≤ L * (n + 1) := by dsimp [s]; nlinarith
    _ ≤ (p + 2) * (n + 1) := Nat.mul_le_mul_right _ hLp
  have hLpL : L ≤ p * L := by nlinarith [hp.pos]
  have hk : k ≤ p * L := hkL.trans hLpL
  have hk2 : k ≤ (p * L) ^ 2 := hk.trans (Nat.le_self_pow (by decide) _)
  calc
    s ^ k ≤ ((p + 2) * (n + 1)) ^ k := Nat.pow_le_pow_left hsp k
    _ = (p + 2) ^ k * (n + 1) ^ k := Nat.mul_pow _ _ _
    _ ≤ (p + 2) ^ (1 * (p * L) ^ 2) * (n + 1) ^ (1 * (p * L)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by simpa using hk2))
        (Nat.pow_le_pow_right (by omega) (by simpa using hk))

/-- **Theorem 2** (c001), arXiv:2304.08376v1, §5, p.16.

For a prime `p` and dimension `n` there are `S = p^{O((p log p)^2)} n^{O(p log p)}`
vectors and a deterministic map sending every `S`-tuple of vectors of `Z_p^n` to
a nonempty zero-sum subsequence. -/
theorem theorem2_zeroSumSubsequence
    (p n : ℕ) (hp : p.Prime) :
    ∃ (S : ℕ) (find : (Fin S → ZVec p n) → Finset (Fin S)) (C : ℕ),
      0 < C ∧
      S ≤ (p + 2) ^ (C * (p * (Nat.log 2 p + 1)) ^ 2) *
          (n + 1) ^ (C * (p * (Nat.log 2 p + 1))) ∧
      ∀ v : Fin S → ZVec p n, IsZeroSumSubsequence p n v (find v) := by
  exact @zeroSumSubsequence_aux p n ⟨hp.ne_zero⟩ hp

end Qatlib.Papers.ZeroSumImran24.MainResults
