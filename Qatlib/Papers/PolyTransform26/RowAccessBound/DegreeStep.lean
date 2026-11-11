/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

set_option backward.isDefEq.respectTransparency false

/-!
# One degree-reducing coefficient step

Fixed arXiv:2610.08714v1, Lemma 4.6 (printed p.32, Section 4.4, Eqs. (4.24)–(4.28)).

A complementary list `θ` assigns to every word `w` a coefficient column
`θ w : Fin q → ℂ` and is *inner* when its finite coefficient correlations vanish
off the empty word:

`∑_w θ_w† θ_{wu} = 0` for every nonempty `u`   (and `= 1` at `u = ∅`).

The paper separates the top degree from the rest.  Choosing an orthonormal
column matrix `Z` and the projection `Π = Z Z†`, the reduced coefficient at word
`w` is

`ψ_w = [ (I − Π) θ_w;  (Z† θ_{1w}); …; (Z† θ_{kw}) ]`   (Eq. (4.27)).

This file formalises the algebraic core of the proof: the per-word expansion
`ψ_w† ψ_{wu} = θ_w† (I−Π) θ_{wu} + ∑_j θ_{jw}† Π θ_{jwu}` and, over a finite
word set, the resulting preservation of the correlations.  The concrete
complementary list supplied by the certificate and the recursive removal of all
degrees are not part of this module.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open scoped Matrix
open Matrix

namespace Qatlib.Papers.PolyTransform26.RowAccessBound

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The finite set of words over `J` whose length is at most `n`.  Every
coefficient list of degree at most `n` is supported on this set. -/
def wordsUpTo : ℕ → Finset (List J)
  | 0 => {[]}
  | n + 1 =>
      wordsUpTo n ∪ (wordsUpTo n).biUnion (fun w => Finset.univ.image (fun j : J => j :: w))

/-- A word belongs to `wordsUpTo n` exactly when its length is at most `n`. -/
theorem mem_wordsUpTo {n : ℕ} {w : List J} : w ∈ wordsUpTo n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero =>
      simp [wordsUpTo]
  | succ n ih =>
      unfold wordsUpTo
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro (h | ⟨w₀, hw₀, j, rfl⟩)
        · exact le_trans (ih.mp h) (Nat.le_succ n)
        · rw [List.length_cons]
          have := ih.mp hw₀
          omega
      · intro h
        rcases w with _ | ⟨j, w₀⟩
        · exact Or.inl (ih.mpr (by simp))
        · right
          refine ⟨w₀, ih.mpr ?_, j, rfl⟩
          rw [List.length_cons] at h
          omega

/-- The Hermitian coefficient pairing `†` on complex columns. -/
def dot {α : Type*} [Fintype α] (a b : α → ℂ) : ℂ := ∑ x, star (a x) * b x

/-- Adjointness of the Hermitian pairing against a matrix–vector product. -/
theorem dot_mulVec_conjTranspose {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℂ) (a : β → ℂ) (b : α → ℂ) :
    dot (Matrix.mulVec M a) b = dot a (Matrix.mulVec (Matrix.conjTranspose M) b) := by
  simp only [dot, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    star_sum, star_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- The Hermitian pairing only sees the projection when both arguments are
projected by an idempotent Hermitian `Π`. -/
theorem dot_projected_left {α : Type*} [Fintype α]
    (P : Matrix α α ℂ) (hPh : P.conjTranspose = P) (hPid : P * P = P)
    (a b : α → ℂ) :
    dot (Matrix.mulVec P a) (Matrix.mulVec P b) = dot a (Matrix.mulVec P b) := by
  have hmv : Matrix.mulVec P (Matrix.mulVec P b) = Matrix.mulVec (P * P) b :=
    Matrix.mulVec_mulVec b P P
  rw [dot_mulVec_conjTranspose P a (Matrix.mulVec P b), hPh, hmv, hPid]

/-- Splitting the Hermitian pairing over a disjoint sum of index types. -/
theorem dot_sum_type {α β : Type*} [Fintype α] [Fintype β]
    (a b : α ⊕ β → ℂ) :
    dot a b =
      dot (fun x => a (Sum.inl x)) (fun x => b (Sum.inl x)) +
      dot (fun y => a (Sum.inr y)) (fun y => b (Sum.inr y)) := by
  simp only [dot, Fintype.sum_sum_type]

/-- Splitting the Hermitian pairing over a product index type. -/
theorem dot_prod {α β : Type*} [Fintype α] [Fintype β]
    (a b : α × β → ℂ) :
    dot a b = ∑ x : α, dot (fun y => a (x, y)) (fun y => b (x, y)) := by
  simp only [dot, Fintype.sum_prod_type]

variable {q e : ℕ}

/-- The rank-`e` projection `Π = Z Z†` onto the span of the orthonormal columns
`Z` (Eq. (4.27)). -/
def Proj (Z : Matrix (Fin q) (Fin e) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  Z * Matrix.conjTranspose Z

/-- `Π = Z Z†` is Hermitian. -/
theorem Proj_conjTranspose (Z : Matrix (Fin q) (Fin e) ℂ) :
    (Proj Z).conjTranspose = Proj Z := by
  simp only [Proj, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- If the columns of `Z` are orthonormal (`Z† Z = 1`), then `Π = Z Z†` is a
projection. -/
theorem Proj_idem (Z : Matrix (Fin q) (Fin e) ℂ)
    (hZ : Matrix.conjTranspose Z * Z = 1) : Proj Z * Proj Z = Proj Z := by
  unfold Proj
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc (Matrix.conjTranspose Z) Z (Matrix.conjTranspose Z), hZ,
    Matrix.one_mul]

/-- The complementary projection `I − Π` is Hermitian. -/
theorem one_sub_Proj_conjTranspose (Z : Matrix (Fin q) (Fin e) ℂ) :
    (1 - Proj Z).conjTranspose = 1 - Proj Z := by
  rw [Matrix.conjTranspose_sub, Proj_conjTranspose, Matrix.conjTranspose_one]

/-- The complementary projection `I − Π` is idempotent. -/
theorem one_sub_Proj_idem (Z : Matrix (Fin q) (Fin e) ℂ)
    (hZ : Matrix.conjTranspose Z * Z = 1) :
    (1 - Proj Z) * (1 - Proj Z) = 1 - Proj Z := by
  have h := Proj_idem Z hZ
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, h]
  abel

/-- The reduced coefficient column of Eq. (4.27): the complementary part on the
identity label followed by the `Z† θ_{j·}` active labels. -/
def psi (θ : List J → Fin q → ℂ) (Z : Matrix (Fin q) (Fin e) ℂ) (w : List J) :
    (Fin q ⊕ (J × Fin e)) → ℂ
  | Sum.inl a => Matrix.mulVec (1 - Proj Z) (θ w) a
  | Sum.inr ⟨j, b⟩ => Matrix.mulVec (Matrix.conjTranspose Z) (θ (j :: w)) b

/-- Conjugating by `Z†` replaces the projection `Π = Z Z†` in the pairing. -/
theorem dot_conjTranspose_mulVec (Z : Matrix (Fin q) (Fin e) ℂ) (a b : Fin q → ℂ) :
    dot (Matrix.mulVec (Matrix.conjTranspose Z) a)
        (Matrix.mulVec (Matrix.conjTranspose Z) b) =
      dot a (Matrix.mulVec (Proj Z) b) := by
  have h := dot_mulVec_conjTranspose (Matrix.conjTranspose Z) a
    (Matrix.mulVec (Matrix.conjTranspose Z) b)
  rw [h, Matrix.conjTranspose_conjTranspose]
  congr 1
  exact Matrix.mulVec_mulVec b Z (Matrix.conjTranspose Z)

omit [DecidableEq J] in
/-- Per-word coefficient calculation of Lemma 4.6: the pairing of two reduced
coefficients expands into the complementary part plus the active parts, exactly
the displayed calculation `ψ_w† ψ_{wu} = θ_w† (I−Π) θ_{wu} + ∑_j θ_{jw}† Π θ_{jwu}`. -/
theorem dot_psi_psi (θ : List J → Fin q → ℂ) (Z : Matrix (Fin q) (Fin e) ℂ)
    (hZ : Matrix.conjTranspose Z * Z = 1) (w u : List J) :
    dot (psi θ Z w) (psi θ Z (w ++ u)) =
      dot (θ w) (Matrix.mulVec (1 - Proj Z) (θ (w ++ u))) +
      ∑ j : J,
        dot (θ (j :: w)) (Matrix.mulVec (Proj Z) (θ (j :: (w ++ u)))) := by
  rw [dot_sum_type]
  have h1 :
      dot (fun x => psi θ Z w (Sum.inl x)) (fun x => psi θ Z (w ++ u) (Sum.inl x)) =
        dot (θ w) (Matrix.mulVec (1 - Proj Z) (θ (w ++ u))) := by
    simp only [psi]
    exact dot_projected_left (1 - Proj Z) (one_sub_Proj_conjTranspose Z)
      (one_sub_Proj_idem Z hZ) (θ w) (θ (w ++ u))
  have h2 :
      dot (fun y => psi θ Z w (Sum.inr y)) (fun y => psi θ Z (w ++ u) (Sum.inr y)) =
        ∑ j : J,
          dot (θ (j :: w)) (Matrix.mulVec (Proj Z) (θ (j :: (w ++ u)))) := by
    simp only [psi]
    rw [dot_prod]
    refine Finset.sum_congr rfl ?_
    intro j _
    show dot (Matrix.mulVec (Matrix.conjTranspose Z) (θ (j :: w)))
        (Matrix.mulVec (Matrix.conjTranspose Z) (θ (j :: (w ++ u)))) =
      dot (θ (j :: w)) (Matrix.mulVec (Proj Z) (θ (j :: (w ++ u))))
    exact dot_conjTranspose_mulVec Z (θ (j :: w)) (θ (j :: (w ++ u)))
  rw [h1, h2]

/-- Splitting a sum over all words of length at most `n` into the empty word
and the nonempty words. -/
theorem sum_wordsUpTo_split_empty (n : ℕ) (f : List J → ℂ) :
    ∑ w ∈ wordsUpTo n, f w =
      f [] + ∑ w ∈ (wordsUpTo n).filter (fun w => w ≠ []), f w := by
  have hset : wordsUpTo (J := J) n =
      insert ([] : List J) ((wordsUpTo (J := J) n).filter (fun w : List J => w ≠ [])) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_filter, ne_eq]
    constructor
    · intro hw
      by_cases h : w = []
      · exact Or.inl h
      · exact Or.inr ⟨hw, h⟩
    · rintro (rfl | ⟨hw, -⟩)
      · exact mem_wordsUpTo.mpr (by simp)
      · exact hw
  have hnot : ([] : List J) ∉ (wordsUpTo (J := J) n).filter (fun w : List J => w ≠ []) := by
    simp
  calc ∑ w ∈ wordsUpTo n, f w
      = ∑ w ∈ insert ([] : List J)
          ((wordsUpTo (J := J) n).filter (fun w : List J => w ≠ [])), f w := by
        conv_lhs => rw [hset]
    _ = f [] + ∑ w ∈ (wordsUpTo (J := J) n).filter (fun w : List J => w ≠ []), f w :=
        Finset.sum_insert hnot

/-- Omitting the words of top length `n` does not change a sum whose top-degree
coefficients vanish. -/
theorem sum_wordsUpTo_eq_of_zero_top {n : ℕ} (hn : 1 ≤ n) {f : List J → ℂ}
    (hf : ∀ w, w.length = n → f w = 0) :
    ∑ w ∈ wordsUpTo n, f w = ∑ w ∈ wordsUpTo (n - 1), f w := by
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [mem_wordsUpTo] at hx ⊢
    omega
  · intro x hx hxnot
    rw [mem_wordsUpTo] at hx
    have hxnot' : ¬ x.length ≤ n - 1 := fun h => hxnot (mem_wordsUpTo.mpr h)
    have hlen : x.length = n := by omega
    exact hf x hlen

/-- Reindexing the nonempty words of length at most `n+1` by their first letter
and the remaining word of length at most `n`. -/
theorem sum_nonempty_wordsUpTo_succ (n : ℕ) (f : List J → ℂ) :
    ∑ w ∈ (wordsUpTo (n + 1)).filter (fun w => w ≠ []), f w =
      ∑ j : J, ∑ w ∈ wordsUpTo n, f (j :: w) := by
  have hset : (wordsUpTo (n + 1)).filter (fun w => w ≠ []) =
      (wordsUpTo n).biUnion (fun w => Finset.univ.image (fun j : J => j :: w)) := by
    ext w
    simp only [Finset.mem_filter, mem_wordsUpTo, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_univ, true_and, ne_eq]
    constructor
    · rintro ⟨hlen, hne⟩
      rcases w with _ | ⟨j, w₀⟩
      · exact absurd rfl hne
      · rw [List.length_cons] at hlen
        exact ⟨w₀, by omega, j, rfl⟩
    · rintro ⟨w₀, hlen, j, hw⟩
      subst hw
      exact ⟨by rw [List.length_cons]; omega, List.cons_ne_nil _ _⟩
  rw [hset]
  have hdisj : Set.PairwiseDisjoint ((wordsUpTo (J := J) n : Set (List J)))
      (fun w : List J => Finset.univ.image (fun j : J => j :: w)) := by
    intro w _ w' _ hne
    change Disjoint (Finset.univ.image (fun j : J => j :: w))
      (Finset.univ.image (fun j : J => j :: w'))
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hx'
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hx'
    exact hne (List.cons.inj (ha.trans hb.symm)).2
  rw [Finset.sum_biUnion hdisj]
  calc ∑ w ∈ wordsUpTo n, ∑ i ∈ Finset.univ.image (fun j : J => j :: w), f i
      = ∑ w ∈ wordsUpTo n, ∑ j : J, f (j :: w) := by
        refine Finset.sum_congr rfl ?_
        intro w _
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact (List.cons.inj hab).1
    _ = ∑ j : J, ∑ w ∈ wordsUpTo n, f (j :: w) := by
        rw [Finset.sum_comm]

/-- The Hermitian pairing is additive in its second argument. -/
theorem dot_add_right {α : Type*} [Fintype α] (a b c : α → ℂ) :
    dot a (b + c) = dot a b + dot a c := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Splitting the second argument through the complementary projection. -/
theorem dot_sub_add_proj {α : Type*} [Fintype α] [DecidableEq α]
    (P : Matrix α α ℂ) (a b : α → ℂ) :
    dot a (Matrix.mulVec (1 - P) b) + dot a (Matrix.mulVec P b) = dot a b := by
  rw [← dot_add_right, ← Matrix.add_mulVec, sub_add_cancel, Matrix.one_mulVec]

/-- A Hermitian projection that kills `a` also kills the pairing of `a` against
a projected column. -/
theorem dot_eq_zero_of_proj_mulVec_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (P : Matrix α α ℂ) (hPh : P.conjTranspose = P)
    (a b : α → ℂ) (ha : Matrix.mulVec P a = 0) :
    dot a (Matrix.mulVec P b) = 0 := by
  have hsymm : dot a (Matrix.mulVec P b) = dot (Matrix.mulVec P a) b := by
    calc dot a (Matrix.mulVec P b) = dot a (Matrix.mulVec P.conjTranspose b) := by
          rw [hPh]
      _ = dot (Matrix.mulVec P a) b := (dot_mulVec_conjTranspose P a b).symm
  rw [hsymm, ha]
  simp only [dot, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero]

/-- Lemma 4.6, correlation preservation: if `θ` is inner of degree at most `d`
and `Π θ_∅ = 0`, the reduced list `ψ` of Eq. (4.27) satisfies the same
coefficient correlations as `θ`. -/
theorem correlation_preserved (θ : List J → Fin q → ℂ) (Z : Matrix (Fin q) (Fin e) ℂ)
    (hZ : Matrix.conjTranspose Z * Z = 1) (d : ℕ) (hd : 1 ≤ d)
    (hsupp : ∀ w, d < w.length → θ w = 0)
    (hPi0 : Matrix.mulVec (Proj Z) (θ []) = 0) (u : List J) :
    (∑ w ∈ wordsUpTo d, dot (psi θ Z w) (psi θ Z (w ++ u))) =
      ∑ w ∈ wordsUpTo d, dot (θ w) (θ (w ++ u)) := by
  have hexp : (∑ w ∈ wordsUpTo d, dot (psi θ Z w) (psi θ Z (w ++ u))) =
      ∑ w ∈ wordsUpTo d,
        (dot (θ w) (Matrix.mulVec (1 - Proj Z) (θ (w ++ u))) +
          ∑ j : J,
            dot (θ (j :: w)) (Matrix.mulVec (Proj Z) (θ (j :: (w ++ u))))) := by
    refine Finset.sum_congr rfl ?_
    intro w _
    exact dot_psi_psi θ Z hZ w u
  have hterm :
      (∑ w ∈ wordsUpTo d, ∑ j : J,
          dot (θ (j :: w)) (Matrix.mulVec (Proj Z) (θ (j :: (w ++ u))))) =
        ∑ w ∈ (wordsUpTo d).filter (fun w => w ≠ []),
          dot (θ w) (Matrix.mulVec (Proj Z) (θ (w ++ u))) := by
    rw [Finset.sum_comm]
    have htrunc : ∀ j : J,
        (∑ w ∈ wordsUpTo d,
            dot (θ (j :: w)) (Matrix.mulVec (Proj Z) (θ (j :: (w ++ u))))) =
          ∑ w ∈ wordsUpTo (d - 1),
            dot (θ (j :: w)) (Matrix.mulVec (Proj Z) (θ (j :: (w ++ u)))) := by
      intro j
      refine sum_wordsUpTo_eq_of_zero_top hd ?_
      intro w hw
      have hlen : d < (j :: w).length := by
        rw [List.length_cons, hw]; omega
      rw [hsupp (j :: w) hlen]
      simp only [Pi.zero_apply, dot, star_zero, zero_mul, Finset.sum_const_zero]
    have hsucc := sum_nonempty_wordsUpTo_succ (d - 1)
      (fun w => dot (θ w) (Matrix.mulVec (Proj Z) (θ (w ++ u))))
    have hd' : d - 1 + 1 = d := Nat.sub_add_cancel hd
    rw [Finset.sum_congr rfl (fun j _ => htrunc j)]
    simp only [List.cons_append] at hsucc ⊢
    rw [← hsucc, hd']
  have hfilter_eq : (∑ w ∈ (wordsUpTo d).filter (fun w => w ≠ []),
        dot (θ w) (Matrix.mulVec (Proj Z) (θ (w ++ u)))) =
      ∑ w ∈ wordsUpTo d, dot (θ w) (Matrix.mulVec (Proj Z) (θ (w ++ u))) := by
    have hsplit := sum_wordsUpTo_split_empty d
      (fun w => dot (θ w) (Matrix.mulVec (Proj Z) (θ (w ++ u))))
    have hzero : dot (θ []) (Matrix.mulVec (Proj Z) (θ ([] ++ u))) = 0 := by
      simpa using
        dot_eq_zero_of_proj_mulVec_eq_zero (Proj Z) (Proj_conjTranspose Z)
          (θ []) (θ u) hPi0
    rw [hsplit, hzero, zero_add]
  rw [hexp, Finset.sum_add_distrib, hterm, hfilter_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro w _
  exact dot_sub_add_proj (Proj Z) (θ w) (θ (w ++ u))

end Qatlib.Papers.PolyTransform26.RowAccessBound
