/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The collision deletion matrix and its Euclidean operator norm

For a tuple length `s = n + 1`, the collision deletion matrix in [MagniezZur2026],
Equation (28), sends a non-injective `s`-tuple to the direct sum, over the choice of a
deleted coordinate, of the remaining tuple when that remaining tuple is injective.  The
matrix below has rows indexed by a coordinate `r` and an injective `(s - 1)`-tuple, and
columns indexed by non-injective `s`-tuples.  Its entries are `0` or `1`, recording whether
deleting `r` produces the indicated injective tuple.

The main combinatorial facts are that every column has at most two nonzero entries and every
row has at most `s - 1` nonzero entries.  Combined with a finite Cauchy--Schwarz estimate,
they give the Euclidean operator-norm bound `‖B‖ ≤ √(2 (s - 1))`, equivalently the squared
estimate `‖B c‖² ≤ 2 (s - 1) ‖c‖²` following [MagniezZur2026], Equation (28). The matrix
norm is the L2 operator norm between the two Euclidean spaces.

## Main statements

* `collisionDeletion_row_card_le`: every row has at most `n` nonzero entries.
* `collisionDeletion_col_card_le`: every column has at most two nonzero entries.
* `collisionDeletion_action_sq_le`: the squared Euclidean action bound.
* `collisionDeletion_l2_opNorm_le`: the Euclidean operator-norm bound.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.CollisionLB26.DeleteNorm

/-- Non-injective tuples of length `n + 1` over `Fin N`. -/
abbrev NonInjectiveTuple (n N : ℕ) := {f : Fin (n + 1) → Fin N // ¬ Function.Injective f}

/-- Rows of the collision deletion matrix: a deleted coordinate together with an injective
`n`-tuple. -/
abbrev CollisionDeletionRow (n N : ℕ) :=
  Σ _r : Fin (n + 1), {z : Fin n → Fin N // Function.Injective z}

/-- Delete coordinate `r` from a tuple. -/
def deleteAt {n N : ℕ} (r : Fin (n + 1)) (f : Fin (n + 1) → Fin N) : Fin n → Fin N :=
  fun j => f (Fin.succAbove r j)

/-- Deleting a coordinate is the same as the standard removal of that coordinate. -/
lemma deleteAt_eq_removeNth {n N : ℕ} (r : Fin (n + 1)) (f : Fin (n + 1) → Fin N) :
    deleteAt r f = Fin.removeNth r f := rfl

/-- A tuple is recovered from its deleted coordinate, its value there, and its deletion. -/
lemma eq_insertNth_deleteAt {n N : ℕ} (r : Fin (n + 1)) (f : Fin (n + 1) → Fin N) :
    f = Fin.insertNth r (f r) (deleteAt r f) := by
  rw [Fin.eq_insertNth_iff]
  exact ⟨rfl, rfl⟩

/-- Inserting a value outside the range of an injective tuple keeps the tuple injective. -/
lemma insertNth_injective_of_forall_ne {n N : ℕ} (r : Fin (n + 1)) (a : Fin N)
    (z : Fin n → Fin N) (hz : Function.Injective z) (ha : ∀ j, z j ≠ a) :
    Function.Injective (Fin.insertNth r a z) := by
  intro i j hij
  by_cases hi : i = r
  · subst i
    rcases Fin.eq_self_or_eq_succAbove r j with h | ⟨j', h⟩
    · exact h.symm
    · subst j
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hij
      exact absurd hij.symm (ha j')
  · obtain ⟨i', rfl⟩ : ∃ i', i = r.succAbove i' := by
      rcases Fin.eq_self_or_eq_succAbove r i with h | ⟨i', h⟩
      · exact absurd h hi
      · exact ⟨i', h⟩
    rcases Fin.eq_self_or_eq_succAbove r j with h | ⟨j', h⟩
    · subst j
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hij
      exact absurd hij (ha i')
    · subst j
      simp only [Fin.insertNth_apply_succAbove] at hij
      exact congrArg (Fin.succAbove r) (hz hij)

/-- If inserting a value into an injective tuple is not injective, the inserted value already
occurs in the tuple. -/
lemma exists_mem_of_insertNth_not_injective {n N : ℕ} (r : Fin (n + 1)) (a : Fin N)
    (z : Fin n → Fin N) (hz : Function.Injective z)
    (h : ¬ Function.Injective (Fin.insertNth r a z)) : ∃ j, z j = a := by
  by_contra hc
  exact h (insertNth_injective_of_forall_ne r a z hz fun j hij => hc ⟨j, hij⟩)

/-- For a fixed row, the nonzero columns form a set of size at most `n`: the inserted value
must be one of the `n` entries of the row tuple. -/
lemma row_card_le {n N : ℕ} (r : Fin (n + 1))
    (z : {z : Fin n → Fin N // Function.Injective z}) :
    (Finset.univ.filter (fun f : NonInjectiveTuple n N => deleteAt r f.1 = z.1)).card ≤ n := by
  classical
  let S := {f : NonInjectiveTuple n N // deleteAt r f.1 = z.1}
  have hchoose (f : S) : ∃ j : Fin n, z.1 j = f.1.1 r := by
    apply exists_mem_of_insertNth_not_injective r (f.1.1 r) z.1 z.2
    have hf' : ¬ Function.Injective (Fin.insertNth r (f.1.1 r) (deleteAt r f.1.1)) := by
      rw [← eq_insertNth_deleteAt r f.1.1]
      exact f.1.2
    rw [f.2] at hf'
    exact hf'
  let ψ : S → Fin n := fun f => Classical.choose (hchoose f)
  have hψ (f : S) : z.1 (ψ f) = f.1.1 r := Classical.choose_spec (hchoose f)
  have hψinj : Function.Injective ψ := by
    intro f g hfg
    apply Subtype.ext
    apply Subtype.ext
    have hfr : f.1.1 r = z.1 (ψ f) := (hψ f).symm
    have hgr : g.1.1 r = z.1 (ψ g) := (hψ g).symm
    calc
      f.1.1 = Fin.insertNth r (f.1.1 r) (deleteAt r f.1.1) := eq_insertNth_deleteAt r f.1.1
      _ = Fin.insertNth r (z.1 (ψ f)) (z.1) := by rw [f.2, hfr]
      _ = Fin.insertNth r (z.1 (ψ g)) (z.1) := by rw [hfg]
      _ = Fin.insertNth r (g.1.1 r) (z.1) := by rw [← hgr]
      _ = Fin.insertNth r (g.1.1 r) (deleteAt r g.1.1) := by rw [g.2]
      _ = g.1.1 := (eq_insertNth_deleteAt r g.1.1).symm
  have hcard : Fintype.card S ≤ Fintype.card (Fin n) := Fintype.card_le_of_injective ψ hψinj
  simpa [S, Fintype.card_subtype] using hcard

/-- If deleting `r` leaves an injective tuple, then any repeated pair of values in the original
tuple must involve the deleted coordinate `r`. -/
lemma deleteAt_injective_index {n N : ℕ} (r : Fin (n + 1)) (f : Fin (n + 1) → Fin N)
    (hr : Function.Injective (deleteAt r f)) {i j : Fin (n + 1)} (hij : i ≠ j)
    (hval : f i = f j) : r = i ∨ r = j := by
  by_contra h
  have hri : i ≠ r := fun h' => h (Or.inl h'.symm)
  have hrj : j ≠ r := fun h' => h (Or.inr h'.symm)
  obtain ⟨i', rfl⟩ : ∃ i', i = r.succAbove i' := by
    rcases Fin.eq_self_or_eq_succAbove r i with h' | ⟨i', h'⟩
    · exact absurd h' hri
    · exact ⟨i', h'⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = r.succAbove j' := by
    rcases Fin.eq_self_or_eq_succAbove r j with h' | ⟨j', h'⟩
    · exact absurd h' hrj
    · exact ⟨j', h'⟩
  have hEq : deleteAt r f i' = deleteAt r f j' := by simpa [deleteAt] using hval
  exact hij (by rw [hr hEq])

/-- A column can have a nonzero entry only for a coordinate whose deletion is injective.  If two
different coordinates both gave injective deletions, the two colliding positions of the
non-injective tuple would have to be those two coordinates. -/
lemma col_card_le {n N : ℕ} (f : NonInjectiveTuple n N) :
    (Finset.univ.filter
      (fun r : Fin (n + 1) => Function.Injective (deleteAt r f.1))).card ≤ 2 := by
  classical
  obtain ⟨i, j, hval, hij⟩ := Function.not_injective_iff.mp f.2
  have hsub : (Finset.univ.filter
        (fun r : Fin (n + 1) => Function.Injective (deleteAt r f.1)))
      ⊆ ({i, j} : Finset (Fin (n + 1))) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rcases deleteAt_injective_index r f.1 hr hij hval with h | h <;> simp [h]
  calc
    (Finset.univ.filter
        (fun r : Fin (n + 1) => Function.Injective (deleteAt r f.1))).card
        ≤ ({i, j} : Finset (Fin (n + 1))).card := Finset.card_le_card hsub
    _ = 2 := by simp [hij]

/-- The collision deletion matrix in [MagniezZur2026], Equation (28). The entry for a row
`(r, z)` and a non-injective tuple `f` is `1` exactly when deleting coordinate `r` from `f`
produces `z`, and `0` otherwise. -/
def collisionDeletion (n N : ℕ) : Matrix (CollisionDeletionRow n N) (NonInjectiveTuple n N) ℂ :=
  fun row col => if deleteAt row.1 col.1 = row.2.1 then 1 else 0

/-- A collision deletion entry is nonzero exactly when the row tuple is the deletion of the
column tuple at the row coordinate. -/
lemma collisionDeletion_ne_zero_iff {n N : ℕ} (row : CollisionDeletionRow n N)
    (col : NonInjectiveTuple n N) :
    collisionDeletion n N row col ≠ 0 ↔ deleteAt row.1 col.1 = row.2.1 := by
  unfold collisionDeletion
  split_ifs <;> simp_all

/-- For tuple length `n + 1 ≥ 2`, every row of the collision deletion matrix has at most
`n` nonzero entries. A row supplies an injective tuple, so the label set is nonempty. -/
lemma collisionDeletion_row_card_le {n N : ℕ} (_hn : 0 < n)
    (row : CollisionDeletionRow n N) :
    (Finset.univ.filter
      (fun col : NonInjectiveTuple n N => collisionDeletion n N row col ≠ 0)).card ≤ n := by
  classical
  have hfilter : (Finset.univ.filter
        (fun col : NonInjectiveTuple n N => collisionDeletion n N row col ≠ 0))
      = Finset.univ.filter
        (fun col : NonInjectiveTuple n N => deleteAt row.1 col.1 = row.2.1) := by
    ext col
    simp [collisionDeletion_ne_zero_iff]
  rw [hfilter]
  exact row_card_le row.1 row.2

/-- Every column of the collision deletion matrix has at most two nonzero entries when
the label set has room for an injective `n`-tuple. -/
lemma collisionDeletion_col_card_le {n N : ℕ} (_hN : n ≤ N) (col : NonInjectiveTuple n N) :
    (Finset.univ.filter
      (fun row : CollisionDeletionRow n N => collisionDeletion n N row col ≠ 0)).card ≤ 2 := by
  classical
  let S : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun r => Function.Injective (deleteAt r col.1))
  let φ : {row : CollisionDeletionRow n N // collisionDeletion n N row col ≠ 0} → S :=
    fun row => by
      refine ⟨row.1.1, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      have hz : Function.Injective row.1.2.1 := row.1.2.2
      have hdel : deleteAt row.1.1 col.1 = row.1.2.1 :=
        (collisionDeletion_ne_zero_iff row.1 col).mp row.2
      simpa [hdel] using hz
  have hφinj : Function.Injective φ := by
    intro row₁ row₂ h
    have hcoord : row₁.1.1 = row₂.1.1 := congrArg (fun x : S => x.1) h
    rcases row₁ with ⟨⟨r₁, z₁⟩, h₁ne⟩
    rcases row₂ with ⟨⟨r₂, z₂⟩, h₂ne⟩
    simp only at hcoord
    subst hcoord
    have h₁ := (collisionDeletion_ne_zero_iff ⟨r₁, z₁⟩ col).mp h₁ne
    have h₂ := (collisionDeletion_ne_zero_iff ⟨r₁, z₂⟩ col).mp h₂ne
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (h₁.symm.trans h₂)))
  have hcard : Fintype.card {row : CollisionDeletionRow n N //
        collisionDeletion n N row col ≠ 0} ≤ Fintype.card S :=
    Fintype.card_le_of_injective φ hφinj
  have hScard : Fintype.card S ≤ 2 := by
    rw [Fintype.card_coe]
    simpa [S] using col_card_le col
  have hcard' : (Finset.univ.filter
      (fun row : CollisionDeletionRow n N => collisionDeletion n N row col ≠ 0)).card
        ≤ Fintype.card S := by
    simpa [Fintype.card_subtype] using hcard
  exact hcard'.trans hScard

/-- Every entry of the collision deletion matrix has norm at most one. -/
lemma collisionDeletion_norm_apply_le {n N : ℕ} (row : CollisionDeletionRow n N)
    (col : NonInjectiveTuple n N) : ‖collisionDeletion n N row col‖ ≤ 1 := by
  unfold collisionDeletion
  split_ifs <;> simp

/-- Sum of the norms of a family bounded by `1` is bounded by the number of nonzero entries. -/
lemma sum_norm_le_card_of_norm_le_one {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (k : ℕ)
    (hk : (Finset.univ.filter (fun i => f i ≠ 0)).card ≤ k) :
    ∑ i, ‖f i‖ ≤ (k : ℝ) := by
  classical
  calc
    (∑ i, ‖f i‖) = ∑ i ∈ (Finset.univ.filter (fun i => f i ≠ 0)), ‖f i‖ := by
      rw [Finset.sum_subset (Finset.filter_subset _ _)]
      intro x _ hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
      simp [hx]
    _ ≤ ∑ _i ∈ (Finset.univ.filter (fun i => f i ≠ 0)), (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => hf i
    _ = ((Finset.univ.filter (fun i => f i ≠ 0)).card : ℝ) := by simp
    _ ≤ (k : ℝ) := by exact_mod_cast hk

/-- A matrix with entries of norm at most one and at most `r` nonzero entries per row and
`k` per column has squared Euclidean action bounded by `r * k` times the squared input norm. -/
lemma sum_norm_mulVec_sq_le {R C : Type*} [Fintype R] [Fintype C]
    (B : Matrix R C ℂ) (r k : ℕ)
    (hrow : ∀ i, (Finset.univ.filter (fun j => B i j ≠ 0)).card ≤ r)
    (hcol : ∀ j, (Finset.univ.filter (fun i => B i j ≠ 0)).card ≤ k)
    (hbound : ∀ i j, ‖B i j‖ ≤ 1) (x : C → ℂ) :
    ∑ i, ‖∑ j, B i j * x j‖ ^ 2 ≤ ((r * k : ℕ) : ℝ) * ∑ j, ‖x j‖ ^ 2 := by
  classical
  have hrow_i (i : R) : ∑ j, (if B i j ≠ 0 then (1 : ℝ) else 0) ≤ (r : ℝ) := by
    rw [← Finset.natCast_card_filter (R := ℝ) (p := fun j => B i j ≠ 0) (s := Finset.univ)]
    exact_mod_cast hrow i
  have hper (i : R) :
      ‖∑ j, B i j * x j‖ ^ 2 ≤ (r : ℝ) * ∑ j, ‖B i j * x j‖ ^ 2 := by
    have hEq : (∑ j, (if B i j ≠ 0 then (1 : ℝ) else 0) * ‖B i j * x j‖)
        = ∑ j, ‖B i j * x j‖ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : B i j = 0 <;> simp [h]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset C)
      (fun j => if B i j ≠ 0 then (1 : ℝ) else 0) (fun j => ‖B i j * x j‖)
    have hsq : ∑ j, (if B i j ≠ 0 then (1 : ℝ) else 0) ^ 2 ≤ (r : ℝ) := by
      simpa using hrow_i i
    calc
      ‖∑ j, B i j * x j‖ ^ 2 ≤ (∑ j, ‖B i j * x j‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
      _ = (∑ j, (if B i j ≠ 0 then (1 : ℝ) else 0) * ‖B i j * x j‖) ^ 2 := by rw [hEq]
      _ ≤ (∑ j, (if B i j ≠ 0 then (1 : ℝ) else 0) ^ 2)
            * (∑ j, ‖B i j * x j‖ ^ 2) := hCS
      _ ≤ (r : ℝ) * ∑ j, ‖B i j * x j‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have houter : ∑ i, ‖∑ j, B i j * x j‖ ^ 2
      ≤ (r : ℝ) * ∑ i, ∑ j, ‖B i j * x j‖ ^ 2 := by
    calc
      ∑ i, ‖∑ j, B i j * x j‖ ^ 2
          ≤ ∑ i, (r : ℝ) * ∑ j, ‖B i j * x j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hper i
      _ = (r : ℝ) * ∑ i, ∑ j, ‖B i j * x j‖ ^ 2 := by rw [Finset.mul_sum]
  have hinner (j : C) : ∑ i, ‖B i j * x j‖ ^ 2 ≤ (k : ℝ) * ‖x j‖ ^ 2 := by
    have hterm (i : R) : ‖B i j * x j‖ ^ 2 = ‖B i j‖ ^ 2 * ‖x j‖ ^ 2 := by
      rw [norm_mul, mul_pow]
    calc
      ∑ i, ‖B i j * x j‖ ^ 2 = ∑ i, ‖B i j‖ ^ 2 * ‖x j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => hterm i
      _ = (∑ i, ‖B i j‖ ^ 2) * ‖x j‖ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (∑ i, ‖B i j‖) * ‖x j‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        refine Finset.sum_le_sum fun i _ => ?_
        have h0 := norm_nonneg (B i j)
        have h1 := hbound i j
        nlinarith
      _ ≤ (k : ℝ) * ‖x j‖ ^ 2 := by
        gcongr
        exact sum_norm_le_card_of_norm_le_one (fun i => B i j) (fun i => hbound i j) k (hcol j)
  calc
    ∑ i, ‖∑ j, B i j * x j‖ ^ 2
        ≤ (r : ℝ) * ∑ i, ∑ j, ‖B i j * x j‖ ^ 2 := houter
    _ = (r : ℝ) * ∑ j, ∑ i, ‖B i j * x j‖ ^ 2 := by rw [Finset.sum_comm]
    _ ≤ (r : ℝ) * ∑ j, (k : ℝ) * ‖x j‖ ^ 2 := by
      gcongr
      exact hinner _
    _ = ((r * k : ℕ) : ℝ) * ∑ j, ‖x j‖ ^ 2 := by
      rw [← Finset.mul_sum]
      push_cast
      ring

/-- The row type of the collision deletion matrix is nonempty once `n ≤ N`: use coordinate
zero and the injective tuple formed by the first `n` labels. -/
lemma collisionDeletionRow_nonempty {n N : ℕ} (hN : n ≤ N) :
    Nonempty (CollisionDeletionRow n N) :=
  ⟨⟨0, ⟨Fin.castLE hN, Fin.castLE_injective hN⟩⟩⟩

/-- The column type of the collision deletion matrix is nonempty for `0 < n` and nonzero `N`:
a constant tuple of length at least two is non-injective. -/
lemma nonInjectiveTuple_nonempty {n N : ℕ} (hn : 0 < n) [NeZero N] :
    Nonempty (NonInjectiveTuple n N) := by
  let a : Fin (n + 1) := ⟨0, by omega⟩
  let b : Fin (n + 1) := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  refine ⟨⟨fun _ => (0 : Fin N), ?_⟩⟩
  intro hinj
  exact hab (hinj rfl)

/-- The squared Euclidean action bound for the matrix in [MagniezZur2026], Equation (28).
The conditions `0 < n` and `n ≤ N` ensure that both indexing types are nonempty. -/
theorem collisionDeletion_action_sq_le {n N : ℕ} (hn : 0 < n) (hN : n ≤ N)
    (x : EuclideanSpace ℂ (NonInjectiveTuple n N)) :
    ‖(EuclideanSpace.equiv (CollisionDeletionRow n N) ℂ).symm
        (collisionDeletion n N *ᵥ WithLp.ofLp x)‖ ^ 2
      ≤ ((2 * n : ℕ) : ℝ) * ‖x‖ ^ 2 := by
  have hsum := sum_norm_mulVec_sq_le (collisionDeletion n N) n 2
    (collisionDeletion_row_card_le hn)
    (collisionDeletion_col_card_le hN)
    (fun row col => collisionDeletion_norm_apply_le row col)
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa [Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hsum (WithLp.ofLp x)

/-- A matrix-vector bound uniform over all vectors gives a Euclidean operator-norm bound. -/
lemma l2_opNorm_le_of_mulVec_norm_le {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq I] (A : Matrix O I ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : EuclideanSpace ℂ I,
      ‖(EuclideanSpace.equiv O ℂ).symm (A *ᵥ WithLp.ofLp x)‖ ≤ C * ‖x‖) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  exact h x

/-- The collision deletion matrix has Euclidean operator norm at most `√(2 n)`, where the tuple
length is `n + 1`. This is the operator-norm form of the estimate following [MagniezZur2026],
Equation (28). -/
theorem collisionDeletion_l2_opNorm_le {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    ‖collisionDeletion n N‖ ≤ Real.sqrt ((2 * n : ℕ) : ℝ) := by
  have hC : 0 ≤ ((2 * n : ℕ) : ℝ) := by positivity
  apply l2_opNorm_le_of_mulVec_norm_le _ (Real.sqrt_nonneg _)
  intro x
  calc
    ‖(EuclideanSpace.equiv (CollisionDeletionRow n N) ℂ).symm
        (collisionDeletion n N *ᵥ WithLp.ofLp x)‖
        = Real.sqrt (‖(EuclideanSpace.equiv (CollisionDeletionRow n N) ℂ).symm
            (collisionDeletion n N *ᵥ WithLp.ofLp x)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((2 * n : ℕ) : ℝ) * ‖x‖ ^ 2) :=
          Real.sqrt_le_sqrt (collisionDeletion_action_sq_le hn hN x)
    _ = Real.sqrt (((2 * n : ℕ) : ℝ)) * Real.sqrt (‖x‖ ^ 2) := Real.sqrt_mul hC _
    _ = Real.sqrt (((2 * n : ℕ) : ℝ)) * ‖x‖ := by rw [Real.sqrt_sq (norm_nonneg _)]

end Qatlib.Papers.CollisionLB26.DeleteNorm
