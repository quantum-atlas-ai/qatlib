/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.CssBuild.Classical
public import Qatlib.Papers.CssCodeCS96.Construction.Repetition
import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The Hamming code family as a bounded consumer

For every check dimension `m`, the Hamming check matrix lists every nonzero
binary vector of `Fin m → ZMod 2` as a column. The family has exact
parameters `[2^m - 1, 2^m - 1 - m, 3]` with `m ≥ 2`, and syndrome decoding
corrects every single error: a nonzero syndrome is itself the error column.
-/

namespace Qatlib.Papers.CssCodeCS96.Construction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.ErrorCorrection.CssBuild
open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Matrix

/-- In the binary field, `a + b = a` forces `b = 0`. -/
theorem zmod2_add_eq_left {a b : ZMod 2} (h : a + b = a) : b = 0 := by
  rcases zmod2_eq01 b with hb | hb
  · rw [hb]
  · subst hb
    rcases zmod2_eq01 a with ha | ha
    · subst ha
      exact absurd h (by decide)
    · subst ha
      exact absurd h (by decide)

/-- In the binary field, `a + b = b` forces `a = 0`. -/
theorem zmod2_add_eq_right {a b : ZMod 2} (h : a + b = b) : a = 0 := by
  rw [add_comm] at h
  exact zmod2_add_eq_left h

/-- Doubling a pointwise sum in characteristic two gives zero. -/
theorem zmod2_add_add (a b : ZMod 2) : a + b + (a + b) = 0 := by
  rw [add_add_add_comm, zmod2_add_self, zmod2_add_self, add_zero]

/-- A unit vector equals one on its own support. -/
theorem single_at {ι : Type*} [DecidableEq ι] (j : ι) :
    (Pi.single j (1 : ZMod 2) : ι → ZMod 2) j = 1 := by
  rw [Pi.single_apply]
  split
  · rfl
  · next h => exact absurd rfl h

/-- A unit vector vanishes off its support. -/
theorem single_off {ι : Type*} [DecidableEq ι] (j k : ι) (hk : ¬k = j) :
    (Pi.single j (1 : ZMod 2) : ι → ZMod 2) k = 0 := by
  rw [Pi.single_apply]
  split
  · next h => exact absurd h hk
  · rfl

/-- The weight of a sum of three distinct unit vectors is three. -/
theorem weight_three {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c : ι)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    bitWeight (Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2)
      + Pi.single c (1 : ZMod 2)) = 3 := by
  have hfilter : Finset.univ.filter (fun i => ((Pi.single a (1 : ZMod 2)
      + Pi.single b (1 : ZMod 2) + Pi.single c (1 : ZMod 2) : ι → ZMod 2)) i ≠ 0)
      = {a, b, c} := by
    ext i
    simp only [Pi.add_apply, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rcases eq_or_ne i a with h | h
    · rw [h, single_at a, single_off b a hab, single_off c a hac]
      simp
    rcases eq_or_ne i b with h2 | h2
    · rw [h2, single_off a b (Ne.symm hab), single_at b, single_off c b hbc]
      simp
    rcases eq_or_ne i c with h3 | h3
    · rw [h3, single_off a c (Ne.symm hac), single_off b c (Ne.symm hbc), single_at c]
      simp
    · rw [single_off a i h, single_off b i h2, single_off c i h3]
      simp only [add_zero, ne_eq, not_true, false_iff, not_or]
      exact ⟨h, h2, h3⟩
  simp only [bitWeight, hfilter]
  rw [Finset.card_insert_of_notMem (fun h => by
        rcases Finset.mem_insert.mp h with h' | h'
        · exact hab h'
        · exact hac (Finset.mem_singleton.mp h')),
    Finset.card_insert_of_notMem (fun h => hbc (Finset.mem_singleton.mp h)),
    Finset.card_singleton]

/-- A binary vector of weight at most one is zero or a unit vector. -/
theorem bitWeight_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → ZMod 2}
    (he : bitWeight e ≤ 1) : e = 0 ∨ ∃ j, e = Pi.single j 1 := by
  rcases eq_or_ne e 0 with h | h
  · exact Or.inl h
  · right
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    have hj1 : e j = 1 := by
      rcases zmod2_eq01 (e j) with h0 | h1
      · exact absurd h0 hj
      · exact h1
    refine ⟨j, funext fun k => ?_⟩
    by_cases hk : k = j
    · rw [hk, hj1, single_at j]
    · have hk0 : e k = 0 := by
        rcases zmod2_eq01 (e k) with h0 | h1
        · exact h0
        · exfalso
          have hsub : ({j, k} : Finset ι) ⊆
              Finset.univ.filter fun i => e i ≠ 0 := by
            intro i hi
            rw [Finset.mem_insert, Finset.mem_singleton] at hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hi with hi | hi
            · rw [hi]; exact hj
            · rw [hi, h1]
              decide
          have h3 := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem
            (fun h => hk (Finset.mem_singleton.mp h).symm)] at h3
          rw [Finset.card_singleton] at h3
          simp only [bitWeight] at he
          omega
      rw [hk0, single_off j k hk]

/-- A binary vector of weight at most two is zero, a unit vector, or the sum
of two distinct unit vectors. -/
theorem bitWeight_le_two {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → ZMod 2}
    (he : bitWeight e ≤ 2) :
    e = 0 ∨ (∃ j, e = Pi.single j 1)
      ∨ ∃ j k, j ≠ k ∧ e = Pi.single j 1 + Pi.single k 1 := by
  rcases eq_or_ne e 0 with h0 | h0
  · exact Or.inl h0
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h0
    have hjne : e j ≠ 0 := hj
    have hj1 : e j = 1 := (zmod2_eq01 _).resolve_left hj
    by_cases hsecond : ∃ k, k ≠ j ∧ e k ≠ 0
    · obtain ⟨k, hkj, hk⟩ := hsecond
      have hk1 : e k = 1 := by
        rcases zmod2_eq01 (e k) with h0 | h1
        · exact absurd h0 hk
        · exact h1
      refine Or.inr (Or.inr ⟨j, k, Ne.symm hkj, funext fun l => ?_⟩)
      show e l = ((Pi.single j (1 : ZMod 2) : ι → ZMod 2)
        + (Pi.single k (1 : ZMod 2) : ι → ZMod 2)) l
      rw [Pi.add_apply]
      by_cases hlj : l = j
      · rw [hlj, hj1, single_at j, single_off k j (Ne.symm hkj)]
        simp
      by_cases hlk : l = k
      · rw [hlk, hk1, single_at k, single_off j k hkj]
        simp
      · have hl0 : e l = 0 := by
          rcases zmod2_eq01 (e l) with h0 | h1
          · exact h0
          · exfalso
            have hsub : ({j, k, l} : Finset ι) ⊆
                Finset.univ.filter fun i => e i ≠ 0 := by
              intro i hi
              simp only [Finset.mem_insert, Finset.mem_singleton] at hi
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rcases hi with hi | hi | hi
              · rw [hi]; exact hjne
              · rw [hi]; exact hk
              · rw [hi, h1]
                decide
            have h4 := Finset.card_le_card hsub
            have hcard : ({j, k, l} : Finset ι).card = 3 := by
              rw [Finset.card_insert_of_notMem
                    (fun h => by
                      rcases Finset.mem_insert.mp h with h' | h'
                      · exact Ne.symm hkj h'
                      · exact Ne.symm hlj (Finset.mem_singleton.mp h')),
                Finset.card_insert_of_notMem
                  (fun h => hlk (Finset.mem_singleton.mp h).symm),
                Finset.card_singleton]
            rw [hcard] at h4
            simp only [bitWeight] at he
            omega
        rw [hl0, single_off j l hlj, single_off k l hlk]
        simp
    · refine Or.inr (Or.inl ⟨j, funext fun l => ?_⟩)
      by_cases hlj : l = j
      · rw [hlj, hj1, single_at j]
      · have hl0 : e l = 0 := by
          rcases eq_or_ne (e l) 0 with h0 | h0
          · exact h0
          · exact absurd ⟨l, hlj, h0⟩ hsecond
        rw [hl0, single_off j l hlj]

/-- The Hamming check matrix: every column is a nonzero binary vector. -/
def hamCheck (m : ℕ) : Matrix (Fin m) {v : Fin m → ZMod 2 // v ≠ 0} (ZMod 2) :=
  Matrix.of fun i w => (w : Fin m → ZMod 2) i

/-- The Hamming code as a shared-component consumer. -/
def hamCode (m : ℕ) : ClCode {v : Fin m → ZMod 2 // v ≠ 0} (Fin m) where
  h := hamCheck m

/-- The Hamming columns are the nonzero vectors themselves. -/
theorem hamCol_eq (m : ℕ) (w : {v : Fin m → ZMod 2 // v ≠ 0}) :
    (hamCheck m).col w = (w : Fin m → ZMod 2) := rfl

/-- Every Hamming column is nonzero. -/
theorem hamCol_ne (m : ℕ) (w : {v : Fin m → ZMod 2 // v ≠ 0}) :
    (hamCheck m).col w ≠ 0 := w.property

/-- Distinct columns come from distinct column indices. -/
theorem hamCol_inj (m : ℕ) {w w' : {v : Fin m → ZMod 2 // v ≠ 0}}
    (h : (hamCheck m).col w = (hamCheck m).col w') : w = w' :=
  Subtype.ext h

/-- Unit vectors among the Hamming columns. -/
def hamUnit (m : ℕ) (i : Fin m) : {v : Fin m → ZMod 2 // v ≠ 0} :=
  ⟨Pi.single i 1, by
    intro h
    have := congrFun h i
    simp at this⟩

/-- The unit columns assemble the identity submatrix. -/
theorem hamUnit_sub (m : ℕ) :
    (hamCheck m).submatrix id (hamUnit m) = 1 := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, hamCheck, Matrix.of_apply, hamUnit]
  rw [Pi.single_apply, Matrix.one_apply]

/-- The Hamming check matrix has full row rank. -/
theorem hamRank (m : ℕ) : Matrix.rank (hamCheck m) = m := by
  have hge := Matrix.rank_submatrix_le (hamCheck m) id (hamUnit m)
  rw [hamUnit_sub, Matrix.rank_one, Fintype.card_fin] at hge
  have hle : Matrix.rank (hamCheck m) ≤ Fintype.card (Fin m) :=
    Matrix.rank_le_card_height _
  rw [Fintype.card_fin] at hle
  exact Nat.le_antisymm hle hge

/-- The Hamming coordinate count is the number of nonzero binary vectors. -/
theorem hamCard (m : ℕ) :
    Fintype.card {v : Fin m → ZMod 2 // v ≠ 0} = 2 ^ m - 1 := by
  classical
  have htotal : Fintype.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Fintype.card_pi]
    simp
  have hfilter := Finset.card_filter_add_card_filter_not
    (p := fun v : Fin m → ZMod 2 => v ≠ 0) (s := Finset.univ)
  have hzero : Finset.univ.filter (fun v : Fin m → ZMod 2 => ¬v ≠ 0) = {0} := by
    ext v
    simp
  rw [hzero, Finset.card_singleton, Finset.card_univ, htotal] at hfilter
  rw [Fintype.card_subtype]
  omega

/-- Hamming syndrome decoding: a nonzero syndrome is the error column. -/
def hamDecode (m : ℕ) :
    (Fin m → ZMod 2) → {v : Fin m → ZMod 2 // v ≠ 0} → ZMod 2 :=
  fun s => if h : s ≠ 0 then Pi.single ⟨s, h⟩ 1 else 0

/-- Hamming syndrome decoding corrects every single error. -/
theorem hamSyn (m : ℕ) : BoundDecode (hamCode m) (hamDecode m) 1 := by
  intro e he
  rcases bitWeight_le_one he with h0 | ⟨j, hj⟩
  · rw [h0]
    show hamDecode m ((hamCheck m) *ᵥ 0) = 0
    rw [Matrix.mulVec_zero]
    simp [hamDecode]
  · rw [hj]
    show hamDecode m ((hamCheck m) *ᵥ (Pi.single j 1)) = Pi.single j 1
    rw [Matrix.mulVec_single_one, hamCol_eq]
    simp only [hamDecode]
    split
    · rfl
    · next h => exact absurd j.property h

/-- The Hamming distance is exactly three whenever two checks exist. -/
theorem hamDist (m : ℕ) (hm : 2 ≤ m) : minDist (hamCode m) = (3 : ℕ∞) := by
  obtain ⟨z0, hz0⟩ : ∃ z0 : Fin m, (z0 : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨z1, hz1⟩ : ∃ z1 : Fin m, (z1 : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hex : z1 ≠ z0 := by
    intro h
    have hval := congrArg Fin.val h
    rw [hz1, hz0] at hval
    simp at hval
  obtain ⟨u, hu⟩ : ∃ u : {v : Fin m → ZMod 2 // v ≠ 0},
      (hamCheck m).col u = ((Pi.single z0 (1 : ZMod 2) : Fin m → ZMod 2)) :=
    ⟨hamUnit m z0, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : {v : Fin m → ZMod 2 // v ≠ 0},
      (hamCheck m).col v = ((Pi.single z1 (1 : ZMod 2) : Fin m → ZMod 2)) :=
    ⟨hamUnit m z1, rfl⟩
  have huv : u ≠ v := by
    intro h
    have hfun : ((Pi.single z0 (1 : ZMod 2) : Fin m → ZMod 2)) z0
        = ((Pi.single z1 (1 : ZMod 2) : Fin m → ZMod 2)) z0 := by
      rw [← hu, ← hv, h]
    rw [single_at z0, single_off z1 z0 (Ne.symm hex)] at hfun
    simp at hfun
  have hsum : (hamCheck m).col u + (hamCheck m).col v ≠ 0 := by
    intro h
    apply huv
    apply hamCol_inj m
    funext i
    exact zmod2_eq_of (by simpa using congrFun h i)
  obtain ⟨l, hl⟩ : ∃ l : {v : Fin m → ZMod 2 // v ≠ 0},
      (hamCheck m).col l = (hamCheck m).col u + (hamCheck m).col v :=
    ⟨⟨_, hsum⟩, rfl⟩
  have hlu : l ≠ u := by
    intro h
    rw [h] at hl
    have hzero : (hamCheck m).col v = 0 := by
      funext i
      have hi : (hamCheck m).col u i + (hamCheck m).col v i = (hamCheck m).col u i := by
        simpa using congrFun hl i
      exact zmod2_add_eq_left hi
    exact hamCol_ne m v hzero
  have hlv : l ≠ v := by
    intro h
    rw [h] at hl
    have hzero : (hamCheck m).col u = 0 := by
      funext i
      have hi : (hamCheck m).col u i + (hamCheck m).col v i = (hamCheck m).col v i := by
        simpa using congrFun hl i
      exact zmod2_add_eq_right hi
    exact hamCol_ne m u hzero
  refine dist_eq (hamCode m) 3
    (w := Pi.single u 1 + Pi.single v 1 + Pi.single l 1) ?_ ?_ ?_ ?_
  · refine (mem_words _ _).mpr (funext fun i => ?_)
    show ((hamCheck m) *ᵥ (Pi.single u 1 + Pi.single v 1
        + Pi.single l 1)) i = (0 : Fin m → ZMod 2) i
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one, Matrix.mulVec_single_one, hl, Pi.add_apply, Pi.zero_apply]
    exact zmod2_add_add _ _
  · intro hzero
    have hfun := congrFun hzero u
    simp only [Pi.add_apply, Pi.zero_apply] at hfun
    rw [single_at u, single_off v u huv, single_off l u (Ne.symm hlu)] at hfun
    simp at hfun
  · exact weight_three u v l huv (Ne.symm hlu) (Ne.symm hlv)
  · intro v hv hne0
    by_contra hcon
    rw [not_le] at hcon
    have hs : (hamCheck m) *ᵥ v = 0 := (mem_words _ _).mp hv
    have h2le : bitWeight v ≤ 2 := by omega
    rcases bitWeight_le_two h2le with h0 | ⟨j, hj⟩ | ⟨j, k, hkj, hjk⟩
    · exact hne0 h0
    · rw [hj, Matrix.mulVec_single_one] at hs
      exact hamCol_ne m j hs
    · rw [hjk, Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hs
      exact hkj (hamCol_inj m (funext fun i => zmod2_eq_of (by simpa using congrFun hs i)))

/-- The Hamming family has the exact textbook parameters. -/
theorem hamParams (m : ℕ) (hm : 2 ≤ m) :
    Fintype.card {v : Fin m → ZMod 2 // v ≠ 0} = 2 ^ m - 1 ∧
      codeDim (hamCode m) = 2 ^ m - 1 - m ∧ minDist (hamCode m) = (3 : ℕ∞) :=
  ⟨hamCard m, by
    have h := dim_add_rank (hamCode m)
    rw [show (hamCode m).h = hamCheck m from rfl, hamRank, hamCard] at h
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 ^ m := ⟨_, rfl⟩
    rw [← hN] at h
    rw [← hN]
    omega, hamDist m hm⟩

end Qatlib.Papers.CssCodeCS96.Construction
