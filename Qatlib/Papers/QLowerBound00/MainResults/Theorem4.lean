/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLowerBound00.MainResults.Theorem2
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.Theorem4

open Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

open Qatlib.Papers.QLowerBound00.MainResults.Theorem2 (source_theorem2)

def blockOf (k : ℕ) (p : Fin (k * k)) : Fin k :=
  ((@finProdFinEquiv k k).symm p).1

def withinBlock (k : ℕ) (p : Fin (k * k)) : Fin k :=
  ((@finProdFinEquiv k k).symm p).2

@[simp] theorem blockOf_mk (k : ℕ) (b j : Fin k) :
    blockOf k (@finProdFinEquiv k k (b, j)) = b := by simp [blockOf]

@[simp] theorem withinBlock_mk (k : ℕ) (b j : Fin k) :
    withinBlock k (@finProdFinEquiv k k (b, j)) = j := by simp [withinBlock]

theorem mk_blockWithin (k : ℕ) (p : Fin (k * k)) :
    @finProdFinEquiv k k (blockOf k p, withinBlock k p) = p := by
  simpa [blockOf, withinBlock] using Equiv.apply_symm_apply (@finProdFinEquiv k k) p

theorem input_eq_mk {k : ℕ} (p : Fin (k * k)) {b j : Fin k}
    (hb : blockOf k p = b) (hj : withinBlock k p = j) :
    p = @finProdFinEquiv k k (b, j) := by
  rw [← mk_blockWithin k p, hb, hj]

theorem bool_eq_not {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

theorem eq_true_of_ne_false {b : Bool} (h : b ≠ false) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem eq_false_of_ne_true {b : Bool} (h : b ≠ true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

def andOfOrs (k : ℕ) (x : Input (k * k)) : Bool := by
  classical
  exact decide (∀ b : Fin k, ∃ j : Fin k, x (@finProdFinEquiv k k (b, j)) = true)

def zeroBlock (k : ℕ) (x : Input (k * k)) (b : Fin k) : Input (k * k) :=
  fun p => if blockOf k p = b then false else x p

theorem zeroBlock_apply (k : ℕ) (x : Input (k * k)) (b : Fin k) (p : Fin (k * k)) :
    zeroBlock k x b p = if blockOf k p = b then false else x p := rfl

@[simp] theorem zeroBlock_mk (k : ℕ) (x : Input (k * k)) (b b' j : Fin k) :
    zeroBlock k x b (@finProdFinEquiv k k (b', j)) =
      if b' = b then false else x (@finProdFinEquiv k k (b', j)) := by
  rw [zeroBlock_apply, blockOf_mk]

def fillBlock (k : ℕ) (y : Input (k * k)) (b j : Fin k) : Input (k * k) :=
  fun p => if p = @finProdFinEquiv k k (b, j) then true else y p

theorem fillBlock_apply (k : ℕ) (y : Input (k * k)) (b j : Fin k) (p : Fin (k * k)) :
    fillBlock k y b j p = if p = @finProdFinEquiv k k (b, j) then true else y p := rfl

def flipAt (k : ℕ) (x : Input (k * k)) (i : Fin (k * k)) : Input (k * k) :=
  fun p => if p = i then !x i else x p

theorem flipAt_apply (k : ℕ) (x : Input (k * k)) (i p : Fin (k * k)) :
    flipAt k x i p = if p = i then !x i else x p := rfl

theorem eq_flipAt_of_diff {k : ℕ} {u v : Input (k * k)} {i : Fin (k * k)}
    (hagree : ∀ j, j ≠ i → u j = v j) (hne : u i ≠ v i) : v = flipAt k u i := by
  funext p
  rw [flipAt_apply]
  by_cases hp : p = i
  · subst hp
    rw [if_pos rfl, bool_eq_not (Ne.symm hne)]
  · rw [if_neg hp]; exact (hagree p hp).symm

theorem flipAt_eq_of_diff {k : ℕ} {u v : Input (k * k)} {i : Fin (k * k)}
    (hagree : ∀ j, j ≠ i → u j = v j) (hne : u i ≠ v i) : u = flipAt k v i := by
  funext p
  rw [flipAt_apply]
  by_cases hp : p = i
  · subst hp
    rw [if_pos rfl, bool_eq_not hne]
  · rw [if_neg hp]; exact hagree p hp

def Xset (k : ℕ) : Finset (Input (k * k)) := by
  classical
  exact univ.filter (fun x => ∀ b : Fin k, ∃! j : Fin k, x (@finProdFinEquiv k k (b, j)) = true)

def Yset (k : ℕ) : Finset (Input (k * k)) := by
  classical
  exact univ.filter (fun y => ∃ b0 : Fin k,
    (∀ j : Fin k, y (@finProdFinEquiv k k (b0, j)) = false) ∧
      (∀ b : Fin k, b ≠ b0 → ∃! j : Fin k, y (@finProdFinEquiv k k (b, j)) = true))

def Rset (k : ℕ) : Finset (InputPair (k * k)) := by
  classical
  exact univ.filter (fun p =>
    p.1 ∈ Xset k ∧ p.2 ∈ Yset k ∧
      ∃ i : Fin (k * k), p.1 i ≠ p.2 i ∧ ∀ j : Fin (k * k), j ≠ i → p.1 j = p.2 j)

theorem mem_Xset {k : ℕ} {x : Input (k * k)} :
    x ∈ Xset k ↔ ∀ b : Fin k, ∃! j : Fin k, x (@finProdFinEquiv k k (b, j)) = true := by
  classical
  simp only [Xset, mem_filter, mem_univ, true_and]

theorem mem_Yset {k : ℕ} {y : Input (k * k)} :
    y ∈ Yset k ↔ ∃ b0 : Fin k,
      (∀ j : Fin k, y (@finProdFinEquiv k k (b0, j)) = false) ∧
        (∀ b : Fin k, b ≠ b0 → ∃! j : Fin k, y (@finProdFinEquiv k k (b, j)) = true) := by
  classical
  simp only [Yset, mem_filter, mem_univ, true_and]

theorem mem_Rset {k : ℕ} {p : InputPair (k * k)} :
    p ∈ Rset k ↔ p.1 ∈ Xset k ∧ p.2 ∈ Yset k ∧
      ∃ i : Fin (k * k), p.1 i ≠ p.2 i ∧ ∀ j : Fin (k * k), j ≠ i → p.1 j = p.2 j := by
  classical
  simp only [Rset, mem_filter, mem_univ, true_and]

theorem mem_Rset_pair {k : ℕ} {x y : Input (k * k)} :
    (x, y) ∈ Rset k ↔ x ∈ Xset k ∧ y ∈ Yset k ∧
      ∃ i : Fin (k * k), x i ≠ y i ∧ ∀ j : Fin (k * k), j ≠ i → x j = y j := by
  simp only [mem_Rset, Prod.fst, Prod.snd]

theorem zeroBlock_mem_Yset {k : ℕ} {x : Input (k * k)} (hx : x ∈ Xset k)
    (b : Fin k) : zeroBlock k x b ∈ Yset k := by
  rw [mem_Yset]
  refine ⟨b, ?_, ?_⟩
  · intro j
    rw [zeroBlock_mk, if_pos rfl]
  · intro b' hb'
    obtain ⟨j0, hj0, huniq⟩ := (mem_Xset.mp hx) b'
    refine ⟨j0, ?_, ?_⟩
    · show zeroBlock k x b (@finProdFinEquiv k k (b', j0)) = true
      rw [zeroBlock_mk, if_neg hb', hj0]
    · intro j' hj'
      have hj'' : zeroBlock k x b (@finProdFinEquiv k k (b', j')) = true := hj'
      rw [zeroBlock_mk, if_neg hb'] at hj''
      exact huniq j' hj''

theorem zeroBlock_diff {k : ℕ} {x : Input (k * k)} (hx : x ∈ Xset k) (b : Fin k) :
    ∃ i : Fin (k * k), x i ≠ zeroBlock k x b i ∧
      ∀ j : Fin (k * k), j ≠ i → x j = zeroBlock k x b j := by
  obtain ⟨j0, hj0, huniq⟩ := (mem_Xset.mp hx) b
  refine ⟨@finProdFinEquiv k k (b, j0), ?_, ?_⟩
  · rw [zeroBlock_mk, if_pos rfl, hj0]
    exact (by decide : (true : Bool) ≠ false)
  · intro p hp
    show x p = (if blockOf k p = b then false else x p)
    by_cases hpb : blockOf k p = b
    · rw [if_pos hpb]
      have hp_eq : p = @finProdFinEquiv k k (b, withinBlock k p) := input_eq_mk p hpb rfl
      have hxpt : x p = false := by
        by_contra h
        have htrue : x p = true := eq_true_of_ne_false h
        have harg : x (@finProdFinEquiv k k (b, withinBlock k p)) = true := by
          rw [← hp_eq]; exact htrue
        have hwi : withinBlock k p = j0 := huniq (withinBlock k p) harg
        exact hp (by rw [hp_eq, hwi])
      exact hxpt
    · rw [if_neg hpb]

theorem R_pair_eq_zeroBlock {k : ℕ} {x y : Input (k * k)} (hx : x ∈ Xset k)
    (hR : (x, y) ∈ Rset k) : ∃ b : Fin k, y = zeroBlock k x b := by
  obtain ⟨_, hyY, i, hne, hagree⟩ := mem_Rset_pair.mp hR

  have hxi : x i = true := by
    by_cases h : x i = true
    · exact h
    · exfalso
      have hxif : x i = false := eq_false_of_ne_true h
      have hyi : y i = true := by
        cases hv : y i
        · exact absurd (hxif.trans hv.symm) hne
        · rfl
      obtain ⟨b0, hzero, hrest⟩ := mem_Yset.mp hyY
      have hb_ne : blockOf k i ≠ b0 := by
        intro hb
        have hi : i = @finProdFinEquiv k k (b0, withinBlock k i) := by
          have h0 : i = @finProdFinEquiv k k (blockOf k i, withinBlock k i) :=
            (mk_blockWithin k i).symm
          rw [hb] at h0
          exact h0
        have hfalse : y i = false := by rw [hi]; exact hzero (withinBlock k i)
        rw [hfalse] at hyi
        exact absurd hyi (by decide)
      obtain ⟨j, hj, huniq⟩ := hrest (blockOf k i) hb_ne
      have hi : i = @finProdFinEquiv k k (blockOf k i, withinBlock k i) :=
        (mk_blockWithin k i).symm
      have hy_at : y (@finProdFinEquiv k k (blockOf k i, withinBlock k i)) = true := by
        rw [← hi]; exact hyi
      have hwi : withinBlock k i = j := huniq (withinBlock k i) hy_at
      obtain ⟨j', hj', huniq'⟩ := (mem_Xset.mp hx) (blockOf k i)
      have hwi' : withinBlock k i ≠ j' := by
        intro hc
        have harg : x (@finProdFinEquiv k k (blockOf k i, withinBlock k i)) = true := by
          rw [hc]; exact hj'
        have htrue : x i = true := by
          rw [← hi] at harg
          exact harg
        rw [hxif] at htrue
        exact absurd htrue (by decide)
      have hpos_ne : @finProdFinEquiv k k (blockOf k i, j') ≠ i := by
        intro hc
        apply hwi'
        rw [hi] at hc
        exact (congrArg Prod.snd ((@finProdFinEquiv k k).injective hc)).symm
      have hytrue : y (@finProdFinEquiv k k (blockOf k i, j')) = true := by
        rw [← hagree _ hpos_ne, hj']
      have huniqj : j' = withinBlock k i := (huniq j' hytrue).trans hwi.symm
      exact hwi' huniqj.symm
  have hyi : y i = false := by
    cases hv : y i
    · rfl
    · exact absurd (hxi.trans hv.symm) hne
  refine ⟨blockOf k i, ?_⟩
  funext p
  show y p = (if blockOf k p = blockOf k i then false else x p)
  by_cases hpi : p = i
  · subst hpi
    rw [if_pos rfl]
    exact hyi
  · rw [← hagree p hpi]
    by_cases hpb : blockOf k p = blockOf k i
    · rw [if_pos hpb]
      obtain ⟨j0, hj0, huniq⟩ := (mem_Xset.mp hx) (blockOf k p)
      have hp_eq : p = @finProdFinEquiv k k (blockOf k p, withinBlock k p) := input_eq_mk p rfl rfl
      have hi_eq : i = @finProdFinEquiv k k (blockOf k p, withinBlock k i) := by
        have h0 : i = @finProdFinEquiv k k (blockOf k i, withinBlock k i) :=
          (mk_blockWithin k i).symm
        rw [hpb.symm] at h0
        exact h0
      by_cases hxp : x p = true
      · have hargp : x (@finProdFinEquiv k k (blockOf k p, withinBlock k p)) = true := by
          rw [← hp_eq]; exact hxp
        have hargi : x (@finProdFinEquiv k k (blockOf k p, withinBlock k i)) = true := by
          rw [← hi_eq]; exact hxi
        have hwi : withinBlock k p = j0 := huniq (withinBlock k p) hargp
        have hwi' : withinBlock k i = j0 := huniq (withinBlock k i) hargi
        exact absurd (by rw [hp_eq, hi_eq, hwi, hwi']) hpi
      · exact eq_false_of_ne_true hxp
    · rw [if_neg hpb]

theorem zeroBlock_inj {k : ℕ} {x : Input (k * k)} (hx : x ∈ Xset k) :
    Function.Injective (fun b : Fin k => zeroBlock k x b) := by
  intro b b' hbb
  by_contra hne
  obtain ⟨j, hj, -⟩ := (mem_Xset.mp hx) b'
  have key : zeroBlock k x b (@finProdFinEquiv k k (b', j)) =
      zeroBlock k x b' (@finProdFinEquiv k k (b', j)) := congrFun hbb _
  have h1 : zeroBlock k x b (@finProdFinEquiv k k (b', j)) = true := by
    rw [zeroBlock_mk, if_neg (Ne.symm hne), hj]
  have h2 : zeroBlock k x b' (@finProdFinEquiv k k (b', j)) = false := by
    rw [zeroBlock_mk, if_pos rfl]
  rw [h1, h2] at key
  exact absurd key (by decide)

theorem pair_zeroBlock_inj {k : ℕ} {x : Input (k * k)} (hx : x ∈ Xset k) :
    Function.Injective (fun b : Fin k => (x, zeroBlock k x b)) := by
  intro b b' h
  exact zeroBlock_inj hx (congrArg Prod.snd h)

theorem fiber_R_X {k : ℕ} {x : Input (k * k)} (hx : x ∈ Xset k) :
    (Rset k).filter (fun p => p.1 = x) =
      (univ : Finset (Fin k)).image (fun b => (x, zeroBlock k x b)) := by
  classical
  ext p
  obtain ⟨a, b⟩ := p
  simp only [mem_filter, mem_image, mem_univ, true_and, Prod.fst, Prod.snd, Prod.mk.injEq]
  constructor
  · rintro ⟨hpR, rfl⟩
    obtain ⟨bb, hbb⟩ := R_pair_eq_zeroBlock hx hpR
    exact ⟨bb, rfl, hbb.symm⟩
  · rintro ⟨bb, rfl, hbb⟩
    rw [← hbb]
    exact ⟨mem_Rset_pair.mpr ⟨hx, zeroBlock_mem_Yset hx bb, zeroBlock_diff hx bb⟩, rfl⟩

theorem card_fiber_X {k : ℕ} {x : Input (k * k)} (hx : x ∈ Xset k) :
    ((Rset k).filter (fun p => p.1 = x)).card = k := by
  rw [fiber_R_X hx, Finset.card_image_of_injective _ (pair_zeroBlock_inj hx), card_univ,
    Fintype.card_fin]

theorem R_pair_eq_fillBlock {k : ℕ} {x y : Input (k * k)} {b0 : Fin k}
    (hzero : ∀ j, y (@finProdFinEquiv k k (b0, j)) = false)
    (hrest : ∀ b, b ≠ b0 → ∃! j, y (@finProdFinEquiv k k (b, j)) = true)
    (hxX : x ∈ Xset k) (hR : (x, y) ∈ Rset k) : ∃ j : Fin k, x = fillBlock k y b0 j := by
  obtain ⟨_, _, i, hne, hagree⟩ := mem_Rset_pair.mp hR

  have hyi : y i = false := by
    by_cases h : y i = false
    · exact h
    · exfalso
      have hyit : y i = true := eq_true_of_ne_false h
      have hb_ne : blockOf k i ≠ b0 := by
        intro hb
        have hi : i = @finProdFinEquiv k k (b0, withinBlock k i) := by
          have h0 : i = @finProdFinEquiv k k (blockOf k i, withinBlock k i) :=
            (mk_blockWithin k i).symm
          rw [hb] at h0
          exact h0
        have hfalse : y i = false := by rw [hi]; exact hzero (withinBlock k i)
        rw [hfalse] at hyit
        exact absurd hyit (by decide)
      obtain ⟨j, hj, huniq⟩ := hrest (blockOf k i) hb_ne
      have hi : i = @finProdFinEquiv k k (blockOf k i, withinBlock k i) :=
        (mk_blockWithin k i).symm
      have hy_at : y (@finProdFinEquiv k k (blockOf k i, withinBlock k i)) = true := by
        rw [← hi]; exact hyit
      have hwi : withinBlock k i = j := huniq (withinBlock k i) hy_at
      have hxif : x i = false := by
        cases hx' : x i
        · rfl
        · exact absurd (hx'.trans hyit.symm) hne
      obtain ⟨j', hj', huniq'⟩ := (mem_Xset.mp hxX) (blockOf k i)
      have hwi' : withinBlock k i ≠ j' := by
        intro hc
        have harg : x (@finProdFinEquiv k k (blockOf k i, withinBlock k i)) = true := by
          rw [hc]; exact hj'
        have htrue : x i = true := by
          rw [← hi] at harg
          exact harg
        rw [hxif] at htrue
        exact absurd htrue (by decide)
      have hpos_ne : @finProdFinEquiv k k (blockOf k i, j') ≠ i := by
        intro hc
        apply hwi'
        rw [hi] at hc
        exact (congrArg Prod.snd ((@finProdFinEquiv k k).injective hc)).symm
      have hytrue : y (@finProdFinEquiv k k (blockOf k i, j')) = true := by
        rw [← hagree _ hpos_ne, hj']
      have huniqj : j' = withinBlock k i := (huniq j' hytrue).trans hwi.symm
      exact hwi' huniqj.symm

  have hxi : x i = true := by
    cases hx' : x i
    · exact absurd (hx'.trans hyi.symm) hne
    · rfl

  have hb0i : blockOf k i = b0 := by
    by_contra hne'
    obtain ⟨j, hj, huniq⟩ := hrest (blockOf k i) hne'
    have hi : i = @finProdFinEquiv k k (blockOf k i, withinBlock k i) :=
      (mk_blockWithin k i).symm
    have hwi : withinBlock k i ≠ j := by
      intro hc
      have harg : y (@finProdFinEquiv k k (blockOf k i, withinBlock k i)) = true := by
        rw [hc]; exact hj
      have htrue : y i = true := by
        rw [← hi] at harg
        exact harg
      rw [hyi] at htrue
      exact absurd htrue (by decide)
    obtain ⟨j', hj', huniq'⟩ := (mem_Xset.mp hxX) (blockOf k i)
    have hpos_ne : @finProdFinEquiv k k (blockOf k i, j) ≠ i := by
      intro hc
      apply hwi
      rw [hi] at hc
      exact (congrArg Prod.snd ((@finProdFinEquiv k k).injective hc)).symm
    have hxtrue : x (@finProdFinEquiv k k (blockOf k i, j)) = true := by
      rw [hagree _ hpos_ne, hj]
    have huniq_j : j = withinBlock k i := by
      have h1 : j = j' := huniq' j hxtrue
      have hargi : x (@finProdFinEquiv k k (blockOf k i, withinBlock k i)) = true := by
        rw [← hi]; exact hxi
      have h2 : withinBlock k i = j' := huniq' (withinBlock k i) hargi
      exact h1.trans h2.symm
    exact hwi huniq_j.symm
  refine ⟨withinBlock k i, ?_⟩
  funext p
  show x p = (if p = @finProdFinEquiv k k (b0, withinBlock k i) then true else y p)
  have hi_mk : i = @finProdFinEquiv k k (b0, withinBlock k i) := input_eq_mk i hb0i rfl
  by_cases hpi : p = i
  · rw [hpi, if_pos hi_mk]
    exact hxi
  · rw [if_neg (by rw [← hi_mk]; exact hpi), hagree p hpi]

theorem fillBlock_mem_Xset {k : ℕ} {y : Input (k * k)} {b0 : Fin k}
    (hzero : ∀ j, y (@finProdFinEquiv k k (b0, j)) = false)
    (hrest : ∀ b, b ≠ b0 → ∃! j, y (@finProdFinEquiv k k (b, j)) = true)
    (jj : Fin k) : fillBlock k y b0 jj ∈ Xset k := by
  rw [mem_Xset]
  intro b
  by_cases hb : b = b0
  · rw [hb]
    refine ⟨jj, ?_, ?_⟩
    · show fillBlock k y b0 jj (@finProdFinEquiv k k (b0, jj)) = true
      rw [fillBlock_apply, if_pos rfl]
    · intro j' hj'
      have hj'' : fillBlock k y b0 jj (@finProdFinEquiv k k (b0, j')) = true := hj'
      rw [fillBlock_apply] at hj''
      by_cases h : (@finProdFinEquiv k k (b0, j')) = @finProdFinEquiv k k (b0, jj)
      · exact congrArg Prod.snd ((@finProdFinEquiv k k).injective h)
      · rw [if_neg h, hzero j'] at hj''
        exact absurd hj'' (by decide)
  · obtain ⟨j0, hj0, huniq⟩ := hrest b hb
    refine ⟨j0, ?_, ?_⟩
    · show fillBlock k y b0 jj (@finProdFinEquiv k k (b, j0)) = true
      rw [fillBlock_apply]
      rw [if_neg]
      · exact hj0
      · intro hc
        exact hb (congrArg Prod.fst ((@finProdFinEquiv k k).injective hc))
    · intro j' hj'
      have hj'' : fillBlock k y b0 jj (@finProdFinEquiv k k (b, j')) = true := hj'
      rw [fillBlock_apply] at hj''
      by_cases h : (@finProdFinEquiv k k (b, j')) = @finProdFinEquiv k k (b0, jj)
      · exact absurd (congrArg Prod.fst ((@finProdFinEquiv k k).injective h)) hb
      · rw [if_neg h] at hj''
        exact huniq j' hj''

theorem fillBlock_inj {k : ℕ} {y : Input (k * k)} {b : Fin k}
    (hz : ∀ j, y (@finProdFinEquiv k k (b, j)) = false) :
    Function.Injective (fun j : Fin k => fillBlock k y b j) := by
  intro j j' hjj
  simp only [] at hjj
  by_contra hne
  have key : fillBlock k y b j (@finProdFinEquiv k k (b, j)) =
      fillBlock k y b j' (@finProdFinEquiv k k (b, j)) := congrFun hjj _
  rw [fillBlock_apply, fillBlock_apply] at key
  by_cases h : (@finProdFinEquiv k k (b, j)) = @finProdFinEquiv k k (b, j')
  · exact hne (congrArg Prod.snd ((@finProdFinEquiv k k).injective h))
  · rw [if_pos rfl, if_neg h, hz j] at key
    exact absurd key (by decide)

theorem pair_fillBlock_inj {k : ℕ} {y : Input (k * k)} {b : Fin k}
    (hz : ∀ j, y (@finProdFinEquiv k k (b, j)) = false) :
    Function.Injective (fun j : Fin k => (fillBlock k y b j, y)) := by
  intro j j' h
  exact fillBlock_inj hz (congrArg Prod.fst h)

theorem fiber_R_Y {k : ℕ} {y : Input (k * k)} (hy : y ∈ Yset k) :
    (Rset k).filter (fun p => p.2 = y) =
      (univ : Finset (Fin k)).image
        (fun j => (fillBlock k y (Classical.choose (mem_Yset.mp hy)) j, y)) := by
  classical
  obtain ⟨hzero, hrest⟩ := Classical.choose_spec (mem_Yset.mp hy)
  ext p
  obtain ⟨a, b⟩ := p
  simp only [mem_filter, mem_image, mem_univ, true_and, Prod.fst, Prod.snd, Prod.mk.injEq]
  constructor
  · rintro ⟨hpR, rfl⟩
    obtain ⟨haX, _, _⟩ := mem_Rset_pair.mp hpR
    obtain ⟨j, hj⟩ := R_pair_eq_fillBlock hzero hrest haX hpR
    exact ⟨j, hj.symm, rfl⟩
  · rintro ⟨j, rfl, rfl⟩
    refine ⟨mem_Rset_pair.mpr ⟨fillBlock_mem_Xset hzero hrest j, hy, ?_⟩, rfl⟩
    refine ⟨@finProdFinEquiv k k (Classical.choose (mem_Yset.mp hy), j), ?_, ?_⟩
    · rw [fillBlock_apply, if_pos rfl, hzero j]
      exact (by decide : (true : Bool) ≠ false)
    · intro p hp
      rw [fillBlock_apply, if_neg (by exact hp)]

theorem card_fiber_Y {k : ℕ} {y : Input (k * k)} (hy : y ∈ Yset k) :
    ((Rset k).filter (fun p => p.2 = y)).card = k := by
  rw [fiber_R_Y hy,
    Finset.card_image_of_injective _
      (pair_fillBlock_inj (b := Classical.choose (mem_Yset.mp hy))
        (Classical.choose_spec (mem_Yset.mp hy)).1),
    card_univ, Fintype.card_fin]

theorem card_diff_X {k : ℕ} {x : Input (k * k)} (hx : x ∈ Xset k) (i : Fin (k * k)) :
    ((Rset k).filter (fun p => p.1 = x ∧ p.2 i ≠ x i)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  rintro ⟨a, b⟩ h1 ⟨a', b'⟩ h2
  simp only [mem_filter, Prod.fst, Prod.snd] at h1 h2
  obtain ⟨h1R, h1a, h1ne⟩ := h1
  obtain ⟨h2R, h2a, h2ne⟩ := h2
  obtain ⟨haX, hbY, i1, hne1, hagree1⟩ := mem_Rset_pair.mp h1R
  obtain ⟨ha'X, hb'Y, i2, hne2, hagree2⟩ := mem_Rset_pair.mp h2R
  have hi1 : i1 = i := by
    by_contra hc
    have hba : b i = a i := (hagree1 i (fun h => hc h.symm)).symm
    exact h1ne (by rw [← h1a]; exact hba)
  have hb : b = flipAt k a i := by
    have h := eq_flipAt_of_diff (u := a) (v := b) (i := i1) hagree1 hne1
    rwa [hi1] at h
  have hi2 : i2 = i := by
    by_contra hc
    have hb'a : b' i = a' i := (hagree2 i (fun h => hc h.symm)).symm
    exact h2ne (by rw [← h2a]; exact hb'a)
  have hb' : b' = flipAt k a' i := by
    have h := eq_flipAt_of_diff (u := a') (v := b') (i := i2) hagree2 hne2
    rwa [hi2] at h
  subst h1a
  subst h2a
  simp [hb, hb']

theorem card_diff_Y {k : ℕ} {y : Input (k * k)} (hy : y ∈ Yset k) (i : Fin (k * k)) :
    ((Rset k).filter (fun p => p.2 = y ∧ p.1 i ≠ y i)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  rintro ⟨a, b⟩ h1 ⟨a', b'⟩ h2
  simp only [mem_filter, Prod.fst, Prod.snd] at h1 h2
  obtain ⟨h1R, h1b, h1ne⟩ := h1
  obtain ⟨h2R, h2b, h2ne⟩ := h2
  obtain ⟨haX, hbY, i1, hne1, hagree1⟩ := mem_Rset_pair.mp h1R
  obtain ⟨ha'X, hb'Y, i2, hne2, hagree2⟩ := mem_Rset_pair.mp h2R
  have hi1 : i1 = i := by
    by_contra hc
    have hab : a i = b i := hagree1 i (fun h => hc h.symm)
    exact h1ne (by rw [← h1b]; exact hab)
  have ha : a = flipAt k b i := by
    have h := flipAt_eq_of_diff (u := a) (v := b) (i := i1) hagree1 hne1
    rwa [hi1] at h
  have hi2 : i2 = i := by
    by_contra hc
    have ha'b : a' i = b' i := hagree2 i (fun h => hc h.symm)
    exact h2ne (by rw [← h2b]; exact ha'b)
  have ha' : a' = flipAt k b' i := by
    have h := flipAt_eq_of_diff (u := a') (v := b') (i := i2) hagree2 hne2
    rwa [hi2] at h
  subst h1b
  subst h2b
  simp [ha, ha']

theorem andOfOrs_true_of_mem_Xset {k : ℕ} {x : Input (k * k)} (hx : x ∈ Xset k) :
    andOfOrs k x = true := by
  rw [andOfOrs, decide_eq_true_iff]
  intro b
  obtain ⟨j, hj, -⟩ := (mem_Xset.mp hx) b
  exact ⟨j, hj⟩

theorem andOfOrs_false_of_mem_Yset {k : ℕ} {y : Input (k * k)} (hy : y ∈ Yset k) :
    andOfOrs k y = false := by
  obtain ⟨b0, hzero, -⟩ := mem_Yset.mp hy
  rw [andOfOrs, decide_eq_false_iff_not]
  intro h
  obtain ⟨j, hj⟩ := h b0
  rw [hzero j] at hj
  exact absurd hj (by decide)

theorem Xset_nonempty {k : ℕ} (hk : 1 ≤ k) : 0 < (Xset k).card := by
  classical
  have hk0 : 0 < k := by omega
  let z : Fin k := ⟨0, hk0⟩
  refine Finset.card_pos.mpr ⟨fun p => decide (withinBlock k p = z), ?_⟩
  rw [mem_Xset]
  intro b
  refine ⟨z, by simp, ?_⟩
  intro j hj
  simpa using hj

theorem Yset_nonempty {k : ℕ} (hk : 1 ≤ k) : 0 < (Yset k).card := by
  classical
  have hk0 : 0 < k := by omega
  let z : Fin k := ⟨0, hk0⟩
  refine Finset.card_pos.mpr
    ⟨fun p => if blockOf k p = z then false else decide (withinBlock k p = z), ?_⟩
  rw [mem_Yset]
  refine ⟨z, ?_, ?_⟩
  · intro j
    simp
  · intro b hb
    refine ⟨z, by simp [hb], ?_⟩
    intro j hj
    simpa [hb] using hj

theorem phaseQuery_smul' {ι : Type*} {n : ℕ} (i : Fin n) (c : Input n → ℂ)
    (ψ : ι → Input n → ℂ) :
    phaseQuery i (fun iw x => c x * ψ iw x) =
      fun iw x => c x * phaseQuery i ψ iw x := by
  funext iw x
  unfold phaseQuery
  by_cases h : x i <;> simp [h]

theorem source_theorem4 (k : ℕ) (hk : 1 ≤ k) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ℕ → ι → Input (k * k) → ℂ) (ans : ι → Bool) (T : ℕ) (ε : ℝ) (iw0 : ι)
    (hinit : ∀ iw x, ψ 0 iw x = if iw = iw0 then 1 else 0)
    (hquery : ∀ j < T, ∃ i : Fin (k * k), ψ (j + 1) = phaseQuery i (ψ j))
    (hnorm : ∀ j x, (∑ iw, ‖ψ j iw x‖ ^ 2) = 1)
    (hsucc : ∀ x : Input (k * k),
      1 - ε ≤ ∑ iw ∈ univ.filter (fun iw => ans iw = andOfOrs k x), ‖ψ T iw x‖ ^ 2)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * (k : ℝ) / 2 ≤ (T : ℝ) := by
  classical
  have hkpos : 0 < k * k := Nat.mul_pos (by omega) (by omega)
  let bit : ℕ → Fin (k * k) :=
    fun j => if h : j < T then Classical.choose (hquery j h) else ⟨0, hkpos⟩
  have hbit : ∀ j < T, ψ (j + 1) = phaseQuery (bit j) (ψ j) := by
    intro j hj
    have hspec := Classical.choose_spec (hquery j hj)
    have hbitj : bit j = Classical.choose (hquery j hj) := by
      show (if h : j < T then Classical.choose (hquery j h) else ⟨0, hkpos⟩) =
        Classical.choose (hquery j hj)
      rw [dif_pos hj]
    rw [hbitj]
    exact hspec
  let φ : ℕ → ι → Input (k * k) → ℂ :=
    fun j iw x => initialState (Xset k) (Yset k) x * ψ j iw x
  have hφinit : ∀ iw x, φ 0 iw x =
      if iw = iw0 then initialState (Xset k) (Yset k) x else 0 := by
    intro iw x
    show initialState (Xset k) (Yset k) x * ψ 0 iw x = _
    rw [hinit iw x]
    by_cases h : iw = iw0 <;> simp [h]
  have hφquery : ∀ j < T, φ (j + 1) = phaseQuery (bit j) (φ j) := by
    intro j hj
    have h := phaseQuery_smul' (bit j) (fun x => initialState (Xset k) (Yset k) x) (ψ j)
    funext iw x
    show initialState (Xset k) (Yset k) x * ψ (j + 1) iw x =
      phaseQuery (bit j) (fun iw x => initialState (Xset k) (Yset k) x * ψ j iw x) iw x
    rw [congrFun (congrFun h iw) x, hbit j hj]
  have hmassφ : ∀ j x,
      mass (φ j) x = (initialAmplitude (Xset k) (Yset k) x) ^ 2 := by
    intro j x
    unfold mass
    have hterm : ∀ iw, ‖φ j iw x‖ ^ 2 =
        (initialAmplitude (Xset k) (Yset k) x) ^ 2 * ‖ψ j iw x‖ ^ 2 := by
      intro iw
      have hf : φ j iw x = (initialAmplitude (Xset k) (Yset k) x : ℂ) * ψ j iw x := rfl
      rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [Finset.sum_congr rfl (fun iw _ => hterm iw), ← Finset.mul_sum, hnorm j x, mul_one]
  have hdisj : Disjoint (Xset k) (Yset k) := by
    rw [Finset.disjoint_left]
    intro z hzX hzY
    have h1 : andOfOrs k z = true := andOfOrs_true_of_mem_Xset hzX
    have h2 : andOfOrs k z = false := andOfOrs_false_of_mem_Yset hzY
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hφmass : ∀ j, (∑ iw, ∑ x ∈ Xset k, ‖φ j iw x‖ ^ 2) +
      (∑ iw, ∑ y ∈ Yset k, ‖φ j iw y‖ ^ 2) ≤ 1 := by
    intro j
    have hXsum : (∑ iw, ∑ x ∈ Xset k, ‖φ j iw x‖ ^ 2) =
        ∑ x ∈ Xset k, (initialAmplitude (Xset k) (Yset k) x) ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ => hmassφ j x)
    have hYsum : (∑ iw, ∑ y ∈ Yset k, ‖φ j iw y‖ ^ 2) =
        ∑ y ∈ Yset k, (initialAmplitude (Xset k) (Yset k) y) ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun y _ => hmassφ j y)
    have hXc : ∑ x ∈ Xset k, (initialAmplitude (Xset k) (Yset k) x) ^ 2 =
        if (Xset k).card = 0 then 0 else 1 / 2 := by
      by_cases h0 : (Xset k).card = 0
      · rw [if_pos h0, Finset.card_eq_zero.mp h0]; simp
      · rw [if_neg h0]
        have hterm : ∀ x ∈ Xset k,
            (initialAmplitude (Xset k) (Yset k) x) ^ 2 = (2 * ((Xset k).card : ℝ))⁻¹ := by
          intro x hxm
          simp only [initialAmplitude, if_pos hxm]
          rw [inv_pow, Real.sq_sqrt (by positivity)]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
        have hXne : ((Xset k).card : ℝ) ≠ 0 := by exact_mod_cast h0
        field_simp
    have hYc : ∑ y ∈ Yset k, (initialAmplitude (Xset k) (Yset k) y) ^ 2 =
        if (Yset k).card = 0 then 0 else 1 / 2 := by
      by_cases h0 : (Yset k).card = 0
      · rw [if_pos h0, Finset.card_eq_zero.mp h0]; simp
      · rw [if_neg h0]
        have hterm : ∀ y ∈ Yset k,
            (initialAmplitude (Xset k) (Yset k) y) ^ 2 = (2 * ((Yset k).card : ℝ))⁻¹ := by
          intro y hym
          have hyX : y ∉ Xset k := fun h => (Finset.disjoint_left.mp hdisj) h hym
          simp only [initialAmplitude, if_neg hyX, if_pos hym]
          rw [inv_pow, Real.sq_sqrt (by positivity)]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
        have hYne : ((Yset k).card : ℝ) ≠ 0 := by exact_mod_cast h0
        field_simp
    rw [hXsum, hYsum, hXc, hYc]
    by_cases hX0 : (Xset k).card = 0 <;> by_cases hY0 : (Yset k).card = 0 <;>
      (simp [hX0, hY0] <;> norm_num)
  have hwrong : ∀ x ∈ Xset k,
      (∑ iw ∈ univ.filter (fun iw => ans iw ≠ true), ‖ψ T iw x‖ ^ 2) ≤ ε := by
    intro x hx
    have hfx : andOfOrs k x = true := andOfOrs_true_of_mem_Xset hx
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := (univ : Finset ι)) (p := fun iw => ans iw = true)
      (f := fun iw => ‖ψ T iw x‖ ^ 2)
    have htotal : (∑ iw, ‖ψ T iw x‖ ^ 2) = 1 := hnorm T x
    have hs := hsucc x
    rw [hfx] at hs
    have heq : (univ.filter (fun iw => ¬ ans iw = true)) =
        univ.filter (fun iw => ans iw ≠ true) := by
      ext iw; simp [ne_eq]
    rw [heq] at hsplit
    linarith
  have hright : ∀ y ∈ Yset k,
      (∑ iw ∈ univ.filter (fun iw => ans iw = true), ‖ψ T iw y‖ ^ 2) ≤ ε := by
    intro y hy
    have hfy : andOfOrs k y = false := andOfOrs_false_of_mem_Yset hy
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := (univ : Finset ι)) (p := fun iw => ans iw = false)
      (f := fun iw => ‖ψ T iw y‖ ^ 2)
    have htotal : (∑ iw, ‖ψ T iw y‖ ^ 2) = 1 := hnorm T y
    have hs := hsucc y
    rw [hfy] at hs
    have heq : (univ.filter (fun iw => ¬ ans iw = false)) =
        univ.filter (fun iw => ans iw = true) := by
      ext iw; cases ans iw <;> simp
    rw [heq] at hsplit
    linarith
  have hmain := source_theorem2 (f := andOfOrs k) (Xset k) (Yset k) (Rset k) k k 1 1 ε T
    bit φ (ψ T) ans iw0
    (fun p hp => by rw [mem_Rset] at hp; exact ⟨hp.1, hp.2.1⟩)
    (fun x hx => le_of_eq (card_fiber_X hx).symm)
    (fun y hy => le_of_eq (card_fiber_Y hy).symm)
    (fun x hx i => card_diff_X hx i)
    (fun y hy i => card_diff_Y hy i)
    (by norm_num) (by norm_num)
    (fun x hx => andOfOrs_true_of_mem_Xset hx)
    (fun y hy => andOfOrs_false_of_mem_Yset hy)
    (Xset_nonempty hk)
    (Yset_nonempty hk)
    hφinit hφquery hφmass (fun iw x => rfl) (fun x => hnorm T x) hwrong hright hε0 hε
  have hk_sqrt : Real.sqrt ((k : ℝ) * (k : ℝ)) = (k : ℝ) := Real.sqrt_mul_self (by positivity)
  have h1_sqrt : Real.sqrt ((1 : ℝ) * (1 : ℝ)) = 1 := by norm_num
  simpa [hk_sqrt, h1_sqrt] using hmain

end Qatlib.Papers.QLowerBound00.MainResults.Theorem4
