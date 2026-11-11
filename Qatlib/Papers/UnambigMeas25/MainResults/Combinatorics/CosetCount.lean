/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnambigMeas25.MainResults.Definitions.UnambigMeasModel

set_option backward.isDefEq.respectTransparency false

/-!
# Coset counting for the dual solutions — Section 4.3, Proposition 20

Paper: Buzet–Chailloux, *Fine-Grained Unambiguous Measurements*,
arXiv:2510.07298v2 (4 Nov 2025).

This file proves the coset inequality underlying Proposition 20 (p. 24–25):
for every dual coset `D` of a full-rank generator matrix `G ∈ Λ_{n-k}` and
every `s`, `∑_{i ∈ D} 2|i|_H ≥ k 2^k`.  The proof avoids the paper's explicit
choice of independent columns: it double-counts
`∑_{i ∈ D} |i|_H = ∑_j #{i ∈ D : i_j ≠ 0}`, shows each non-constant
coordinate is balanced (exactly half of `D`, by the translation involution
`i ↦ i + w` with `w_j = 1`), and bounds the number of constant-zero
coordinates by `n - k` via `|ker G| = 2^k ≤ |{x : x|_Z = 0}| ≤ 2^{n-|Z|}`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults.CosetCount

open Matrix BigOperators

/-! ### Small `F₂` facts -/

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma z2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Doubling vanishes in `ZMod 2`. -/
lemma z2_add_self (z : ZMod 2) : z + z = 0 := by
  rcases z2_cases z with rfl | rfl <;> decide

/-- `z + 1 = 0` iff `z = 1` in `ZMod 2`. -/
lemma z2_add_one (z : ZMod 2) : z + 1 = 0 ↔ z = 1 := by
  rcases z2_cases z with rfl | rfl <;> decide

/-- `z + 1 = 1` iff `z = 0` in `ZMod 2`. -/
lemma z2_add_one' (z : ZMod 2) : z + 1 = 1 ↔ z = 0 := by
  rcases z2_cases z with rfl | rfl <;> decide

/-- Bridge between filtered cardinals and subtype cardinals. -/
private lemma card_filter_univ {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Fintype.card {x : α // p x} := by
  have e : {x : α // p x} ≃ ↥(Finset.univ.filter p) :=
    Equiv.subtypeEquivRight (fun x => by simp)
  rw [Fintype.card_congr e, Fintype.card_coe]

/-! ### Fibres of full-rank matrices over `F₂` -/

variable {n m : ℕ}

/-- The dual coset `D_G(s)` as a `Finset`. -/
def fibreSet (G : MatZ m n) (s : Fin m → ZMod 2) : Finset (F2 n) :=
  Finset.univ.filter (fun i => matVec G i = s)

/-- The kernel of `G` as a `Finset`. -/
def kerSet (G : MatZ m n) : Finset (F2 n) :=
  Finset.univ.filter (fun i => matVec G i = 0)

/-- `matVec` is additive. -/
lemma matVec_add (G : MatZ m n) (a b : F2 n) :
    matVec G (a + b) = matVec G a + matVec G b := by
  simp [matVec, Matrix.mulVec_add]

/-- Membership in the dual-coset `Finset`. -/
lemma mem_fibreSet {G : MatZ m n} {s : Fin m → ZMod 2} {i : F2 n} :
    i ∈ fibreSet G s ↔ matVec G i = s := by
  simp [fibreSet]

/-- Membership in the kernel `Finset`. -/
lemma mem_kerSet {G : MatZ m n} {i : F2 n} :
    i ∈ kerSet G ↔ matVec G i = 0 := by
  simp [kerSet]

/-- Rank–nullity over `F₂`: `finrank (ker G) = n - rank G`. -/
lemma finrank_ker_eq (G : MatZ m n) :
    Module.finrank (ZMod 2) (LinearMap.ker G.mulVecLin) = n - Matrix.rank G := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) G.mulVecLin
  have hdom : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrange : Module.finrank (ZMod 2) (LinearMap.range G.mulVecLin)
      = Matrix.rank G := rfl
  rw [hdom] at hrn
  omega

/-- `|ker G| = 2^(n - rank G)` for matrices over `F₂`. -/
lemma card_kerSet (G : MatZ m n) :
    (kerSet G).card = 2 ^ (n - Matrix.rank G) := by
  classical
  have hfin : Fintype.card ↥(LinearMap.ker G.mulVecLin) = 2 ^ (n - Matrix.rank G) := by
    rw [show Fintype.card ↥(LinearMap.ker G.mulVecLin)
          = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (LinearMap.ker G.mulVecLin) from
        Module.card_eq_pow_finrank,
      finrank_ker_eq, ZMod.card]
  have hker : (kerSet G).card = Fintype.card {x : F2 n // matVec G x = 0} := by
    show (Finset.univ.filter (fun i => matVec G i = 0)).card = _
    exact card_filter_univ (fun i => matVec G i = 0)
  have hglue : Fintype.card {x : F2 n // matVec G x = 0}
      = Fintype.card ↥(LinearMap.ker G.mulVecLin) :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by
      simp [LinearMap.mem_ker, matVec]))
  rw [hker, hglue, hfin]

/-- A full-rank matrix over `F₂` has surjective `mulVec`. -/
lemma exists_fibre (G : Lam n m) (s : Fin m → ZMod 2) :
    ∃ v : F2 n, matVec G.1 v = s := by
  have hrange : LinearMap.range G.1.mulVecLin = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    show Module.finrank (ZMod 2) (LinearMap.range G.1.mulVecLin) = _
    rw [← Matrix.rank, G.2, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨v, hv⟩ := (LinearMap.range_eq_top.mp hrange) s
  exact ⟨v, by simpa [matVec] using hv⟩

/-- Every dual coset has exactly `2^(n - m)` elements. -/
lemma card_fibreSet (G : Lam n m) (s : Fin m → ZMod 2) :
    (fibreSet G.1 s).card = 2 ^ (n - m) := by
  obtain ⟨v, hv⟩ := exists_fibre G s
  classical
  have hvv : v + v = 0 := by funext r; exact z2_add_self _
  have himg : (kerSet G.1).image (fun x => v + x) = fibreSet G.1 s := by
    ext i
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_fibreSet, matVec_add, mem_kerSet.mp hx, hv, add_zero]
    · intro hi
      refine ⟨i + v, ?_, ?_⟩
      · rw [mem_kerSet, matVec_add, mem_fibreSet.mp hi, hv]
        funext r
        exact z2_add_self _
      · have hrr : v + (i + v) = i + (v + v) := by ring
        rw [hrr, hvv, add_zero]
  have h1 := congrArg Finset.card himg
  rw [Finset.card_image_of_injective _ (fun a b hab => add_left_cancel (a := v) hab),
    card_kerSet, G.2] at h1
  exact h1.symm

/-! ### Balanced coordinates inside a coset -/

/-- Involution balance: if `w ∈ ker G` has `w j = 1`, then the elements of the
coset `D_G(s)` with `i j ≠ 0` are in bijection (via `i ↦ i + w`) with those
with `i j = 0`; hence `2 · #{i ∈ D : i j ≠ 0} = |D|`. -/
lemma two_mul_card_filter (G : MatZ m n) (s : Fin m → ZMod 2) (j : Fin n) (w : F2 n)
    (hw : matVec G w = 0) (hwj : w j = 1) :
    2 * ((fibreSet G s).filter (fun i => i j ≠ 0)).card = (fibreSet G s).card := by
  classical
  set D := fibreSet G s with hD
  set P := D.filter (fun i => i j ≠ 0) with hP
  set Q := D.filter (fun i => i j = 0) with hQ
  have hmemD : ∀ i : F2 n, i ∈ D ↔ matVec G i = s := fun _ => mem_fibreSet
  have hsub : ∀ i ∈ D, (i + w) ∈ D := by
    intro i hi
    rw [hmemD, matVec_add, (hmemD i).mp hi, hw, add_zero]
  have htog0 : ∀ i : F2 n, i j ≠ 0 → (i + w) j = 0 := by
    intro i hi
    rcases z2_cases (i j) with h | h
    · exact absurd h hi
    · have : (i + w) j = i j + w j := by simp [Pi.add_apply]
      rw [this, h, hwj]
      decide
  have htog1 : ∀ i : F2 n, i j = 0 → (i + w) j ≠ 0 := by
    intro i hi
    have : (i + w) j = i j + w j := by simp [Pi.add_apply]
    rw [this, hi, hwj]
    decide
  have hvw : w + w = 0 := by funext r; exact z2_add_self _
  have hPQ : P.image (fun i => i + w) = Q := by
    ext i
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [hP, Finset.mem_filter] at hx
      simp only [hQ, Finset.mem_filter]
      exact ⟨hsub x hx.1, htog0 x hx.2⟩
    · intro hi
      simp only [hQ, Finset.mem_filter] at hi
      refine ⟨i + w, ?_, ?_⟩
      · simp only [hP, Finset.mem_filter]
        exact ⟨hsub i hi.1, htog1 i hi.2⟩
      · have hrr : (i + w) + w = i + (w + w) := by ring
        rw [hrr, hvw, add_zero]
  have hcard : P.card = Q.card := by
    have h := congrArg Finset.card hPQ
    have hpi : (P.image (fun i => i + w)).card = P.card :=
      Finset.card_image_of_injective _ (fun a b hab => add_right_cancel hab)
    rw [hpi] at h
    exact h
  have hunion : P ∪ Q = D := by
    ext i
    simp only [Finset.mem_union, hP, hQ, Finset.mem_filter]
    constructor
    · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd
    · intro hi
      rcases z2_cases (i j) with h | h
      · exact Or.inr ⟨hi, h⟩
      · exact Or.inl ⟨hi, by rw [h]; exact one_ne_zero⟩
  have hinter : P ∩ Q = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    simp only [Finset.mem_inter, hP, hQ, Finset.mem_filter] at hx
    exact hx.1.2 hx.2.2
  have hcu : (P ∪ Q).card = P.card + Q.card :=
    Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hinter)
  rw [← hunion, hcu, hcard]
  omega

/-! ### The coset weight inequality (Proposition 20 core) -/

/-- Main counting bound: every dual coset of `G ∈ Λ_{n-k}` (here written with
`k = n - m`) carries total Hamming weight at least `k · 2^(k-1)`. -/
theorem coset_weight_sum (G : Lam n m) (s : Fin m → ZMod 2) :
    (n - m) * 2 ^ (n - m - 1) ≤ ∑ i ∈ fibreSet G.1 s, hammingWeight i := by
  classical
  by_cases hk : n - m = 0
  · simp [hk]
  have hkm : m < n := by omega
  set D := fibreSet G.1 s with hD
  have hDcard : D.card = 2 ^ (n - m) := card_fibreSet G s
  set c : Fin n → ℕ := fun j => (D.filter (fun i => i j ≠ 0)).card with hc
  have hw_eq : ∀ i : F2 n, hammingWeight i = ∑ j : Fin n, if i j ≠ 0 then 1 else 0 := by
    intro i
    rw [hammingWeight, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsum : ∑ i ∈ D, hammingWeight i = ∑ j, c j := by
    rw [Finset.sum_congr rfl (fun i _ => hw_eq i), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  set Z : Finset (Fin n) := Finset.univ.filter (fun j => ∀ i ∈ D, i j = 0) with hZ
  obtain ⟨v, hv⟩ := exists_fibre G s
  have hker_vanish : ∀ x ∈ kerSet G.1, ∀ j ∈ Z, x j = 0 := by
    intro x hx j hj
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hvx : (v + x) ∈ D := by
      rw [hD, mem_fibreSet, matVec_add, hv, (mem_kerSet.mp hx), add_zero]
    have hvxj : (v + x) j = 0 := hj _ hvx
    have hvj : v j = 0 := hj _ (by rw [hD, mem_fibreSet]; exact hv)
    have hsplit : (v + x) j = v j + x j := by simp [Pi.add_apply]
    rw [hsplit, hvj] at hvxj
    simpa using hvxj
  have hZcard : Z.card ≤ m := by
    set V : Finset (F2 n) := Finset.univ.filter (fun x => ∀ j ∈ Z, x j = 0) with hV
    have hsub : kerSet G.1 ⊆ V := by
      intro x hx
      simp only [hV, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hker_vanish x hx
    have h1 : 2 ^ (n - m) ≤ V.card := by
      calc 2 ^ (n - m) = (kerSet G.1).card := by rw [card_kerSet, G.2]
        _ ≤ V.card := Finset.card_le_card hsub
    have h2 : V.card ≤ 2 ^ (n - Z.card) := by
      classical
      have hinj_inj : Function.Injective
          (fun (x : {x : F2 n // ∀ j ∈ Z, x j = 0}) (j : ↥(Zᶜ)) => x.1 (j : Fin n)) := by
        intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        refine Subtype.ext (?_ : x = y)
        funext j
        by_cases hj : j ∈ Z
        · rw [hx j hj, hy j hj]
        · have hjc : j ∈ Zᶜ := by simpa using hj
          exact congrFun hxy ⟨j, hjc⟩
      have hcardV : Fintype.card {x : F2 n // ∀ j ∈ Z, x j = 0} = V.card := by
        rw [hV]
        exact (card_filter_univ (fun (x : F2 n) => ∀ j ∈ Z, x j = 0)).symm
      have hcardfun : Fintype.card ((j : ↥(Zᶜ)) → ZMod 2)
          = (2 : ℕ) ^ (Zᶜ : Finset (Fin n)).card := by
        simp
        rw [Finset.card_compl, Fintype.card_fin]
      calc V.card = Fintype.card {x : F2 n // ∀ j ∈ Z, x j = 0} := hcardV.symm
        _ ≤ Fintype.card ((j : ↥(Zᶜ)) → ZMod 2) :=
              Fintype.card_le_of_injective (f := fun
                (x : {x : F2 n // ∀ j ∈ Z, x j = 0}) (j : ↥(Zᶜ)) => x.1 (j : Fin n)) hinj_inj
        _ = (2 : ℕ) ^ (Zᶜ : Finset (Fin n)).card := hcardfun
        _ = 2 ^ (n - Z.card) := by
            simp [Finset.card_compl, Fintype.card_fin]
    have hle : n - m ≤ n - Z.card := by
      have hp := h1.trans h2
      rwa [Nat.pow_le_pow_iff_right (show (1 : ℕ) < 2 by norm_num)] at hp
    omega
  have hcpos : ∀ j ∈ Zᶜ, 2 ^ (n - m - 1) ≤ c j := by
    intro j hj
    have hjZ : j ∉ Z := by simpa using hj
    show 2 ^ (n - m - 1) ≤ (D.filter (fun i => i j ≠ 0)).card
    obtain ⟨i₀, hi₀D, hi₀j⟩ : ∃ i₀ ∈ D, i₀ j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hjZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
    by_cases hzero : ∃ i₁ ∈ D, i₁ j = 0
    · obtain ⟨i₁, hi₁D, hi₁j⟩ := hzero
      have h0 : matVec G.1 i₀ = s := mem_fibreSet.mp hi₀D
      have h1 : matVec G.1 i₁ = s := mem_fibreSet.mp hi₁D
      have hw : matVec G.1 (i₀ + i₁) = 0 := by
        rw [matVec_add, h0, h1]
        funext r
        exact z2_add_self _
      have hwj : (i₀ + i₁) j = 1 := by
        have hsplit : (i₀ + i₁) j = i₀ j + i₁ j := by simp [Pi.add_apply]
        rw [hsplit, hi₁j]
        rcases z2_cases (i₀ j) with h | h
        · exact absurd h hi₀j
        · rw [h]
          simp
      have hbal := two_mul_card_filter G.1 s j (i₀ + i₁) hw hwj
      rw [← hD] at hbal
      have hsplit : 2 ^ (n - m) = 2 * 2 ^ (n - m - 1) := by
        have hnm : n - m = (n - m - 1) + 1 := by omega
        rw [hnm, Nat.pow_succ,
          show n - m - 1 + 1 - 1 = n - m - 1 from by omega]
        exact mul_comm _ _
      have heq : 2 * {i ∈ D | i j ≠ 0}.card = 2 * 2 ^ (n - m - 1) := by
        rw [← hsplit, ← hDcard]
        exact hbal
      omega
    · push Not at hzero
      have hfil : (D.filter (fun i => i j ≠ 0)) = D := Finset.filter_eq_self.mpr hzero
      have hcj : (D.filter (fun i => i j ≠ 0)).card = 2 ^ (n - m) := by
        rw [hfil, hDcard]
      have hge : 2 ^ (n - m - 1) ≤ 2 ^ (n - m) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
  calc ∑ i ∈ D, hammingWeight i = ∑ j, c j := hsum
    _ = ∑ j ∈ Z, c j + ∑ j ∈ Zᶜ, c j := (Finset.sum_add_sum_compl Z c).symm
    _ ≥ (n - Z.card) * 2 ^ (n - m - 1) := by
        have h1 : ∑ j ∈ Zᶜ, c j ≥ (n - Z.card) * 2 ^ (n - m - 1) := by
          have hle := Finset.sum_le_sum (fun j hj => hcpos j hj)
          calc ∑ j ∈ Zᶜ, c j ≥ ∑ j ∈ Zᶜ, 2 ^ (n - m - 1) := hle
            _ = Zᶜ.card * 2 ^ (n - m - 1) := Finset.sum_const _
            _ = (n - Z.card) * 2 ^ (n - m - 1) := by
                rw [Finset.card_compl, Fintype.card_fin]
        have h2 : ∑ j ∈ Z, c j ≥ 0 := Nat.zero_le _
        omega
    _ ≥ (n - m) * 2 ^ (n - m - 1) := Nat.mul_le_mul_right _ (by omega)
