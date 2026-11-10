/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP05.MainResults.MatrixSumCount.Lemma5
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults.MatrixSumCount

open scoped Classical BigOperators

variable (p r : ℕ)

lemma matEntry_diag [NeZero p] (b : ZMod p) (i : Fin r) : matEntry p r b i i = b := by
  unfold matEntry binomMod
  rw [if_pos (le_refl _)]
  have h : (i : ℕ) - (i : ℕ) + 1 = 1 := by omega
  rw [h, Nat.choose_one_right, ZMod.natCast_zmod_val]

lemma matEntry_eq_zero_of_lt (b : ZMod p) (i j : Fin r) (h : j < i) :
    matEntry p r b i j = 0 := by
  have hj : (j : ℕ) < (i : ℕ) := h
  unfold matEntry
  rw [if_neg (by omega)]

lemma matEntry_sub_blockTriangular (b c : ZMod p) :
    Matrix.BlockTriangular
      (matEntry p r b - matEntry p r c : Matrix (Fin r) (Fin r) (ZMod p)) id := by
  intro i j hji
  simp only [Pi.sub_apply]
  rw [matEntry_eq_zero_of_lt p r b i j (by simpa using hji),
    matEntry_eq_zero_of_lt p r c i j (by simpa using hji), sub_zero]

lemma matEntry_sub_diag [NeZero p] (b c : ZMod p) (i : Fin r) :
    (matEntry p r b - matEntry p r c) i i = b - c := by
  simp only [Pi.sub_apply, matEntry_diag p r b i, matEntry_diag p r c i]

lemma matEntry_sub_det [NeZero p] (b c : ZMod p) :
    Matrix.det (matEntry p r b - matEntry p r c : Matrix (Fin r) (Fin r) (ZMod p))
      = (b - c) ^ r := by
  rw [Matrix.det_of_upperTriangular (matEntry_sub_blockTriangular p r b c)]
  simp only [matEntry_sub_diag p r b c, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def matSumLin (b : Fin r → ZMod p) :
    (Fin r → Fin r → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p) where
  toFun x := matSum p r x b
  map_add' x y := by
    funext i
    simp only [matSum, matVec, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext i
    simp only [matSum, matVec, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring

@[simp]
lemma matSumLin_apply (b : Fin r → ZMod p) (x : Fin r → Fin r → ZMod p) :
    matSumLin p r b x = matSum p r x b := rfl

theorem matSumLin_sub_surjective [Fact p.Prime] {b c : Fin r → ZMod p} (hbc : b ≠ c) :
    Function.Surjective (matSumLin p r b - matSumLin p r c) := by
  intro w

  obtain ⟨j₀, hj₀⟩ : ∃ j₀, b j₀ ≠ c j₀ := by
    by_contra h
    push Not at h
    exact hbc (funext h)

  set D : Matrix (Fin r) (Fin r) (ZMod p) := matEntry p r (b j₀) - matEntry p r (c j₀) with hD
  have hdet : D.det ≠ 0 := by
    rw [hD, matEntry_sub_det p r]
    exact pow_ne_zero _ (sub_ne_zero.mpr hj₀)
  have hunit : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective D.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hinj' : Function.Injective (⇑(Matrix.mulVecLin D)) := by
    simpa only [Matrix.coe_mulVecLin] using hinj
  have hsurjD : Function.Surjective (Matrix.mulVecLin D) :=
    LinearMap.injective_iff_surjective.mp hinj'
  obtain ⟨v, hv⟩ := hsurjD w

  set X : Fin r → Fin r → ZMod p := Function.update (fun _ : Fin r => (0 : Fin r → ZMod p)) j₀ v
    with hX
  have hzero : ∀ j, j ≠ j₀ → X j = 0 := by
    intro j hj
    simp [hX, hj]
  have hval : X j₀ = v := by simp [hX]
  refine ⟨X, ?_⟩
  funext i
  have hb : (∑ j, matVec p r (b j) (X j) i) = matVec p r (b j₀) v i := by
    rw [Finset.sum_eq_single j₀]
    · simp [hval]
    · intro j _ hj; simp [hzero j hj, matVec]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  have hc : (∑ j, matVec p r (c j) (X j) i) = matVec p r (c j₀) v i := by
    rw [Finset.sum_eq_single j₀]
    · simp [hval]
    · intro j _ hj; simp [hzero j hj, matVec]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  rw [LinearMap.sub_apply, matSumLin_apply, matSumLin_apply, Pi.sub_apply]
  simp only [matSum]
  rw [hb, hc]
  have hDw : Matrix.mulVec D v = w := by
    simpa only [Matrix.mulVecLin_apply] using hv
  have hDiff : matVec p r (b j₀) v - matVec p r (c j₀) v = Matrix.mulVec D v := by
    rw [hD]
    rw [show Matrix.mulVec (matEntry p r (b j₀) - matEntry p r (c j₀)) v
          = Matrix.mulVec (matEntry p r (b j₀)) v - Matrix.mulVec (matEntry p r (c j₀)) v
        from map_sub (Matrix.mulVec.addMonoidHomLeft v) _ _]
    rfl
  rw [show matVec p r (b j₀) v i - matVec p r (c j₀) v i
        = (Matrix.mulVec D v) i from congrFun hDiff i, hDw]

theorem card_fiber [Fact p.Prime] {b c : Fin r → ZMod p} (hbc : b ≠ c) :
    Fintype.card {x : Fin r → Fin r → ZMod p // matSum p r x b = matSum p r x c}
      = p ^ (r * r - r) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set L : (Fin r → Fin r → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p) :=
    matSumLin p r b - matSumLin p r c with hL
  have hiff : ∀ x : Fin r → Fin r → ZMod p,
      (matSum p r x b = matSum p r x c) ↔ (x ∈ LinearMap.ker L) := by
    intro x
    rw [LinearMap.mem_ker, hL, LinearMap.sub_apply, matSumLin_apply, matSumLin_apply,
      sub_eq_zero]
  have hcard_sub : Fintype.card {x : Fin r → Fin r → ZMod p // matSum p r x b = matSum p r x c}
      = Fintype.card (LinearMap.ker L) :=
    Fintype.card_congr (Equiv.subtypeEquivRight hiff)
  rw [hcard_sub]
  have hsurj : Function.Surjective L := by
    rw [hL]; exact matSumLin_sub_surjective p r hbc
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdimcod : Module.finrank (ZMod p) (Fin r → ZMod p) = r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hdimdom : Module.finrank (ZMod p) (Fin r → Fin r → ZMod p) = r * r := by
    rw [Module.finrank_pi_fintype (R := ZMod p) (M := fun _ : Fin r => (Fin r → ZMod p))]
    simp [hdimcod, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [hrange, finrank_top, hdimcod, hdimdom] at hrn
  have hker : Module.finrank (ZMod p) (LinearMap.ker L) = r * r - r := by
    rw [← hrn, Nat.add_sub_cancel_left]
  rw [Module.card_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker L), ZMod.card, hker]

lemma sum_indicator_mul {α : Type*} [Fintype α] [DecidableEq α] (a a' : α) :
    (∑ w : α, (if a = w then (1 : ℝ) else 0) * (if a' = w then (1 : ℝ) else 0))
      = if a = a' then (1 : ℝ) else 0 := by
  by_cases h : a = a'
  · subst h
    rw [if_pos rfl]
    have hpt : ∀ w : α, (if a = w then (1 : ℝ) else 0) * (if a = w then (1 : ℝ) else 0)
        = (if a = w then (1 : ℝ) else 0) := by
      intro w
      by_cases hw : a = w <;> simp [hw]
    calc (∑ w : α, (if a = w then (1 : ℝ) else 0) * (if a = w then (1 : ℝ) else 0))
        = ∑ w : α, (if a = w then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro w _; exact hpt w
      _ = 1 := Fintype.sum_ite_eq a (fun _ => (1 : ℝ))
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro w _
    by_cases hw : a = w
    · rw [if_pos hw, if_neg (fun hh => h (hw.trans hh.symm)), mul_zero]
    · rw [if_neg hw, zero_mul]

lemma sum_sq_eq_pairs [NeZero p] (x : Fin r → Fin r → ZMod p) :
    (∑ w : Fin r → ZMod p, ((solutions p r x w).card : ℝ) ^ 2)
      = ∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p,
          (if matSum p r x b = matSum p r x c then (1 : ℝ) else 0) := by
  have hcard : ∀ w : Fin r → ZMod p, ((solutions p r x w).card : ℝ)
      = ∑ b : Fin r → ZMod p, (if matSum p r x b = w then (1 : ℝ) else 0) := by
    intro w
    rw [solutions, Finset.natCast_card_filter]
  calc (∑ w : Fin r → ZMod p, ((solutions p r x w).card : ℝ) ^ 2)
      = ∑ w : Fin r → ZMod p,
          (∑ b : Fin r → ZMod p, (if matSum p r x b = w then (1 : ℝ) else 0)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro w _
        rw [hcard w]
    _ = ∑ w : Fin r → ZMod p, ∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p,
          ((if matSum p r x b = w then (1 : ℝ) else 0) *
           (if matSum p r x c = w then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [pow_two, Fintype.sum_mul_sum]
    _ = ∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p, ∑ w : Fin r → ZMod p,
          ((if matSum p r x b = w then (1 : ℝ) else 0) *
           (if matSum p r x c = w then (1 : ℝ) else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_comm]
    _ = ∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p,
          (if matSum p r x b = matSum p r x c then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        exact sum_indicator_mul (matSum p r x b) (matSum p r x c)

lemma sum_ind_over_x [Fact p.Prime] (b c : Fin r → ZMod p) :
    (∑ x : Fin r → Fin r → ZMod p,
        (if matSum p r x b = matSum p r x c then (1 : ℝ) else 0))
      = if b = c then (Fintype.card (Fin r → Fin r → ZMod p) : ℝ)
        else (p : ℝ) ^ (r * r - r) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  by_cases h : b = c
  · subst h
    rw [if_pos rfl]
    have hpt : ∀ x : Fin r → Fin r → ZMod p,
        (if matSum p r x b = matSum p r x b then (1 : ℝ) else 0) = 1 :=
      fun _ => if_pos rfl
    rw [Finset.sum_congr rfl (fun x _ => hpt x)]
    simp
  · rw [if_neg h]
    have hfilter : (∑ x : Fin r → Fin r → ZMod p,
        (if matSum p r x b = matSum p r x c then (1 : ℝ) else 0))
        = ((Finset.univ.filter (fun x : Fin r → Fin r → ZMod p =>
            matSum p r x b = matSum p r x c)).card : ℝ) := by
      rw [Finset.natCast_card_filter]
    rw [hfilter]
    have hsub : Fintype.card {x : Fin r → Fin r → ZMod p // matSum p r x b = matSum p r x c}
        = (Finset.univ.filter (fun x : Fin r → Fin r → ZMod p =>
            matSum p r x b = matSum p r x c)).card :=
      Fintype.card_subtype _
    rw [← hsub, card_fiber p r h, Nat.cast_pow]

theorem second_moment [Fact p.Prime] :
    (∑ xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p),
        (((solutions p r xw.1 xw.2).card : ℝ)) ^ 2)
      ≤ (2 - ((p : ℝ) ^ r)⁻¹) *
          (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hMnat : Fintype.card (Fin r → ZMod p) = p ^ r := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hM : (Fintype.card (Fin r → ZMod p) : ℝ) = (p : ℝ) ^ r := by
    rw [hMnat, Nat.cast_pow]
  have hNnat : Fintype.card (Fin r → Fin r → ZMod p) = p ^ (r * r) := by
    rw [Fintype.card_fun, hMnat, Fintype.card_fin, ← pow_mul]
  have hN : (Fintype.card (Fin r → Fin r → ZMod p) : ℝ) = (p : ℝ) ^ (r * r) := by
    rw [hNnat, Nat.cast_pow]

  have hsumexp : r + (r * r - r) = r * r := by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel (Nat.le_mul_self r)
  have hMD : (Fintype.card (Fin r → ZMod p) : ℝ) * (p : ℝ) ^ (r * r - r)
      = (Fintype.card (Fin r → Fin r → ZMod p) : ℝ) := by
    rw [hM, hN, ← pow_add, hsumexp]
  have hcardprod : (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ)
      = (Fintype.card (Fin r → Fin r → ZMod p) : ℝ) *
          (Fintype.card (Fin r → ZMod p) : ℝ) := by
    rw [Fintype.card_prod, Nat.cast_mul]

  have hinner : ∀ b : Fin r → ZMod p,
      (∑ c : Fin r → ZMod p,
          (if b = c then (Fintype.card (Fin r → Fin r → ZMod p) : ℝ)
            else (p : ℝ) ^ (r * r - r)))
        = ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) - (p : ℝ) ^ (r * r - r))
          + (Fintype.card (Fin r → ZMod p) : ℝ) * (p : ℝ) ^ (r * r - r) := by
    intro b
    have hpt : ∀ c : Fin r → ZMod p,
        (if b = c then (Fintype.card (Fin r → Fin r → ZMod p) : ℝ)
          else (p : ℝ) ^ (r * r - r))
        = (if b = c then ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) - (p : ℝ) ^ (r * r - r))
            else 0) + (p : ℝ) ^ (r * r - r) := by
      intro c
      by_cases h : b = c
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h, zero_add]
    calc (∑ c : Fin r → ZMod p,
          (if b = c then (Fintype.card (Fin r → Fin r → ZMod p) : ℝ)
            else (p : ℝ) ^ (r * r - r)))
        = ∑ c : Fin r → ZMod p,
            ((if b = c then ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) - (p : ℝ) ^ (r * r - r))
              else 0) + (p : ℝ) ^ (r * r - r)) := by
          apply Finset.sum_congr rfl; intro c _; exact hpt c
      _ = (∑ c : Fin r → ZMod p,
            (if b = c then ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) - (p : ℝ) ^ (r * r - r))
              else 0)) + ∑ _c : Fin r → ZMod p, (p : ℝ) ^ (r * r - r) := by
          rw [Finset.sum_add_distrib]
      _ = ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) - (p : ℝ) ^ (r * r - r))
          + (Fintype.card (Fin r → ZMod p) : ℝ) * (p : ℝ) ^ (r * r - r) := by
          rw [Fintype.sum_ite_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

  have hvalue : (∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p,
        (if b = c then (Fintype.card (Fin r → Fin r → ZMod p) : ℝ)
          else (p : ℝ) ^ (r * r - r)))
      = 2 * ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) *
            (Fintype.card (Fin r → ZMod p) : ℝ))
        - (Fintype.card (Fin r → Fin r → ZMod p) : ℝ) := by
    calc (∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p,
          (if b = c then (Fintype.card (Fin r → Fin r → ZMod p) : ℝ)
            else (p : ℝ) ^ (r * r - r)))
        = ∑ _b : Fin r → ZMod p,
            (((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) - (p : ℝ) ^ (r * r - r))
              + (Fintype.card (Fin r → ZMod p) : ℝ) * (p : ℝ) ^ (r * r - r)) := by
          apply Finset.sum_congr rfl; intro b _; exact hinner b
      _ = (Fintype.card (Fin r → ZMod p) : ℝ) *
            (((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) - (p : ℝ) ^ (r * r - r))
              + (Fintype.card (Fin r → ZMod p) : ℝ) * (p : ℝ) ^ (r * r - r)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 2 * ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) *
              (Fintype.card (Fin r → ZMod p) : ℝ))
          - (Fintype.card (Fin r → Fin r → ZMod p) : ℝ) := by
          nlinarith [hMD]

  have hMpos : (0 : ℝ) < (Fintype.card (Fin r → ZMod p) : ℝ) := by
    have h : 0 < Fintype.card (Fin r → ZMod p) := Fintype.card_pos
    exact_mod_cast h
  have harith :
      2 * ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) *
            (Fintype.card (Fin r → ZMod p) : ℝ))
        - (Fintype.card (Fin r → Fin r → ZMod p) : ℝ)
      ≤ (2 - ((p : ℝ) ^ r)⁻¹) *
          (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ) := by
    rw [hcardprod, ← hM]
    have hMne : (Fintype.card (Fin r → ZMod p) : ℝ) ≠ 0 := ne_of_gt hMpos
    field_simp
    linarith
  calc (∑ xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p),
        (((solutions p r xw.1 xw.2).card : ℝ)) ^ 2)
      = ∑ x : Fin r → Fin r → ZMod p, ∑ w : Fin r → ZMod p,
          ((solutions p r x w).card : ℝ) ^ 2 :=
        Fintype.sum_prod_type' (fun x w => ((solutions p r x w).card : ℝ) ^ 2)
    _ = ∑ x : Fin r → Fin r → ZMod p, ∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p,
          (if matSum p r x b = matSum p r x c then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact sum_sq_eq_pairs p r x
    _ = ∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p, ∑ x : Fin r → Fin r → ZMod p,
          (if matSum p r x b = matSum p r x c then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_comm]
    _ = ∑ b : Fin r → ZMod p, ∑ c : Fin r → ZMod p,
          (if b = c then (Fintype.card (Fin r → Fin r → ZMod p) : ℝ)
            else (p : ℝ) ^ (r * r - r)) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        exact sum_ind_over_x p r b c
    _ = 2 * ((Fintype.card (Fin r → Fin r → ZMod p) : ℝ) *
            (Fintype.card (Fin r → ZMod p) : ℝ))
        - (Fintype.card (Fin r → Fin r → ZMod p) : ℝ) := hvalue
    _ ≤ (2 - ((p : ℝ) ^ r)⁻¹) *
          (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ) := harith

theorem lemma5 [Fact p.Prime] :
    4 * ((Finset.univ.filter (fun xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p) =>
        (solutions p r xw.1 xw.2).card = 1 ∨ (solutions p r xw.1 xw.2).card = 2)).card : ℝ)
      ≥ (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have := (Fact.out : p.Prime).two_le
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ‹2 ≤ p›
    linarith
  have hδ0 : (0 : ℝ) ≤ ((p : ℝ) ^ r)⁻¹ := le_of_lt (inv_pos.mpr (pow_pos hp0 r))
  have hδ1 : ((p : ℝ) ^ r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hp1)
  exact lemma5_of_second_moment p r ((p : ℝ) ^ r)⁻¹ hδ0 hδ1 (second_moment p r)

end Qatlib.Papers.SemidirectHSP05.MainResults.MatrixSumCount
