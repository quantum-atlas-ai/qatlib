/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.Group
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.ZMod.Basic
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

open scoped commutatorElement

theorem zpowers_cycGen (n : ℕ) [NeZero n] : Subgroup.zpowers (cycGen n) = ⊤ := by
  letI : Fintype (Cyc n) := Fintype.ofEquiv (ZMod n) Multiplicative.ofAdd
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_cycGen, card_Cyc]

theorem exists_nat_pow_of_zpowers_top {G : Type*} [Group G] [Finite G]
    {g : G} (h : Subgroup.zpowers g = ⊤) (b : G) : ∃ k : ℕ, g ^ k = b := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (by rw [h]; exact Subgroup.mem_top b)
  refine ⟨(m % (Nat.card G : ℤ)).toNat, ?_⟩
  have hcard : (Nat.card G : ℤ) ≠ 0 := by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne'
  have hg : g ^ Nat.card G = 1 := by
    letI : Fintype G := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  rw [← hm, zpow_eq_zpow_emod' m (n := Nat.card G) hg]
  conv_rhs => rw [← Int.toNat_of_nonneg (Int.emod_nonneg m hcard), zpow_natCast]

theorem zpowers_comm {G : Type*} [Group G] {x a b : G}
    (ha : a ∈ Subgroup.zpowers x) (hb : b ∈ Subgroup.zpowers x) : a * b = b * a := by
  haveI : IsMulCommutative (Subgroup.zpowers x) := inferInstance
  exact congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨b, hb⟩)

theorem zpowers_conj_mem {G : Type*} [Group G] {x a b : G}
    (ha : a ∈ Subgroup.zpowers x) (hb : b ∈ Subgroup.zpowers x) :
    a * b * a⁻¹ ∈ Subgroup.zpowers x := by
  rw [zpowers_comm ha hb, mul_assoc, mul_inv_cancel, mul_one]
  exact hb

theorem φ_gen_apply (p r : ℕ) [NeZero (p ^ r)]
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ)
    (a : Cyc (p ^ r)) :
    φ (cycGen (p ^ 2)) a = a ^ (p ^ (r - 2) + 1) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by
    rw [zpowers_cycGen (p ^ r)]
    exact Subgroup.mem_top a)
  rw [← hk, map_zpow, hφ]
  rw [← zpow_natCast (cycGen (p ^ r)) (p ^ (r - 2) + 1), ← zpow_mul]
  conv_rhs => rw [← zpow_natCast (cycGen (p ^ r) ^ k) (p ^ (r - 2) + 1), ← zpow_mul]
  rw [mul_comm]

theorem φ_pow_apply (p r : ℕ) [NeZero (p ^ r)]
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ) (l : ℕ)
    (a : Cyc (p ^ r)) :
    ((φ (cycGen (p ^ 2))) ^ l) a = a ^ (p ^ (r - 2) + 1) ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [pow_succ', MulAut.mul_apply, ih, φ_gen_apply p r φ hφ]
      rw [← pow_mul, pow_succ]

theorem y_conj_mem (p r : ℕ) (hp : p.Prime)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ)
    (l : ℕ) (k : ℤ) :
    yGen p r φ ^ l * (xGen p r φ ^ p ^ (r - 2)) ^ k * (yGen p r φ ^ l)⁻¹
      ∈ Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2)) := by
  haveI hnzr : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI hnz2 : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hEq : yGen p r φ ^ l * (xGen p r φ ^ p ^ (r - 2)) ^ k * (yGen p r φ ^ l)⁻¹
      = (xGen p r φ ^ p ^ (r - 2)) ^ ((p ^ (r - 2) + 1) ^ l * k) := by
    have hy : yGen p r φ ^ l = SemidirectProduct.inr (cycGen (p ^ 2) ^ l) := by
      rw [yGen, map_pow]
    have hx : (xGen p r φ ^ p ^ (r - 2)) ^ k
        = SemidirectProduct.inl ((cycGen (p ^ r) ^ p ^ (r - 2)) ^ k) := by
      rw [xGen, map_zpow, map_pow]
    have hxr : (xGen p r φ ^ p ^ (r - 2)) ^ ((p ^ (r - 2) + 1) ^ l * k)
        = SemidirectProduct.inl
            ((cycGen (p ^ r) ^ p ^ (r - 2)) ^ ((p ^ (r - 2) + 1) ^ l * k)) := by
      rw [xGen, map_zpow, map_pow]
    rw [hy, hx, hxr, ← map_inv, ← SemidirectProduct.inl_aut]
    rw [SemidirectProduct.inl_injective.eq_iff]
    rw [show φ (cycGen (p ^ 2) ^ l) = (φ (cycGen (p ^ 2))) ^ l from map_pow φ _ l]
    rw [show (cycGen (p ^ r) ^ p ^ (r - 2) : Cyc (p ^ r))
          = cycGen (p ^ r) ^ ((p ^ (r - 2) : ℕ) : ℤ) from (zpow_natCast _ _).symm]
    rw [map_zpow, map_zpow, φ_pow_apply p r φ hφ]
    rw [show cycGen (p ^ r) ^ (p ^ (r - 2) + 1) ^ l
          = cycGen (p ^ r) ^ ((((p ^ (r - 2) + 1) ^ l : ℕ) : ℤ)) from (zpow_natCast _ _).symm]
    rw [← zpow_mul, ← zpow_mul, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [hEq]
  exact Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩

theorem K0_normal (p r : ℕ) (hp : p.Prime)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ) :
    (Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2))).Normal := by
  haveI hnzr : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI hnz2 : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : Finite (SDG p r φ) := Nat.finite_of_card_ne_zero (by
    rw [card_SDG_prime_pow p r hp φ]; exact pow_ne_zero _ hp.ne_zero)
  apply Subgroup.Normal.mk
  intro n hn g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← hk]
  obtain ⟨m, hm⟩ := exists_nat_pow_of_zpowers_top (zpowers_cycGen (p ^ r)) g.left
  obtain ⟨l, hl⟩ := exists_nat_pow_of_zpowers_top (zpowers_cycGen (p ^ 2)) g.right
  have hg : g = xGen p r φ ^ m * yGen p r φ ^ l := by
    rw [← SemidirectProduct.inl_left_mul_inr_right g, ← hm, ← hl]
    show SemidirectProduct.inl (cycGen (p ^ r) ^ m)
        * SemidirectProduct.inr (cycGen (p ^ 2) ^ l)
        = xGen p r φ ^ m * yGen p r φ ^ l
    rw [xGen, yGen, map_pow, map_pow]
  rw [hg]
  have hgroup : (xGen p r φ ^ m * yGen p r φ ^ l)
        * (xGen p r φ ^ p ^ (r - 2)) ^ k
        * (xGen p r φ ^ m * yGen p r φ ^ l)⁻¹
      = xGen p r φ ^ m
        * (yGen p r φ ^ l * (xGen p r φ ^ p ^ (r - 2)) ^ k
            * (yGen p r φ ^ l)⁻¹)
        * (xGen p r φ ^ m)⁻¹ := by
    group
  rw [hgroup]
  have hB : yGen p r φ ^ l * (xGen p r φ ^ p ^ (r - 2)) ^ k
      * (yGen p r φ ^ l)⁻¹ ∈ Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2)) :=
    y_conj_mem p r hp φ hφ l k
  have hxA : xGen p r φ ^ m ∈ Subgroup.zpowers (xGen p r φ) :=
    Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m
  have hKle : Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2))
      ≤ Subgroup.zpowers (xGen p r φ) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) (p ^ (r - 2))
  have hconj : xGen p r φ ^ m
        * (yGen p r φ ^ l * (xGen p r φ ^ p ^ (r - 2)) ^ k
            * (yGen p r φ ^ l)⁻¹)
        * (xGen p r φ ^ m)⁻¹
      = yGen p r φ ^ l * (xGen p r φ ^ p ^ (r - 2)) ^ k
            * (yGen p r φ ^ l)⁻¹ := by
    rw [zpowers_comm hxA (hKle hB), mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact hB

theorem closure_xGen_yGen (p r : ℕ) (hp : p.Prime)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Subgroup.closure ({xGen p r φ, yGen p r φ} : Set (SDG p r φ)) = ⊤ := by
  haveI hnzr : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI hnz2 : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : Finite (SDG p r φ) := Nat.finite_of_card_ne_zero (by
    rw [card_SDG_prime_pow p r hp φ]; exact pow_ne_zero _ hp.ne_zero)
  rw [eq_top_iff]
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  apply Subgroup.mul_mem
  · obtain ⟨m, hm⟩ := exists_nat_pow_of_zpowers_top (zpowers_cycGen (p ^ r)) g.left
    have hgm : SemidirectProduct.inl g.left = xGen p r φ ^ m := by
      rw [← hm, xGen, map_pow]
    rw [hgm]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [xGen])) m
  · obtain ⟨l, hl⟩ := exists_nat_pow_of_zpowers_top (zpowers_cycGen (p ^ 2)) g.right
    have hgl : SemidirectProduct.inr g.right = yGen p r φ ^ l := by
      rw [← hl, yGen, map_pow]
    rw [hgl]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [yGen])) l

theorem commutator_yGen_xGen (p r : ℕ) [NeZero (p ^ r)]
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ) :
    ⁅yGen p r φ, xGen p r φ⁆ = xGen p r φ ^ p ^ (r - 2) := by
  rw [commutatorElement_def]
  have hconj : yGen p r φ * xGen p r φ * (yGen p r φ)⁻¹
      = xGen p r φ ^ (p ^ (r - 2) + 1) := by
    rw [xGen, yGen, ← map_inv, ← SemidirectProduct.inl_aut, hφ, map_pow]
  rw [hconj]
  have hpow : xGen p r φ ^ (p ^ (r - 2) + 1)
      = xGen p r φ ^ (p ^ (r - 2)) * xGen p r φ := pow_succ _ _
  rw [hpow, mul_assoc, mul_inv_cancel, mul_one]

theorem classOne_commutator_le (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ) :
    commutator (SDG p r φ) ≤
      Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2)) := by
  haveI hnzr : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI hnz2 : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : Finite (SDG p r φ) := Nat.finite_of_card_ne_zero (by
    rw [card_SDG_prime_pow p r hp φ]; exact pow_ne_zero _ hp.ne_zero)
  let K : Subgroup (SDG p r φ) := Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2))
  have hKnormal : K.Normal := K0_normal p r hp φ hφ
  haveI : K.Normal := hKnormal
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)]
  let π : SDG p r φ →* SDG p r φ ⧸ K := QuotientGroup.mk' K
  have hset : ({π (xGen p r φ), π (yGen p r φ)} : Set (SDG p r φ ⧸ K))
      = π '' ({xGen p r φ, yGen p r φ} : Set (SDG p r φ)) := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact ⟨xGen p r φ, Or.inl rfl, h.symm⟩
      · exact ⟨yGen p r φ, Or.inr rfl, h.symm⟩
    · rintro ⟨w, hw, hπ⟩
      rcases hw with hw | hw
      · subst w; exact Or.inl hπ.symm
      · subst w; exact Or.inr hπ.symm
  have htop : Subgroup.closure
      ({π (xGen p r φ), π (yGen p r φ)} : Set (SDG p r φ ⧸ K)) = ⊤ := by
    rw [hset, ← MonoidHom.map_closure, closure_xGen_yGen p r hp φ,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective K)]
  have mk_one : ∀ y : SDG p r φ, y ∈ K → π y = 1 := by
    intro y hy
    change (QuotientGroup.mk' K) y = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy
  have hxy : ⁅xGen p r φ, yGen p r φ⁆ ∈ K := by
    rw [show ⁅xGen p r φ, yGen p r φ⁆ = (⁅yGen p r φ, xGen p r φ⁆)⁻¹ from by
      rw [commutatorElement_inv]]
    rw [commutator_yGen_xGen p r φ hφ]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hyx : ⁅yGen p r φ, xGen p r φ⁆ ∈ K := by
    rw [commutator_yGen_xGen p r φ hφ]
    exact Subgroup.mem_zpowers _
  have hcomm : ∀ a ∈ ({π (xGen p r φ), π (yGen p r φ)} : Set (SDG p r φ ⧸ K)),
      ∀ b ∈ ({π (xGen p r φ), π (yGen p r φ)} : Set (SDG p r φ ⧸ K)),
        a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · have h1 : ⁅π (xGen p r φ), π (yGen p r φ)⁆ = 1 := by
        rw [← map_commutatorElement]
        exact mk_one _ hxy
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · have h1 : ⁅π (yGen p r φ), π (xGen p r φ)⁆ = 1 := by
        rw [← map_commutatorElement]
        exact mk_one _ hyx
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · rfl
  haveI : IsMulCommutative
      (↥(Subgroup.closure ({π (xGen p r φ), π (yGen p r φ)} : Set (SDG p r φ ⧸ K)))) :=
    Subgroup.isMulCommutative_closure (fun a ha b hb _ => hcomm a ha b hb)
  refine IsMulCommutative.of_comm (fun a b => ?_)
  have ha : a ∈ Subgroup.closure ({π (xGen p r φ), π (yGen p r φ)} : Set (SDG p r φ ⧸ K)) := by
    rw [htop]; trivial
  have hb : b ∈ Subgroup.closure ({π (xGen p r φ), π (yGen p r φ)} : Set (SDG p r φ ⧸ K)) := by
    rw [htop]; trivial
  exact congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨b, hb⟩)

end Qatlib.Papers.SemidirectHSP07.MainResults
