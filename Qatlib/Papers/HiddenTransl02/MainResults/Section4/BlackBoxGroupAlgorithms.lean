/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false
noncomputable section

namespace Qatlib.Papers.HiddenTransl02.MainResults.Section4

section GroupOps

variable {G Γ : Type*}

section SubgroupSuperposition

variable [Group G]

theorem leftMul_bijective_on_subgroup (H : Subgroup G) {g : G} (hg : g ∈ H) :
    Function.Bijective (fun h : H => (⟨g * (h : G), H.mul_mem hg h.2⟩ : H)) := by
  constructor
  · intro h₁ h₂ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (mul_left_cancel h)
  · intro h
    refine ⟨⟨g⁻¹ * (h : G), H.mul_mem (H.inv_mem hg) h.2⟩, ?_⟩
    apply Subtype.ext
    simp

theorem uniform_subgroup_weights_sum (H : Subgroup G) [Fintype H] [Nonempty H] :
    ∑ _h : H, ((Fintype.card H : ℝ)⁻¹) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end SubgroupSuperposition

section CompatibleEncoding

variable {Code : Type*}
variable [Group G]

def quotientEncoding (N : Subgroup G) (enc : G → Code) (x : G) : Code :=
  enc (Quotient.out (QuotientGroup.mk x : G ⧸ N))

theorem quotientEncoding_exists_representative (N : Subgroup G) (enc : G → Code) (x : G) :
    ∃ y : G, y⁻¹ * x ∈ N ∧ quotientEncoding N enc x = enc y := by
  refine ⟨Quotient.out (QuotientGroup.mk x : G ⧸ N), ?_, rfl⟩
  have hq : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ N)) : G ⧸ N)
      = QuotientGroup.mk x := by
    simp
  exact (QuotientGroup.eq).mp hq

theorem quotientEncoding_eq_of_mem (N : Subgroup G) (enc : G → Code) {x y : G}
    (h : y⁻¹ * x ∈ N) : quotientEncoding N enc x = quotientEncoding N enc y := by
  have h' : x⁻¹ * y ∈ N := by
    simpa using N.inv_mem h
  have hq : (QuotientGroup.mk x : G ⧸ N) = QuotientGroup.mk y := (QuotientGroup.eq).mpr h'
  simp only [quotientEncoding, hq]

end CompatibleEncoding

section OrbitSuperposition

variable [Group G] [MulAction G Γ]

theorem orbit_equiv_quotient_stabilizer (φ : Γ) :
    Nonempty (MulAction.orbit G φ ≃ (G ⧸ MulAction.stabilizer G φ)) :=
  ⟨MulAction.orbitEquivQuotientStabilizer G φ⟩

theorem fiber_eq_coset (φ ψ : Γ) (x : G) (hx : x • φ = ψ) :
    {y : G | y • φ = ψ} = {y : G | y⁻¹ * x ∈ MulAction.stabilizer G φ} := by
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hy
    have hy' : y • φ = ψ := hy
    have : (y⁻¹ * x) • φ = φ := by
      rw [mul_smul, hx, ← hy', inv_smul_smul]
    exact this
  · intro hy
    have hfix : (y⁻¹ * x) • φ = φ := hy
    calc y • φ = y • ((y⁻¹ * x) • φ) := by rw [hfix]
      _ = (y * (y⁻¹ * x)) • φ := by rw [← mul_smul]
      _ = x • φ := by rw [mul_inv_cancel_left]
      _ = ψ := hx

end OrbitSuperposition

section SelfReduction

variable [Group G]

theorem exists_normal_correction (N H : Subgroup G) (u z : G)
    (hz : ∃ h ∈ H, ∃ n ∈ N, z = u * h * n) :
    ∃ n ∈ N, u⁻¹ * z * n ∈ H := by
  obtain ⟨h, hh, n, hn, rfl⟩ := hz
  refine ⟨n⁻¹, N.inv_mem hn, ?_⟩
  have heq : u⁻¹ * (u * h * n) * n⁻¹ = h := by group
  rw [heq]
  exact hh

theorem biUnion_coset_eq (N H : Subgroup G) :
    (⋃ h : H, (fun x => (h : G) * x) '' ((H ⊓ N : Subgroup G) : Set G)) = (H : Set G) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨h, y, hy, rfl⟩
    exact H.mul_mem h.2 hy.1
  · intro hx
    exact ⟨⟨x, hx⟩, 1, ⟨Subgroup.one_mem H, Subgroup.one_mem N⟩, mul_one x⟩

theorem coset_subset_of_inter (N H : Subgroup G) (h : H) :
    (fun x => (h : G) * x) '' ((H ⊓ N : Subgroup G) : Set G) ⊆ (H : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  exact H.mul_mem h.2 hy.1

theorem translatingCoset_self_eq_stabilizer [MulAction G Γ] (φ : Γ) :
    {u : G | u • φ = φ} = (MulAction.stabilizer G φ : Set G) := rfl

end SelfReduction

section TranslatingCosetUniqueness

variable [Group G] [MulAction G Γ]

def leftCoset (u : G) (H : Subgroup G) : Set G := {g | u⁻¹ * g ∈ H}

theorem leftCoset_eq_of_both_translate {φ₀ φ₁ : Γ} {u v : G}
    (hu : u • φ₁ = φ₀) (hv : v • φ₁ = φ₀) :
    leftCoset u (MulAction.stabilizer G φ₁) = leftCoset v (MulAction.stabilizer G φ₁) := by
  have hmem : u⁻¹ * v ∈ MulAction.stabilizer G φ₁ := by
    show (u⁻¹ * v) • φ₁ = φ₁
    rw [mul_smul, hv, ← hu, inv_smul_smul]
  ext g
  simp only [leftCoset, Set.mem_setOf_eq]
  constructor
  · intro hg
    have hinv : v⁻¹ * u ∈ MulAction.stabilizer G φ₁ := by
      simpa using (MulAction.stabilizer G φ₁).inv_mem hmem
    have : v⁻¹ * g = (v⁻¹ * u) * (u⁻¹ * g) := by group
    rw [this]
    exact (MulAction.stabilizer G φ₁).mul_mem hinv hg
  · intro hg
    have : (u⁻¹ * g) = (u⁻¹ * v) * (v⁻¹ * g) := by group
    rw [this]
    exact (MulAction.stabilizer G φ₁).mul_mem hmem hg

end TranslatingCosetUniqueness

end GroupOps

set_option autoImplicit false
set_option warningAsError false
noncomputable section

section SeriesBounds

variable {G : Type*} [Group G]

theorem pow_mem_of_quotient_pow (N : Subgroup G) [N.Normal] (g : G) (m : ℕ)
    (h : (QuotientGroup.mk g : G ⧸ N) ^ m = 1) : g ^ m ∈ N := by
  rw [← QuotientGroup.eq_one_iff]
  have hm : QuotientGroup.mk (g ^ m) = (QuotientGroup.mk g : G ⧸ N) ^ m := rfl
  rw [hm, h]

theorem pow_mul_eq_one_of_exponent (N : Subgroup G) [N.Normal] (e s : ℕ)
    (hN : ∀ x ∈ N, x ^ e = 1)
    (hQ : ∀ g : G, (QuotientGroup.mk g : G ⧸ N) ^ s = 1) (g : G) :
    g ^ (e * s) = 1 := by
  have hs : g ^ s ∈ N := pow_mem_of_quotient_pow N g s (hQ g)
  have h : (g ^ s) ^ e = 1 := hN _ hs
  rw [← pow_mul] at h
  rwa [mul_comm] at h

theorem pow_card_quotient_mem (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)] (g : G) :
    g ^ Fintype.card (G ⧸ N) ∈ N := by
  apply pow_mem_of_quotient_pow
  exact pow_card_eq_one

theorem pow_mul_card_quotient_eq_one (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]
    (e : ℕ) (hN : ∀ x ∈ N, x ^ e = 1) (g : G) :
    g ^ (e * Fintype.card (G ⧸ N)) = 1 :=
  pow_mul_eq_one_of_exponent N e (Fintype.card (G ⧸ N)) hN
    (fun _ => pow_card_eq_one) g

theorem pow_pow_mem_of_chain (N : ℕ → Subgroup G) (e : ℕ) (htop : N 0 = ⊤)
    (hstep : ∀ i : ℕ, ∀ x ∈ N i, x ^ e ∈ N (i + 1)) (g : G) :
    ∀ r : ℕ, g ^ (e ^ r) ∈ N r
  | 0 => by
      rw [pow_zero, pow_one, htop]
      exact Subgroup.mem_top g
  | r + 1 => by
      have hIH : g ^ (e ^ r) ∈ N r := pow_pow_mem_of_chain N e htop hstep g r
      have h := hstep r (g ^ (e ^ r)) hIH
      have h' : g ^ (e ^ r * e) ∈ N (r + 1) := by
        rw [pow_mul]
        exact h
      simpa [pow_succ] using h'

end SeriesBounds

end

section DerivedSeriesBound

variable {G : Type*} [Group G]

theorem pow_pow_derivedSeries_eq_one (e m : ℕ)
    (hbot : derivedSeries G m = ⊥)
    (hstep : ∀ i : ℕ, ∀ x ∈ derivedSeries G i, x ^ e ∈ derivedSeries G (i + 1))
    (g : G) : g ^ (e ^ m) = 1 := by
  have hmem : g ^ (e ^ m) ∈ derivedSeries G m :=
    pow_pow_mem_of_chain (derivedSeries G) e (derivedSeries_zero G) hstep g m
  rw [hbot] at hmem
  simpa using hmem

theorem exists_pow_pow_eq_one_of_solvable [Group.IsSolvable G] (e : ℕ)
    (hstep : ∀ i : ℕ, ∀ x ∈ derivedSeries G i, x ^ e ∈ derivedSeries G (i + 1)) :
    ∃ m : ℕ, ∀ g : G, g ^ (e ^ m) = 1 := by
  obtain ⟨m, hm⟩ := Group.IsSolvable.solvable (G := G)
  exact ⟨m, fun g => pow_pow_derivedSeries_eq_one e m hm hstep g⟩

end DerivedSeriesBound
end Qatlib.Papers.HiddenTransl02.MainResults.Section4
