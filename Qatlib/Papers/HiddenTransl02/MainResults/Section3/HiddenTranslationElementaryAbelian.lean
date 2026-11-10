/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.HiddenTransl02.MainResults.Section3

section Reductions

variable {G Γ S : Type*}

section Orbit

variable [Group G] [MulAction G Γ]

theorem orbit_eq_range (φ : Γ) :
    MulAction.orbit G φ = Set.range (fun x : G => x • φ) := by
  rfl

theorem translatingCoset_nonempty_iff_orbit_inter (φ₀ φ₁ : Γ) :
    (∃ u : G, u • φ₁ = φ₀) ↔ (MulAction.orbit G φ₀ ∩ MulAction.orbit G φ₁).Nonempty := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u • φ₁, ⟨1, by simp⟩, ⟨u, rfl⟩⟩
  · rintro ⟨ψ, ⟨x, hx⟩, ⟨y, hy⟩⟩
    have hy' : y • φ₁ = ψ := hy
    have hx' : x • φ₀ = ψ := hx
    refine ⟨x⁻¹ * y, ?_⟩
    calc (x⁻¹ * y) • φ₁ = x⁻¹ • (y • φ₁) := by rw [mul_smul]
      _ = x⁻¹ • (x • φ₀) := by rw [hy', ← hx']
      _ = φ₀ := inv_smul_smul x φ₀

theorem ranges_disjoint_of_translatingCoset_empty {φ₀ φ₁ : Γ}
    (h : ¬ ∃ u : G, u • φ₁ = φ₀) :
    Set.range (fun x : G => x • φ₀) ∩ Set.range (fun x : G => x • φ₁) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ψ ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  have hy' : y • φ₁ = ψ := hy
  have hx' : x • φ₀ = ψ := hx
  apply h
  refine ⟨x⁻¹ * y, ?_⟩
  calc (x⁻¹ * y) • φ₁ = x⁻¹ • (y • φ₁) := by rw [mul_smul]
    _ = x⁻¹ • (x • φ₀) := by rw [hy', ← hx']
    _ = φ₀ := inv_smul_smul x φ₀

end Orbit

section TwoOracle

def doubledFst {f₀ f₁ : G → S} (x : G) : S × S := (f₀ x, f₁ x)

def doubledSnd [InvolutiveInv G] {f₀ f₁ : G → S} (x : G) : S × S := (f₁ x, f₀ x⁻¹)

theorem doubledFst_injective {f₀ f₁ : G → S} (h : Function.Injective f₀) :
    Function.Injective (doubledFst (f₀ := f₀) (f₁ := f₁)) := by
  intro x y hxy
  simp only [doubledFst, Prod.mk.injEq] at hxy
  exact h hxy.1

theorem doubled_translation {f₀ f₁ : G → S} [AddGroup G] {u : G}
    (htrans : ∀ x, f₀ x = f₁ (x + u))
    (hsym : ∀ x, f₀ (-(x + u)) = f₁ x) :
    ∀ x, doubledFst (f₀ := f₀) (f₁ := f₁) x =
      (fun y => (f₁ y, f₀ (-y))) (x + u) := by
  intro x
  show (f₀ x, f₁ x) = (f₁ (x + u), f₀ (-(x + u)))
  rw [htrans x, hsym x]

end TwoOracle

section DoubleCover

variable [AddCommGroup G]
variable (F : G × ZMod 2 → S)

def slice (b : ZMod 2) (x : G) : S := F (x, b)

theorem slice_translation {H : AddSubgroup (G × ZMod 2)} {u : G}
    (hmem : (u, 1) ∈ H) (hH : ∀ z, z ∈ H → ∀ w, F (w + z) = F w) :
    ∀ x, slice F 0 x = slice F 1 (x + u) := by
  intro x
  have h := hH (u, 1) hmem (x, 0)
  simpa [slice, add_comm, add_left_comm, add_assoc] using h.symm

theorem slice_stabilized {H : AddSubgroup (G × ZMod 2)}
    (hH : ∀ z, z ∈ H → ∀ w, F (w + z) = F w) {x : G} (hx : (x, 0) ∈ H) :
    ∀ y, slice F 0 (y + x) = slice F 0 y := by
  intro y
  have h := hH (x, 0) hx (y, 0)
  simpa [slice, add_comm] using h

end DoubleCover

end Reductions

set_option autoImplicit false
set_option warningAsError true
noncomputable section

section Counting

open Finset

variable {p n : ℕ}

def dotU (u : Fin n → ZMod p) : (Fin n → ZMod p) →+ ZMod p where
  toFun y := ∑ i, y i * u i
  map_zero' := by simp
  map_add' := by
    intro x y
    simp [Finset.sum_add_distrib, add_mul]

theorem fiber_dotU_eq (u : Fin n → ZMod p) (k : ZMod p) :
    {y : Fin n → ZMod p | dotU u y = k} = {y | ∑ i, y i * u i = k} := rfl

theorem fiber_disjoint {A : Type*} [AddCommGroup A] (φ : A →+ ZMod p) {a b : ZMod p}
    (hab : a ≠ b) : Disjoint {x : A | φ x = a} {x : A | φ x = b} := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact hab (hx.symm.trans hy)

theorem iUnion_fiber {A : Type*} [AddCommGroup A] (φ : A →+ ZMod p) :
    (⋃ a : ZMod p, {x : A | φ x = a}) = Set.univ := by
  ext x
  simp [Set.mem_iUnion]

theorem fiber_eq_translate {A : Type*} [AddCommGroup A] (φ : A →+ ZMod p) {a b : ZMod p}
    {z : A} (hz : φ z = a - b) :
    {x : A | φ x = a} = (fun x => x + z) '' {x : A | φ x = b} := by
  ext x
  constructor
  · intro hx
    refine ⟨x - z, ?_, ?_⟩
    · show φ (x - z) = b
      rw [map_sub, hx, hz]
      abel
    · abel
  · rintro ⟨y, hy, rfl⟩
    show φ (y + z) = a
    rw [map_add, hy, hz]
    abel

theorem fiber_card_eq {A : Type*} [AddCommGroup A] [Fintype A] (φ : A →+ ZMod p)
    {a b : ZMod p} (hb : ∃ z : A, φ z = a - b) :
    Fintype.card {x : A // φ x = a} = Fintype.card {x : A // φ x = b} := by
  classical
  obtain ⟨z, hz⟩ := hb
  refine Fintype.card_congr ?_
  refine
    { toFun := fun x => ⟨x.1 - z, ?_⟩
      invFun := fun x => ⟨x.1 + z, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · show φ (x.1 - z) = b
    rw [map_sub, x.2, hz]
    abel
  · show φ (x.1 + z) = a
    rw [map_add, x.2, hz]
    abel
  · intro x
    exact Subtype.ext (sub_add_cancel _ _)
  · intro x
    exact Subtype.ext (add_sub_cancel_right _ _)

theorem dotU_surjective [Fact p.Prime] {u : Fin n → ZMod p} (hu : u ≠ 0) :
    Function.Surjective (dotU u) := by
  intro a
  obtain ⟨i, hi⟩ : ∃ i : Fin n, u i ≠ 0 := by
    by_contra h
    have hu0 : ∀ i, u i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    exact hu (funext hu0)
  refine ⟨(Pi.single i (a * (u i)⁻¹) : Fin n → ZMod p), ?_⟩
  show ∑ j, (Pi.single i (a * (u i)⁻¹) : Fin n → ZMod p) j * u j = a
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_assoc, inv_mul_cancel₀ hi, mul_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Counting

end

end Qatlib.Papers.HiddenTransl02.MainResults.Section3
