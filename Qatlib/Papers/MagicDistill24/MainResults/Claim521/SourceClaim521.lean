/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.QuditF1024

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Claim 5.2.1 (arXiv:2408.07764v2, p.~42, Eqs (252)–(255))

Let `C̃ = m_w(C)` be the code obtained from `C` by componentwise multiplication
by a vector `w` with every `w_i ≠ 0`. Then
`(C̃)^⊥ = m_{w^{-1}}(C^⊥)`, where `(w^{-1})_i = w_i^{-1}`. Because the map
`m_{w^{-1}}` preserves Hamming weight (`|m_{w^{-1}}(v)| = |v|`), the dual code
`(C̃)^⊥` has the same distance as `C^⊥`.

The paper proves the inclusion `m_{w^{-1}}(C^⊥) ⊆ (C̃)^⊥` directly and closes it
by dimension (`dim(C̃)^⊥ = N − dim C̃ = N − dim C = dim C^⊥ = dim m_{w^{-1}}(C^⊥)`,
Eqs (252)–(255)). We instead prove the equality on membership, which avoids the
dimension count.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Claim521

open Finset
open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Componentwise scaling `m_w : x ↦ (fun i => w i * x i)`, an `𝔽_q`-linear map
(the paper's `m_w`, Definition 5.1.1). -/
noncomputable def scaleLin {n : ℕ} (w : Fin n → F1024) :
    (Fin n → F1024) →ₗ[F1024] (Fin n → F1024) where
  toFun x := fun i => w i * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' a x := by ext i; simp [mul_left_comm]

/-- The dual code `C^⊥` with respect to the standard dot product
`⟪x, y⟫ = ∑_i x_i y_i` over `𝔽_q`. -/
noncomputable def codeDual {n : ℕ} (C : Submodule F1024 (Fin n → F1024)) :
    Submodule F1024 (Fin n → F1024) where
  carrier := {x | ∀ y ∈ C, ∑ i, x i * y i = 0}
  zero_mem' := by
    intro y _
    simp
  add_mem' := by
    intro x z hx hz y hy
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hx y hy, hz y hy, add_zero]
  smul_mem' := by
    intro a x hx y hy
    simp only [Pi.smul_apply, smul_eq_mul]
    have hsum : (∑ i, a * x i * y i) = a * ∑ i, x i * y i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum, hx y hy, mul_zero]

/-- Fixed arXiv:2408.07764v2, Claim 5.2.1 (p.~42, Eqs (252)–(255)): for a code
`C ≤ 𝔽_q^n` and a nowhere-zero weight vector `w`, the dual of the scaled code
`m_w(C)` is `m_{w^{-1}}(C^⊥)`. -/
theorem source_claim_5_2_1 {n : ℕ}
    (C : Submodule F1024 (Fin n → F1024)) (w : Fin n → F1024) (hw : ∀ i, w i ≠ 0) :
    codeDual (Submodule.map (scaleLin w) C)
      = Submodule.map (scaleLin (fun i => (w i)⁻¹)) (codeDual C) := by
  ext x
  constructor
  · -- `x ∈ (m_w C)^⊥  ⟹  x = m_{w^{-1}}(w • x)` with `w • x ∈ C^⊥`.
    intro hx
    have hwx : (fun i => w i * x i) ∈ codeDual C := by
      intro y hy
      have hmem : (fun i => w i * y i) ∈ Submodule.map (scaleLin w) C :=
        Submodule.mem_map.mpr ⟨y, hy, rfl⟩
      have h0 := hx _ hmem
      rwa [show (∑ i, (fun i => w i * x i) i * y i)
              = ∑ i, x i * (fun i => w i * y i) i from
            Finset.sum_congr rfl (fun i _ => by ring)]
    refine Submodule.mem_map.mpr ⟨_, hwx, ?_⟩
    ext i
    simp only [scaleLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [inv_mul_cancel_left₀ (hw i)]
  · -- `x = m_{w^{-1}}(z)`, `z ∈ C^⊥`  ⟹  `x ∈ (m_w C)^⊥`.
    rintro ⟨z, hz, rfl⟩
    intro y hy
    obtain ⟨c, hc, hcy⟩ := Submodule.mem_map.mp hy
    subst hcy
    simp only [scaleLin, LinearMap.coe_mk, AddHom.coe_mk]
    have hsum : (∑ i, (w i)⁻¹ * z i * (w i * c i)) = ∑ i, z i * c i :=
      Finset.sum_congr rfl (fun i _ => by
        field_simp [hw i])
    rw [hsum]
    exact hz _ hc

end Qatlib.Papers.MagicDistill24.MainResults.Claim521
