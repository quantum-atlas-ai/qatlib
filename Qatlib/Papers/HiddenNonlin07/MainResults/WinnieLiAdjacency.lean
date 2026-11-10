/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.HiddenNonlin07.MainResults.WinnieLiAdjacency

open scoped BigOperators Matrix
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def quadForm {d : ℕ} (x : Fin d → F) : F := ∑ j, x j ^ 2

def sphere {d : ℕ} (r : F) : Finset (Fin d → F) := univ.filter fun x => quadForm x = r

theorem mem_sphere {d : ℕ} {r : F} {x : Fin d → F} : x ∈ sphere r ↔ quadForm x = r := by
  simp [sphere]

theorem neg_mem_sphere {d : ℕ} {r : F} {x : Fin d → F} :
    x ∈ sphere r ↔ -x ∈ sphere r := by
  rw [mem_sphere, mem_sphere, quadForm, quadForm]
  constructor
  · intro h
    simpa [neg_sq] using h
  · intro h
    simpa [neg_sq] using h

theorem sum_sphere_neg {d : ℕ} (g : (Fin d → F) → ℂ) :
    (∑ s ∈ sphere (d := d) 1, g (-s)) = ∑ s ∈ sphere (d := d) 1, g s := by
  classical
  refine Finset.sum_nbij' (fun s => -s) (fun s => -s) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simpa using neg_mem_sphere.mp hs
  · intro s hs
    simpa using neg_mem_sphere.mp hs
  · intro s _
    simp
  · intro s _
    simp
  · intro s _
    simp

def adj (d : ℕ) : Matrix (Fin d → F) (Fin d → F) ℂ :=
  fun x y => if quadForm (x - y) = 1 then 1 else 0

theorem adj_add {d : ℕ} (a x y : Fin d → F) : adj d (x + a) (y + a) = adj d x y := by
  have h : x + a - (y + a) = x - y := by abel
  simp only [adj, h]

theorem adj_comm {d : ℕ} (x y : Fin d → F) : adj d x y = adj d y x := by
  have h : y - x = -(x - y) := by abel
  have hq : quadForm (-(x - y)) = quadForm (x - y) := by
    rw [quadForm, quadForm]
    apply Finset.sum_congr rfl
    intro j _
    have hneg : (-(x - y)) j = -(x j - y j) := by
      simp only [Pi.neg_apply, Pi.sub_apply]
    rw [hneg, neg_sq]
    simp only [Pi.sub_apply]
  simp only [adj, h, hq]

theorem mulVec_adj {d : ℕ} (v : (Fin d → F) → ℂ) (x : Fin d → F) :
    (adj d *ᵥ v) x = ∑ s ∈ sphere 1, v (x - s) := by
  classical
  have hunfold : (adj d *ᵥ v) x = ∑ y, adj d x y * v y := rfl
  rw [hunfold]
  have hL : (∑ y, adj d x y * v y) =
      ∑ y, if quadForm (x - y) = 1 then v y else 0 := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : quadForm (x - y) = 1 <;> simp [adj, h]
  have hR : (∑ s ∈ sphere (d := d) 1, v (x - s)) =
      ∑ s, if quadForm s = 1 then v (x - s) else 0 := by
    rw [sphere, Finset.sum_filter]
  rw [hL, hR]
  refine Fintype.sum_equiv
    { toFun := fun s => x - s
      invFun := fun s => x - s
      left_inv := fun s => by ext i; simp only [Pi.sub_apply]; ring
      right_inv := fun s => by ext i; simp only [Pi.sub_apply]; ring }
    (fun y => if quadForm (x - y) = 1 then v y else 0)
    (fun s => if quadForm s = 1 then v (x - s) else 0) ?_
  intro y
  have h : x - (x - y) = y := by ext i; simp only [Pi.sub_apply]; ring
  simp only [Equiv.coe_fn_mk]
  rw [h]

noncomputable def sphereState {d : ℕ} (x : Fin d → F) : (Fin d → F) → ℂ :=
  ∑ s ∈ sphere 1, Pi.single (x + s) (1 : ℂ)

theorem mulVec_adj_sphereState {d : ℕ} (x y : Fin d → F) :
    (adj d *ᵥ sphereState x) y =
      ∑ s ∈ sphere 1, ∑ t ∈ sphere 1, (if x + s + t = y then (1 : ℂ) else 0) := by
  classical
  rw [mulVec_adj]
  apply Finset.sum_congr rfl
  intro s _
  rw [sphereState, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Pi.single_apply]
  by_cases h : y - s = x + t
  · have h2 : x + s + t = y := by
      rw [show x + s + t = x + t + s by abel, ← h]
      abel
    rw [if_pos h, if_pos h2]
  · have h2 : x + s + t ≠ y := by
      intro hh
      apply h
      rw [← hh]
      abel
    rw [if_neg h, if_neg h2]

theorem center_coefficient {d : ℕ} (x : Fin d → F) :
    (adj d *ᵥ sphereState x) x = ((sphere (F := F) (d := d) (1 : F)).card : ℂ) := by
  classical
  rw [mulVec_adj]
  have hterm : ∀ s ∈ sphere (d := d) 1, sphereState x (x - s) = (1 : ℂ) := by
    intro s hs
    rw [sphereState, Finset.sum_apply]
    rw [Finset.sum_eq_single (-s)]
    · have hxs : x + -s = x - s := by abel
      simp only [Pi.single_apply, hxs, if_true]
    · intro t _ hne
      by_cases ht : x + t = x - s
      · have hneg : x + t = x + -s := by
          rw [sub_eq_add_neg] at ht
          exact ht
        exact absurd (add_left_cancel hneg) hne
      · simp [ht]
    · intro hmem
      exact absurd (neg_mem_sphere.mp hs) hmem
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem sphere_one_nonempty {d : ℕ} (hd : 0 < d) :
    (sphere (F := F) (d := d) (1 : F)).Nonempty := by
  refine ⟨Pi.single (⟨0, hd⟩ : Fin d) (1 : F), ?_⟩
  rw [mem_sphere, quadForm]
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp
  · intro j _ hj
    simp only [Pi.single_apply, hj, if_false, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
  · intro h
    exact absurd (Finset.mem_univ _) h

def onesMat (d : ℕ) : Matrix (Fin d → F) (Fin d → F) ℂ := fun _ _ => 1

noncomputable def adjBar (d : ℕ) : Matrix (Fin d → F) (Fin d → F) ℂ :=
  adj d - (((sphere (F := F) (d := d) 1).card : ℂ) /
      (Fintype.card (Fin d → F) : ℂ)) • onesMat d

theorem onesMat_mulVec (d : ℕ) (v : (Fin d → F) → ℂ) (x : Fin d → F) :
    (onesMat d *ᵥ v) x = ∑ y, v y := by
  classical
  simp [Matrix.mulVec, dotProduct, onesMat]

theorem sum_sphereState (d : ℕ) (x : Fin d → F) :
    (∑ y, sphereState x y) = ((sphere (F := F) (d := d) 1).card : ℂ) := by
  classical
  rw [sphereState]
  simp only [Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun s _ => ?_)]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [Finset.sum_eq_single (x + s)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem adjBar_center_coefficient (d : ℕ) (x : Fin d → F) :
    (adjBar d *ᵥ sphereState x) x =
      ((sphere (F := F) (d := d) 1).card : ℂ) -
        ((sphere (F := F) (d := d) 1).card : ℂ) ^ 2 /
          (Fintype.card (Fin d → F) : ℂ) := by
  classical
  have hN : (Fintype.card (Fin d → F) : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card (Fin d → F) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
    exact_mod_cast hpos.ne'
  rw [adjBar, Matrix.sub_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [center_coefficient, onesMat_mulVec, sum_sphereState]
  field_simp

theorem adjBar_center_amplitude {d : ℕ} (hd : 0 < d) (x : Fin d → F) :
    (adjBar d *ᵥ sphereState x) x /
        ((Real.sqrt (((sphere (F := F) (d := d) 1).card : ℝ)) : ℂ)) =
      ((Real.sqrt (((sphere (F := F) (d := d) 1).card : ℝ)) : ℂ)) *
        (1 - ((sphere (F := F) (d := d) 1).card : ℂ) /
          (Fintype.card (Fin d → F) : ℂ)) := by
  classical
  have hcard : 0 < ((sphere (F := F) (d := d) 1).card : ℝ) := by
    have := Finset.card_pos.mpr (sphere_one_nonempty (F := F) hd)
    exact_mod_cast this
  have hs : ((Real.sqrt (((sphere (F := F) (d := d) 1).card : ℝ))) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hcard).ne'
  have hsq : ((Real.sqrt (((sphere (F := F) (d := d) 1).card : ℝ))) : ℂ) ^ 2 =
      ((sphere (F := F) (d := d) 1).card : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_cast
  rw [adjBar_center_coefficient]
  rw [div_eq_iff hs]
  calc ((sphere (F := F) (d := d) 1).card : ℂ) -
        ((sphere (F := F) (d := d) 1).card : ℂ) ^ 2 / (Fintype.card (Fin d → F) : ℂ)
      = ((sphere (F := F) (d := d) 1).card : ℂ) *
          (1 - ((sphere (F := F) (d := d) 1).card : ℂ) /
            (Fintype.card (Fin d → F) : ℂ)) := by ring
    _ = ((Real.sqrt (((sphere (F := F) (d := d) 1).card : ℝ)) : ℂ)) ^ 2 *
          (1 - ((sphere (F := F) (d := d) 1).card : ℂ) /
            (Fintype.card (Fin d → F) : ℂ)) := by rw [hsq]
    _ = (((Real.sqrt (((sphere (F := F) (d := d) 1).card : ℝ)) : ℂ)) *
          (1 - ((sphere (F := F) (d := d) 1).card : ℂ) /
            (Fintype.card (Fin d → F) : ℂ))) *
          ((Real.sqrt (((sphere (F := F) (d := d) 1).card : ℝ)) : ℂ)) := by ring

theorem adjBar_mulVec_one (d : ℕ) :
    adjBar d *ᵥ (fun _ : Fin d → F => (1 : ℂ)) = 0 := by
  classical
  funext x
  have hN : (Fintype.card (Fin d → F) : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card (Fin d → F) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
    exact_mod_cast hpos.ne'
  rw [adjBar, Matrix.sub_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  rw [mulVec_adj, onesMat_mulVec]
  rw [show (∑ s ∈ sphere (F := F) (d := d) 1, (1 : ℂ)) =
      ((sphere (F := F) (d := d) 1).card : ℂ) by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]]
  rw [show (∑ _y : Fin d → F, (1 : ℂ)) = (Fintype.card (Fin d → F) : ℂ) by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]]
  field_simp
  ring

theorem mulVec_adj_addChar {d : ℕ} (Ψ : AddChar (Fin d → F) ℂ) :
    adj d *ᵥ (fun x => Ψ x) = (∑ s ∈ sphere 1, Ψ s) • (fun x => Ψ x) := by
  classical
  funext x
  rw [mulVec_adj]
  have hterm : ∀ s ∈ sphere (d := d) 1, Ψ (x - s) = Ψ x * Ψ (-s) := by
    intro s _
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum]
  rw [sum_sphere_neg]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Qatlib.Papers.HiddenNonlin07.MainResults.WinnieLiAdjacency
