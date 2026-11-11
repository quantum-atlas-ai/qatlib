/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# StateHSP24 — the hidden cut as an Abelian StateHSP instance (Fact 4.3)

Bouland–Giurgica-Tiron–Wright, fixed arXiv:2410.12706v1, Section 4.3, Fact 4.3.

For a cut `C ⊆ [n]` the hidden subgroup of `Z₂^n` is
`H_C = {0^n, 1_C 0_C̄, 0_C 1_C̄, 1^n} ≅ Z₂²`.  We realise it as the image of the
additive homomorphism `(a,b) ↦ a·1_C0_C̄ + b·0_C1_C̄` from `Z₂ × Z₂`, prove that
it is injective for a nontrivial proper cut (hence `|H_C| = 4`), and compute the
standard-HSP Fourier sampling law: the weight of `y` is `4 / 2^n` when `y` is
orthogonal to both cut strings and `0` otherwise, i.e. the uniform law on the
`(n-2)`-dimensional subspace `H_C^⊥`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.StateHSP24.MainResults

open scoped BigOperators

variable {n : ℕ}

/-- `Z₂` has only the two elements `0` and `1`. -/
theorem zmod2_eq_zero_or_one : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

/-- Every element of `Z₂` is an involution. -/
theorem zmod2_add_self : ∀ t : ZMod 2, t + t = 0 := by decide

/-! ## The cut strings and the hidden subgroup -/

/-- The bit string `1_C 0_C̄` (ones exactly on `C`). -/
def cutVector (C : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ C then 1 else 0

/-- The all-ones string `1^n`. -/
def allOneVector (n : ℕ) : Fin n → ZMod 2 := fun _ => 1

/-- The complementary cut string `0_C 1_C̄ = 1^n - 1_C 0_C̄`. -/
def complVector (C : Finset (Fin n)) : Fin n → ZMod 2 := allOneVector n - cutVector C

/-- The additive homomorphism `(a,b) ↦ a·1_C0_C̄ + b·0_C1_C̄` from `Z₂²` into
`Z₂^n`; its image is the hidden cut subgroup. -/
def cutHom (C : Finset (Fin n)) : (ZMod 2 × ZMod 2) →+ (Fin n → ZMod 2) where
  toFun p := p.1 • cutVector C + p.2 • complVector C
  map_zero' := by simp [complVector]
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel

/-- The hidden subgroup `H_C = {0^n, 1_C0_C̄, 0_C1_C̄, 1^n}` as the image of
`cutHom`. -/
def cutSubgroup (C : Finset (Fin n)) : Finset (Fin n → ZMod 2) :=
  Finset.univ.image (cutHom C)

/-- Each cut string is orthogonal to the other in the sense
`1_C0_C̄ + 0_C1_C̄ = 1^n`. -/
theorem cutVector_add_compl (C : Finset (Fin n)) :
    cutVector C + complVector C = allOneVector n := by
  ext i
  by_cases h : i ∈ C <;> simp [cutVector, complVector, allOneVector, h]

/-- The four named elements of `H_C` are exactly the image of `cutHom`. -/
theorem mem_cutSubgroup (C : Finset (Fin n)) (x : Fin n → ZMod 2) :
    x ∈ cutSubgroup C ↔
      x = 0 ∨ x = cutVector C ∨ x = complVector C ∨ x = allOneVector n := by
  constructor
  · intro hx
    rw [cutSubgroup, Finset.mem_image] at hx
    obtain ⟨p, _, rfl⟩ := hx
    rcases zmod2_eq_zero_or_one p.1 with h1 | h1 <;>
      rcases zmod2_eq_zero_or_one p.2 with h2 | h2
    · left
      simp [cutHom, h1, h2]
    · right; right; left
      simp [cutHom, h1, h2]
    · right; left
      simp [cutHom, h1, h2]
    · right; right; right
      have hp : p = (1, 1) := Prod.ext h1 h2
      subst hp
      show cutHom C (1, 1) = allOneVector n
      rw [show cutHom C (1, 1) =
        (1 : ZMod 2) • cutVector C + (1 : ZMod 2) • complVector C from rfl,
        one_smul, one_smul, complVector]
      abel
  · intro hx
    rw [cutSubgroup, Finset.mem_image]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, Finset.mem_univ _, by simp [cutHom]⟩
    · exact ⟨(1, 0), Finset.mem_univ _, by simp [cutHom]⟩
    · exact ⟨(0, 1), Finset.mem_univ _, by simp [cutHom]⟩
    · exact ⟨(1, 1), Finset.mem_univ _, by
        rw [show cutHom C (1, 1) =
          (1 : ZMod 2) • cutVector C + (1 : ZMod 2) • complVector C from rfl,
          one_smul, one_smul, complVector]
        abel⟩

/-- The two cut vectors are linearly independent for a nontrivial proper cut. -/
theorem cutHom_injective (C : Finset (Fin n)) (hC : C.Nonempty) (hC' : Cᶜ.Nonempty) :
    Function.Injective (cutHom C) := by
  obtain ⟨i, hi⟩ := hC
  obtain ⟨j, hj⟩ := hC'
  intro p q hpq
  have hi' : i ∉ Cᶜ := by simpa using hi
  have h1 : p.1 = q.1 := by
    have h := congrFun hpq i
    simpa [cutHom, cutVector, complVector, allOneVector, hi] using h
  have h2 : p.2 = q.2 := by
    have h := congrFun hpq j
    have hj' : j ∉ C := by simpa using hj
    simpa [cutHom, cutVector, complVector, allOneVector, hj'] using h
  exact Prod.ext h1 h2

/-- `H_C ≅ Z₂²`: the hidden cut subgroup has four elements for a nontrivial
proper cut. -/
theorem cutSubgroup_card (C : Finset (Fin n)) (hC : C.Nonempty) (hC' : Cᶜ.Nonempty) :
    (cutSubgroup C).card = 4 := by
  rw [cutSubgroup, Finset.card_image_of_injective _ (cutHom_injective C hC hC')]
  simp

/-- Every element of `H_C` is an involution (characteristic two). -/
theorem cutSubgroup_add_self (C : Finset (Fin n)) (x : Fin n → ZMod 2)
    (hx : x ∈ cutSubgroup C) : x + x = 0 := by
  rw [cutSubgroup, Finset.mem_image] at hx
  obtain ⟨p, _, rfl⟩ := hx
  have hp : p + p = 0 := by
    ext <;> exact zmod2_add_self _
  rw [← map_add, hp, map_zero]

/-- `H_C` is closed under addition (it is a subgroup). -/
theorem cutSubgroup_add_mem (C : Finset (Fin n)) (x y : Fin n → ZMod 2)
    (hx : x ∈ cutSubgroup C) (hy : y ∈ cutSubgroup C) :
    x + y ∈ cutSubgroup C := by
  rw [cutSubgroup, Finset.mem_image] at hx hy ⊢
  obtain ⟨p, _, rfl⟩ := hx
  obtain ⟨q, _, rfl⟩ := hy
  exact ⟨p + q, Finset.mem_univ _, map_add (cutHom C) p q⟩

/-! ## The standard-HSP Fourier distribution -/

/-- The `Z₂` dot product `x · y = ∑ᵢ xᵢ yᵢ`. -/
def dotProd (x y : Fin n → ZMod 2) : ZMod 2 := ∑ i, x i * y i

/-- The sign character `(-1)^{x·y}`, valued in `ℚ`. -/
def signChar (x y : Fin n → ZMod 2) : ℚ := if dotProd x y = 0 then 1 else -1

/-- The dot product is additive in its first argument. -/
theorem dotProd_add (x z y : Fin n → ZMod 2) :
    dotProd (x + z) y = dotProd x y + dotProd z y := by
  simp only [dotProd, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The sign character is multiplicative. -/
theorem signChar_add (x z y : Fin n → ZMod 2) :
    signChar (x + z) y = signChar x y * signChar z y := by
  unfold signChar
  rw [dotProd_add]
  rcases zmod2_eq_zero_or_one (dotProd x y) with hx | hx <;>
    rcases zmod2_eq_zero_or_one (dotProd z y) with hz | hz <;>
    simp [hx, hz] <;> decide

/-- `cutHom` sends `(0,0)` to the zero string. -/
@[simp] theorem cutHom_zero_zero (C : Finset (Fin n)) :
    cutHom C (0, 0) = 0 := by simp [cutHom]

/-- `cutHom` sends `(0,1)` to `0_C1_C̄`. -/
@[simp] theorem cutHom_zero_one (C : Finset (Fin n)) :
    cutHom C (0, 1) = complVector C := by simp [cutHom]

/-- `cutHom` sends `(1,0)` to `1_C0_C̄`. -/
@[simp] theorem cutHom_one_zero (C : Finset (Fin n)) :
    cutHom C (1, 0) = cutVector C := by simp [cutHom]

/-- `cutHom` sends `(1,1)` to the sum of the two cut strings. -/
@[simp] theorem cutHom_one_one (C : Finset (Fin n)) :
    cutHom C (1, 1) = cutVector C + complVector C := by simp [cutHom]

/-- The character sum over `H_C` factorises over the two `Z₂` factors. -/
theorem signChar_sum_cutSubgroup (C : Finset (Fin n)) (hC : C.Nonempty) (hC' : Cᶜ.Nonempty)
    (y : Fin n → ZMod 2) :
    ∑ x ∈ cutSubgroup C, signChar x y =
      (1 + signChar (cutVector C) y) * (1 + signChar (complVector C) y) := by
  rw [cutSubgroup, Finset.sum_image (fun a _ b _ h => cutHom_injective C hC hC' h),
    Fintype.sum_prod_type]
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rw [huniv, Finset.sum_pair h01, Finset.sum_pair h01, Finset.sum_pair h01]
  have hzero : signChar (0 : Fin n → ZMod 2) y = 1 := by simp [signChar, dotProd]
  have hsum : signChar (cutVector C + complVector C) y =
      signChar (cutVector C) y * signChar (complVector C) y :=
    signChar_add _ _ _
  simp only [cutHom_zero_zero, cutHom_zero_one, cutHom_one_zero, cutHom_one_one,
    hzero, hsum]
  ring

/-- The character sum vanishes off the orthogonal complement and equals `4` on
it. -/
theorem signChar_sum_cutSubgroup_eq (C : Finset (Fin n)) (hC : C.Nonempty)
    (hC' : Cᶜ.Nonempty) (y : Fin n → ZMod 2) :
    ∑ x ∈ cutSubgroup C, signChar x y =
      if dotProd (cutVector C) y = 0 ∧ dotProd (complVector C) y = 0 then 4 else 0 := by
  rw [signChar_sum_cutSubgroup C hC hC' y]
  by_cases h1 : dotProd (cutVector C) y = 0 <;>
    by_cases h2 : dotProd (complVector C) y = 0
  · simp [signChar, h1, h2]
    norm_num
  · have h2' : signChar (complVector C) y = -1 := by simp [signChar, h2]
    have h1' : signChar (cutVector C) y = 1 := by simp [signChar, h1]
    simp [h1, h2, h1', h2']
  · have h1' : signChar (cutVector C) y = -1 := by simp [signChar, h1]
    have h2' : signChar (complVector C) y = 1 := by simp [signChar, h2]
    simp [h1, h2, h1', h2']
  · have h1' : signChar (cutVector C) y = -1 := by simp [signChar, h1]
    have h2' : signChar (complVector C) y = -1 := by simp [signChar, h2]
    simp [h1, h2, h1', h2']

/-- The standard-HSP Fourier weight of the hidden cut subgroup. -/
def fourierWeight (C : Finset (Fin n)) (y : Fin n → ZMod 2) : ℚ :=
  (1 / (2 : ℚ) ^ n) * ∑ x ∈ cutSubgroup C, signChar x y

/-- **Fact 4.3** (hidden cut as Abelian StateHSP): the standard-HSP Fourier
sampling law of the hidden cut subgroup is uniform on the cut subspace
`H_C^⊥ = {y : y·1_C0_C̄ = y·0_C1_C̄ = 0}` with mass `4 / 2^n = 2^{-n+2}`, and zero
elsewhere. -/
theorem fact4_3_fourier_distribution (C : Finset (Fin n)) (hC : C.Nonempty)
    (hC' : Cᶜ.Nonempty) (y : Fin n → ZMod 2) :
    fourierWeight C y =
      if dotProd (cutVector C) y = 0 ∧ dotProd (complVector C) y = 0
      then (4 : ℚ) / (2 : ℚ) ^ n else 0 := by
  rw [fourierWeight, signChar_sum_cutSubgroup_eq C hC hC' y]
  by_cases h : dotProd (cutVector C) y = 0 ∧ dotProd (complVector C) y = 0
  · simp only [if_pos h]
    ring_nf
  · simp only [if_neg h]
    simp

end Qatlib.Papers.StateHSP24.MainResults
