/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GroupExtTest13.MainResults.AlgebraParts

@[expose] public section


/-! Counterexamples to missing hypotheses in the old interfaces.
These concern the legacy Lean statements, not the source paper. -/

set_option autoImplicit false

namespace Qatlib.Papers.GroupExtTest13.MainResults

open scoped BigOperators
open Qatlib.Papers.GroupExtTest13.MainResults

/-- A normalized cochain that couples two independent binary coordinates. -/
def mixedSection (x : CyclicProduct (fun _ : Fin 2 => 2)) : ℤ :=
  if x 0 = 1 ∧ x 1 = 1 then 1 else 0

/-- A trivial kernel map accepts this nonfactorised coboundary as a factor set. -/
theorem lemma37_false :
    let d := fun _ : Fin 2 => 2
    let ι := (1 : Multiplicative ℤ →* Unit)
    IsFFormSection d (fun _ => ()) ∧
      IsFactorSetD d ι (fun _ => ()) (coboundary mixedSection) ∧
      IsFactorSetD d ι (fun _ => ()) (fun _ _ => 0) ∧
      EquivalentExtensions ι ι ∧
      coboundary mixedSection ∈ B2 ∧ coboundary mixedSection ∉ BF2 d := by
  dsimp only
  refine ⟨⟨fun _ => (), fun _ => Subsingleton.elim _ _⟩,
    (fun _ _ => rfl), (fun _ _ => rfl), ⟨MulEquiv.refl _, fun _ => rfl⟩,
    ⟨mixedSection, by simp [mixedSection], rfl⟩, ?_⟩
  rintro ⟨a, ha⟩
  let x : CyclicProduct (fun _ : Fin 2 => 2) := fun i => if i = 0 then 1 else 0
  let y : CyclicProduct (fun _ : Fin 2 => 2) := fun i => if i = 1 then 1 else 0
  have h := congrFun (congrFun ha x) y
  rw [FForm_coboundary] at h
  norm_num [coboundary, mixedSection, x, y, Fin.sum_univ_two, ZMod.val_one] at h

/-- Modulus-one coordinates make every normal-form parameter invisible. -/
theorem modulus_one (α : Fin 2 → ℤ) (β : Fin 2 → Fin 2 → ℤ) :
    paramForm (fun _ : Fin 2 => 1) α β = 0 := by
  funext x y
  have hx : x = 0 := Subsingleton.elim _ _
  have hy : y = 0 := Subsingleton.elim _ _
  simp [hx, hy, paramForm]

/-- The legacy Lemma 3.10 allows trivial cyclic factors and cannot recover beta. -/
theorem lemma310_false :
    let d := fun _ : Fin 2 => 1
    let α := fun _ : Fin 2 => (0 : ℤ)
    let β := fun _ _ : Fin 2 => (0 : ℤ)
    let β' := fun _ _ : Fin 2 => (1 : ℤ)
    paramForm d α β ∈ Z2 ∧ paramForm d α β' ∈ Z2 ∧
      (paramForm d α β - paramForm d α β') ∈ BF2 d ∧
      ¬ (∀ i j, i < j → β i j = β' i j) := by
  dsimp only
  rw [modulus_one, modulus_one]
  have hz : (0 : CyclicProduct (fun _ : Fin 2 => 1) →
      CyclicProduct (fun _ : Fin 2 => 1) → ℤ) ∈ Z2 := by
    constructor
    · constructor <;> intro x <;> rfl
    · intro x y z
      rfl
  refine ⟨hz, hz, ?_, ?_⟩
  · refine ⟨fun _ => 0, ?_⟩
    funext x y
    simp [coboundary, FForm]
  · intro h
    have := h 0 1 (by decide)
    norm_num at this

/-- A noninjective kernel map accepts a factor set with arbitrary nonzero value. -/
theorem factor_set_bad :
    IsFactorSetD (fun _ : Fin 1 => 1)
      (1 : Multiplicative ℤ →* Unit) (fun _ => ()) (fun _ _ => 1) := by
  intro x y
  rfl

/-- The constant section in the bad factor-set example has the required product form. -/
theorem product_section :
    ∀ x : CyclicProduct (fun _ : Fin 1 => 1),
      () = fprod (fun i : Fin 1 => (() : Unit) ^ (x i).val) := by
  intro x
  exact Subsingleton.elim _ _

/-- That accepted factor set has no carry/commutator normal form, refuting old 3.9. -/
theorem lemma39_false :
    ¬ ∃ (α : Fin 1 → ℤ) (β : Fin 1 → Fin 1 → ℤ),
      ∀ x y : CyclicProduct (fun _ : Fin 1 => 1),
        (1 : ℤ) =
          (∑ i, (if 1 ≤ (x i).val + (y i).val then (1 : ℤ) else 0) • α i) +
            ∑ i, ∑ j, (if i < j then (((y i).val : ℤ) * (x j).val) • β i j else 0) := by
  rintro ⟨α, β, h⟩
  have h0 := h 0 0
  norm_num at h0

end Qatlib.Papers.GroupExtTest13.MainResults
