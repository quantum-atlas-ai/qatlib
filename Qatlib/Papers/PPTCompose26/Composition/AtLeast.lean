/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PPTCompose26.Composition.Main
public import Qatlib.Foundations.PPTMatrix.OperatorCones.PairLemma

@[expose] public section




/-!
# More maps: compositions of at least `2(d-1)` PPT maps

Following an entanglement-breaking map by a completely positive map keeps it entanglement
breaking, so Theorem 1 extends to compositions of **at least** `2(d-1)` PPT maps.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n p : Type*}

/-- `(Φ_1, …, Φ_k) ++ (Ψ_1, …, Ψ_l)` composes to `(Ψ_l ∘ ⋯ ∘ Ψ_1) ∘ (Φ_k ∘ ⋯ ∘ Φ_1)`. -/
theorem compList_append (L₁ L₂ : List (Module.End ℂ (Matrix n n ℂ))) :
    compList (L₁ ++ L₂) = compList L₂ ∘ₗ compList L₁ := by
  induction L₁ with
  | nil => rw [List.nil_append, compList_nil, LinearMap.comp_id]
  | cons φ L₁ ih => rw [List.cons_append, compList_cons, compList_cons, ih, LinearMap.comp_assoc]

/-- An entanglement-breaking map followed by a completely positive map is entanglement
breaking. -/
theorem IsEntanglementBreaking.comp_of_isCompletelyPositive [Finite n]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsEntanglementBreaking Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsEntanglementBreaking (Ψ ∘ₗ Φ) := by
  refine ⟨hΨ.comp hΦ.1, fun k X hX => ?_⟩
  obtain ⟨N, A, B, hA, hB, hY⟩ := hΦ.2 k X hX
  rw [refMap_comp, LinearMap.comp_apply, hY, map_sum]
  refine IsSeparable.sum _ fun i _ => ?_
  rw [refMap_kronecker]
  exact IsSeparable.kronecker (hA i) (hΨ.posSemidef_apply (hB i))

/-- A PPT map after a completely positive map is PPT. -/
theorem IsPPTMap.comp_isCompletelyPositive {q : Type*} {Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ}
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΨ : IsPPTMap Ψ) (hΦ : IsCompletelyPositive Φ) :
    IsPPTMap (Ψ ∘ₗ Φ) :=
  ⟨hΨ.1.comp hΦ, hΨ.2.comp_isCompletelyPositive hΦ⟩

/-- If `|n| ≤ j + 1`, every ordered composition of at least `2 j` PPT maps on `M_n` is
entanglement breaking. -/
theorem isEntanglementBreaking_compList_of_le [Fintype n] [DecidableEq n] (j : ℕ)
    (L : List (Module.End ℂ (Matrix n n ℂ))) (hL : 2 * j ≤ L.length)
    (hP : ∀ φ ∈ L, IsPPTMap φ) (hj : Fintype.card n ≤ j + 1) :
    IsEntanglementBreaking (compList L) := by
  rw [← List.take_append_drop (2 * j) L, compList_append]
  refine IsEntanglementBreaking.comp_of_isCompletelyPositive ?_ ?_
  · refine isEntanglementBreaking_compList j _ ?_ (fun φ hφ => hP φ (List.mem_of_mem_take hφ)) hj
    rw [List.length_take]
    omega
  · exact isCompletelyPositive_compList _ fun φ hφ => (hP φ (List.mem_of_mem_drop hφ)).1

end Qatlib.Papers.PPTCompose26.Composition
