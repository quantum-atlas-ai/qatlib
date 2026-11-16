/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.SchmidtFacts
public import Qatlib.Foundations.PPTMatrix.OperatorCones.Maps

@[expose] public section




/-!
# The Schmidt-number iteration

Given the reduction property of a pair of PPT maps (Lemma 5: one pair lowers the Schmidt-number
bound `s` to `max (s - 1) 1`), `j` pairs lower it to `max (s - j) 1` (Eq. (25)), and
`2 (d - 1)` PPT maps on `M_d` compose to an entanglement-breaking map (Theorem 1).

The reduction property enters as the hypothesis `hcore`; it is discharged in `Main.lean`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n : Type*}

/-- Ordered compositions of completely positive maps are completely positive. -/
theorem isCompletelyPositive_compList :
    ∀ (L : List (Module.End ℂ (Matrix n n ℂ))), (∀ φ ∈ L, IsCompletelyPositive φ) →
      IsCompletelyPositive (compList L)
  | [], _ => by
      rw [compList_nil]
      exact isCompletelyPositive_id
  | φ :: L, h => by
      rw [compList_cons]
      exact (isCompletelyPositive_compList L fun ψ hψ => h ψ (by simp [hψ])).comp
        (h φ (by simp))

/-- Two leading maps in the ordered list act as one consecutive pair before the remaining maps. -/
theorem refMap_compList_cons_cons (φ₁ φ₂ : Module.End ℂ (Matrix n n ℂ))
    (L : List (Module.End ℂ (Matrix n n ℂ))) (X : Matrix (κ × n) (κ × n) ℂ) :
    refMap κ (compList (φ₁ :: φ₂ :: L)) X =
      refMap κ (compList L) (refMap κ (φ₂ ∘ₗ φ₁) X) := by
  rw [compList_cons, compList_cons, LinearMap.comp_assoc, refMap_comp]
  rfl

/-- The ordered composition of `m` copies of `T` is `T ^ m`. -/
theorem compList_replicate (T : Module.End ℂ (Matrix n n ℂ)) :
    ∀ m : ℕ, compList (List.replicate m T) = T ^ m
  | 0 => by
      rw [List.replicate_zero, compList_nil, pow_zero]
      rfl
  | m + 1 => by
      rw [List.replicate_succ, compList_cons, compList_replicate T m, pow_succ]
      rfl

/-- The truncated Schmidt-number bound decreases by one additional pair under iteration. -/
private theorem max_step (s j : ℕ) : max (max (s - 1) 1 - j) 1 ≤ max (s - (j + 1)) 1 := by
  rcases le_total (s - 1) 1 with h | h
  · rw [max_eq_right h, max_eq_right (Nat.sub_le 1 j)]
    exact le_max_right _ _
  · rw [max_eq_left h]
    have e : s - 1 - j = s - (j + 1) := by omega
    rw [e]

section iteration

variable [Fintype n]

/-- Eq. (25): `j` pairs of PPT maps lower a Schmidt-number bound `s` to `max (s - j) 1`. -/
theorem hasSchmidtNumberLE_refMap_compList_of_core
    (hcore : ∀ (φ₁ φ₂ : Module.End ℂ (Matrix n n ℂ)), IsPPTMap φ₁ → IsPPTMap φ₂ →
      ∀ (s : ℕ) (X : Matrix (κ × n) (κ × n) ℂ), HasSchmidtNumberLE s X →
        HasSchmidtNumberLE (max (s - 1) 1) (refMap κ (φ₂ ∘ₗ φ₁) X)) :
    ∀ (j : ℕ) (L : List (Module.End ℂ (Matrix n n ℂ))), L.length = 2 * j →
      (∀ φ ∈ L, IsPPTMap φ) → ∀ (s : ℕ) (X : Matrix (κ × n) (κ × n) ℂ),
        HasSchmidtNumberLE s X → HasSchmidtNumberLE (max (s - j) 1) (refMap κ (compList L) X)
  | 0, [], _, _, s, X, hX => by
      rw [compList_nil, refMap_id, LinearMap.id_apply]
      exact hX.mono (le_max_of_le_left (Nat.sub_zero s).ge)
  | 0, _ :: _, hL, _, _, _, _ => by
      simp only [List.length_cons] at hL
      omega
  | j + 1, [], hL, _, _, _, _ => by
      simp only [List.length_nil] at hL
      omega
  | j + 1, [_], hL, _, _, _, _ => by
      simp only [List.length_cons, List.length_nil] at hL
      omega
  | j + 1, φ₁ :: φ₂ :: L, hL, hP, s, X, hX => by
      have hL' : L.length = 2 * j := by
        simp only [List.length_cons] at hL
        omega
      have h₁ : IsPPTMap φ₁ := hP φ₁ (by simp)
      have h₂ : IsPPTMap φ₂ := hP φ₂ (by simp)
      have hP' : ∀ φ ∈ L, IsPPTMap φ := fun φ hφ => hP φ (by simp [hφ])
      have hstep := hcore φ₁ φ₂ h₁ h₂ s X hX
      have hrec := hasSchmidtNumberLE_refMap_compList_of_core hcore j L hL' hP' _ _ hstep
      rw [refMap_compList_cons_cons]
      exact hrec.mono (max_step s j)

/-- Theorem 1 in list form: if `|n| ≤ j + 1`, any ordered composition of `2 j` PPT maps on `M_n`
is entanglement breaking. -/
theorem isEntanglementBreaking_compList_of_core
    (hcore : ∀ (k : ℕ) (φ₁ φ₂ : Module.End ℂ (Matrix n n ℂ)), IsPPTMap φ₁ → IsPPTMap φ₂ →
      ∀ (s : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ), HasSchmidtNumberLE s X →
        HasSchmidtNumberLE (max (s - 1) 1) (refMap (Fin k) (φ₂ ∘ₗ φ₁) X))
    (j : ℕ) (L : List (Module.End ℂ (Matrix n n ℂ))) (hL : L.length = 2 * j)
    (hP : ∀ φ ∈ L, IsPPTMap φ) (hj : Fintype.card n ≤ j + 1) :
    IsEntanglementBreaking (compList L) := by
  refine ⟨isCompletelyPositive_compList L fun φ hφ => (hP φ hφ).1, fun k X hX => ?_⟩
  have h0 : HasSchmidtNumberLE (Fintype.card n) X :=
    (hasSchmidtNumberLE_min_card hX).mono (min_le_right _ _)
  have h1 := hasSchmidtNumberLE_refMap_compList_of_core (hcore k) j L hL hP _ X h0
  exact IsSeparable.of_hasSchmidtNumberLE_one (h1.mono (max_le (by omega) le_rfl))

/-- If `|n| ≤ j + 1`, the power `T ^ (2 j)` of a PPT map on `M_n` is entanglement breaking. -/
theorem isEntanglementBreaking_pow_of_core
    (hcore : ∀ (k : ℕ) (φ₁ φ₂ : Module.End ℂ (Matrix n n ℂ)), IsPPTMap φ₁ → IsPPTMap φ₂ →
      ∀ (s : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ), HasSchmidtNumberLE s X →
        HasSchmidtNumberLE (max (s - 1) 1) (refMap (Fin k) (φ₂ ∘ₗ φ₁) X))
    {T : Module.End ℂ (Matrix n n ℂ)} (hT : IsPPTMap T) (j : ℕ)
    (hj : Fintype.card n ≤ j + 1) : IsEntanglementBreaking (T ^ (2 * j)) := by
  rw [← compList_replicate]
  refine isEntanglementBreaking_compList_of_core hcore j _ (by simp) (fun φ hφ => ?_) hj
  rw [List.eq_of_mem_replicate hφ]
  exact hT

/-- The entanglement-breaking index of a PPT map on `M_n` is at most `2 j` when
`|n| ≤ j + 1` and `1 ≤ j`. -/
theorem ebIndex_le_of_core
    (hcore : ∀ (k : ℕ) (φ₁ φ₂ : Module.End ℂ (Matrix n n ℂ)), IsPPTMap φ₁ → IsPPTMap φ₂ →
      ∀ (s : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ), HasSchmidtNumberLE s X →
        HasSchmidtNumberLE (max (s - 1) 1) (refMap (Fin k) (φ₂ ∘ₗ φ₁) X))
    {T : Module.End ℂ (Matrix n n ℂ)} (hT : IsPPTMap T) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : Fintype.card n ≤ j + 1) : ebIndex T ≤ ((2 * j : ℕ) : ℕ∞) := by
  unfold ebIndex
  exact iInf_le_of_le (2 * j) (iInf_le_of_le (by omega)
    (iInf_le_of_le (isEntanglementBreaking_pow_of_core hcore hT j hj) le_rfl))

end iteration

end Qatlib.Papers.PPTCompose26.Composition
