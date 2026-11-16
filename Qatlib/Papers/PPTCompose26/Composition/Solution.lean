/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PPTCompose26.Composition.Root

@[expose] public section


/-!
# Dimension-indexed PPT composition endpoints

These results specialize the finite-index theorems in `Main` and `AtLeast` to
matrix algebras `M_d(ℂ)`. They prove the `2(d-1)` composition and index bounds,
the extension to longer lists, and insertion of completely positive maps.
The Choi equivalences and identity/zero/transpose checks keep the unnormalized
matrix model and map-composition direction explicit.
-/


open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

/-- Establishes `compose_ppt_maps_entanglementBreaking`: `IsEntanglementBreaking (compList (List.ofFn Φ))`, for the stated parameters. -/
theorem compose_ppt_maps_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i)) :
    IsEntanglementBreaking (compList (List.ofFn Φ)) := by
  refine isEntanglementBreaking_compList (d - 1) (List.ofFn Φ) (by simp) (fun φ hφ => ?_)
    (by rw [Fintype.card_fin]; omega)
  rw [List.mem_ofFn] at hφ
  obtain ⟨i, rfl⟩ := hφ
  exact hΦ i

/-- Establishes `ebIndex_le_of_isPPTMap`: `ebIndex T ≤ ((2 * (d - 1) : ℕ) : ℕ∞)`, for the stated parameters. -/
theorem ebIndex_le_of_isPPTMap (d : ℕ) (hd : 2 ≤ d) (T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hT : IsPPTMap T) : ebIndex T ≤ ((2 * (d - 1) : ℕ) : ℕ∞) :=
  ebIndex_le hT (d - 1) (by omega) (by rw [Fintype.card_fin]; omega)

/-- Establishes `compose_at_least_ppt_maps_entanglementBreaking`: `IsEntanglementBreaking (compList (List.ofFn Φ))`, for the stated parameters. -/
theorem compose_at_least_ppt_maps_entanglementBreaking (d : ℕ) (hd : 2 ≤ d) (N : ℕ)
    (hN : 2 * (d - 1) ≤ N) (Φ : Fin N → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hΦ : ∀ i, IsPPTMap (Φ i)) :
    IsEntanglementBreaking (compList (List.ofFn Φ)) := by
  refine isEntanglementBreaking_compList_of_le (d - 1) (List.ofFn Φ) (by simpa using hN)
    (fun φ hφ => ?_) (by rw [Fintype.card_fin]; omega)
  rw [List.mem_ofFn] at hφ
  obtain ⟨i, rfl⟩ := hφ
  exact hΦ i

/-- Establishes `compose_ppt_map_interleaved_entanglementBreaking`: `IsEntanglementBreaking (compList (T :: List.ofFn fun i => T ∘ₗ S i))`, for the stated parameters. -/
theorem compose_ppt_map_interleaved_entanglementBreaking (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) (hT : IsPPTMap T)
    (S : Fin (2 * (d - 1) - 1) → Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hS : ∀ i, IsCompletelyPositive (S i)) :
    IsEntanglementBreaking (compList (T :: List.ofFn fun i => T ∘ₗ S i)) := by
  refine isEntanglementBreaking_compList (d - 1) _ ?_ (fun φ hφ => ?_) (by rw [Fintype.card_fin]; omega)
  · simp only [List.length_cons, List.length_ofFn]
    omega
  · rcases List.mem_cons.mp hφ with rfl | hφ
    · exact hT
    · rw [List.mem_ofFn] at hφ
      obtain ⟨i, rfl⟩ := hφ
      exact IsPPTMap.comp_isCompletelyPositive hT (hS i)

/-- Establishes `exists_posSemidef_not_isSeparable`: `∃ X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ, X.PosSemidef ∧ ¬ Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable X`, for the stated parameters. -/
theorem exists_posSemidef_not_isSeparable (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ,
      X.PosSemidef ∧ ¬ Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable X :=
  ⟨pureState (bellVec d), Matrix.posSemidef_vecMulVec_self_star _, not_isSeparable_bell d hd⟩

/-- Establishes `id_not_entanglementBreaking`: `¬ IsEntanglementBreaking (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))`, for the stated parameters. -/
theorem id_not_entanglementBreaking (d : ℕ) (hd : 2 ≤ d) :
    ¬ IsEntanglementBreaking (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) :=
  not_isEntanglementBreaking_id d hd

/-- Establishes `choi_isCompletelyPositive_iff`: `IsCompletelyPositive Φ ↔ (refMap (Fin d) Φ (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))).PosSemidef`, for the stated parameters. -/
theorem choi_isCompletelyPositive_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsCompletelyPositive Φ ↔
      (refMap (Fin d) Φ
        (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))).PosSemidef :=
  isCompletelyPositive_iff_choi Φ

/-- Establishes `choi_isPPTMap_iff`: `IsPPTMap Φ ↔ (refMap (Fin d) Φ (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))).PosSemidef ∧ (partialTransposeRef (refMap (Fin d) Φ (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0)))).PosSemidef`, for the stated parameters. -/
theorem choi_isPPTMap_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsPPTMap Φ ↔
      (refMap (Fin d) Φ
          (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))).PosSemidef ∧
        (partialTransposeRef (refMap (Fin d) Φ
          (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0)))).PosSemidef :=
  isPPTMap_iff_choi Φ

/-- Establishes `choi_isEntanglementBreaking_iff`: `IsEntanglementBreaking Φ ↔ Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable (refMap (Fin d) Φ (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0)))`, for the stated parameters. -/
theorem choi_isEntanglementBreaking_iff {d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsEntanglementBreaking Φ ↔
      Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable (refMap (Fin d) Φ
        (pureState (fun x : Fin d × Fin d => if x.1 = x.2 then (1 : ℂ) else 0))) :=
  isEntanglementBreaking_iff_choi Φ

/-- Establishes `transposeMap_isCompletelyCopositive_not_isCompletelyPositive`: `IsCompletelyCopositive (transposeMap (Fin 2)) ∧ ¬ IsCompletelyPositive (transposeMap (Fin 2))`, for the stated parameters. -/
theorem transposeMap_isCompletelyCopositive_not_isCompletelyPositive :
    IsCompletelyCopositive (transposeMap (Fin 2)) ∧
      ¬ IsCompletelyPositive (transposeMap (Fin 2)) :=
  isCompletelyCopositive_and_not_isCompletelyPositive_transposeMap

/-- Establishes `compList_pair`: `compList [Φ₁, Φ₂] = Φ₂ ∘ₗ Φ₁`, for the stated parameters. -/
theorem compList_pair {d : ℕ} (Φ₁ Φ₂ : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) :
    compList [Φ₁, Φ₂] = Φ₂ ∘ₗ Φ₁ := by
  rw [compList_cons, compList_cons, compList_nil, LinearMap.id_comp]

/-- Establishes `zero_map_isPPTMap_and_ebIndex_eq_one`: `IsPPTMap (0 : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) ∧ ebIndex (0 : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) = 1`, for the stated parameters. -/
theorem zero_map_isPPTMap_and_ebIndex_eq_one (d : ℕ) :
    IsPPTMap (0 : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) ∧
      ebIndex (0 : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) = 1 :=
  ⟨isPPTMap_zero, ebIndex_zero⟩

/-- Establishes `ebIndex_id_eq_top`: `ebIndex (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) = ⊤`, for the stated parameters. -/
theorem ebIndex_id_eq_top (d : ℕ) (hd : 2 ≤ d) :
    ebIndex (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) = ⊤ := by
  have hpow : ∀ k : ℕ,
      (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) ^ k = LinearMap.id := by
    intro k
    induction k with
    | zero => rw [pow_zero]; rfl
    | succ k ih => rw [pow_succ, ih, Module.End.mul_eq_comp, LinearMap.id_comp]
  refine top_le_iff.mp ?_
  unfold ebIndex
  refine le_iInf fun m => le_iInf fun _ => le_iInf fun h => ?_
  rw [hpow m] at h
  exact absurd h (not_isEntanglementBreaking_id d hd)

end Qatlib.Papers.PPTCompose26.Composition
