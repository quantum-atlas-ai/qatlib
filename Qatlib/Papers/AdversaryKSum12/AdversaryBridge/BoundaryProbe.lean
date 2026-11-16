/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdversaryKSum12.ArrayWitness.SourceModel

@[expose] public section


set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.AdversaryKSum12.AdversaryBridge
open Qatlib.Papers.AdversaryKSum12.ArrayWitness

/-- The singleton alphabet's full length-one array meets the literal orthogonal-array promise. -/
theorem singleton_array_valid :
    IsOrthogonalArray (Finset.univ : Finset (Fin 1 → Fin 1)) := by
  intro i g
  exact ⟨0, Finset.mem_univ _, fun a _ => Subsingleton.elim _ _⟩

/-- At n=q=k=1 every column is illegal, so the legacy column-deleted matrix is zero. -/
theorem singleton_deleted_zero (A : Matrix (AdvRow 1 1 1) (Fin 1 → Fin 1) ℝ) :
    removeIllegal (fun _ _ => Finset.univ) A = 0 := by
  ext r y
  have hy : IsIllegal (fun (_ : Finset (Fin 1)) (_ : _ ) =>
      (Finset.univ : Finset (Fin 1 → Fin 1))) y := by
    exact ⟨Finset.univ, by simp, Finset.mem_univ _⟩
  change (if IsIllegal (fun _ _ => Finset.univ) y then 0 else A r y) = 0
  exact ite_eq_left hy

/-- A positive uniform lower bound cannot hold at the literal singleton boundary. -/
theorem singleton_lower_refuted (c : ℝ) (hc : 0 < c) :
    ¬ c * (1 : ℝ) * (1 : ℝ) ^ ((1 : ℝ) / 2) ≤
      ‖removeIllegal (fun _ _ => Finset.univ)
        (advGamma 1 1 1 (fun _ _ => Finset.univ) (fun _ => 1))‖ := by
  rw [singleton_deleted_zero]
  simpa using (not_le.mpr hc)

end Qatlib.Papers.AdversaryKSum12.AdversaryBridge
