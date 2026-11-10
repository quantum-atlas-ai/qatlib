/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.SignGeneric
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults

def flipAt {ν : ℕ} (i : Fin ν) (x : Fin ν → Bool) : Fin ν → Bool :=
  Function.update x i (Bool.not (x i))

theorem flipAt_flipAt {ν : ℕ} (i : Fin ν) (x : Fin ν → Bool) :
    flipAt i (flipAt i x) = x := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [flipAt]
  · simp [flipAt, hk]

def cubeEdge {ν : ℕ} (x y : Fin ν → Bool) : Prop :=
  ∃ i : Fin ν, y = flipAt i x

def bits {ν : ℕ} (S : Finset (Fin ν)) : Fin ν → Bool :=
  fun i => decide (i ∈ S)

theorem bits_insert {ν : ℕ} {S : Finset (Fin ν)} {i : Fin ν} (hi : i ∉ S) :
    bits (insert i S) = flipAt i (bits S) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [bits, flipAt, hi]
  · simp [bits, flipAt, hk]

theorem bits_reachable {ν : ℕ} (S : Finset (Fin ν)) :
    Relation.ReflTransGen cubeEdge (fun _ => false) (bits S) := by
  induction S using Finset.induction with
  | empty =>
      have h : bits (∅ : Finset (Fin ν)) = fun _ => false := by
        funext k
        simp [bits]
      rw [h]
  | insert i S hi ih =>
      rw [bits_insert hi]
      exact Relation.ReflTransGen.tail ih ⟨i, rfl⟩

theorem eq_bits_filter {ν : ℕ} (x : Fin ν → Bool) :
    x = bits (Finset.univ.filter (fun i => x i = true)) := by
  funext k
  by_cases hk : x k = true
  · simp [bits, hk]
  · simp [bits, hk]

theorem cube_connected {ν : ℕ} (x : Fin ν → Bool) :
    Relation.ReflTransGen cubeEdge (fun _ => false) x := by
  rw [eq_bits_filter x]
  exact bits_reachable _

theorem hypercube_sign_recovery {ν : ℕ} (s t : (Fin ν → Bool) → ℝ)
    (hs0 : ∀ v, s v ≠ 0)
    (hroot : s (fun _ => false) = t (fun _ => false))
    (hedge : ∀ v w : Fin ν → Bool, cubeEdge v w → s v * s w = t v * t w) :
    s = t :=
  sign_function_eq_of_connected cubeEdge (fun _ => false) s t hs0 hroot hedge
    cube_connected

theorem hypercube_sign_recovery_pos {ν : ℕ} (s t : (Fin ν → Bool) → ℝ)
    (hs0 : ∀ v, s v ≠ 0)
    (hroot : 0 < s (fun _ => false)) (hroot' : 0 < t (fun _ => false))
    (habs : ∀ v, s v ^ 2 = t v ^ 2)
    (hedge : ∀ v w : Fin ν → Bool, cubeEdge v w → s v * s w = t v * t w) :
    s = t :=
  sign_function_eq_of_connected_pos cubeEdge (fun _ => false) s t hs0 hroot hroot' habs
    hedge cube_connected

end Qatlib.Papers.ThermalRate98.MainResults
