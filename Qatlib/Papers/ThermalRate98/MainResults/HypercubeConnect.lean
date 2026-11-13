/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.SignGeneric

/-!
# Hypercube connectivity and real amplitude recovery

This module defines single-coordinate bit flips and proves that every Boolean register string is
reachable from the all-false string. The resulting connectivity supports the relative-sign
reconstruction argument associated with [LidarWang1999].

The recovery statements identify real functions from their products along cube edges and a fixed
root value, or from squared magnitudes and a positive root convention, assuming the first
function is everywhere nonzero.

## Main statements

* `cube_connected`: every Boolean string is reachable by successive bit flips.
* `hypercube_sign_recovery`: edge products and an agreed root value determine the function.
* `hypercube_sign_recovery_pos`: squared magnitudes, edge products, and positive root values
  determine the function.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults

/-- The Boolean string obtained from `x` by negating its coordinate at `i`. -/
def flipAt {ν : ℕ} (i : Fin ν) (x : Fin ν → Bool) : Fin ν → Bool :=
  Function.update x i (Bool.not (x i))

/-- Flipping the same coordinate twice restores the original Boolean string. -/
theorem flipAt_flipAt {ν : ℕ} (i : Fin ν) (x : Fin ν → Bool) :
    flipAt i (flipAt i x) = x := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [flipAt]
  · simp [flipAt, hk]

/-- Two Boolean strings form a cube edge when the second is obtained from the first by flipping
one coordinate. -/
def cubeEdge {ν : ℕ} (x y : Fin ν → Bool) : Prop :=
  ∃ i : Fin ν, y = flipAt i x

/-- The Boolean indicator string of the finite coordinate set `S`. -/
def bits {ν : ℕ} (S : Finset (Fin ν)) : Fin ν → Bool :=
  fun i => decide (i ∈ S)

/-- Inserting a previously absent coordinate into `S` flips that coordinate in its Boolean
indicator string. -/
theorem bits_insert {ν : ℕ} {S : Finset (Fin ν)} {i : Fin ν} (hi : i ∉ S) :
    bits (insert i S) = flipAt i (bits S) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [bits, flipAt, hi]
  · simp [bits, flipAt, hk]

/-- The indicator string of any finite coordinate set is reachable from the all-false string
through finitely many cube edges. -/
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

/-- Every Boolean string is the indicator of the set of coordinates where it is true. -/
theorem eq_bits_filter {ν : ℕ} (x : Fin ν → Bool) :
    x = bits (Finset.univ.filter (fun i => x i = true)) := by
  funext k
  by_cases hk : x k = true
  · simp [bits, hk]
  · simp [bits, hk]

/-- Every Boolean register string is reachable from the all-false string by successive
coordinate flips. This supplies the connectivity used in the sign recovery argument
associated with [LidarWang1999]. -/
theorem cube_connected {ν : ℕ} (x : Fin ν → Bool) :
    Relation.ReflTransGen cubeEdge (fun _ => false) x := by
  rw [eq_bits_filter x]
  exact bits_reachable _

/-- Two real functions on the Boolean cube are equal if the first is everywhere nonzero, their
values agree at the all-false root, and their products agree across every cube edge. This
formalizes the propagation of relative-sign information discussed in [LidarWang1999]. -/
theorem hypercube_sign_recovery {ν : ℕ} (s t : (Fin ν → Bool) → ℝ)
    (hs0 : ∀ v, s v ≠ 0)
    (hroot : s (fun _ => false) = t (fun _ => false))
    (hedge : ∀ v w : Fin ν → Bool, cubeEdge v w → s v * s w = t v * t w) :
    s = t :=
  sign_function_eq_of_connected cubeEdge (fun _ => false) s t hs0 hroot hedge
    cube_connected

/-- Two real functions on the Boolean cube are equal if the first is everywhere nonzero, both
root values are positive, their squared values agree, and their edge products agree. This is
the positive-root version of the sign recovery argument associated with [LidarWang1999]. -/
theorem hypercube_sign_recovery_pos {ν : ℕ} (s t : (Fin ν → Bool) → ℝ)
    (hs0 : ∀ v, s v ≠ 0)
    (hroot : 0 < s (fun _ => false)) (hroot' : 0 < t (fun _ => false))
    (habs : ∀ v, s v ^ 2 = t v ^ 2)
    (hedge : ∀ v w : Fin ν → Bool, cubeEdge v w → s v * s w = t v * t w) :
    s = t :=
  sign_function_eq_of_connected_pos cubeEdge (fun _ => false) s t hs0 hroot hroot' habs
    hedge cube_connected

end Qatlib.Papers.ThermalRate98.MainResults
