/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.LocalConjugation
import Qatlib.Papers.LowEnergyProd24.LocalModel.Expansion
import Qatlib.Papers.LowEnergyProd24.RetainedError.PsdNested

/-!
# Weighted bounds for local and grouped commutators

Imaginary-time weighting commutes with finite sums, allowing local commutator estimates to pass
to grouped commutators. At weight `1 / (2 * J * k * d)`, `actual_weighted_nested` combines the
connected-word count with the seed-group size to obtain an explicit factorial majorant. See
[HejaziZiniArrazola2024].

## Main statements

* `actual_weighted_local_nested`: For positive `J`, `k`, and `d`, the weighted norm of a local
  nested commutator of order `w.length` is at most `(2 * J)^(w.length + 1)`.
* `actual_weighted_group_nested`: For positive `J`, `k`, and `d`, the weighted norm of grouped
  commutators around one local seed is at most `(k * d)^xs.length * xs.length! * (2 *
  J)^(xs.length + 1)`.
* `actual_weighted_nested`: For positive `J`, `k`, and `d` and at most `L` seed labels, the
  weighted grouped nested commutator norm is at most `L * (k * d)^xs.length * xs.length! * (2 *
  J)^(xs.length + 1)`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- Weighting the sum of a finite matrix list equals the sum of the weighted matrices. -/
theorem weighted_list_sum {α : Type*} (h : Hamiltonian N R M k d J) (lam : ℝ)
    (l : List α) (A : α → Matrix (Register N) (Register N) ℂ) :
    weighted h.total (l.map A).sum lam = (l.map (fun a => weighted h.total (A a) lam)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, weighted, mul_zero, zero_mul]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, weighted, mul_add, add_mul] at *
    rw [ih]

/-- For positive `J`, `k`, and `d`, the weighted norm of a local nested commutator of order
`w.length` is at most `(2 * J)^(w.length + 1)`. -/
theorem actual_weighted_local_nested (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (seed : Fin R) (w : List (Fin R)) :
    ‖weighted h.total (h.nested seed w) (1/(2*J*k*d))‖ ≤ (2*J)^(w.length+1) := by
  calc
    _ ≤ 2^(w.length+1)*‖h.nested seed w‖ :=
      actual_local_conjugation_half h hJ hk hd (h.region seed w) w.length
        (h.region_card seed w) (h.nested seed w) (h.nested_supported seed w)
    _ ≤ 2^(w.length+1)*J^(w.length+1) := by
      gcongr
      exact h.nested_norm hJ.le seed w
    _ = _ := (mul_pow _ _ _).symm

/-- For positive `J`, `k`, and `d`, the weighted norm of grouped commutators around one local
seed is at most `(k * d)^xs.length * xs.length! * (2 * J)^(xs.length + 1)`. -/
theorem actual_weighted_group_nested (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (seed : Fin R) (xs : List (Fin M)) :
    ‖weighted h.total (h.groupNested seed xs) (1/(2*J*k*d))‖ ≤
      ((k*d)^xs.length*xs.length.factorial : ℕ)*(2*J)^(xs.length+1) := by
  rw [h.connected_expansion, weighted_list_sum]
  calc
    _ ≤ ((h.words seed xs).map (fun w => ‖weighted h.total (h.nested seed w) (1/(2*J*k*d))‖)).sum :=
      Hamiltonian.norm_map_sum_le _ _
    _ ≤ ((h.words seed xs).map (fun _ => (2*J)^(xs.length+1))).sum :=
      List.sum_le_sum (fun w hw => by
        simpa only [h.words_length seed xs w hw] using
            actual_weighted_local_nested h hJ hk hd seed w)
    _ = (h.words seed xs).length*(2*J)^(xs.length+1) := by
      induction h.words seed xs with
      | nil => simp
      | cons w l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons] at *
        push_cast
        rw [ih]
        ring
    _ ≤ _ := by
      gcongr
      exact h.words_count seed xs

/-- A nested commutator around a grouped seed is the sum of the grouped nested commutators
around its individual local labels. -/
theorem actual_nested_seed_sum (h : Hamiltonian N R M k d J) (seed : Fin M) (xs : List (Fin M)) :
    RetainedError.nested h seed xs = ∑ i ∈ h.labels seed, h.groupNested i xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [RetainedError.nested, ih, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib, Hamiltonian.groupNested]

/-- For positive `J`, `k`, and `d` and at most `L` seed labels, the weighted grouped nested
commutator norm is at most `L * (k * d)^xs.length * xs.length! * (2 * J)^(xs.length + 1)`. -/
theorem actual_weighted_nested (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ) (seed : Fin M)
    (hL : (h.labels seed).card ≤ L) (xs : List (Fin M)) :
    ‖weighted h.total (RetainedError.nested h seed xs) (1/(2*J*k*d))‖ ≤
      (L : ℝ)*((k*d)^xs.length*xs.length.factorial : ℕ)*(2*J)^(xs.length+1) := by
  rw [actual_nested_seed_sum, weighted_sum]
  calc
    _ ≤ ∑ i ∈ h.labels seed, ‖weighted h.total (h.groupNested i xs) (1/(2*J*k*d))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ h.labels seed,
        ((k*d)^xs.length*xs.length.factorial : ℕ)*(2*J)^(xs.length+1) := by
      gcongr with i hi
      exact actual_weighted_group_nested h hJ hk hd i xs
    _ = (h.labels seed).card*(((k*d)^xs.length*xs.length.factorial : ℕ)*(2*J)^(xs.length+1)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hc : ((h.labels seed).card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      calc
        _ ≤ (L : ℝ)*(((k*d)^xs.length*xs.length.factorial : ℕ)*(2*J)^(xs.length+1)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring
end Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
