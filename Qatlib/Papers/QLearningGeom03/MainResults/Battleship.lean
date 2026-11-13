/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Qatlib.Papers.QLearningGeom03.MainResults.GroupAlgebraZN

/-!
# Cyclic battleship learning matrices

This module defines the symmetric cyclic ship window `shipWindow`, its phase function `epsBS`,
and the normalized battleship matrix `bsMatrix`. It expresses the matrix in the cyclic group
algebra and computes its Fourier coefficients using character sums and a finite geometric
series, following the battleship examples in [HunzikerEtAl2003].

## Main statements

* `bs_matrix_eq`: Group-algebra representation of the battleship matrix.
* `bs_eigenvalue`: Character-sum expression for the unnormalized phase eigenvalues.
* `bs_window_geom_closed`: Closed geometric-series formula for nonzero frequencies.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {N : ℕ} [NeZero N]

/-- The cyclic window consisting of the residues of the integers from -r through r. -/
def shipWindow (r : ℕ) : Finset (ZMod N) :=
  (Finset.range (2 * r + 1)).image (fun t => ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N))

omit [NeZero N] in

/-- If 2r + 1 ≤ N, the map t ↦ t - r into `ZMod N` is injective on the range from 0 through 2r. -/
lemma shipWindow_injOn {r : ℕ} (h : 2 * r + 1 ≤ N) :
    ∀ t ∈ Finset.range (2 * r + 1), ∀ t' ∈ Finset.range (2 * r + 1),
      ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N)
        = ((t' : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) → t = t' := by
  intro t ht t' ht' hts
  simp only [Finset.mem_range] at ht ht'
  have hcast : ((t : ℕ) : ZMod N) = ((t' : ℕ) : ZMod N) := by
    have h' : ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) + ((r : ℕ) : ZMod N)
        = ((t' : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) + ((r : ℕ) : ZMod N) := by rw [hts]
    simpa [sub_add_cancel] using h'
  have hmod := (ZMod.natCast_eq_natCast_iff t t' N).mp hcast
  exact Nat.ModEq.eq_of_lt_of_lt hmod (lt_of_lt_of_le ht h) (lt_of_lt_of_le ht' h)

/-- If 2r + 1 ≤ N, the cyclic ship window contains exactly 2r + 1 elements. -/
lemma shipWindow_card {r : ℕ} (h : 2 * r + 1 ≤ N) : (shipWindow (N := N) r).card = 2 * r + 1 := by
  rw [shipWindow, Finset.card_image_of_injOn]
  · exact Finset.card_range _
  · intro t ht t' ht'
    exact shipWindow_injOn h t (by simpa using ht) t' (by simpa using ht')

omit [NeZero N] in

/-- Membership in the cyclic ship window is invariant under negation. -/
lemma shipWindow_neg (r : ℕ) (k : ZMod N) :
    -k ∈ shipWindow (N := N) r ↔ k ∈ shipWindow (N := N) r := by
  simp only [shipWindow, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, htk⟩
    refine ⟨2 * r - t, by omega, ?_⟩
    have hcast : (((2 * r - t : ℕ)) : ZMod N) = ((2 * r : ℕ) : ZMod N) - ((t : ℕ) : ZMod N) := by
      rw [Nat.cast_sub (by omega)]
    have hk : k = -(((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N)) := by
      rw [htk]
      simp
    rw [hcast, hk]
    push_cast
    ring
  · rintro ⟨t, ht, htk⟩
    refine ⟨2 * r - t, by omega, ?_⟩
    have hcast : (((2 * r - t : ℕ)) : ZMod N) = ((2 * r : ℕ) : ZMod N) - ((t : ℕ) : ZMod N) := by
      rw [Nat.cast_sub (by omega)]
    have hk : -k = -(((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N)) := by
      rw [htk]
    rw [hcast, hk]
    push_cast
    ring

/-- The battleship phase function, equal to -1 on `shipWindow r` and 1 outside it. -/
noncomputable def epsBS (r : ℕ) (k : ZMod N) : ℂ := if k ∈ shipWindow (N := N) r then -1 else 1

/-- The battleship phase function is invariant under negation. -/
lemma epsBS_neg (r : ℕ) (k : ZMod N) : epsBS (N := N) r (-k) = epsBS (N := N) r k := by
  unfold epsBS
  by_cases h : k ∈ shipWindow (N := N) r
  · rw [ite_eq_left ((shipWindow_neg r k).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((shipWindow_neg r k).mp hc)), ite_eq_right h]

/-- The battleship matrix with entry `epsBS r (a - x)` divided by √N. -/
noncomputable def bsMatrix (r : ℕ) : Matrix (ZMod N) (ZMod N) ℂ :=
  fun x a => (((Real.sqrt N : ℝ) : ℂ)⁻¹) * epsBS (N := N) r (a - x)

/-- The battleship matrix is 1/√N times the group-algebra matrix of its phase function, as in
[HunzikerEtAl2003]. -/
theorem bs_matrix_eq (r : ℕ) :
    bsMatrix (N := N) r
      = (((Real.sqrt N : ℝ) : ℂ)⁻¹) • groupAlgebraElem (fun k => epsBS (N := N) r k) := by
  ext x a
  rw [Matrix.smul_apply, groupAlgebraElem_apply, smul_eq_mul, bsMatrix]
  have hneg : a - x = -(x - a) := by abel
  rw [hneg, epsBS_neg]

/-- The cyclic character `chiN j` takes the value 1 at zero. -/
lemma chiN_zero_left (j : ZMod N) : chiN j 0 = 1 := by
  unfold chiN
  rw [mul_zero, AddChar.map_zero_eq_one]

/-- The cyclic character pairing is symmetric in its two arguments. -/
lemma chiN_comm (j k : ZMod N) : chiN j k = chiN k j := by
  unfold chiN
  rw [mul_comm]

/-- The sum of a cyclic character over its second argument is N at zero frequency and zero
otherwise. -/
lemma chiN_sum_left (j : ZMod N) :
    (∑ x : ZMod N, chiN j x) = if j = 0 then ((N : ℕ) : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun x _ => chiN_comm j x), chiN_sum]
  by_cases h : j = 0
  · rw [ite_eq_left h, ite_eq_left h, ZMod.card]
  · rw [ite_eq_right h, ite_eq_right h]
    simp

omit [NeZero N] in

/-- The battleship phase function equals one minus twice the indicator of the ship window. -/
lemma epsBS_eq_indicator (r : ℕ) (k : ZMod N) :
    epsBS (N := N) r k = 1 - 2 * (if k ∈ shipWindow (N := N) r then (1 : ℂ) else 0) := by
  unfold epsBS
  by_cases h : k ∈ shipWindow (N := N) r
  · rw [ite_eq_left h, ite_eq_left h]; norm_num
  · rw [ite_eq_right h, ite_eq_right h]; norm_num

/-- The Fourier coefficient of `epsBS r` is the zero-frequency contribution minus twice the
character sum over the ship window. This computes the phase eigenvalues used in
[HunzikerEtAl2003]. -/
theorem bs_eigenvalue (r : ℕ) (j : ZMod N) :
    (∑ x : ZMod N, epsBS (N := N) r x * chiN j x)
      = (if j = 0 then ((N : ℕ) : ℂ) else 0)
        - 2 * (∑ k ∈ shipWindow (N := N) r, chiN j k) := by
  have hpt : ∀ x : ZMod N, epsBS (N := N) r x * chiN j x
      = chiN j x - 2 * ((if x ∈ shipWindow (N := N) r then (1 : ℂ) else 0) * chiN j x) := by
    intro x
    rw [epsBS_eq_indicator]
    ring
  have hsplit : (∑ x : ZMod N, epsBS (N := N) r x * chiN j x)
      = (∑ x : ZMod N, chiN j x)
        - 2 * (∑ x : ZMod N, (if x ∈ shipWindow (N := N) r then (1 : ℂ) else 0) * chiN j x) := by
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hind : (∑ x : ZMod N, (if x ∈ shipWindow (N := N) r then (1 : ℂ) else 0) * chiN j x)
      = ∑ k ∈ shipWindow (N := N) r, chiN j k := by
    have hterm : ∀ x : ZMod N,
        (if x ∈ shipWindow (N := N) r then (1 : ℂ) else 0) * chiN j x
          = if x ∈ shipWindow (N := N) r then chiN j x else 0 := by
      intro x
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsplit, chiN_sum_left, hind]

/-- If 2r + 1 ≤ N, the zero-frequency Fourier coefficient of `epsBS r` is N - 2(2r + 1). -/
theorem bs_lambda_zero {r : ℕ} (h : 2 * r + 1 ≤ N) :
    (∑ x : ZMod N, epsBS (N := N) r x * chiN 0 x)
      = ((N : ℕ) : ℂ) - 2 * (((2 * r + 1 : ℕ)) : ℂ) := by
  rw [bs_eigenvalue]
  rw [ite_eq_left rfl]
  have hsum : (∑ k ∈ shipWindow (N := N) r, chiN 0 k)
      = (((2 * r + 1 : ℕ)) : ℂ) := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [chiN_comm 0 k, chiN_zero_left]), Finset.sum_const,
      shipWindow_card h, nsmul_eq_mul, mul_one]
  rw [hsum]

/-- The t-th power of `chiN j 1` equals the character evaluated at the residue of `t`. -/
lemma chiN_pow_natCast (j : ZMod N) (t : ℕ) :
    (chiN j 1) ^ t = chiN j ((t : ℕ) : ZMod N) := by
  induction t with
  | zero => rw [Nat.cast_zero, chiN_zero_right, pow_zero]
  | succ k ih =>
    rw [Nat.cast_succ, chiN_add_right, ← ih, pow_succ]

/-- If 2r + 1 ≤ N, the character sum over the ship window is a phase factor times a geometric
sum of length 2r + 1. -/
lemma bs_window_geom {r : ℕ} (h : 2 * r + 1 ≤ N) (j : ZMod N) :
    (∑ k ∈ shipWindow (N := N) r, chiN j k)
      = chiN j (-((r : ℕ) : ZMod N))
        * ∑ t ∈ Finset.range (2 * r + 1), (chiN j 1) ^ t := by
  rw [shipWindow, Finset.sum_image (shipWindow_injOn h)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) = ((t : ℕ) : ZMod N) + (-((r : ℕ) : ZMod N))
    by abel, chiN_add_right, chiN_pow_natCast, mul_comm]

/-- At a nonzero frequency, `chiN j 1` is different from 1. -/
lemma chiN_one_ne_one {j : ZMod N} (hj : j ≠ 0) : chiN j 1 ≠ 1 := by
  intro hone
  apply hj
  have h1 : ZMod.stdAddChar (N := N) j = 1 := by simpa [chiN] using hone
  have h0 : ZMod.stdAddChar (N := N) (0 : ZMod N) = 1 := AddChar.map_zero_eq_one _
  exact ZMod.injective_stdAddChar (h1.trans h0.symm)

/-- For a nonzero frequency and 2r + 1 ≤ N, the ship-window character sum equals its phase
factor times the geometric-series quotient. -/
theorem bs_window_geom_closed {r : ℕ} (h : 2 * r + 1 ≤ N) {j : ZMod N} (hj : j ≠ 0) :
    (∑ k ∈ shipWindow (N := N) r, chiN j k)
      = chiN j (-((r : ℕ) : ZMod N))
        * (((chiN j 1) ^ (2 * r + 1) - 1) / (chiN j 1 - 1)) := by
  rw [bs_window_geom h, geom_sum_eq (chiN_one_ne_one hj)]

end Qatlib.Papers.QLearningGeom03.MainResults
