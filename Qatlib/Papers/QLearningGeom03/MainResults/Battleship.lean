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
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {N : ℕ} [NeZero N]

def shipWindow (r : ℕ) : Finset (ZMod N) :=
  (Finset.range (2 * r + 1)).image (fun t => ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N))

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

lemma shipWindow_card {r : ℕ} (h : 2 * r + 1 ≤ N) : (shipWindow (N := N) r).card = 2 * r + 1 := by
  rw [shipWindow, Finset.card_image_of_injOn]
  · exact Finset.card_range _
  · intro t ht t' ht'
    exact shipWindow_injOn h t (by simpa using ht) t' (by simpa using ht')

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

noncomputable def epsBS (r : ℕ) (k : ZMod N) : ℂ := if k ∈ shipWindow (N := N) r then -1 else 1

lemma epsBS_neg (r : ℕ) (k : ZMod N) : epsBS (N := N) r (-k) = epsBS (N := N) r k := by
  unfold epsBS
  by_cases h : k ∈ shipWindow (N := N) r
  · rw [if_pos ((shipWindow_neg r k).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((shipWindow_neg r k).mp hc)), if_neg h]

noncomputable def bsMatrix (r : ℕ) : Matrix (ZMod N) (ZMod N) ℂ :=
  fun x a => (((Real.sqrt N : ℝ) : ℂ)⁻¹) * epsBS (N := N) r (a - x)

theorem bs_matrix_eq (r : ℕ) :
    bsMatrix (N := N) r
      = (((Real.sqrt N : ℝ) : ℂ)⁻¹) • groupAlgebraElem (fun k => epsBS (N := N) r k) := by
  ext x a
  rw [Matrix.smul_apply, groupAlgebraElem_apply, smul_eq_mul, bsMatrix]
  have hneg : a - x = -(x - a) := by abel
  rw [hneg, epsBS_neg]

lemma chiN_zero_left (j : ZMod N) : chiN j 0 = 1 := by
  unfold chiN
  rw [mul_zero, AddChar.map_zero_eq_one]

lemma chiN_comm (j k : ZMod N) : chiN j k = chiN k j := by
  unfold chiN
  rw [mul_comm]

lemma chiN_sum_left (j : ZMod N) :
    (∑ x : ZMod N, chiN j x) = if j = 0 then ((N : ℕ) : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun x _ => chiN_comm j x), chiN_sum]
  by_cases h : j = 0
  · rw [if_pos h, if_pos h, ZMod.card]
  · rw [if_neg h, if_neg h]
    simp

lemma epsBS_eq_indicator (r : ℕ) (k : ZMod N) :
    epsBS (N := N) r k = 1 - 2 * (if k ∈ shipWindow (N := N) r then (1 : ℂ) else 0) := by
  unfold epsBS
  by_cases h : k ∈ shipWindow (N := N) r
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

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

theorem bs_lambda_zero {r : ℕ} (h : 2 * r + 1 ≤ N) :
    (∑ x : ZMod N, epsBS (N := N) r x * chiN 0 x)
      = ((N : ℕ) : ℂ) - 2 * (((2 * r + 1 : ℕ)) : ℂ) := by
  rw [bs_eigenvalue]
  rw [if_pos rfl]
  have hsum : (∑ k ∈ shipWindow (N := N) r, chiN 0 k)
      = (((2 * r + 1 : ℕ)) : ℂ) := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [chiN_comm 0 k, chiN_zero_left]), Finset.sum_const,
      shipWindow_card h, nsmul_eq_mul, mul_one]
  rw [hsum]

lemma chiN_pow_natCast (j : ZMod N) (t : ℕ) :
    (chiN j 1) ^ t = chiN j ((t : ℕ) : ZMod N) := by
  induction t with
  | zero => rw [Nat.cast_zero, chiN_zero_right, pow_zero]
  | succ k ih =>
    rw [Nat.cast_succ, chiN_add_right, ← ih, pow_succ]

lemma bs_window_geom {r : ℕ} (h : 2 * r + 1 ≤ N) (j : ZMod N) :
    (∑ k ∈ shipWindow (N := N) r, chiN j k)
      = chiN j (-((r : ℕ) : ZMod N))
        * ∑ t ∈ Finset.range (2 * r + 1), (chiN j 1) ^ t := by
  rw [shipWindow, Finset.sum_image (shipWindow_injOn h)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show ((t : ℕ) : ZMod N) - ((r : ℕ) : ZMod N) = ((t : ℕ) : ZMod N) + (-((r : ℕ) : ZMod N))
    by abel, chiN_add_right, chiN_pow_natCast, mul_comm]

lemma chiN_one_ne_one {j : ZMod N} (hj : j ≠ 0) : chiN j 1 ≠ 1 := by
  intro hone
  apply hj
  have h1 : ZMod.stdAddChar (N := N) j = 1 := by simpa [chiN] using hone
  have h0 : ZMod.stdAddChar (N := N) (0 : ZMod N) = 1 := AddChar.map_zero_eq_one _
  exact ZMod.injective_stdAddChar (h1.trans h0.symm)

theorem bs_window_geom_closed {r : ℕ} (h : 2 * r + 1 ≤ N) {j : ZMod N} (hj : j ≠ 0) :
    (∑ k ∈ shipWindow (N := N) r, chiN j k)
      = chiN j (-((r : ℕ) : ZMod N))
        * (((chiN j 1) ^ (2 * r + 1) - 1) / (chiN j 1 - 1)) := by
  rw [bs_window_geom h, geom_sum_eq (chiN_one_ne_one hj)]

end Qatlib.Papers.QLearningGeom03.MainResults
