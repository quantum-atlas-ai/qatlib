/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHMassProducts
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Multilinear expansions of summable families

This module expands continuous multilinear maps applied to absolutely convergent series. The
tuple-indexed expansion and its grouping by total index provide summation tools for the
perturbative estimates associated with [AftabAnTrivisa2026].

## Main statements

* `map_hasSum`: the full expansion over tuples of natural numbers.
* `grouped_hasSum`: the expansion grouped over finite antidiagonals.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MultilinearSums

open scoped BigOperators Classical
set_option warningAsError false

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in

/-- A continuous multilinear map applied to every tuple from an absolutely summable sequence
yields an absolutely summable family. -/
theorem norm_summable {n : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (D : ℕ → E) (hD : Summable fun j => ‖D j‖) :
    Summable (fun v : Fin n → ℕ => ‖f (fun i => D (v i))‖) := by
  have hm := (BCHMassProducts.tuple_hasSum (fun j => ‖D j‖) hD (fun _ => norm_nonneg _) n).summable
  exact (hm.mul_left ‖f‖).of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => f.le_opNorm _)

/-- A continuous multilinear map commutes with an absolutely convergent sum in all its
arguments, with the expansion indexed by tuples of natural numbers. -/
theorem map_hasSum (n : ℕ) (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (D : ℕ → E) (hD : Summable fun j => ‖D j‖) (x : E) (hx : HasSum D x) :
    HasSum (fun v : Fin n → ℕ => f (fun i => D (v i))) (f (fun _ => x)) := by
  induction n with
  | zero =>
    have h := hasSum_unique (fun v : Fin 0 → ℕ => f (fun i => D (v i)))
    convert! h using 1
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
    have he : ((fun v : Fin (n + 1) → ℕ => f (fun i => D (v i))) ∘ e) =
        (fun z : ℕ × (Fin n → ℕ) => f (Fin.cons (D z.1) (fun i => D (z.2 i)))) := by
      funext z
      change f (D ∘ Fin.cons z.1 z.2) = _
      rw [Fin.comp_cons]
      rfl
    have hp := e.summable_iff.mpr (norm_summable f D hD).of_norm
    rw [he] at hp
    have hrows (j : ℕ) :
        HasSum (fun v : Fin n → ℕ => f (Fin.cons (D j) (fun i => D (v i))))
          (f (Fin.cons (D j) (fun _ => x))) := by
      exact ih (f.curryLeft (D j))
    let g : E →L[ℝ] F :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F (fun _ => x)).comp f.curryLeft
    have hh := hx.mapL g
    change HasSum (fun j => f (Fin.cons (D j) (fun _ => x)))
      (f (Fin.cons x (fun _ => x))) at hh
    have hconst : (Fin.cons x (fun _ : Fin n => x)) = (fun _ : Fin (n + 1) => x) := by
      funext i
      cases i using Fin.cases <;> rfl
    rw [hconst] at hh
    have heq := (hp.hasSum.prod_fiberwise hrows).unique hh
    apply e.hasSum_iff.mp
    rw [he]
    exact heq ▸ hp.hasSum

/-- Grouping the multilinear expansion by the sum of its tuple indices preserves its sum. -/
theorem grouped_hasSum (n : ℕ) (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (D : ℕ → E) (hD : Summable fun j => ‖D j‖) (x : E) (hx : HasSum D x) :
    HasSum (fun k => ∑ v ∈ Finset.finAntidiagonal n k, f (fun i => D (v i)))
      (f (fun _ => x)) := by
  have h := (BCHMassProducts.degreeEquiv n).hasSum_iff.mpr (map_hasSum n f D hD x hx)
  apply h.sigma
  intro k
  change HasSum (fun v : ↥(Finset.finAntidiagonal n k) => f (fun i => D (v.1 i))) _
  have he : (∑ v : ↥(Finset.finAntidiagonal n k), f (fun i => D (v.1 i))) =
      ∑ v ∈ Finset.finAntidiagonal n k, f (fun i => D (v i)) :=
    Finset.sum_coe_sort (Finset.finAntidiagonal n k) (fun v : Fin n → ℕ => f (fun i => D (v i)))
  rw [← he]
  exact hasSum_fintype _

end Qatlib.Papers.CommutLCHS26.MainResults.MultilinearSums
