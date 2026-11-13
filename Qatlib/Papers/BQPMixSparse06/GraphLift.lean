/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Theorem2PathsReduction

/-!
# Invariant blocks of the signed graph lift

The signed-to-unsigned conversion `blockConvert` decomposes into antisymmetric and symmetric
two-point sectors. The theorem `blockConvert_decomp` identifies these sectors with the signed
matrix and its entrywise absolute value, respectively, in the graph-lift construction of
[JanzingWocjan2006].

## Main statements

* `blockConvert_decomp`: decomposes the lifted matrix using `phiMinus` and `phiPlus`.
* `lift_automorphism`: the lift is invariant under swapping the two copies of every vertex.
* `blockConvert_row_card`: the number of nonzero entries in each lifted row is preserved.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.GraphLift

open Finset Matrix
open Qatlib.Papers.BQPMixSparse06.MainResults

/-- The integer nonzero indicator: zero at `a = 0` and one otherwise; it equals absolute value
on `{-1, 0, 1}`. -/
def absEntry (a : ℤ) : ℤ := if a = 0 then 0 else 1

/-- The integer matrix formed by applying the nonzero indicator `absEntry` to each entry of `A`. -/
def absMat {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  A.map absEntry

/-- The doubled matrix with entry `u s * A i j * v t` at `((s, i), (t, j))`. -/
def outerLift {N : ℕ} (u v : Fin 2 → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  fun p q => u p.1 * v q.1 * A p.2 q.2

/-- For entries in `{-1, 0, 1}`, each lifted entry splits into its antisymmetric signed part and
symmetric absolute-value part [JanzingWocjan2006]. -/
theorem blockConvert_entry_decomp {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (i j : Fin N) (s t : Fin 2) :
    blockConvert A (s, i) (t, j) =
      phiMinus s * (A i j : ℝ) * phiMinus t +
        phiPlus s * (absEntry (A i j) : ℝ) * phiPlus t := by
  rcases hA i j with h | h | h
  · fin_cases s <;> fin_cases t <;>
      simp [h, blockConvert, gammaBlock, phiMinus, phiPlus, absEntry] <;>
      nlinarith [hsq_sqrt_two]
  · fin_cases s <;> fin_cases t <;>
      simp [h, blockConvert, gammaBlock, phiMinus, phiPlus, absEntry]
  · fin_cases s <;> fin_cases t <;>
      simp [h, blockConvert, gammaBlock, phiMinus, phiPlus, absEntry] <;>
      nlinarith [hsq_sqrt_two]

/-- The lift of a matrix with entries in `{-1, 0, 1}` is the sum of the antisymmetric lift of
the signed matrix and the symmetric lift of its entrywise absolute value
[JanzingWocjan2006]. -/
theorem blockConvert_decomp {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) :
    blockConvert A =
      outerLift phiMinus phiMinus (realCast A) +
        outerLift phiPlus phiPlus (realCast (absMat A)) := by
  ext p q
  obtain ⟨s, i⟩ := p
  obtain ⟨t, j⟩ := q
  simp only [Matrix.add_apply, outerLift, realCast, absMat, Matrix.map_apply]
  rw [blockConvert_entry_decomp A hA i j s t]
  ring

/-- Simultaneously swapping the two copies of every vertex leaves the signed-to-unsigned graph
lift unchanged [JanzingWocjan2006]. -/
theorem lift_automorphism {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) :
    pairFlip * blockConvert A * pairFlip = blockConvert A :=
  pairFlip_conj_blockConvert A hA

/-- For a matrix with entries in `{-1, 0, 1}`, each lifted row has exactly as many nonzero
entries as its original row [JanzingWocjan2006]. -/
theorem blockConvert_row_card {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (s : Fin 2) (i : Fin N) :
    (univ.filter (fun q : Fin 2 × Fin N => blockConvert A (s, i) q ≠ 0)).card =
      (univ.filter (fun j : Fin N => A i j ≠ 0)).card := by
  classical
  have hAnz : ∀ j : Fin N, A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
    intro j
    rcases hA i j with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hpair : (∑ q ∈ (univ : Finset (Fin 2 × Fin N)),
        (if blockConvert A (s, i) q ≠ 0 then (1:ℕ) else 0)) =
      ∑ j : Fin N, ∑ t : Fin 2,
        (if blockConvert A (s, i) (t, j) ≠ 0 then (1:ℕ) else 0) := by
    rw [Fintype.sum_prod_type (γ := ℕ)]
    exact Finset.sum_comm
  have hL : (univ.filter (fun q : Fin 2 × Fin N => blockConvert A (s, i) q ≠ 0)).card =
      ∑ j, (if A i j = 0 then (0:ℕ) else 1) := by
    rw [Finset.card_filter (p := fun q : Fin 2 × Fin N => blockConvert A (s, i) q ≠ 0)
      (s := (univ : Finset (Fin 2 × Fin N)))]
    rw [hpair]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [blockConvert]
    have hcf : (∑ x : Fin 2, (if gammaBlock (A i j) s x ≠ 0 then (1:ℕ) else 0)) =
        (univ.filter (fun t : Fin 2 => gammaBlock (A i j) s t ≠ 0)).card := by
      simpa using (Finset.card_filter
        (p := fun t : Fin 2 => gammaBlock (A i j) s t ≠ 0)
        (s := (univ : Finset (Fin 2)))).symm
    exact hcf.trans (gammaBlock_row_nz (A i j) (hAnz j) s)
  have hR : (univ.filter (fun j : Fin N => A i j ≠ 0)).card =
      ∑ j, (if A i j = 0 then (0:ℕ) else 1) := by
    rw [Finset.card_filter (p := fun j : Fin N => A i j ≠ 0)
      (s := (univ : Finset (Fin N)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : A i j = 0 <;> simp [h]
  rw [hL, hR]

end Qatlib.Papers.BQPMixSparse06.GraphLift
