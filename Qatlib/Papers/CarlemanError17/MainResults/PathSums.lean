/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CarlemanError17.MainResults.Core.SourceModel

@[expose] public section


/-! # Finite path recurrence and endpoints for arXiv:1711.02552v1, Proposition 5.6.
These algebraic path identities do not assert a Duhamel formula or a truncation error bound.
-/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped BigOperators
namespace Qatlib.Papers.CarlemanError17.MainResults.PathSums
open Qatlib.Papers.CarlemanError17.MainResults.Core

/-- Definition 5.5 (p.19, Eq. (47)–(48)), in the `q = 1` case of the quadratic ODE.
`pathSum F ν i j = C^(ν)_{i,i+j}` is the sum over all paths of `ν` jumps from site `i`
to site `i+j` with individual jump length at most `1`, i.e. every step is either the
stay `A^{i'}_{i'}` or the move `A^{i'}_{i'+1}`.

We define it by the recurrence (59) used in the proof of Proposition 5.6
("split off the last jump"), so that the recurrence is definitional:
`C^(ν+1)_{i,i+j} = C^(ν)_{i,i+j} A^{i+j}_{i+j} + C^(ν)_{i,i+j−1} A^{i+j−1}_{i+j}`,
with `C^(0)_{i,i} = I` and `C^(0)_{i,i+j} = 0` for `j > 0`. -/
def pathSum {n : ℕ} (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) :
    (ν : ℕ) → (i j : ℕ) → Matrix (TP n i) (TP n (i + j)) ℝ
  | 0, i, 0 => 1
  | 0, i, (j + 1) => 0
  | (ν + 1), i, 0 => reindexTP rfl (by omega) (pathSum F ν i 0 * transfer F i 0)
  | (ν + 1), i, (j + 1) =>
      reindexTP rfl (by omega) (pathSum F ν i (j + 1) * transfer F (i + (j + 1)) 0)
      + reindexTP rfl (by omega) (pathSum F ν i j * transfer F (i + j) 1)

/-- The closed endpoint product of Proposition 5.6.3: `A^i_{i+1} A^{i+1}_{i+2} ⋯
A^{i+ν−1}_{i+ν}`, the path with `ν` moves of length one. -/
def endProd {n : ℕ} (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) :
    (ν : ℕ) → (i : ℕ) → Matrix (TP n i) (TP n (i + ν)) ℝ
  | 0, i => 1
  | (ν + 1), i => reindexTP rfl (by omega) (endProd F ν i * transfer F (i + ν) 1)

/-- Casting a matrix along reflexivity is the identity. -/
lemma reindexTP_refl {n a c : ℕ} (A : Matrix (TP n a) (TP n c) ℝ) :
    reindexTP rfl rfl A = A := by
  ext i j
  simp [reindexTP, tpCast]

/-- Remark 1 (p.19): a path of `ν` jumps with individual length at most `1` cannot
travel a distance `j > ν`, so `C^(ν)_{i,i+j} = 0` for `j > ν`. -/
lemma pathSum_eq_zero_of_lt {n : ℕ}
    (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) :
    ∀ (ν : ℕ) (i j : ℕ), ν < j → pathSum F ν i j = 0
  | 0, i, j, _ => by
      cases j with
      | zero => omega
      | succ j => rfl
  | (ν + 1), i, j, h => by
      cases j with
      | zero => omega
      | succ j =>
          simp only [pathSum]
          rw [pathSum_eq_zero_of_lt F ν i (j + 1) (by omega),
              pathSum_eq_zero_of_lt F ν i j (by omega)]
          simp [reindexTP]

/-- Proposition 5.6.2 (p.20): the endpoint `j = 0` is the `ν`-fold product of the
"stay" maps, `C^(ν)_{i,i} = (A^i_i)^ν`. -/
lemma pathSum_zero {n : ℕ} (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) (i : ℕ) :
    ∀ ν : ℕ, pathSum F ν i 0 = (transfer F i 0) ^ ν
  | 0 => by rfl
  | (ν + 1) => by
      simp only [pathSum]
      rw [reindexTP_refl, pathSum_zero F i ν, pow_succ]

/-- Proposition 5.6.3 (p.20): the endpoint `j = ν` is the `ν`-fold product of the
"move" maps, `C^(ν)_{i,i+ν} = A^i_{i+1} A^{i+1}_{i+2} ⋯ A^{i+ν−1}_{i+ν}`. -/
lemma pathSum_endProd {n : ℕ} (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) (i : ℕ) :
    ∀ ν : ℕ, pathSum F ν i ν = endProd F ν i
  | 0 => by rfl
  | (ν + 1) => by
      simp only [pathSum]
      rw [pathSum_eq_zero_of_lt F ν i (ν + 1) (by omega)]
      rw [Matrix.zero_mul, pathSum_endProd F i ν]
      simp only [endProd]
      ext a b
      simp [reindexTP, tpCast]

/-- Proposition 5.6 (p.20, Eq. (59)).  For `i ≥ 1`, `ν ≥ 2`:
1. for `1 ≤ j ≤ ν−1`, `C^(ν)_{i,i+j} = C^(ν−1)_{i,i+j} A^{i+j}_{i+j}
   + C^(ν−1)_{i,i+j−1} A^{i+j−1}_{i+j}`;
2. for `j = 0`, `C^(ν)_{i,i} = (A^i_i)^ν`;
3. for `j = ν`, `C^(ν)_{i,i+ν} = A^i_{i+1} A^{i+1}_{i+2} ⋯ A^{i+ν−1}_{i+ν}`.

The recurrence of item 1 is definitional for `pathSum` (it is the "split off the last
jump" decomposition); the endpoint forms are proved by induction on `ν`. -/
theorem prop_five_six {n : ℕ} (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ)
    (i : ℕ) (_hi : 1 ≤ i) (ν : ℕ) (hν : 2 ≤ ν) :
    (∀ (j : ℕ) (hj1 : 1 ≤ j) (_hj2 : j ≤ ν - 1),
        pathSum F ν i j
          = reindexTP (n := n) (a := i) (b := i) (c := (i + j) + 0) (d := i + j)
              rfl (by omega) (pathSum F (ν - 1) i j * transfer F (i + j) 0)
            + reindexTP (n := n) (a := i) (b := i) (c := (i + (j - 1)) + 1) (d := i + j)
                rfl (by omega)
                (pathSum F (ν - 1) i (j - 1) * transfer F (i + (j - 1)) 1))
      ∧ pathSum F ν i 0 = (transfer F i 0) ^ ν
      ∧ pathSum F ν i ν = endProd F ν i := by
  /-
  Paper source: arXiv:1711.02552v1, Proposition 5.6, p.20, Eq. (59).
  Item 1 is the defining recurrence of `pathSum` (split off the last jump): writing
  `ν = ν'+1` and `j = j'+1`, the two sides are definitionally equal.
  Items 2 and 3 are inductions on `ν` (`pathSum_zero`, `pathSum_endProd`); the extra
  summands vanish by Remark 1 (`pathSum_eq_zero_of_lt`).
  -/
  refine ⟨?_, pathSum_zero F i ν, pathSum_endProd F i ν⟩
  intro j hj1 _hj2
  obtain ⟨ν', rfl⟩ : ∃ ν', ν = ν' + 1 := ⟨ν - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rfl


end Qatlib.Papers.CarlemanError17.MainResults.PathSums
