/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLie
import Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarCoeff
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarWord

open scoped BigOperators Classical
open BCHWordLie BCHWordLog BCHDynkin

variable {A R : Type} [Ring A] [Algebra ℚ A] [CommRing R] [Algebra R A]

theorem generatorSeries_zero : generatorSeries (0 : A) = 1 := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [generatorSeries, PowerSeries.coeff_one]

omit [Algebra ℚ A] in

theorem commute_smul_same (r s : R) (X : A) : Commute (r • X) (s • X) := by
  show (r • X) * (s • X) = (s • X) * (r • X)
  simp only [smul_mul_smul_comm, mul_comm r s]

theorem wordSeries_append (xs ys : List A) :
    wordSeries (xs ++ ys) = wordSeries xs * wordSeries ys := by
  simp only [wordSeries, List.map_append, List.prod_append]

theorem wordSeries_smul_block (X : A) (rs : List R) :
    wordSeries (rs.map (fun r => r • X)) = generatorSeries (rs.sum • X) := by
  induction rs with
  | nil => simp [wordSeries, generatorSeries_zero]
  | cons r rs ih =>
    change generatorSeries (r • X) * wordSeries (rs.map (fun s => s • X)) = _
    rw [ih, List.sum_cons, add_smul, generatorSeries_add _ _ (commute_smul_same _ _ _)]

theorem wordSeries_clone_blocks {ι σ : Type*} (xs : List ι) (positions : ι → List σ)
    (r : σ → R) (X : ι → A) :
    wordSeries (xs.flatMap (fun i => (positions i).map (fun j => r j • X i))) =
      wordSeries (xs.map (fun i => ((positions i).map r).sum • X i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [List.flatMap_cons, wordSeries_append, ih, List.map_cons]
    change wordSeries ((positions i).map (fun j => r j • X i)) * _ =
      generatorSeries (((positions i).map r).sum • X i) * _
    congr 1
    simpa only [List.map_map, Function.comp_def] using
      wordSeries_smul_block (X i) ((positions i).map r)

theorem logCoefficient_clone_blocks {ι σ : Type*} (xs : List ι) (positions : ι → List σ)
    (r : σ → R) (X : ι → A) (n : ℕ) :
    logCoefficient (wordSeries (xs.flatMap (fun i =>
      (positions i).map (fun j => r j • X i)))) n =
        logCoefficient (wordSeries (xs.map (fun i =>
          ((positions i).map r).sum • X i))) n := by
  rw [wordSeries_clone_blocks]

theorem evaluate_log_clone_blocks {ι σ : Type} (xs : List ι) (positions : ι → List σ)
    (base : σ → ι) (hbase : ∀ i, ∀ j ∈ positions i, base j = i)
    (r : σ → R) (X : ι → A) (n : ℕ) :
    evaluateWords (fun j => r j • X (base j))
      (logCoefficient (wordSeries ((xs.flatMap positions).map letter)) n) =
        evaluateWords (fun i => ((positions i).map r).sum • X i)
          (logCoefficient (wordSeries (xs.map letter)) n) := by
  rw [← logCoefficient_map, ← logCoefficient_map, wordSeries_map, wordSeries_map]
  simp only [List.map_map, evaluateWords_letter, Function.comp_def]
  have hlist : (xs.flatMap positions).map (fun j => r j • X (base j)) =
      xs.flatMap (fun i => (positions i).map (fun j => r j • X i)) := by
    rw [List.map_flatMap]
    congr 1
    funext i
    exact List.map_congr_left fun j hj => by rw [hbase i j hj]
  rw [hlist, logCoefficient_clone_blocks]

theorem evaluate_log_sigma_clones {ι : Type} (xs : List ι) (m : ι → ℕ)
    (r : (Σ i, Fin (m i)) → R) (X : ι → A) (n : ℕ) :
    evaluateWords (fun j : Σ i, Fin (m i) => r j • X j.1)
      (logCoefficient (wordSeries
        ((xs.flatMap (fun i => List.ofFn
          (fun j : Fin (m i) => (⟨i, j⟩ : Σ i, Fin (m i))))).map letter)) n) =
        evaluateWords (fun i => (∑ j : Fin (m i), r ⟨i, j⟩) • X i)
          (logCoefficient (wordSeries (xs.map letter)) n) := by
  have hb (i : ι) (j : Σ i, Fin (m i))
      (hj : j ∈ List.ofFn (fun k : Fin (m i) => (⟨i, k⟩ : Σ i, Fin (m i)))) : j.1 = i := by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hj
    rfl
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using
    evaluate_log_clone_blocks xs
      (fun i => List.ofFn (fun j : Fin (m i) => (⟨i, j⟩ : Σ i, Fin (m i))))
      Sigma.fst hb r X n

end Qatlib.Papers.CommutLCHS26.MainResults.BCHPolarWord
