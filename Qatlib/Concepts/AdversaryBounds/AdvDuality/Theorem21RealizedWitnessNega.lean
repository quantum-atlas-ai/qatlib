/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

set_option maxRecDepth 8192

private def witnessS (x y : Fin 20) : ℤ :=
  if kushilevitzFunW x = kushilevitzFunW y then 0 else 1

private noncomputable def witnessT (x y : Fin 20) : ℤ :=
  if kushilevitzFunW x = kushilevitzFunW y then 0
  else if kushilevitzDist x y = 2 then 1 else if kushilevitzDist x y = 4 then -1 else 0

private noncomputable def filterS (i : Fin 6) (x y : Fin 20) : ℤ :=
  if kushilevitzInputW x i ≠ kushilevitzInputW y i then witnessS x y else 0

private noncomputable def filterT (i : Fin 6) (x y : Fin 20) : ℤ :=
  if kushilevitzInputW x i ≠ kushilevitzInputW y i then witnessT x y else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

private theorem filter_integer_square : ∀ (i : Fin 6) (x z : Fin 20),
    (∑ y : Fin 20, filterS i x y * filterS i y z) +
      5 * (∑ y : Fin 20, filterT i x y * filterT i y z) =
      if x = z then 25 else 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

private theorem filter_integer_cross : ∀ (i : Fin 6) (x z : Fin 20),
    (∑ y : Fin 20, (filterS i x y * filterT i y z + filterT i x y * filterS i y z)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

private theorem witness_integer_row : ∀ x : Fin 20,
    (∑ y : Fin 20, witnessS x y) = 10 ∧ (∑ y : Fin 20, witnessT x y) = 3 := by
  decide +kernel

private theorem witness_formula (x y : Fin 20) :
    kushilevitzGammaW x y =
      ((witnessS x y : ℂ) + (Real.sqrt 5 : ℂ) * (witnessT x y : ℂ)) / 5 := by
  classical
  unfold kushilevitzGammaW witnessS witnessT kushilevitzWeight
  split_ifs <;> simp_all [kushilevitzWeightA, kushilevitzWeightB, kushilevitzWeightC,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub]
  all_goals ring

private theorem filter_formula (i : Fin 6) (x y : Fin 20) :
    advFilter kushilevitzInputW kushilevitzGammaW i x y =
      ((filterS i x y : ℂ) + (Real.sqrt 5 : ℂ) * (filterT i x y : ℂ)) / 5 := by
  classical
  unfold advFilter filterS filterT
  split_ifs <;> simp [witness_formula]

private theorem sqrt_five_complex : (Real.sqrt 5 : ℂ) * (Real.sqrt 5 : ℂ) = 5 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)

private theorem witness_dist_symm (x y : Fin 20) : kushilevitzDist y x = kushilevitzDist x y := by
  unfold kushilevitzDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]

private theorem witness_hermitian : kushilevitzGammaW.IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, kushilevitzGammaW]
  rw [witness_dist_symm]
  by_cases h : kushilevitzFunW x = kushilevitzFunW y
  · rw [if_pos h, if_pos h.symm]
    exact star_zero _
  · simp only [h, Ne.symm h, if_false, Complex.star_def, Complex.conj_ofReal]

private theorem filter_hermitian (i : Fin 6) :
    (advFilter kushilevitzInputW kushilevitzGammaW i).IsHermitian := by
  change (advFilter kushilevitzInputW kushilevitzGammaW i)ᴴ = _
  ext x y
  change star (if kushilevitzInputW y i ≠ kushilevitzInputW x i then kushilevitzGammaW y x else 0) =
    if kushilevitzInputW x i ≠ kushilevitzInputW y i then kushilevitzGammaW x y else 0
  by_cases h : kushilevitzInputW x i ≠ kushilevitzInputW y i
  · rw [if_pos h, if_pos (Ne.symm h)]
    exact congrFun (congrFun witness_hermitian x) y
  · have h' := not_ne_iff.mp h
    simp only [h', ne_self_iff_false, if_false, star_zero]

private theorem scalar_square (s t u v : ℂ) :
    ((s + (Real.sqrt 5 : ℂ) * t) / 5) * ((u + (Real.sqrt 5 : ℂ) * v) / 5) =
      (s * u + 5 * (t * v) + (Real.sqrt 5 : ℂ) * (s * v + t * u)) / 25 := by
  linear_combination t * v / 25 * sqrt_five_complex

private theorem filter_square (i : Fin 6) :
    advFilter kushilevitzInputW kushilevitzGammaW i *
      advFilter kushilevitzInputW kushilevitzGammaW i = 1 := by
  classical
  ext x z
  rw [Matrix.mul_apply]
  simp_rw [filter_formula, scalar_square]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hmain : (∑ y : Fin 20, (filterS i x y : ℂ) * (filterS i y z : ℂ)) +
      5 * (∑ y : Fin 20, (filterT i x y : ℂ) * (filterT i y z : ℂ)) =
      if x = z then 25 else 0 := by
    exact_mod_cast filter_integer_square i x z
  have hcross : (∑ y : Fin 20,
      ((filterS i x y : ℂ) * (filterT i y z : ℂ) +
      (filterT i x y : ℂ) * (filterS i y z : ℂ))) = 0 := by
    exact_mod_cast filter_integer_cross i x z
  rw [hmain, hcross]
  by_cases h : x = z <;> simp [h, Matrix.one_apply]

private theorem filter_norm (i : Fin 6) :
    ‖advFilter kushilevitzInputW kushilevitzGammaW i‖ = 1 := by
  apply l2_norm_unitary_eq_one
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    filter_hermitian i]
  exact filter_square i

private theorem witness_filter_bound : advFilterBound kushilevitzInputW kushilevitzGammaW ≤ 1 := by
  unfold advFilterBound
  simp_rw [filter_norm]
  rw [List.ofFn_const]
  norm_num [List.replicate, List.foldl]

private theorem witness_row (x : Fin 20) :
    (∑ y : Fin 20, kushilevitzGammaW x y) = (2 + 3 * Real.sqrt 5 / 5 : ℝ) := by
  simp_rw [witness_formula]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs : (∑ y : Fin 20, (witnessS x y : ℂ)) = 10 := by
    exact_mod_cast (witness_integer_row x).1
  have ht : (∑ y : Fin 20, (witnessT x y : ℂ)) = 3 := by
    exact_mod_cast (witness_integer_row x).2
  rw [hs, ht]
  push_cast
  ring

private theorem witness_norm : (2 + 3 * Real.sqrt 5 / 5) ≤ ‖kushilevitzGammaW‖ := by
  let u := Uniform (Fin 20)
  have hu : Normalized u := normalized_uniform (by norm_num)
  have hun : ‖toEuclidean_fromVec u‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec u).mp hu
  have hact : kushilevitzGammaW *ᵥ u = ((2 + 3 * Real.sqrt 5 / 5 : ℝ) : ℂ) • u := by
    ext x
    change (∑ y : Fin 20, kushilevitzGammaW x y * (Real.sqrt (Fintype.card (Fin 20)) : ℂ)⁻¹) = _
    rw [← Finset.sum_mul, witness_row]
    rfl
  have h := l2_norm_mulVec_fromVec_le kushilevitzGammaW u
  rw [hact] at h
  have hpos : 0 ≤ (2 + 3 * Real.sqrt 5 / 5 : ℝ) := by positivity
  have hsmul : ‖toEuclidean_fromVec (((2 + 3 * Real.sqrt 5 / 5 : ℝ) : ℂ) • u)‖ =
      (2 + 3 * Real.sqrt 5 / 5) * ‖toEuclidean_fromVec u‖ := by
    simp only [toEuclidean_fromVec, WithLp.toLp_smul, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  rw [hsmul, hun, mul_one, mul_one] at h
  exact h

theorem theorem21RealizedWitness : Theorem21RealizedWitness := by
  refine ⟨witness_hermitian, ?_, witness_filter_bound, witness_norm⟩
  intro x y h
  simp [kushilevitzGammaW, h]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
