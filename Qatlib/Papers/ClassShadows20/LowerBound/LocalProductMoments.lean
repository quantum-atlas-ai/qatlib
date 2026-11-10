/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.LocalShotPauliMomentSubgoalStat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliPairRecords
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qatlib.Papers.ClassShadows20.LowerBound
open Matrix
open scoped Classical BigOperators ComplexOrder

noncomputable def localPauliOverlap {J : Type} (Uf : J → Operator 2)
    (P : Operator 2) (a : Option (Fin 3)) (u : J) : ℝ :=
  match a with
  | none => 1
  | some b => (Matrix.trace (pauliMatrix b * (Uf u)ᴴ * P * Uf u)).re

lemma localShotValue_factor {n : ℕ} {J : Type} (Uf : J → Operator 2)
    (w : ℝ) (ψ : Fin n → Operator 2) (uw : Fin n → J)
    (hψ : ∀ j, IsPureDensityOperator (ψ j))
    (hU : ∀ j, Uf (uw j) ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (ε : ℝ) (a : Fin n → Option (Fin 3)) :
    localShotValue Uf w ψ uw (theorem6CodeState n ε a) =
      w * (1 + 3 * ε * ∏ j, localPauliOverlap Uf (ψ j) (a j) (uw j)) := by
  let Q : Fin n → Operator 2 := fun j => (Uf (uw j))ᴴ * ψ j * Uf (uw j)
  have ht : ∀ j, Matrix.trace (Q j) = 1 := by
    intro j
    have hu : Uf (uw j) * (Uf (uw j))ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hU j)
    dsimp [Q]
    rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, (hψ j).1.2]
  have hv : ∀ j,
      Matrix.trace (Q j * tensorPauliWordFactor (a j)) =
        (localPauliOverlap Uf (ψ j) (a j) (uw j) : ℂ) := by
    intro j
    cases ha : a j with
    | none => simp [tensorPauliWordFactor, ht, localPauliOverlap]
    | some b =>
      have hi : (Matrix.trace (pauliMatrix b * Q j)).im = 0 :=
        pauli_pair_hermitian_trace_real _ _ (pauliMatrix_conjTranspose b)
          ((hψ j).1.1.conjTranspose_mul_mul_same (Uf (uw j))).isHermitian
      rw [Matrix.trace_mul_comm]
      simp only [tensorPauliWordFactor, localPauliOverlap]
      apply Complex.ext
      · simp [Q, Matrix.mul_assoc]
      · simpa only [Complex.ofReal_im, Q, Matrix.mul_assoc] using hi
  have hcycle := Matrix.trace_mul_cycle
    (tensorPauliProduct n ψ * tensorPauliProduct n (fun j => Uf (uw j)))
    (theorem6CodeState n ε a) (tensorPauliProduct n (fun j => Uf (uw j)))ᴴ
  have hQ : (tensorPauliProduct n (fun j => Uf (uw j)))ᴴ *
      (tensorPauliProduct n ψ * tensorPauliProduct n (fun j => Uf (uw j))) =
        tensorPauliProduct n Q := by
    rw [tensorPauliProduct_conjTranspose, ← Matrix.mul_assoc,
      tensorPauliProduct_mul, tensorPauliProduct_mul]
  unfold localShotValue
  rw [show Matrix.trace (tensorPauliProduct n ψ *
      (tensorPauliProduct n (fun j => Uf (uw j)) * theorem6CodeState n ε a *
        (tensorPauliProduct n (fun j => Uf (uw j)))ᴴ)) =
      Matrix.trace (tensorPauliProduct n Q * theorem6CodeState n ε a) by
        simpa only [Matrix.mul_assoc, hQ] using hcycle]
  rw [theorem6CodeState, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    tensorPauliWord, tensorPauliProduct_mul, tensorPauliProduct_trace,
    tensorPauliProduct_trace]
  simp_rw [ht, hv]
  simp only [← Complex.ofReal_prod, Finset.prod_const_one, Complex.add_re,
    Complex.smul_re, Complex.ofReal_re, smul_eq_mul, Complex.one_re]
  have hd : (2 ^ n : ℝ) ≠ 0 := by positivity
  field_simp

lemma localPauliOverlap_product_moments {n k : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (κ : FinDist J) (Uf : J → Operator 2) (ψ : Fin n → Operator 2)
    (a : Fin n → Option (Fin 3)) (hk : 1 ≤ k) (hS : tensorPauliWeight a = k)
    (hm : ∀ j b, ∑ u, κ.prob u * localPauliOverlap Uf (ψ j) (some b) u = 0)
    (hs : ∀ j b, ∑ u, κ.prob u * (localPauliOverlap Uf (ψ j) (some b) u)^2 = 1/3) :
    (∑ uw, κ.probOf uw * ∏ j, localPauliOverlap Uf (ψ j) (a j) (uw j)) = 0 ∧
    (∑ uw, κ.probOf uw * (∏ j, localPauliOverlap Uf (ψ j) (a j) (uw j))^2) =
      1 / (3 ^ k : ℝ) := by
  have hmean : ∀ j, ∑ u, κ.prob u * localPauliOverlap Uf (ψ j) (a j) u =
      if (a j).isSome then 0 else 1 := by
    intro j
    cases a j with
    | none => simpa [localPauliOverlap] using κ.sum_one
    | some b => simpa using hm j b
  have hsecond : ∀ j, ∑ u, κ.prob u * (localPauliOverlap Uf (ψ j) (a j) u)^2 =
      (1/3 : ℝ)^(if (a j).isSome then 1 else 0) := by
    intro j
    cases a j with
    | none => simpa [localPauliOverlap] using κ.sum_one
    | some b => simpa using hs j b
  have hsupport : ∃ j, (a j).isSome = true := by
    by_contra hn
    have hz : tensorPauliWeight a = 0 := by
      unfold tensorPauliWeight
      apply Finset.sum_eq_zero
      intro j _
      have hn' : ¬ (a j).isSome = true := fun hj => hn ⟨j, hj⟩
      rw [if_neg hn']
    omega
  constructor
  · rw [κ.expect_prod, Finset.prod_congr rfl (fun j _ => hmean j)]
    obtain ⟨j, hj⟩ := hsupport
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  · simp_rw [← Finset.prod_pow]
    rw [κ.expect_prod (fun j u => (localPauliOverlap Uf (ψ j) (a j) u)^2),
      Finset.prod_congr rfl (fun j _ => hsecond j),
      Finset.prod_pow_eq_pow_sum]
    change (1 / 3 : ℝ)^tensorPauliWeight a = _
    rw [hS, div_pow, one_pow]

lemma local_affine_moments {U : Type} [Fintype U] (p Z : U → ℝ)
    (k : ℕ) (hp : ∑ u, p u = 1) (hZ : ∑ u, p u * Z u = 0)
    (hZ2 : ∑ u, p u * (Z u)^2 = 1 / (3 ^ k : ℝ))
    (w ε : ℝ) :
    (∑ u, p u * (w * (1 + 3 * ε * Z u))) = w ∧
    (∑ u, p u * (w * (1 + 3 * ε * Z u))^2) =
      w^2 * (1 + 9 * ε^2 / (3 ^ k : ℝ)) := by
  constructor
  · calc
      _ = w * (∑ u, p u) + (3 * w * ε) * (∑ u, p u * Z u) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = w := by rw [hp, hZ]; ring
  · calc
      _ = w^2 * (∑ u, p u) + (6 * w^2 * ε) * (∑ u, p u * Z u) +
          (9 * w^2 * ε^2) * (∑ u, p u * (Z u)^2) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by rw [hp, hZ, hZ2]; ring

end Qatlib.Papers.ClassShadows20.LowerBound
