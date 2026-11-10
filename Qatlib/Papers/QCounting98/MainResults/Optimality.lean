/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ApproxPolynomialBlockSensitivityBeal
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveBlockSensitivityQueryBoundBeal
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped Classical BigOperators

namespace Qatlib.Papers.QCounting98.MainResults.Optimality

def thresholdDecision (N t : ℕ) : (Fin N → Bool) → Bool :=
  fun x => (Finset.univ.filter (fun i => x i = true)).card ≤ t

theorem blockSensitivity_thresholdDecision_ge (N t : ℕ) (ht : t ≤ N) :
    N - t ≤ blockSensitivity (thresholdDecision N t) := by
  classical

  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N))) (by simpa using ht)

  let x : Fin N → Bool := fun i => decide (i ∈ S)
  have hfilter : (Finset.univ.filter (fun i : Fin N => x i = true)) = S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, x]
    exact decide_eq_true_iff
  have hxcard : (Finset.univ.filter (fun i : Fin N => x i = true)).card = t := by
    rw [hfilter, hScard]

  let Z : Finset (Fin N) := Finset.univ \ S
  have hZcard : Z.card = N - t := by
    change (Finset.univ \ S).card = N - t
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hScard]

  let 𝔅 : Finset (Finset (Fin N)) := Z.image (fun i => ({i} : Finset (Fin N)))
  have h𝔅card : 𝔅.card = N - t := by
    change (Z.image (fun i => ({i} : Finset (Fin N)))).card = N - t
    rw [Finset.card_image_of_injective _ Finset.singleton_injective, hZcard]

  have hflip_card (i : Fin N) (hiS : i ∉ S) :
      (Finset.univ.filter (fun j : Fin N => flipBlock x ({i} : Finset (Fin N)) j = true)).card
        = t + 1 := by
    have hset :
        (Finset.univ.filter (fun j : Fin N => flipBlock x ({i} : Finset (Fin N)) j = true))
          = insert i S := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, flipBlock,
        Finset.mem_singleton, Finset.mem_insert]
      by_cases hji : j = i
      · subst hji
        simp [x, hiS]
      · simp [x, hji]
    rw [hset, Finset.card_insert_of_notMem hiS, hScard]

  have hSensitive : ∀ B ∈ 𝔅, BlockSensitive (thresholdDecision N t) x B := by
    intro B hB
    obtain ⟨i, hiZ, rfl⟩ := Finset.mem_image.mp hB
    have hiS : i ∉ S := by
      simp only [Z, Finset.mem_sdiff, Finset.mem_univ, true_and] at hiZ
      exact hiZ
    have hxtrue : thresholdDecision N t x = true := by
      unfold thresholdDecision
      rw [hxcard]
      exact decide_eq_true (le_refl t)
    have hflipfalse : thresholdDecision N t (flipBlock x {i}) = false := by
      unfold thresholdDecision
      rw [hflip_card i hiS]
      exact decide_eq_false (by omega)
    unfold BlockSensitive
    rw [hxtrue, hflipfalse]
    decide

  have hDisj : ∀ B₁ ∈ 𝔅, ∀ B₂ ∈ 𝔅, B₁ ≠ B₂ → B₁ ∩ B₂ = ∅ := by
    intro B₁ hB₁ B₂ hB₂ hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB₁
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB₂
    have hij : i ≠ j := by
      intro h
      exact hne (by rw [h])
    exact Finset.singleton_inter_of_notMem (by simpa using hij)

  have hle : 𝔅.card ≤ blockSensitivityAt (thresholdDecision N t) x := by
    unfold blockSensitivityAt
    apply Finset.le_sup
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSensitive, hDisj⟩

  have hsup : blockSensitivityAt (thresholdDecision N t) x
      ≤ blockSensitivity (thresholdDecision N t) := by
    unfold blockSensitivity
    exact Finset.le_sup
      (s := Finset.univ.image
        (fun y => blockSensitivityAt (thresholdDecision N t) y))
      (f := id)
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  rw [h𝔅card] at hle
  exact le_trans hle hsup

theorem thresholdDecision_polynomial_degree_lower
    (N t : ℕ) (ht : t ≤ N) (p : MvPolynomial (Fin N) ℝ)
    (hp0 : ∀ x : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p)
    (hp1 : ∀ x : Fin N → Bool,
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ≤ 1)
    (hpq : ∀ x : Fin N → Bool,
      |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p -
        (if thresholdDecision N t x then (1 : ℝ) else 0)| ≤ 1 / 3) :
    ((N - t : ℕ) : ℝ) ≤ 16 * (p.totalDegree : ℝ) ^ 2 := by
  have hpoly : ∀ x : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ∧
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ≤ 1 ∧
      |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p -
        (if thresholdDecision N t x then (1 : ℝ) else 0)| ≤ 1 / 3 :=
    fun x => ⟨hp0 x, hp1 x, hpq x⟩
  have hbound :=
    approximatePolynomialBlockSensitivity N (thresholdDecision N t) p (1 / 3)
      (by norm_num) (by norm_num) hpoly
  have hbs := blockSensitivity_thresholdDecision_ge N t ht
  have hbscast : ((N - t : ℕ) : ℝ) ≤ (blockSensitivity (thresholdDecision N t) : ℝ) := by
    exact_mod_cast hbs
  nlinarith [hbound, hbscast]

theorem thresholdDecision_boundedError_query_depth_lower
    (N t : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin N × Bool) × W)) (ψ : QState ((Fin N × Bool) × W))
    (hP : observedWellFormed P) (hψ : Normalized ψ) (ht : t ≤ N)
    (herror : ∀ x : Fin N → Bool,
      |observedAcceptance (workspaceBitOracle (W := W) x) P ψ -
        (if thresholdDecision N t x then (1 : ℝ) else 0)| ≤ 1 / 3) :
    N - t ≤ 16 * observedQueryDepth P ^ 2 := by
  have hbs :=
    (adaptiveBlockSensitivityQueryBound N W P ψ (thresholdDecision N t) hP hψ).1 herror
  exact le_trans (blockSensitivity_thresholdDecision_ge N t ht) hbs

theorem thresholdDecision_query_depth_ge_sqrt
    (N t : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin N × Bool) × W)) (ψ : QState ((Fin N × Bool) × W))
    (hP : observedWellFormed P) (hψ : Normalized ψ) (ht : t ≤ N)
    (herror : ∀ x : Fin N → Bool,
      |observedAcceptance (workspaceBitOracle (W := W) x) P ψ -
        (if thresholdDecision N t x then (1 : ℝ) else 0)| ≤ 1 / 3) :
    Real.sqrt ((N - t : ℕ) : ℝ) ≤ 4 * (observedQueryDepth P : ℝ) := by
  have hmain := thresholdDecision_boundedError_query_depth_lower N t W P ψ hP hψ ht herror
  have hcast : ((N - t : ℕ) : ℝ) ≤ 16 * (observedQueryDepth P : ℝ) ^ 2 := by
    exact_mod_cast hmain
  have hroot := Real.sqrt_le_sqrt hcast
  rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
    show Real.sqrt (16 : ℝ) = 4 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)],
    Real.sqrt_sq (Nat.cast_nonneg _)] at hroot

end Qatlib.Papers.QCounting98.MainResults.Optimality
