/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedStat

open scoped BigOperators

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

lemma zoo_counting_two_dimensional_phase_action_col_normSq
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : A * A.conjTranspose = 1) (k : Fin (n + 1)) :
    (∑ i, Complex.normSq (A i k) : ℝ) = 1 := by
  have hcomm : A.conjTranspose * A = 1 := mul_eq_one_comm.mp hA
  have h1 : (∑ i, star (A i k) * A i k : ℂ) = 1 := by
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M k k) hcomm
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    simpa using h
  have h2 : ((∑ i, Complex.normSq (A i k) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum, ← h1]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  exact_mod_cast h2

lemma zoo_counting_two_dimensional_phase_action_overlap_good
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool) :
    (∑ i, star (A i 0) * RankOneReflection.goodPart g (fun i => A i 0) i : ℂ) =
      ((∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : g i <;>
    simp [RankOneReflection.goodPart, h, ← Complex.normSq_eq_conj_mul_self]

lemma zoo_counting_two_dimensional_phase_action_overlap_bad
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool) :
    (∑ i, star (A i 0) * RankOneReflection.badPart g (fun i => A i 0) i : ℂ) =
      ((∑ i, Complex.normSq (RankOneReflection.badPart g (fun i => A i 0) i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : g i <;>
    simp [RankOneReflection.badPart, h, ← Complex.normSq_eq_conj_mul_self]

lemma zoo_counting_two_dimensional_phase_action_bad_normSq
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) :
    (∑ i, Complex.normSq (RankOneReflection.badPart g (fun i => A i 0) i) : ℝ) =
      1 - ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i) := by
  have hcol := zoo_counting_two_dimensional_phase_action_col_normSq A hA 0
  have hsplit : ∀ i : Fin (n + 1), Complex.normSq (A i 0) =
      Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i) +
        Complex.normSq (RankOneReflection.badPart g (fun i => A i 0) i) := by
    intro i
    by_cases h : g i <;> simp [RankOneReflection.goodPart, RankOneReflection.badPart, h]
  rw [← hcol, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
  ring

lemma zoo_counting_two_dimensional_phase_action_collected
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (φ ϕ : ℂ) (hA : A * A.conjTranspose = 1) :
    (RankOneReflection.iterate A g φ ϕ).mulVec
        (RankOneReflection.goodPart g (fun i => A i 0)) =
      (ϕ * ((1 - φ) * ((∑ i, Complex.normSq
          (RankOneReflection.goodPart g (fun i => A i 0) i) : ℝ) : ℂ) - 1)) •
        RankOneReflection.goodPart g (fun i => A i 0) +
      (ϕ * (1 - φ) * ((∑ i, Complex.normSq
          (RankOneReflection.goodPart g (fun i => A i 0) i) : ℝ) : ℂ)) •
        RankOneReflection.badPart g (fun i => A i 0) ∧
    (RankOneReflection.iterate A g φ ϕ).mulVec
        (RankOneReflection.badPart g (fun i => A i 0)) =
      (-((1 - φ) * ((∑ i, Complex.normSq
          (RankOneReflection.goodPart g (fun i => A i 0) i) : ℝ) : ℂ) + φ)) •
        RankOneReflection.badPart g (fun i => A i 0) +
      ((1 - φ) * (1 - ((∑ i, Complex.normSq
          (RankOneReflection.goodPart g (fun i => A i 0) i) : ℝ) : ℂ))) •
        RankOneReflection.goodPart g (fun i => A i 0) := by
  obtain ⟨hgood, hbad⟩ :=
    zoo_counting_good_bad_phase_action n A g φ ϕ (fun i => A i 0) hA
  rw [zoo_counting_two_dimensional_phase_action_overlap_good] at hgood
  rw [zoo_counting_two_dimensional_phase_action_overlap_bad,
    zoo_counting_two_dimensional_phase_action_bad_normSq A g hA] at hbad
  rw [Complex.ofReal_sub, Complex.ofReal_one] at hbad
  constructor
  · funext i
    have hi := congrFun hgood i
    have hp : A i 0 = RankOneReflection.goodPart g (fun i => A i 0) i +
        RankOneReflection.badPart g (fun i => A i 0) i := by
      by_cases h : g i <;> simp [RankOneReflection.goodPart, RankOneReflection.badPart, h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hp] at hi
    rw [hi]
    ring
  · funext i
    have hi := congrFun hbad i
    have hp : A i 0 = RankOneReflection.goodPart g (fun i => A i 0) i +
        RankOneReflection.badPart g (fun i => A i 0) i := by
      by_cases h : g i <;> simp [RankOneReflection.goodPart, RankOneReflection.badPart, h]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at hi ⊢
    rw [hp] at hi
    rw [hi]
    ring

lemma zoo_counting_two_dimensional_phase_action_span_invariant
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (φ ϕ : ℂ) (hA : A * A.conjTranspose = 1) :
    ∀ w ∈ Submodule.span ℂ {RankOneReflection.goodPart g (fun i => A i 0),
        RankOneReflection.badPart g (fun i => A i 0)},
      (RankOneReflection.iterate A g φ ϕ).mulVec w ∈
        Submodule.span ℂ {RankOneReflection.goodPart g (fun i => A i 0),
          RankOneReflection.badPart g (fun i => A i 0)} := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain rfl | rfl : x = RankOneReflection.goodPart g (fun i => A i 0) ∨
          x = RankOneReflection.badPart g (fun i => A i 0) := by
        simpa using hx
      · rw [(zoo_counting_two_dimensional_phase_action_collected A g φ ϕ hA).1]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [(zoo_counting_two_dimensional_phase_action_collected A g φ ϕ hA).2]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  | zero =>
      rw [Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [Matrix.mulVec_add]
      exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih =>
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ r ih

theorem zoo_counting_two_dimensional_phase_action :
    ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (φ ϕ : ℂ),
  A * A.conjTranspose = 1 →
  ‖φ‖ = 1 → ‖ϕ‖ = 1 →
  let ψ : Fin (n + 1) → ℂ := fun i => A i 0;
  let ψa := RankOneReflection.goodPart g ψ;
  let ψb := RankOneReflection.badPart g ψ;
  let a : ℝ := ∑ i, Complex.normSq (ψa i);
  (RankOneReflection.iterate A g φ ϕ).mulVec ψa =
    (ϕ * ((1 - φ) * (a : ℂ) - 1)) • ψa +
      (ϕ * (1 - φ) * (a : ℂ)) • ψb ∧
  (RankOneReflection.iterate A g φ ϕ).mulVec ψb =
    (-((1 - φ) * (a : ℂ) + φ)) • ψb +
      ((1 - φ) * (1 - (a : ℂ))) • ψa := by
  intro n A g φ ϕ hA _hφ _hϕ
  exact zoo_counting_two_dimensional_phase_action_collected A g φ ϕ hA

theorem zoo_counting_two_dimensional_phase_action_contract :
    Lemma3RestrictedSpec.expected :=
  zoo_counting_two_dimensional_phase_action

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
