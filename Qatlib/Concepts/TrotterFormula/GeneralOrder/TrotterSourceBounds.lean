/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Qatlib.Concepts.LchsSimulation.LchsRep.ImaginaryTimeProduct
import Qatlib.Concepts.InteractionEvo.CayleyTransform
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LchsSimulation.LchsRep
open Qatlib.Concepts.InteractionEvo.CayleyTransform

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open scoped ComplexConjugate
set_option warningAsError false

private noncomputable def fourthOrderSegments {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil ((100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε)) ^ ((1 : ℝ) / 4)))

private noncomputable def generalOrderSegments {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε : ℝ) : ℕ :=
  max 1
    (Nat.ceil
      ((((Nat.factorial (2 * (k + 1)) : ℝ) *
          Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
            (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^
        ((1 : ℝ) / (2 * (k + 1)))))

private theorem exp_smul_negI_eq_evolution {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) :
    NormedSpace.exp (t • ((-Complex.I) • A)) = HamiltonianEvolution A t := by
  unfold HamiltonianEvolution
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul]
  ring

private theorem antiHermitian_smul_real {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (a : ℝ) (hX : Xᴴ = -X) : (a • X)ᴴ = -(a • X) := by
  change star (a • X) = -(a • X)
  simp only [star_smul, star_trivial, Matrix.star_eq_conjTranspose, hX, smul_neg]

private theorem antiHermitian_sum {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (hxs : ∀ X ∈ xs, Xᴴ = -X) : xs.sumᴴ = -xs.sum := by
  induction xs with
  | nil => simp
  | cons X xs ih =>
    simp only [List.sum_cons, Matrix.conjTranspose_add, hxs X (by simp),
      ih (by intro Y hY; exact hxs Y (by simp [hY])), neg_add]

private theorem rpow_root_pow {u e : ℝ} (hu : 0 ≤ u) {m : ℕ} (_hm : m ≠ 0)
    (he : e * (m : ℝ) = 1) : (u ^ e) ^ m = u := by
  have h1 : (u ^ e) ^ m = (u ^ e) ^ ((m : ℝ)) := (Real.rpow_natCast (u ^ e) m).symm
  rw [h1, ← Real.rpow_mul hu, he, Real.rpow_one]

private theorem commutatorSum_le_two_sq {D Λ : ℕ} (H : Fin Λ → Operator D) (b : ℝ)
    (hb : ∀ i, ‖H i‖ ≤ b) : pfCommutatorSum H ≤ 2 * (Λ : ℝ) ^ 2 * b ^ 2 := by
  have hpair : ∀ j k : Fin Λ,
      (if j < k then ‖pfComm (H j) (H k)‖ else 0) ≤ 2 * b ^ 2 := by
    intro j k
    by_cases hjk : j < k
    · rw [if_pos hjk]
      have hAB : ‖pfComm (H j) (H k)‖ ≤ ‖H j‖ * ‖H k‖ + ‖H k‖ * ‖H j‖ := by
        rw [pfComm]
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      have hbb : ‖H j‖ * ‖H k‖ + ‖H k‖ * ‖H j‖ ≤ 2 * b ^ 2 := by
        have hj := hb j
        have hk := hb k
        have hb0 : 0 ≤ b := (norm_nonneg (H j)).trans hj
        have hmul : ‖H j‖ * ‖H k‖ ≤ b * b :=
          mul_le_mul hj hk (norm_nonneg _) hb0
        nlinarith [hmul]
      exact hAB.trans hbb
    · rw [if_neg hjk]
      positivity
  have hsum : pfCommutatorSum H ≤ ∑ _j : Fin Λ, ∑ _k : Fin Λ, 2 * b ^ 2 := by
    unfold pfCommutatorSum
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hpair j k
  have hcard : (∑ _j : Fin Λ, ∑ _k : Fin Λ, 2 * b ^ 2) = 2 * (Λ : ℝ) ^ 2 * b ^ 2 := by
    simp [Finset.sum_const, Fintype.card_fin, sq]
    ring
  exact hsum.trans_eq hcard

theorem clause19 : Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.GeometricCostSpec := by
  intro D Λ r b d occ F t ε price hFR hB hH hr hε
  have hb : ∀ i, ‖(F i).op‖ ≤ b := hB.1
  have hCS := commutatorSum_le_two_sq (fun i => (F i).op) b hb
  refine ⟨hCS, ?_, ?_, ?_, ?_⟩
  · exact product_formula_finite_family_segmented D Λ r (fun i => (F i).op) t hr hH
  · have hr' : 0 < finiteRangeSegments Λ b t ε := by
      unfold finiteRangeSegments
      omega
    have herr := product_formula_finite_family_segmented D Λ
      (finiteRangeSegments Λ b t ε) (fun i => (F i).op) t hr' hH
    have hword := product_formula_actual_word_and_tariffs D Λ
      (finiteRangeSegments Λ b t ε) (fun i => (F i).op) t price hH
    refine ⟨?_, hword.2.1⟩
    have hrceil : t ^ 2 * (2 * (Λ : ℝ) ^ 2 * b ^ 2) / ε ≤
        ((finiteRangeSegments Λ b t ε : ℕ) : ℝ) := by
      unfold finiteRangeSegments
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_max_iff.mpr (Or.inr (le_refl _))
    have hcast : (0 : ℝ) ≤ ((finiteRangeSegments Λ b t ε : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpos : (0 : ℝ) < 2 * ((finiteRangeSegments Λ b t ε : ℕ) : ℝ) := by positivity
    have hge : t ^ 2 * (2 * (Λ : ℝ) ^ 2 * b ^ 2) ≤
        ε * (2 * ((finiteRangeSegments Λ b t ε : ℕ) : ℝ)) := by
      have heq : ε * (t ^ 2 * (2 * (Λ : ℝ) ^ 2 * b ^ 2) / ε) =
          t ^ 2 * (2 * (Λ : ℝ) ^ 2 * b ^ 2) := by
        field_simp
      have hK : (0 : ℝ) ≤ t ^ 2 * (2 * (Λ : ℝ) ^ 2 * b ^ 2) := by positivity
      calc t ^ 2 * (2 * (Λ : ℝ) ^ 2 * b ^ 2)
          = ε * (t ^ 2 * (2 * (Λ : ℝ) ^ 2 * b ^ 2) / ε) := heq.symm
        _ ≤ ε * ((finiteRangeSegments Λ b t ε : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hrceil hε.le
        _ ≤ ε * (2 * ((finiteRangeSegments Λ b t ε : ℕ) : ℝ)) := by
            nlinarith [hcast, hε.le]
    refine herr.trans ?_
    refine le_trans (mul_le_mul_of_nonneg_left hCS ?_) ?_
    · exact div_nonneg (by positivity) hpos.le
    · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact hge
  · refine ⟨List.ofFn (fun i : Fin Λ => [i]), ?_, ?_, ?_⟩
    · intro i
      refine List.mem_flatten.mpr ⟨[i], List.mem_ofFn.mpr ⟨i, rfl⟩, by simp⟩
    · intro l hl
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
      intro x hx y hy hxy
      simp only [List.mem_singleton] at hx hy
      rw [hx, hy] at hxy
      exact absurd rfl hxy
    · simp
  · exact (product_formula_actual_word_and_tariffs D Λ r (fun i => (F i).op) t price hH).2.2.1

private theorem recursiveSuzuki_matched_error {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) (hr : 0 < r) :
    ‖(Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord hs k t r).prod -
        NormedSpace.exp (t • hs.sum)‖ ≤
      ((Nat.factorial (2 * (k + 1)) : ℝ) *
        Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
          (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
        |t| ^ (2 * (k + 1) + 1)) /
      ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * (r : ℝ) ^ (2 * (k + 1))) := by
  have hword : (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord hs k t r).prod =
      Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzukiExponentialWord
        (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (t / r) ^ r :=
    Qatlib.Concepts.TrotterFormula.GeneralOrder.pf_segment_word_prod (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) t r
  rw [hword]
  exact Qatlib.Concepts.TrotterFormula.GeneralOrder.pf_matched_word_segmented_skew
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) hs.sum (2 * (k + 1)) r t
    (by omega) hr
    (fun n hn => Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursive_suzuki_all_even_order_coefficients I hs k n hn)
    (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators_antiHermitian hs k hhs)
    (antiHermitian_sum hs hhs)

theorem clause17 : ∀ (I : Type) [Fintype I] [DecidableEq I],
    @Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.GeneralOrderWordBoundSpec I _ _ ∧
      ∀ (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε : ℝ),
        (∀ X ∈ hs, Xᴴ = -X) → 0 < ε →
          ‖(Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiWord hs k t
              (generalOrderSegments hs k t ε)).prod -
            NormedSpace.exp (t • hs.sum)‖ ≤ ε := by
  intro I _ _
  refine ⟨?_, ?_⟩
  · intro hs k r t price hhs hr
    obtain ⟨hu, hl, he⟩ :=
      Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursive_suzuki_actual_simulation_and_cost I hs k r t hhs hr
    refine ⟨hu, hl, ?_, ?_, ?_⟩
    · exact he
    · exact recursiveSuzuki_matched_error hs k r t hhs hr
    · simp [List.map_flatten, List.map_replicate, List.sum_flatten, List.sum_replicate]
  · intro hs k t ε hhs hε
    have hr' : 0 < generalOrderSegments hs k t ε := by
      unfold generalOrderSegments
      omega
    have hα : (0 : ℝ) ≤ Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
        (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hbound := recursiveSuzuki_matched_error hs k
      (generalOrderSegments hs k t ε) t hhs hr'

    have hu0 : (0 : ℝ) ≤
        (((Nat.factorial (2 * (k + 1)) : ℝ) *
            Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
              (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
            |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) := by
      have hn : (0 : ℝ) ≤ (Nat.factorial (2 * (k + 1)) : ℝ) *
          Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
            (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1) := by
        exact mul_nonneg (mul_nonneg (by positivity) hα) (by positivity)
      have hd : (0 : ℝ) < (Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε := by positivity
      exact div_nonneg hn hd.le
    have hrc : (((Nat.factorial (2 * (k + 1)) : ℝ) *
            Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
              (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
            |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^ ((1 : ℝ) / (2 * (k + 1))) ≤
        ((generalOrderSegments hs k t ε : ℕ) : ℝ) := by
      unfold generalOrderSegments
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_max_iff.mpr (Or.inr (le_refl _))
    have hrm : (((Nat.factorial (2 * (k + 1)) : ℝ) *
            Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
              (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
            |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ≤
        ((generalOrderSegments hs k t ε : ℕ) : ℝ) ^ (2 * (k + 1)) := by
      have hkey : ((((Nat.factorial (2 * (k + 1)) : ℝ) *
            Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
              (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
            |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) ^ ((1 : ℝ) / (2 * (k + 1)))) ^
            (2 * (k + 1)) =
          (((Nat.factorial (2 * (k + 1)) : ℝ) *
            Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
              (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
            |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε)) :=
        rpow_root_pow hu0 (by positivity) (by push_cast; field_simp)
      refine le_trans hkey.symm.le
        (pow_le_pow_left₀ (Real.rpow_nonneg hu0 _) hrc (2 * (k + 1)))

    have hB0 : (0 : ℝ) ≤ (Nat.factorial (2 * (k + 1) + 1) : ℝ) := by positivity
    have hden : (0 : ℝ) < (Nat.factorial (2 * (k + 1) + 1) : ℝ) *
        ((generalOrderSegments hs k t ε : ℕ) : ℝ) ^ (2 * (k + 1)) := by positivity
    refine hbound.trans ?_
    rw [div_le_iff₀ hden]
    have hf : ε * ((Nat.factorial (2 * (k + 1) + 1) : ℝ) *
        (((Nat.factorial (2 * (k + 1)) : ℝ) *
            Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
              (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
            |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε))) =
        (Nat.factorial (2 * (k + 1)) : ℝ) *
          Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
            (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1) := by
      have hBne : ((Nat.factorial (2 * (k + 1) + 1) : ℝ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      field_simp
    calc (Nat.factorial (2 * (k + 1)) : ℝ) *
          Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
            (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
          |t| ^ (2 * (k + 1) + 1)
          = ε * ((Nat.factorial (2 * (k + 1) + 1) : ℝ) *
              (((Nat.factorial (2 * (k + 1)) : ℝ) *
            Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaSelf
              (Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
            |t| ^ (2 * (k + 1) + 1)) /
          ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * ε))) := hf.symm
      _ ≤ ε * ((Nat.factorial (2 * (k + 1) + 1) : ℝ) *
            ((generalOrderSegments hs k t ε : ℕ) : ℝ) ^ (2 * (k + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrm hB0) hε.le

theorem walkGoal : ∀ (I : Type) [Fintype I] [DecidableEq I],
    @Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.FourthOrderWordBoundSpec I _ _ ∧
      ∀ (A B : Matrix I I ℂ) (t ε : ℝ),
        A.IsHermitian → B.IsHermitian → 0 < ε →
          ‖Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Run A B t (fourthOrderSegments A B t ε) -
              Qatlib.Foundations.PureStateMath.HamiltonianEvolution (A + B) t‖ ≤ ε := by
  intro I _ _
  refine ⟨?_, ?_⟩
  · intro A B t r price hA hB hr
    have hmain :=
      Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki_fourth_order_actual_word_and_cost I A B t r hA hB hr
    have hXanti : ((-Complex.I) • A)ᴴ = -((-Complex.I) • A) := by
      rw [Matrix.conjTranspose_smul, hA.eq]
      simp
    have hYanti : ((-Complex.I) • B)ᴴ = -((-Complex.I) • B) := by
      rw [Matrix.conjTranspose_smul, hB.eq]
      simp
    have hXYanti : ((-Complex.I) • A + (-Complex.I) • B)ᴴ =
        -((-Complex.I) • A + (-Complex.I) • B) := by
      rw [Matrix.conjTranspose_add, hXanti, hYanti, neg_add]
    have hgens : ∀ Z ∈ Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Generators
        ((-Complex.I) • A) ((-Complex.I) • B), Zᴴ = -Z := by
      intro Z hZ
      simp only [Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Generators, List.mem_append,
          or_assoc] at hZ
      rcases hZ with h1 | h2 | h3 | h4 | h5
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        rcases h1 with h | h | h <;> subst h
        all_goals first
          | exact antiHermitian_smul_real _ _ hXanti
          | exact antiHermitian_smul_real _ _ hYanti
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with h | h | h <;> subst h
        all_goals first
          | exact antiHermitian_smul_real _ _ hXanti
          | exact antiHermitian_smul_real _ _ hYanti
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
        rcases h3 with h | h | h <;> subst h
        all_goals first
          | exact antiHermitian_smul_real _ _ hXanti
          | exact antiHermitian_smul_real _ _ hYanti
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
        rcases h4 with h | h | h <;> subst h
        all_goals first
          | exact antiHermitian_smul_real _ _ hXanti
          | exact antiHermitian_smul_real _ _ hYanti
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h5
        rcases h5 with h | h | h <;> subst h
        all_goals first
          | exact antiHermitian_smul_real _ _ hXanti
          | exact antiHermitian_smul_real _ _ hYanti
    refine ⟨hmain.1, hmain.2.1, hmain.2.2, ?_, ?_, ?_, ?_⟩
    · have hword : Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Run A B t r =
          Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzukiExponentialWord
            (Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Generators ((-Complex.I) • A) ((-Complex.I) • B))
            (t / r) ^ r := by
        rw [Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Run_eq_power,
          Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Generators_actual_word]
      have htarget : NormedSpace.exp (t • ((-Complex.I) • A + (-Complex.I) • B)) =
          Qatlib.Foundations.PureStateMath.HamiltonianEvolution (A + B) t := by
        rw [show (-Complex.I) • A + (-Complex.I) • B = (-Complex.I) • (A + B) from
          (smul_add _ _ _).symm, exp_smul_negI_eq_evolution]
      rw [hword, ← htarget]
      exact Qatlib.Concepts.TrotterFormula.GeneralOrder.pf_matched_word_segmented_skew
        (Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Generators ((-Complex.I) • A) ((-Complex.I) • B))
        ((-Complex.I) • A + (-Complex.I) • B) 4 r t (by norm_num) hr
        (fun n hn => Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Generators_first_five_coefficients
          _ _ n (by omega))
        hgens hXYanti
    · have hmode :=
        Qatlib.Concepts.TrotterFormula.GeneralOrder.pfConjWord_ordered_remainder_norm_mode true
          (Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki4Generators ((-Complex.I) • A) ((-Complex.I) • B))
          ((-Complex.I) • A + (-Complex.I) • B) 6 (t / r)
          (fun _ Z hZ => hgens Z hZ)
      rw [Qatlib.Concepts.TrotterFormula.GeneralOrder.pfCommAlphaOrderedV2_scaled]
      simpa using! hmode
    · have h15 : Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.suzuki4SlotLabels.length = 15 := by
        decide
      simp [List.length_flatten, h15]
      omega
    · have hL : Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.suzuki4SlotLabels =
          [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0] := by decide
      have hsumL : (Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.suzuki4SlotLabels.map price).sum =
          10 * price 0 + 5 * price 1 := by
        rw [hL]
        simp
        ring
      simp [List.map_flatten, List.map_replicate, List.sum_flatten, List.sum_replicate,
        hsumL]
  · intro A B t ε hA hB hε
    have hr' : 0 < fourthOrderSegments A B t ε := by
      unfold fourthOrderSegments
      omega
    have hbound :=
      (Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzuki_fourth_order_actual_word_and_cost I A B t
        (fourthOrderSegments A B t ε) hA hB hr').2.2
    have hbase : (0 : ℝ) ≤
        100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε) := by
      have hN : (0 : ℝ) ≤ ‖A‖ + ‖B‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
      positivity
    have hu0 : (0 : ℝ) ≤
        (100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_nonneg hbase _
    have hrc : (100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε)) ^ ((1 : ℝ) / 4) ≤
        ((fourthOrderSegments A B t ε : ℕ) : ℝ) := by
      unfold fourthOrderSegments
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_max_iff.mpr (Or.inr (le_refl _))
    have hrm : 100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε) ≤
        ((fourthOrderSegments A B t ε : ℕ) : ℝ) ^ 4 := by
      have hkey : ((100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε)) ^ ((1 : ℝ) / 4)) ^ 4 =
          100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε) :=
        rpow_root_pow hbase (by norm_num : (4 : ℕ) ≠ 0)
          (by norm_num : ((1 : ℝ) / 4) * (4 : ℝ) = 1)
      refine le_trans hkey.symm.le (pow_le_pow_left₀ hu0 hrc 4)
    have hrpos : (0 : ℝ) < ((fourthOrderSegments A B t ε : ℕ) : ℝ) ^ 4 := by
      have : (1 : ℝ) ≤ ((fourthOrderSegments A B t ε : ℕ) : ℝ) := by
        unfold fourthOrderSegments
        exact_mod_cast le_max_left _ _
      positivity
    refine hbound.trans ?_
    rw [div_le_iff₀ hrpos]
    have hfield : ε * (100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε)) =
        100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5) := by
      field_simp
    calc 100 * (‖A‖ + ‖B‖) ^ 5 * |t| ^ 5
        = ε * (100 * ((‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / ε)) := by rw [hfield]; ring
      _ ≤ ε * ((fourthOrderSegments A B t ε : ℕ) : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left hrm hε.le

private theorem star_eq_conj (z : ℂ) : star z = conj z := (starRingEnd_apply z).symm

private theorem schattenOne_eq_traceNorm {D : ℕ} (A : Operator D) :
    SchattenOne A = Matrix.traceNorm A := by
  have hpsd : (A.conjTranspose * A).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self A
  rw [Matrix.traceNorm, SchattenOne,
    CFC.sqrt_eq_real_sqrt _ (Matrix.PosSemidef.nonneg hpsd),
    cfcₙ_eq_cfc (by fun_prop) (by simp)]
  rfl

private theorem sum_conj_mul_self_eq {D : ℕ} (w : Fin D → ℂ) :
    (∑ i, conj (w i) * w i) = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.conj_mul (w i), Complex.ofReal_pow]
  rfl

private theorem sum_mul_conj_self_eq {D : ℕ} (w : Fin D → ℂ) :
    (∑ i, w i * conj (w i)) = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.mul_conj (w i), Complex.ofReal_pow]
  rfl

private theorem traceNorm_rank1 {D : ℕ} (x w : Fin D → ℂ) :
    Matrix.traceNorm (Matrix.of fun i j => x i * conj (w j))
      = Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ i, ‖w i‖ ^ 2) := by
  set sx : ℝ := ∑ i, ‖x i‖ ^ 2 with hsxdef
  set sw : ℝ := ∑ i, ‖w i‖ ^ 2 with hswdef
  have hsx0 : 0 ≤ sx := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsw0 : 0 ≤ sw := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hXX : ((Matrix.of fun i j => x i * conj (w j))ᴴ * (Matrix.of fun i j => x i * conj (w j)))
      = ((sx : ℂ) • (Matrix.of fun i j => w i * conj (w j))) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, star_eq_conj]
    have hterm : ∀ k : Fin D,
        (conj (x k * conj (w i))) * (x k * conj (w j))
            = (w i * (conj (x k) * x k)) * conj (w j) := by
      intro k
      rw [map_mul, Complex.conj_conj]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul, ← Finset.mul_sum,
      sum_conj_mul_self_eq]
    ring
  rcases eq_or_lt_of_le hsw0 with h0 | h0
  · have hsw0' : sw = 0 := h0.symm
    have hw0 : w = 0 := by
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (‖w i‖))).mp hsw0' i (Finset.mem_univ i)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    have hX0 : (Matrix.of fun i j => x i * conj (w j)) = 0 := by
      ext i j; simp [hw0]
    rw [hX0, Matrix.traceNorm_zero, hsw0']
    simp
  · set c := Real.sqrt sw with hcdef
    have hc0 : 0 < c := Real.sqrt_pos.mpr h0
    have hcne : c ≠ 0 := ne_of_gt hc0
    have hcsw : c * c = sw := Real.mul_self_sqrt hsw0
    set γ : ℂ := ((c : ℝ) : ℂ)⁻¹ with hγdef
    have hconjγ : ∀ i, conj (γ * w i) = γ * conj (w i) := by
      intro i
      rw [hγdef, map_mul, Complex.conj_inv, Complex.conj_ofReal]
    have hnormγ : ‖γ‖ = c⁻¹ := by
      rw [hγdef, norm_inv, Complex.norm_of_nonneg hc0.le]
    have hwn1 : ∑ i, ‖γ * w i‖ ^ 2 = 1 := by
      have hterm : ∀ i : Fin D, ‖γ * w i‖ ^ 2 = ‖γ‖ ^ 2 * ‖w i‖ ^ 2 := by
        intro i; rw [norm_mul, mul_pow]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, hnormγ, ← hswdef,
        ← hcsw]
      field_simp
    set Pn : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun i j => (γ * w i) * conj (γ * w j)
      with hPndef
    have hPP : Pn * Pn = Pn := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.of_apply, hPndef]
      have hterm : ∀ k : Fin D,
          ((γ * w i) * conj (γ * w k)) * ((γ * w k) * conj (γ * w j))
              = ((γ * w i) * (conj (γ * w k) * (γ * w k))) * conj (γ * w j) :=
        fun k => by ring
      rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul, ← Finset.mul_sum,
        sum_conj_mul_self_eq, hwn1, Complex.ofReal_one, mul_one]
    have hγγ : ((sw : ℝ) : ℂ) * (γ * γ) = 1 := by
      rw [hγdef, ← mul_inv, ← Complex.ofReal_mul, ← hcsw]
      exact_mod_cast (mul_inv_cancel₀ (mul_ne_zero hcne hcne))
    have hPscale : (Matrix.of fun i j => w i * conj (w j)) = ((sw : ℝ) : ℂ) • Pn := by
      ext i j
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hPndef]
      rw [hconjγ j]
      have h4 : ((sw : ℝ) : ℂ) * ((γ * w i) * (γ * conj (w j)))
          = ((sw : ℝ) : ℂ) * (γ * γ) * (w i * conj (w j)) := by ring
      rw [h4, hγγ, one_mul]
    have hXXn : ((Matrix.of fun i j => x i * conj (w j))ᴴ * (Matrix.of fun i j => x i * conj (w j)))
        = ((sx * sw : ℝ) : ℂ) • Pn := by
      rw [hXX, hPscale, smul_smul, ← Complex.ofReal_mul]
    have hDpos : 0 < D := by
      by_contra hD
      have hD0 : D = 0 := Nat.le_zero.mp (Nat.not_lt.mp hD)
      haveI hempty : IsEmpty (Fin D) := by rw [hD0]; exact inferInstance
      have huniv : (Finset.univ : Finset (Fin D)) = ∅ := Finset.univ_eq_empty
      rw [hswdef, huniv, Finset.sum_empty] at h0
      exact absurd h0 (lt_irrefl 0)
    obtain ⟨k₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hDpos
    set C : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun (k : Fin D) (j : Fin D) =>
      if k = k₀ then conj (γ * w j) else 0 with hCdef
    have hCPn : Cᴴ * C = Pn := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply, hPndef,
        hCdef, star_eq_conj]
      have hterm : ∀ k : Fin D,
          conj (if k = k₀ then conj (γ * w i) else 0) *
              (if k = k₀ then conj (γ * w j) else 0)
            = if k = k₀ then (γ * w i) * conj (γ * w j) else 0 := by
        intro k; by_cases hk : k = k₀ <;> simp [hk]
      rw [Finset.sum_congr rfl (fun k _ => hterm k),
        Finset.sum_ite_eq' Finset.univ k₀ (fun k => (γ * w i) * conj (γ * w j))]
      simp
    have hPnpsd : Pn.PosSemidef := by
      rw [← hCPn]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    have hz : Real.sqrt (sx * sw) * Real.sqrt (sx * sw) = sx * sw :=
      Real.mul_self_sqrt (mul_nonneg hsx0 hsw0)
    have hPSDz : (((Real.sqrt (sx * sw) : ℝ) : ℂ) • Pn).PosSemidef := by
      have hC' : (((Real.sqrt (Real.sqrt (sx * sw)) : ℝ) : ℂ) • C)ᴴ
          * (((Real.sqrt (Real.sqrt (sx * sw)) : ℝ) : ℂ) • C)
          = ((Real.sqrt (sx * sw) : ℝ) : ℂ) • Pn := by
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          star_eq_conj, Complex.conj_ofReal, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (Real.sqrt_nonneg _), hCPn]
      rw [← hC']
      exact Matrix.posSemidef_conjTranspose_mul_self _
    have hsqr : CFC.sqrt (((Matrix.of fun i j => x i * conj (w j))ᴴ *
        (Matrix.of fun i j => x i * conj (w j))))
        = ((Real.sqrt (sx * sw) : ℝ) : ℂ) • Pn := by
      refine CFC.sqrt_unique ?_ ?_
      · have hsmul : (((Real.sqrt (sx * sw) : ℝ) : ℂ) • Pn) * (((Real.sqrt (sx * sw) : ℝ) : ℂ) • Pn)
          = (((Real.sqrt (sx * sw) : ℝ) : ℂ) * ((Real.sqrt (sx * sw) : ℝ) : ℂ)) • (Pn * Pn) := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
          have hterm : ∀ k : Fin D,
              (((Real.sqrt (sx * sw) : ℝ) : ℂ) * Pn i k) *
                  (((Real.sqrt (sx * sw) : ℝ) : ℂ) * Pn k j)
                = (((Real.sqrt (sx * sw) : ℝ) : ℂ) * ((Real.sqrt (sx * sw) : ℝ) : ℂ)) *
                    (Pn i k * Pn k j) := fun k => by ring
          rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
        rw [hsmul, hPP, ← Complex.ofReal_mul, hz]
        exact hXXn.symm
      · exact Matrix.nonneg_iff_posSemidef.mpr hPSDz
    rw [Matrix.traceNorm, hsqr, Matrix.trace_smul]
    have htr : Pn.trace = 1 := by
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.of_apply, hPndef]
      rw [sum_mul_conj_self_eq, hwn1, Complex.ofReal_one]
    rw [htr, smul_eq_mul, mul_one, hcdef, Real.sqrt_mul hsx0]
    exact Complex.ofReal_re _

private theorem traceNorm_outerProduct_sub_le {D : ℕ} (a b : Fin D → ℂ)
    (ha : ∑ i, ‖a i‖ ^ 2 = 1) (hb : ∑ i, ‖b i‖ ^ 2 = 1) :
    Matrix.traceNorm (outerProduct a - outerProduct b)
      ≤ 2 * Real.sqrt (∑ i, ‖a i - b i‖ ^ 2) := by
  have hsplit : outerProduct a - outerProduct b
      = (Matrix.of fun i j => (a i - b i) * conj (a j))
        + (Matrix.of fun i j => b i * conj (a j - b j)) := by
    ext i j
    simp only [outerProduct, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, map_sub]
    ring
  have h1 : Matrix.traceNorm (Matrix.of fun i j => (a i - b i) * conj (a j))
      = Real.sqrt (∑ i, ‖a i - b i‖ ^ 2) := by
    rw [traceNorm_rank1, ha, Real.sqrt_one, mul_one]
  have h2 : Matrix.traceNorm (Matrix.of fun i j => b i * conj (a j - b j))
      = Real.sqrt (∑ i, ‖a i - b i‖ ^ 2) := by
    rw [traceNorm_rank1, hb, Real.sqrt_one, one_mul]
  rw [hsplit]
  have hsum : Matrix.traceNorm (Matrix.of fun i j => (a i - b i) * conj (a j))
      + Matrix.traceNorm (Matrix.of fun i j => b i * conj (a j - b j))
      ≤ 2 * Real.sqrt (∑ i, ‖a i - b i‖ ^ 2) := by
    rw [h1, h2]
    linarith
  exact (Matrix.traceNorm_add_le _ _).trans hsum

private theorem gibbs_measurement_repetition {p η : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ m : ℕ, (1 - p) ^ m ≤ η ∧ (m : ℝ) * p ≤ Real.log (1 / η) + 1 := by
  have hinv : 1 < 1 / η := by
    rw [one_div]
    exact (one_lt_inv₀ hη0).mpr hη1
  have hlog : 0 < Real.log (1 / η) := Real.log_pos hinv
  refine ⟨Nat.ceil (Real.log (1 / η) / p), ?_, ?_⟩
  · by_cases hp1' : 1 - p = 0
    · have hxpos : 0 < Real.log (1 / η) / p := div_pos hlog hp
      have hm : 1 ≤ Nat.ceil (Real.log (1 / η) / p) := Nat.ceil_pos.mpr hxpos
      rw [hp1', zero_pow (by omega : (Nat.ceil (Real.log (1 / η) / p) : ℕ) ≠ 0)]
      exact le_of_lt hη0
    · have hpne1 : p ≠ 1 := fun h => hp1' (by rw [h]; ring)
      have h1p : 0 < 1 - p := sub_pos.mpr (lt_of_le_of_ne hp1 hpne1)
      have hlog1p : Real.log (1 - p) ≤ -p := by
        have h := Real.log_le_sub_one_of_pos h1p
        linarith
      have hlog1pneg : Real.log (1 - p) ≤ 0 := by linarith
      rw [← Real.log_le_log_iff (pow_pos h1p _) hη0, Real.log_pow]
      have hx0 : 0 ≤ Real.log (1 / η) / p := div_nonneg hlog.le hp.le
      have h1 : (Nat.ceil (Real.log (1 / η) / p) : ℝ) * Real.log (1 - p)
          ≤ (Real.log (1 / η) / p) * Real.log (1 - p) :=
        mul_le_mul_of_nonpos_right (Nat.le_ceil _) hlog1pneg
      have h2 : (Real.log (1 / η) / p) * Real.log (1 - p)
          ≤ (Real.log (1 / η) / p) * (-p) := by
        have h2' := mul_le_mul_of_nonneg_right hlog1p hx0
        rw [mul_comm (Real.log (1 / η) / p) (Real.log (1 - p)),
          mul_comm (Real.log (1 / η) / p) (-p)]
        exact h2'
      have h3 : (Real.log (1 / η) / p) * (-p) = -Real.log (1 / η) := by
        rw [mul_neg, div_mul_cancel₀ _ hp.ne']
      have h4 : Real.log η = -Real.log (1 / η) := by
        rw [one_div, Real.log_inv]
        linarith
      linarith
  · have hm : (Nat.ceil (Real.log (1 / η) / p) : ℝ)
        < Real.log (1 / η) / p + 1 := Nat.ceil_lt_add_one (div_nonneg hlog.le hp.le)
    have h5 : (Nat.ceil (Real.log (1 / η) / p) : ℝ) * p
        < (Real.log (1 / η) / p + 1) * p := mul_lt_mul_of_pos_right hm hp
    have h6 : (Real.log (1 / η) / p + 1) * p = Real.log (1 / η) + p := by
      field_simp
    linarith

theorem clause25 : Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.NormalizedGibbsConsumptionSpec := by
  intro D A B R β r ψ hA hB hR hβ hr hψ Y U η v y p hgap
  have hcons := imaginary_product_actual_postselection_consumer (Fin D) A B β r ψ
    hA hB hβ hr hψ hgap
  refine ⟨⟨hcons.1, hcons.2.2, hcons.2.1⟩, ?_, ?_⟩
  · have hη0 : 0 ≤ η := by
      show 0 ≤ β ^ 2 * ‖A * B - B * A‖ / (2 * (r : ℝ))
      positivity
    have hv0 : (0:ℝ) < ‖v‖ := lt_of_le_of_lt hη0 hgap
    have hvne : v ≠ 0 := by
      intro h
      rw [h] at hv0
      simp at hv0
    have hyne : y ≠ 0 := by
      intro h
      have h0' : (0:ℝ) < ‖v‖ - η := sub_pos.mpr hgap
      have h1' : (0:ℝ) < ‖y‖ ^ 2 := lt_of_lt_of_le (pow_pos h0' 2) hcons.1
      rw [h] at h1'
      simp at h1'
    have hny : ‖NormedSpace.normalize y‖ = 1 :=
      NormedSpace.norm_normalize_eq_one_iff.mpr hyne
    have hnv : ‖NormedSpace.normalize v‖ = 1 :=
      NormedSpace.norm_normalize_eq_one_iff.mpr hvne
    have ha : ∑ i, ‖WithLp.ofLp (NormedSpace.normalize y) i‖ ^ 2 = 1 := by
      have h := EuclideanSpace.norm_sq_eq (NormedSpace.normalize y)
      rw [hny, one_pow] at h
      exact h.symm
    have hb : ∑ i, ‖WithLp.ofLp (NormedSpace.normalize v) i‖ ^ 2 = 1 := by
      have h := EuclideanSpace.norm_sq_eq (NormedSpace.normalize v)
      rw [hnv, one_pow] at h
      exact h.symm
    have hsq : ∑ i, ‖WithLp.ofLp (NormedSpace.normalize y) i
        - WithLp.ofLp (NormedSpace.normalize v) i‖ ^ 2
        = ‖NormedSpace.normalize y - NormedSpace.normalize v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => by
        simp
    have htr := traceNorm_outerProduct_sub_le (WithLp.ofLp (NormedSpace.normalize y))
      (WithLp.ofLp (NormedSpace.normalize v)) ha hb
    have hroot : Real.sqrt (∑ i, ‖WithLp.ofLp (NormedSpace.normalize y) i
        - WithLp.ofLp (NormedSpace.normalize v) i‖ ^ 2)
        = ‖NormedSpace.normalize y - NormedSpace.normalize v‖ := by
      rw [hsq, Real.sqrt_sq (norm_nonneg _)]
    rw [hroot] at htr
    have hkey : SchattenOne (outerProduct (WithLp.ofLp (NormedSpace.normalize y))
        - outerProduct (WithLp.ofLp (NormedSpace.normalize v))) / 2 ≤ 2 * (η / ‖v‖) := by
      have h6 : 2 * ‖NormedSpace.normalize y - NormedSpace.normalize v‖
          ≤ 2 * (2 * η / ‖v‖) := mul_le_mul_of_nonneg_left hcons.2.1 (by norm_num)
      have h7 : Matrix.traceNorm (outerProduct (WithLp.ofLp (NormedSpace.normalize y))
          - outerProduct (WithLp.ofLp (NormedSpace.normalize v)))
          ≤ 2 * (2 * η / ‖v‖) := htr.trans h6
      have h8 : SchattenOne (outerProduct (WithLp.ofLp (NormedSpace.normalize y))
          - outerProduct (WithLp.ofLp (NormedSpace.normalize v)))
          ≤ 2 * (2 * η / ‖v‖) := by rw [schattenOne_eq_traceNorm]; exact h7
      have h11 : 2 * (2 * η / ‖v‖) / 2 = 2 * (η / ‖v‖) := by ring
      have h9 : SchattenOne (outerProduct (WithLp.ofLp (NormedSpace.normalize y))
          - outerProduct (WithLp.ofLp (NormedSpace.normalize v))) / 2
          ≤ 2 * (2 * η / ‖v‖) / 2 := by linarith
      rw [h11] at h9
      exact h9
    show SchattenOne (outerProduct (WithLp.ofLp (NormedSpace.normalize y))
        - outerProduct (WithLp.ofLp (NormedSpace.normalize v))) / 2
        ≤ 2 * (η / ‖v‖) + 2 * Real.sqrt (1 - p)
    exact hkey.trans (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * Real.sqrt (1 - p)))
  · intro hp hη0 hη1
    have hy1 : ‖y‖ ≤ 1 := hcons.2.2
    have hp1 : p ≤ 1 := by
      show ‖y‖ ^ 2 ≤ 1
      have h0y : 0 ≤ ‖y‖ := norm_nonneg y
      nlinarith [h0y, hy1]
    exact gibbs_measurement_repetition hp hp1 hη0 hη1

private theorem pfNestedCommList_zero_head {I : Type} [Fintype I]
    (w : List (Matrix I I ℂ)) : pfNestedCommList ((0 : Matrix I I ℂ) :: w) = 0 := by
  have hind : ∀ l : List (Matrix I I ℂ), l.foldl (fun D Y => pfComm Y D) 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons Y r ih =>
      rw [List.foldl_cons]
      have h0 : pfComm Y 0 = 0 := by simp [pfComm]
      rw [h0]
      exact ih
  simp only [pfNestedCommList]
  exact hind w

theorem clause14_refuted :
    ¬ (∀ (I : Type) [Fintype I] [DecidableEq I],
        @Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.Eq47IdentitySpec I _ _) := by
  intro h
  have h1 := h (Fin 2)
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  set X : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, (Real.pi : ℂ) * Complex.I]
    with hXdef
  set V : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1] with hVdef
  have hXanti : Xᴴ = -X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hXdef, Matrix.diagonal, Matrix.conjTranspose_apply, RCLike.star_def]
  have hex : NormedSpace.exp X = V := by
    rw [hXdef, Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hVdef, Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  have hword1 : suzukiExponentialWord [X] 1 = NormedSpace.exp X := by
    simp [suzukiExponentialWord]
  have hTaylor : ∀ n, n < 1 → suzukiSeries [X] n =
      ((n.factorial : ℝ)⁻¹) • ((0 : Matrix (Fin 2) (Fin 2) ℂ) ^ n) := by
    intro n hn
    interval_cases n
    simp
  have hc := h1 [X] 0 1 (by norm_num)
    (by
      intro Y hY
      have hy : Y = X := List.mem_singleton.mp hY
      simpa only [hy] using! hXanti)
    (by rw [Matrix.conjTranspose_zero, neg_zero]) hTaylor
  have hc1 := (hc 1).1
  have hsum : ∑ n ∈ Finset.range 1, (1 : ℝ) ^ n • suzukiSeries [X] n = 1 := by
    rw [Finset.sum_range_one]
    simp
  have hR : eq47Remainder [X] 0 1 1 = 0 := by
    rw [eq47Remainder]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [eq47CompositionTerm, pfNestedCommList_zero_head, smul_zero, smul_zero]
  rw [hR, hsum, hword1, hex] at hc1
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hc1
  norm_num [hVdef, Matrix.diagonal] at hentry

private theorem pfInterpret_eq_one_of_ones {D : ℕ} (L : List (Operator D × ℕ))
    (h : ∀ x ∈ L, x.1 = 1) : pfInterpret L = 1 := by
  induction L with
  | nil => rfl
  | cons x r ih =>
    rw [pfInterpret, List.foldl_cons, h x (by simp), one_mul]
    exact ih (fun y hy => h y (by simp [hy]))

theorem clause20_refuted : ¬ Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs.LongRangeCostSpec := by
  intro h
  letI : NormedAlgebra ℚ (Matrix (Fin 1) (Fin 1) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  set H : Fin 2 → Fin 2 → Operator 1 :=
    fun x y => if x = y then 0 else ((1 / 64 : ℝ) : ℂ) • 1 with hHdef
  have hHdiag : ∀ x : Fin 2, H x x = 0 := by intro x; simp [hHdef]
  have hHoff : ∀ x y : Fin 2, x ≠ y → H x y = ((1 / 64 : ℝ) : ℂ) • 1 := by
    intro x y hxy; simp [hHdef, hxy]
  have hHerm : ∀ x y : Fin 2, (H x y).IsHermitian := by
    intro x y
    by_cases hxy : x = y
    · rw [hxy, hHdiag y]; exact Matrix.isHermitian_zero
    · rw [hHoff x y hxy]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.conjTranspose_apply, Matrix.smul_apply]
  have hdist : ∀ x y : Fin 2, torusDist 2 x y ≤ ((0 : ℕ) : ℤ) ↔ x = y := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [torusDist]
  have hFam : LongRangeFamily 1 2 (1 / 8 : ℝ) ((3 : ℕ) : ℝ) H := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro x y
    by_cases hxy : x = y
    · rw [hxy, hHdiag y]
      simp
      rw [show torusDist 2 y y = 0 from by
          fin_cases y <;> simp [torusDist],
        Int.cast_zero, add_zero]
      norm_num
    · rw [hHoff x y hxy]
      have hd1 : torusDist 2 x y = 1 := by
        fin_cases x <;> fin_cases y <;> first
          | exact absurd rfl hxy
          | simp [torusDist]
      rw [hd1]
      rw [show (1 + ((1 : ℤ) : ℝ)) = 2 from by norm_num, Real.rpow_natCast]
      rw [norm_smul, norm_one]
      norm_num
  have hsum : (∑ x, ∑ y, H x y : Operator 1) = ((1 / 32 : ℝ) : ℂ) • 1 := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [hHdiag 0, hHdiag 1, hHoff 0 1 (by decide), hHoff 1 0 (by decide)]
    rw [zero_add, add_zero, ← add_smul]
    have hc : ((1 / 64 : ℝ) : ℂ) + ((1 / 64 : ℝ) : ℂ) = ((1 / 32 : ℝ) : ℂ) := by norm_num
    rw [hc]
  have htrunc0 : ∀ x y : Fin 2, longRangeTruncated 1 2 0 H x y = 0 := by
    intro x y
    unfold longRangeTruncated
    by_cases hxy : torusDist 2 x y ≤ ((0 : ℕ) : ℤ)
    · have hxe : x = y := (hdist x y).mp hxy
      rw [if_pos hxy, hxe, hHdiag y]
    · rw [if_neg hxy]
  have hflat0 : longRangeFlat 1 2 0 H = fun _ : Fin (2 * 2) => (0 : Operator 1) := by
    funext ij
    obtain ⟨x, y, hx, hy⟩ : ∃ x y : Fin 2,
        (finProdFinEquiv.symm ij).1 = x ∧ (finProdFinEquiv.symm ij).2 = y :=
      ⟨_, _, rfl, rfl⟩
    unfold longRangeFlat
    rw [hx, hy]
    exact htrunc0 x y
  have hfam1 : pfFamily (longRangeFlat 1 2 0 H) (32 * Real.pi) 1 = 1 := by
    rw [hflat0, pfFamily]
    refine pfInterpret_eq_one_of_ones _ fun x hx => ?_
    simp only [pfFamilyWord] at hx
    rw [List.mem_flatten] at hx
    obtain ⟨L, hL, hxL⟩ := hx
    rw [List.mem_replicate] at hL
    obtain ⟨-, rfl⟩ := hL
    rw [List.mem_ofFn] at hxL
    obtain ⟨j, hj⟩ := hxL
    rw [← hj]
    simp [HamiltonianEvolution]
  have hexpmI : Complex.exp (-((Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
    rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hev : HamiltonianEvolution (((1 / 32 : ℝ) : ℂ) • (1 : Operator 1)) (32 * Real.pi)
      = (-1 : ℂ) • 1 := by
    unfold HamiltonianEvolution
    rw [smul_smul]
    have hc : (-Complex.I * ((32 * Real.pi : ℝ) : ℂ)) * ((1 / 32 : ℝ) : ℂ)
        = -((Real.pi : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hc]
    have hdiag : (-((Real.pi : ℝ) : ℂ) * Complex.I) • (1 : Operator 1)
        = Matrix.diagonal ![-((Real.pi : ℝ) : ℂ) * Complex.I] := by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.diagonal, Matrix.smul_apply, smul_eq_mul]
    rw [hdiag, Matrix.exp_diagonal]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  have hcom0 : pfCommutatorSum (fun _ : Fin (2 * 2) => (0 : Operator 1)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    refine Finset.sum_eq_zero fun k _ => ?_
    split
    · simp [pfComm]
    · rfl
  have hc3 := (h 1 2 1 0 1 (1 / 8 : ℝ) ((3 : ℕ) : ℝ) H (32 * Real.pi) 1
      (fun _ => 0) hFam hHerm (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).2.2.1
  have hnorm2 : ((1 : Operator 1) - (-1 : ℂ) • (1 : Operator 1)) = ((2 : ℝ) : ℂ) • 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.sub_apply]
  rw [hfam1, hsum, hev, hflat0, hcom0, hnorm2, norm_smul, norm_one, mul_one] at hc3
  rw [show (1 + ((0 : ℕ) : ℝ)) = 1 from by norm_num, Real.one_rpow, mul_zero,
    add_zero] at hc3
  norm_num at hc3

private theorem lightCone_involution_evolution {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (hM : M.IsHermitian) (hsq : M * M = 1) :
    HamiltonianEvolution M (Real.pi / 2) = (-Complex.I) • M := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hM.eigenvectorUnitary
  let d : Matrix I I ℂ := Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ))
  have hdiag : d * d = 1 := by
    have h := congrArg (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (star hM.eigenvectorUnitary)) hsq
    simpa only [map_mul, map_one, hM.conjStarAlgAut_star_eigenvectorUnitary] using! h
  have hlam (i : I) : hM.eigenvalues i = 1 ∨ hM.eigenvalues i = -1 := by
    have h := congrArg (fun A : Matrix I I ℂ => (A i i).re) hdiag
    simp only [d, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.one_re] at h
    exact mul_self_eq_one_iff.mp h
  have hd : HamiltonianEvolution d (Real.pi / 2) = (-Complex.I) • d := by
    dsimp only [d]
    rw [cayley_evolution_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
      rcases hlam i with h | h
      · simp only [h, Complex.ofReal_one, mul_one]
        push_cast
        simpa only [neg_div] using! Complex.exp_neg_pi_div_two_mul_I
      · simp only [h, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, mul_neg, neg_neg]
        push_cast
        simp
    · simp [hij]
  have hMd : M = e d := hM.spectral_theorem
  have hevo : HamiltonianEvolution (e d) (Real.pi / 2) =
      e (HamiltonianEvolution d (Real.pi / 2)) := by
    letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    unfold HamiltonianEvolution
    rw [← map_smul]
    exact (NormedSpace.map_exp e e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional _).symm
  rw [hMd, hevo, hd, map_smul]
private abbrev lightConeRefQMat := Matrix (Fin 4) (Fin 4) ℚ
private def lightConeRefAq : lightConeRefQMat := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]
private def lightConeRefBq : lightConeRefQMat := !![1,0,0,0; 0,0,0,1; 0,0,1,0; 0,1,0,0]
private def lightConeRefCq : lightConeRefQMat := !![3/5,4/5,0,0; 4/5,-3/5,0,0;
  0,0,3/5,4/5; 0,0,4/5,-3/5]
private def lightConeRefOq : lightConeRefQMat := !![1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,-1]
private noncomputable def lightConeRefLift : lightConeRefQMat →+* Operator 4 :=
    (algebraMap ℚ ℂ).mapMatrix
private def lightConeRefA : Operator 4 := lightConeRefLift lightConeRefAq
private def lightConeRefB : Operator 4 := lightConeRefLift lightConeRefBq
private def lightConeRefC : Operator 4 := lightConeRefLift lightConeRefCq
private def lightConeRefO : Operator 4 := lightConeRefLift lightConeRefOq

private theorem lightConeRefLift_transpose (M : lightConeRefQMat) : (lightConeRefLift M)ᴴ = lightConeRefLift Mᵀ := by
  ext i j
  simp [lightConeRefLift, Matrix.conjTranspose_apply]

private theorem lightConeRefLift_hermitian (M : lightConeRefQMat) (hM : Mᵀ = M) : (lightConeRefLift M).IsHermitian := by
  change (lightConeRefLift M)ᴴ = lightConeRefLift M
  rw [lightConeRefLift_transpose, hM]

private theorem lightConeRefLift_involution (M : lightConeRefQMat) (hM : M * M = 1) : lightConeRefLift M * lightConeRefLift M = 1 := by
  rw [← map_mul, hM, map_one]

private theorem lightConeRefAC_comm : lightConeRefA * lightConeRefC = lightConeRefC * lightConeRefA := by
  exact (map_mul lightConeRefLift lightConeRefAq lightConeRefCq).symm.trans
    ((congrArg lightConeRefLift (show lightConeRefAq * lightConeRefCq = lightConeRefCq * lightConeRefAq by decide +kernel)).trans (map_mul lightConeRefLift lightConeRefCq lightConeRefAq))

private theorem lightConeRefAO_comm : lightConeRefA * lightConeRefO = lightConeRefO * lightConeRefA := by
  exact (map_mul lightConeRefLift lightConeRefAq lightConeRefOq).symm.trans
    ((congrArg lightConeRefLift (show lightConeRefAq * lightConeRefOq = lightConeRefOq * lightConeRefAq by decide +kernel)).trans (map_mul lightConeRefLift lightConeRefOq lightConeRefAq))

private theorem lightConeRefBO_comm : lightConeRefB * lightConeRefO = lightConeRefO * lightConeRefB := by
  exact (map_mul lightConeRefLift lightConeRefBq lightConeRefOq).symm.trans
    ((congrArg lightConeRefLift (show lightConeRefBq * lightConeRefOq = lightConeRefOq * lightConeRefBq by decide +kernel)).trans (map_mul lightConeRefLift lightConeRefOq lightConeRefBq))
private def lightConeRefFamily (i : Fin 4) : LocalTerm 4 4 :=
  match i.val with
  | 0 => ⟨0, {2,3}, lightConeRefA⟩
  | 1 => ⟨1, {1,2}, lightConeRefB⟩
  | 2 => ⟨2, {0,1}, lightConeRefC⟩
  | _ => ⟨3, ∅, 0⟩

private theorem lightConeRef_hermitian (i : Fin 4) : ((lightConeRefFamily i).op).IsHermitian := by
  fin_cases i
  · exact lightConeRefLift_hermitian lightConeRefAq (by decide +kernel)
  · exact lightConeRefLift_hermitian lightConeRefBq (by decide +kernel)
  · exact lightConeRefLift_hermitian lightConeRefCq (by decide +kernel)
  · exact Matrix.isHermitian_zero

private theorem lightConeRef_involution (i : Fin 4) (hi : i ≠ 3) : (lightConeRefFamily i).op * (lightConeRefFamily i).op = 1 := by
  fin_cases i
  · exact lightConeRefLift_involution lightConeRefAq (by decide +kernel)
  · exact lightConeRefLift_involution lightConeRefBq (by decide +kernel)
  · exact lightConeRefLift_involution lightConeRefCq (by decide +kernel)
  · contradiction

private theorem lightConeRef_finite_range : IsFiniteRangeFamily lightConeRefFamily := by
  intro i j hd
  fin_cases i <;> fin_cases j <;> simp [lightConeRefFamily, Finset.disjoint_left] at hd ⊢
  all_goals simp [pfComm, lightConeRefAC_comm]

private theorem lightConeRef_bounded : FiniteRangeBounded lightConeRefFamily (‖lightConeRefA‖ + ‖lightConeRefB‖ + ‖lightConeRefC‖) 2 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp only [lightConeRefFamily] <;> norm_num <;>
      nlinarith [norm_nonneg lightConeRefA, norm_nonneg lightConeRefB, norm_nonneg lightConeRefC]
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

private theorem lightConeRef_outside (i : Fin 4) (hi : Disjoint (lightConeRefFamily i).support {0}) :
    pfComm (lightConeRefFamily i).op lightConeRefO = 0 := by
  fin_cases i <;> simp [lightConeRefFamily, Finset.disjoint_left] at hi ⊢
  all_goals simp [pfComm, lightConeRefAO_comm, lightConeRefBO_comm]

private theorem lightConeRef_labels : coneLabels lightConeRefFamily {0} 1 = {1, 2} := by
  ext i
  fin_cases i <;>
    norm_num [coneLabels, lightConeSites, supportThickening, lightConeRefFamily, Finset.disjoint_left,
      Fin.univ_succ]
  all_goals norm_num [Fin.ext_iff]

private theorem lightConeRef_evolution (i : Fin 4) (hi : i ≠ 3) :
    HamiltonianEvolution (lightConeRefFamily i).op (Real.pi / 2) = (-Complex.I) • (lightConeRefFamily i).op :=
  lightCone_involution_evolution (lightConeRefFamily i).op (lightConeRef_hermitian i) (lightConeRef_involution i hi)

private theorem lightConeRef_full_word : pfInterpret (pfFamilyWord (fun i => (lightConeRefFamily i).op) (Real.pi / 2) 1)
    = (Complex.I) • (lightConeRefC * lightConeRefB * lightConeRefA) := by
  have ha : HamiltonianEvolution (lightConeRefFamily 0).op (Real.pi / 2) = (-Complex.I) • lightConeRefA :=
    lightConeRef_evolution 0 (by decide)
  have hb : HamiltonianEvolution (lightConeRefFamily 1).op (Real.pi / 2) = (-Complex.I) • lightConeRefB :=
    lightConeRef_evolution 1 (by decide)
  have hc : HamiltonianEvolution (lightConeRefFamily 2).op (Real.pi / 2) = (-Complex.I) • lightConeRefC :=
    lightConeRef_evolution 2 (by decide)
  have hd : (lightConeRefFamily 3).op = 0 := rfl
  have hw : pfFamilyWord (fun i => (lightConeRefFamily i).op) (Real.pi / 2) 1 =
      [(HamiltonianEvolution (lightConeRefFamily 0).op (Real.pi / 2), 0),
       (HamiltonianEvolution (lightConeRefFamily 1).op (Real.pi / 2), 1),
       (HamiltonianEvolution (lightConeRefFamily 2).op (Real.pi / 2), 2),
       (HamiltonianEvolution (lightConeRefFamily 3).op (Real.pi / 2), 3)] := by
    simp only [pfFamilyWord, List.replicate_one, List.flatten_singleton,
      List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Nat.zero_add,
      Nat.cast_one, div_one]
    rfl
  rw [hw]
  simp only [pfInterpret, List.foldl_cons, List.foldl_nil, ha, hb, hc, hd]
  simp [HamiltonianEvolution, smul_smul, Matrix.mul_assoc]

private theorem lightConeRef_four_word_filter {α : Type} (u0 u1 u2 u3 : α) (keep : α × ℕ → Bool)
    (h0 : keep (u0, 0) = false) (h1 : keep (u1, 1) = true)
    (h2 : keep (u2, 2) = true) (h3 : keep (u3, 3) = false) :
    [(u0, 0), (u1, 1), (u2, 2), (u3, 3)].filter keep = [(u1, 1), (u2, 2)] := by
  simp [h0, h1, h2, h3]

private theorem lightConeRef_filtered_four_family {D : ℕ} (H : Fin 4 → Operator D) (t : ℝ)
    (keep : ℕ → Bool) (h0 : keep 0 = false) (h1 : keep 1 = true)
    (h2 : keep 2 = true) (h3 : keep 3 = false) :
    pfInterpret ((pfFamilyWord H t 1).filter (fun x => keep x.2)) =
      HamiltonianEvolution (H 2) t * HamiltonianEvolution (H 1) t := by
  have hw : pfFamilyWord H t 1 =
      [(HamiltonianEvolution (H 0) t, 0), (HamiltonianEvolution (H 1) t, 1),
        (HamiltonianEvolution (H 2) t, 2), (HamiltonianEvolution (H 3) t, 3)] := by
    simp only [pfFamilyWord, List.replicate_one, List.flatten_singleton,
      List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Nat.zero_add,
      Nat.cast_one, div_one]
    rfl
  rw [hw, lightConeRef_four_word_filter _ _ _ _ (fun x => keep x.2) h0 h1 h2 h3]
  simp only [pfInterpret, List.foldl_cons, List.foldl_nil, Matrix.mul_one]

private theorem lightConeRef_two_phase_product {D : ℕ} (U V : Operator D) :
    ((-Complex.I) • U) * ((-Complex.I) • V) = (-1 : ℂ) • (U * V) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

private theorem lightConeRef_phase_conjugation {D : ℕ} (s : ℂ) (P O : Operator D)
    (hs : star s * s = 1) : (s • P)ᴴ * O * (s • P) = Pᴴ * O * P := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm s (star s), hs, one_smul]

private theorem lightConeRef_cone_word : pfInterpret (coneWord lightConeRefFamily (Real.pi / 2) 1 {0}) =
    (-1 : ℂ) • (lightConeRefC * lightConeRefB) := by
  have ha : HamiltonianEvolution lightConeRefB (Real.pi / 2) = (-Complex.I) • lightConeRefB :=
    lightConeRef_evolution 1 (by decide)
  have hb : HamiltonianEvolution lightConeRefC (Real.pi / 2) = (-Complex.I) • lightConeRefC :=
    lightConeRef_evolution 2 (by decide)
  have himage : (coneLabels lightConeRefFamily {0} 1).image Fin.val = {1, 2} := by
    rw [lightConeRef_labels]
    decide +kernel
  let keep : ℕ → Bool := fun n => decide (n ∈ (coneLabels lightConeRefFamily {0} 1).image Fin.val)
  have h0 : keep 0 = false := by simp [keep, himage]
  have h1 : keep 1 = true := by simp [keep, himage]
  have h2 : keep 2 = true := by simp [keep, himage]
  have h3 : keep 3 = false := by simp [keep, himage]
  unfold coneWord
  change pfInterpret ((pfFamilyWord (fun i => (lightConeRefFamily i).op) (Real.pi / 2) 1).filter
    (fun x => keep x.2)) = _
  rw [lightConeRef_filtered_four_family (fun i => (lightConeRefFamily i).op) (Real.pi / 2) keep h0 h1 h2 h3]
  change HamiltonianEvolution lightConeRefC (Real.pi / 2) * HamiltonianEvolution lightConeRefB
      (Real.pi / 2) = _
  rw [ha, hb]
  exact lightConeRef_two_phase_product lightConeRefC lightConeRefB

private theorem lightConeRef_full_conjugation : (lightConeRefC * lightConeRefB * lightConeRefA)ᴴ * lightConeRefO * (lightConeRefC * lightConeRefB * lightConeRefA) =
    lightConeRefLift ((lightConeRefCq * lightConeRefBq * lightConeRefAq)ᵀ * lightConeRefOq * (lightConeRefCq * lightConeRefBq * lightConeRefAq)) := by
  simp only [lightConeRefA, lightConeRefB, lightConeRefC, lightConeRefO,
      ← map_mul lightConeRefLift, lightConeRefLift_transpose]

private theorem lightConeRef_cone_conjugation : (lightConeRefC * lightConeRefB)ᴴ * lightConeRefO * (lightConeRefC * lightConeRefB) =
    lightConeRefLift ((lightConeRefCq * lightConeRefBq)ᵀ * lightConeRefOq * (lightConeRefCq * lightConeRefBq)) := by
  simp only [lightConeRefB, lightConeRefC, lightConeRefO, ← map_mul lightConeRefLift,
      lightConeRefLift_transpose]

theorem clause21_refuted : ¬ LightConeObservableSpec := by
  intro h
  have he := (h 4 4 1 (‖lightConeRefA‖ + ‖lightConeRefB‖ + ‖lightConeRefC‖) 2 2 lightConeRefFamily (Real.pi / 2) lightConeRefO {0}
    lightConeRef_finite_range lightConeRef_bounded lightConeRef_hermitian (by decide) lightConeRef_outside).1
  rw [lightConeRef_full_word, lightConeRef_cone_word] at he
  rw [lightConeRef_phase_conjugation Complex.I (lightConeRefC * lightConeRefB * lightConeRefA) lightConeRefO (by simp),
    lightConeRef_phase_conjugation (-1) (lightConeRefC * lightConeRefB) lightConeRefO (by norm_num)] at he
  rw [lightConeRef_full_conjugation, lightConeRef_cone_conjugation] at he
  have hx := congrArg (fun M : Operator 4 => (M 0 3).re) he
  have hl :
      ((lightConeRefCq * lightConeRefBq * lightConeRefAq)ᵀ * lightConeRefOq * (lightConeRefCq * lightConeRefBq * lightConeRefAq)) 0 3 = -24/25 := by decide +kernel
  have hr :
      ((lightConeRefCq * lightConeRefBq)ᵀ * lightConeRefOq * (lightConeRefCq * lightConeRefBq)) 0 3 = 24/25 := by decide +kernel
  change (((((lightConeRefCq * lightConeRefBq * lightConeRefAq)ᵀ * lightConeRefOq * (lightConeRefCq * lightConeRefBq * lightConeRefAq)) 0 3 : ℚ) : ℂ).re) =
    (((((lightConeRefCq * lightConeRefBq)ᵀ * lightConeRefOq * (lightConeRefCq * lightConeRefBq)) 0 3 : ℚ) : ℂ).re) at hx
  rw [hl, hr] at hx
  norm_num at hx

private noncomputable def zeroPhaseGenerator : Matrix (Reg 0) (Reg 0) ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) • 1

private theorem zeroPhaseGenerator_skew : zeroPhaseGeneratorᴴ = -zeroPhaseGenerator := by
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst j
  simp [zeroPhaseGenerator, Matrix.conjTranspose_apply, Matrix.smul_apply,
    smul_eq_mul]

private theorem zeroPhaseGenerator_exp :
    NormedSpace.exp ((1 / 2 : ℝ) • zeroPhaseGenerator) = (-1 : Matrix (Reg 0) (Reg 0) ℂ) := by
  have hd : (1 / 2 : ℝ) • zeroPhaseGenerator =
      Matrix.diagonal (fun _ : Reg 0 => (Real.pi : ℂ) * Complex.I) := by
    ext i j
    simp [zeroPhaseGenerator, Matrix.diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    ring
  rw [hd, Matrix.exp_diagonal]
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst j
  simp [Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.exp_pi_mul_I]

private theorem zeroPhaseGenerator_word :
    recursiveSuzukiWord [zeroPhaseGenerator] 0 1 1 = [-1, -1] := by
  norm_num [recursiveSuzukiWord, recursiveSuzukiGenerators]
  simpa only [one_div] using! zeroPhaseGenerator_exp

theorem zero_wire_suzuki_phase_word :
    let X := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) • (1 : Matrix (Reg 0) (Reg 0) ℂ)
    Xᴴ = -X ∧ recursiveSuzukiWord [X] 0 1 1 = [-1, -1] :=
  ⟨zeroPhaseGenerator_skew, zeroPhaseGenerator_word⟩

private theorem zero_wire_gate_word_nil (gs : List (LocalQFTGate 0)) : gs = [] := by
  cases gs with
  | nil => rfl
  | cons g _ =>
    cases g with
    | h i => exact Fin.elim0 i
    | cp i _ _ _ => exact Fin.elim0 i
    | swap i _ => exact Fin.elim0 i

theorem zero_wire_native_neg_one_error (gs : List (LocalQFTGate 0)) :
    ‖localProgramMatrix gs - (-1 : Matrix (Reg 0) (Reg 0) ℂ)‖ = 2 := by
  rw [zero_wire_gate_word_nil gs, localProgramMatrix_nil]
  have heq : (1 : Matrix (Reg 0) (Reg 0) ℂ) - (-1) = (2 : ℂ) • 1 := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq, norm_smul, norm_one]
  norm_num

theorem clause27_zero_register_false : ¬ ExponentialSynthesisSpec := by
  intro h
  obtain ⟨synth, bits, space, compile, hvisit, _⟩ :=
    h 0 0 1 [zeroPhaseGenerator] 1 1
      (by simpa using! zeroPhaseGenerator_skew) (by norm_num) (by norm_num)
  have hm : (-1 : Matrix (Reg 0) (Reg 0) ℂ) ∈
      recursiveSuzukiWord [zeroPhaseGenerator] 0 1 1 := by
    rw [zeroPhaseGenerator_word]
    simp
  have he := (hvisit (-1) hm).2.2.2.2.1
  rw [zero_wire_native_neg_one_error] at he
  norm_num at he

end Qatlib.Concepts.TrotterFormula.GeneralOrder
