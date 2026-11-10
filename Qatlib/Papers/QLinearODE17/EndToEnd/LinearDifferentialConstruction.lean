/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.EndToEnd.LinearDifferentialConstructionDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.EncodingCore

set_option autoImplicit false

namespace Qatlib.Papers.QLinearODE17.EndToEnd

open Qatlib
open Matrix
open scoped Classical Matrix.Norms.L2Operator BigOperators
set_option warningAsError false

theorem sparseRowMass_eq_positions {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A : Matrix O I ℂ) (o : O) :
    sparseRowMass A o = ∑ i ∈ sparsePositions A o, ‖A o i‖ := by
  unfold sparseRowMass sparsePositions
  calc
    (∑ i, ‖A o i‖) = ∑ i ∈ (Finset.univ : Finset I),
        if A o i ≠ 0 then ‖A o i‖ else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : A o i = 0 <;> simp [hi]
    _ = ∑ i ∈ Finset.univ.filter (fun i => A o i ≠ 0), ‖A o i‖ :=
      (Finset.sum_filter _ _).symm

theorem sparseColumnMass_eq_positions {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A : Matrix O I ℂ) (i : I) :
    sparseColumnMass A i = ∑ o ∈ Finset.univ.filter (fun o => A o i ≠ 0), ‖A o i‖ := by
  unfold sparseColumnMass
  calc
    (∑ o, ‖A o i‖) = ∑ o ∈ (Finset.univ : Finset O),
        if A o i ≠ 0 then ‖A o i‖ else 0 := by
      apply Finset.sum_congr rfl
      intro o _
      by_cases hi : A o i = 0 <;> simp [hi]
    _ = ∑ o ∈ Finset.univ.filter (fun o => A o i ≠ 0), ‖A o i‖ :=
      (Finset.sum_filter _ _).symm

theorem sparseRowAccessCost_le {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A : Matrix O I ℂ) (s : ℕ) (o : O)
    (hs : ∀ n : O, (Finset.univ.filter (fun c => A n c ≠ 0)).card ≤ s) :
    sparseRowAccessCost A o ≤ s := by
  exact hs o

theorem sparseColumnAccessCost_le {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A : Matrix O I ℂ) (s : ℕ) (i : I)
    (hs : ∀ c : I, (Finset.univ.filter (fun n => A n c ≠ 0)).card ≤ s) :
    sparseColumnAccessCost A i ≤ s := by
  exact hs i

theorem taylorRHS_zero_outside_support {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (h : ℝ) (x_in b : QState N)
    (r : Fin (m * (k + 1) + p + 1) × N) :
    (r.1 : ℕ) ∉ taylorRHSSupport m k p →
      taylorRHS m k p h x_in b r = 0 := by
  intro hn
  have hn0 : (r.1 : ℕ) ≠ 0 := by
    intro h0
    apply hn
    simp only [taylorRHSSupport, Finset.mem_union, Finset.mem_singleton]
    exact Or.inl h0
  rw [taylorRHS, if_neg hn0]
  by_cases h1 : (r.1 : ℕ) ≤ m * (k + 1) ∧ (r.1 : ℕ) % (k + 1) = 1
  · exfalso
    apply hn
    have hdecomp : (k + 1) * ((r.1 : ℕ) / (k + 1)) + 1 = (r.1 : ℕ) := by
      have h := Nat.mod_add_div (r.1 : ℕ) (k + 1)
      omega
    have hil : (r.1 : ℕ) / (k + 1) < m := by
      have hlt : (k + 1) * ((r.1 : ℕ) / (k + 1)) < m * (k + 1) := by omega
      rw [Nat.mul_comm (k + 1) ((r.1 : ℕ) / (k + 1))] at hlt
      exact Nat.lt_of_mul_lt_mul_right hlt
    simp only [taylorRHSSupport, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    have hdecomp' : ((r.1 : ℕ) / (k + 1)) * (k + 1) + 1 = (r.1 : ℕ) := by
      simpa [Nat.mul_comm] using! hdecomp
    exact Or.inr ⟨(r.1 : ℕ) / (k + 1), hil, hdecomp'⟩
  · simp [h1]

theorem taylorRHS_at_zero {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (h : ℝ) (x_in b : QState N) (n : N) :
    taylorRHS m k p h x_in b (Prod.mk ⟨0, by omega⟩ n) = x_in n := by
  simp [taylorRHS]

theorem controlled_prepare_actual_cost {J K I : Type} [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (PL PR : Matrix J J ℂ) (U : J → Matrix (K × I) (K × I) ℂ) (j₀ : J) (k₀ : K)
    (hPL : PL ∈ Matrix.unitaryGroup J ℂ) (hPR : PR ∈ Matrix.unitaryGroup J ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (K × I) ℂ) :
    IsUnitaryCircuit (pairedCircuit PL PR U) ∧
    QueryCount (pairedCircuit PL PR U) = 0 ∧
    GateCount (pairedCircuit PL PR U) = 3 ∧
    compress (pairedFrame j₀ k₀) (pairedBody PL PR U) (pairedFrame j₀ k₀) =
      ∑ j, (star (PL j j₀) * PR j j₀) • compress (encodingFiber k₀) (U j)
        (encodingFiber k₀) := by
  have h := paired_prepare_actual_corner_and_word PL PR U j₀ k₀ hPL hPR hU
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.1⟩

structure SolveRunCost where

  accessQueries : ℕ

  inverseQueries : ℕ

  inverseGates : ℕ

  prepareGates : ℕ

  readoutGates : ℕ
  deriving DecidableEq, Repr

theorem padding_quality_of_sum_bound (p kq m : ℕ) (g : ℝ) (hg : 0 < g) (hm : 0 < m)
    (hbound : (p : ℝ) + 77 * (m : ℝ) * g ^ 2 < (4 : ℝ) ^ kq) :
    1 / Real.sqrt ((p : ℝ) + 77 * (m : ℝ) * g ^ 2) > (1 : ℝ) / 2 ^ kq := by
  have hpos : 0 < (p : ℝ) + 77 * (m : ℝ) * g ^ 2 := by positivity
  have h2 : (0 : ℝ) < 2 ^ kq := by positivity
  have h4 : ((2 : ℝ) ^ kq) ^ 2 = (4 : ℝ) ^ kq := by
    calc
      ((2 : ℝ) ^ kq) ^ 2 = 2 ^ (kq * 2) := (pow_mul 2 kq 2).symm
      _ = 2 ^ (2 * kq) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ kq := pow_mul 2 2 kq
      _ = 4 ^ kq := by norm_num
  have hsqrt : Real.sqrt ((p : ℝ) + 77 * (m : ℝ) * g ^ 2) < 2 ^ kq := by
    rw [← h4] at hbound
    exact (Real.sqrt_lt' h2).2 hbound
  have hlt : (1 : ℝ) / 2 ^ kq < (1 : ℝ) /
      Real.sqrt ((p : ℝ) + 77 * (m : ℝ) * g ^ 2) := by
    rw [div_lt_div_iff₀ h2 (Real.sqrt_pos.2 hpos)]
    linarith
  linarith

theorem section7PaddingCount_quality (kq m : ℕ) (g : ℝ) (hg : 0 < g) (hm : 0 < m)
    (hroom : Nat.ceil (77 * (m : ℝ) * g ^ 2) + 1 < 4 ^ kq) :
    1 / Real.sqrt ((section7PaddingCount kq m g : ℝ) + 77 * (m : ℝ) * g ^ 2) >
      (1 : ℝ) / 2 ^ kq := by
  have hle1 : Nat.ceil (77 * (m : ℝ) * g ^ 2) + 1 ≤ 4 ^ kq := by omega
  have hle0 : Nat.ceil (77 * (m : ℝ) * g ^ 2) ≤ 4 ^ kq := by omega
  have hcast : (section7PaddingCount kq m g : ℝ) =
      (4 : ℝ) ^ kq - (Nat.ceil (77 * (m : ℝ) * g ^ 2) : ℝ) - 1 := by
    rw [section7PaddingCount]
    rw [Nat.cast_sub (by omega : 1 ≤ 4 ^ kq - Nat.ceil (77 * (m : ℝ) * g ^ 2))]
    rw [Nat.cast_sub hle0]
    push_cast
    ring
  have hceil : (Nat.ceil (77 * (m : ℝ) * g ^ 2) : ℝ) ≥ 77 * (m : ℝ) * g ^ 2 := by
    exact_mod_cast Nat.le_ceil _
  have hbound : (section7PaddingCount kq m g : ℝ) + 77 * (m : ℝ) * g ^ 2
      < (4 : ℝ) ^ kq := by
    rw [hcast]
    linarith
  exact padding_quality_of_sum_bound (section7PaddingCount kq m g) kq m g hg hm hbound

theorem section7LabelCount_eq (pars : Section7Parameters) :
    section7LabelCount pars = pars.m * (pars.k + 1) + pars.p + 1 := rfl

theorem eq112QueryCount_eq (pars : Section7Parameters) (s nq : ℕ) :
    eq112QueryCount pars s nq = (2 * nq - 1) + s * (pars.m + pars.p + 1) := rfl

theorem eq112_cutoff_closed_form (κq kq : ℕ) :
    explicitInverseCutoff κq (kq + 2) = κq * κq * (kq + κq + 3) := by
  rw [(explicit_inverse_cutoff_integer_formula κq (kq + 2)).1]
  ring

theorem roundFiniteDigit_error (x : ℝ) (bits : ℕ) :
    |(roundFiniteDigit x bits).value - x| ≤ (1 : ℝ) / 2 ^ bits := by
  have hn : (Nat.floor (|x| * 2 ^ bits) : ℝ) ≤ |x| * 2 ^ bits := by
    have hpos : 0 ≤ |x| * 2 ^ bits := by positivity
    exact_mod_cast Nat.floor_le hpos
  have hn' : |x| * 2 ^ bits < (Nat.floor (|x| * 2 ^ bits) : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one _
  have hkey : |x| - (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits =
      (|x| * 2 ^ bits - (Nat.floor (|x| * 2 ^ bits) : ℝ)) / 2 ^ bits := by
    field_simp
  have hnonneg : 0 ≤ |x| - (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits := by
    rw [hkey]
    have hpos : (0 : ℝ) < 2 ^ bits := by positivity
    have hle : 0 ≤ |x| * 2 ^ bits - (Nat.floor (|x| * 2 ^ bits) : ℝ) := by linarith
    positivity
  have hlt : |x| - (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits < 1 / 2 ^ bits := by
    rw [hkey]
    have hpos : (0 : ℝ) < 2 ^ bits := by positivity
    rw [div_lt_div_iff₀ hpos hpos]
    have hA : |x| * 2 ^ bits - (Nat.floor (|x| * 2 ^ bits) : ℝ) < 1 := by linarith
    nlinarith
  have hval : (roundFiniteDigit x bits).value =
      (if x < 0 then -1 else 1) * (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits := by
    simp [roundFiniteDigit, FiniteDigit.value]
  rw [hval]
  by_cases hs : x < 0
  · rw [if_pos hs]
    have hkey2 : -1 * (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits - x =
        |x| - (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits := by
      rw [abs_of_neg hs]
      ring
    rw [hkey2, abs_of_nonneg (by
      linarith : 0 ≤ |x| - (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits)]
    exact hlt.le
  · rw [if_neg hs]
    have hkey2 : 1 * (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits - x =
        -(|x| - (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits) := by
      rw [abs_of_nonneg (by linarith [hs] : 0 ≤ x)]
      ring
    rw [hkey2, abs_neg, abs_of_nonneg (by
      linarith : 0 ≤ |x| - (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits)]
    exact hlt.le

theorem finiteDigit_counts (x : ℝ) (bits : ℕ) :
    finiteDigitBitCount (roundFiniteDigit x bits) = bits + 1 ∧
      finiteDigitGateCount (roundFiniteDigit x bits) = bits := by
  simp [finiteDigitBitCount, finiteDigitGateCount, roundFiniteDigit]

theorem smallOrderUniformConstant_bound {k b : ℕ} (hb : 1 ≤ b) (hbk : b ≤ k)
    (z : ℂ) (h1 : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖taylorTransPoly k b z‖ ≤ smallOrderUniformConstant k b := by
  exact taylorTransPoly_le hb hbk z h1 hre

theorem frozenUniformConstant_valid_from_five {k b : ℕ} (hk : 5 ≤ k) (hb : 1 ≤ b)
    (hbk : b ≤ k) (z : ℂ) (h1 : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖taylorTransPoly k b z‖ ≤ frozenUniformConstant :=
  taylorTransPoly_uniform hk hb hbk z h1 hre

theorem frozenUniformConstant_fails_at_three :
    ‖taylorTransPoly 3 2 (Complex.I : ℂ)‖ > frozenUniformConstant := by
  have hpoly : taylorTransPoly 3 2 (Complex.I : ℂ) = 1 + (Complex.I : ℂ) / 3 := by
    have hIcc : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [taylorTransPoly, hIcc]
    simp [Finset.sum_insert, Finset.sum_singleton]
    ring
  rw [hpoly]
  have hsq : ‖(1 : ℂ) + (Complex.I : ℂ) / 3‖ ^ 2 = 10 / 9 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.I_re, Complex.I_im]
    ring
  have hnonneg : 0 ≤ ‖(1 : ℂ) + (Complex.I : ℂ) / 3‖ := norm_nonneg _
  have hgt : (10 / 9 : ℝ) > (31 / 30) ^ 2 := by norm_num
  by_contra hcon
  have hle : ‖(1 : ℂ) + (Complex.I : ℂ) / 3‖ ≤ 31 / 30 := le_of_not_gt hcon
  have hsqle : ‖(1 : ℂ) + (Complex.I : ℂ) / 3‖ ^ 2 ≤ (31 / 30) ^ 2 := by nlinarith
  linarith

theorem padding_distribution_small_k {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (M : Matrix N N ℂ) (h : ℝ)
    (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (j : ℕ) (hj : j ≤ p) :
    taylorBlock x (taylorFinalLabel m k p j hj) =
      taylorBlock x (taylorTimeLabel m k p m (le_refl m)) := by
  exact (taylorNatBlock_eq x (taylorFinalLabel m k p j hj)).symm.trans
    (taylorNatBlock_pad m k p M h x_in b x hx j hj)

end Qatlib.Papers.QLinearODE17.EndToEnd
