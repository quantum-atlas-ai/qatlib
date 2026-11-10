/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.SphereNets.FiniteNet
import Qatlib.Papers.QCircApprox95.MainResults.MeasureBounds
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix Metric Set Module MeasureTheory
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QCircApprox95.MainResults

theorem finrank_matrix_real (N : ℕ) :
    Module.finrank ℝ (Matrix (Fin N) (Fin N) ℂ) = 2 * (N * N) := by
  change Module.finrank ℝ (Fin N → Fin N → ℂ) = 2 * (N * N)
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem one_add_four_div_le_sq {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    1 + 4 / δ ≤ (2 / δ) ^ 2 := by
  have hsq : δ ^ 2 ≤ δ / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hδ hδ0.le]
  have hlin : 4 * δ ≤ 2 := by nlinarith
  have key : δ ^ 2 + 4 * δ ≤ 4 := by nlinarith
  rw [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
    le_div_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)]
  have he : (1 + 4 / δ) * δ ^ 2 = δ ^ 2 + 4 * δ := by
    field_simp
  rw [he]
  exact key

theorem net_card_arithmetic (n : ℕ) (hn : 1 ≤ n) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    (1 + 4 / δ) ^ (2 * (2 ^ n) * (2 ^ n)) ≤
      (2 / δ) ^ (2 ^ (4 * n)) := by

  set N : ℕ := 2 ^ n with hNdef
  have hN2 : 2 ≤ N := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hbase : (1 : ℝ) ≤ 2 / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith

  have hstep : 1 + 4 / δ ≤ (2 / δ) ^ 2 := one_add_four_div_le_sq hδ0 hδ

  have hpow : (1 + 4 / δ) ^ (2 * N * N) ≤
      ((2 / δ) ^ 2) ^ (2 * N * N) := pow_le_pow_left₀ (by positivity) hstep _
  have hpow' : ((2 / δ) ^ 2) ^ (2 * N * N) = (2 / δ) ^ (4 * N * N) := by
    rw [← pow_mul]
    congr 1
    ring

  have hNexp : 4 * N * N ≤ N * N * N * N := by
    have h4 : 4 ≤ N * N := by nlinarith
    calc 4 * N * N = 4 * (N * N) := by ring
      _ ≤ (N * N) * (N * N) := Nat.mul_le_mul_right (N * N) h4
      _ = N * N * N * N := by ring
  have hpow'' : (2 / δ) ^ (4 * N * N) ≤ (2 / δ) ^ (N * N * N * N) :=
    pow_le_pow_right₀ hbase hNexp
  have hNpow : N * N * N * N = 2 ^ (4 * n) := by
    rw [hNdef, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  calc (1 + 4 / δ) ^ (2 * (2 ^ n) * (2 ^ n))
      = (1 + 4 / δ) ^ (2 * N * N) := by rw [hNdef]
    _ ≤ ((2 / δ) ^ 2) ^ (2 * N * N) := hpow
    _ = (2 / δ) ^ (4 * N * N) := hpow'
    _ ≤ (2 / δ) ^ (N * N * N * N) := hpow''
    _ = (2 / δ) ^ (2 ^ (4 * n)) := by rw [hNpow]

theorem quantitative_unitary_net (n : ℕ) (hn : 1 ≤ n) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ s : Finset (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
      (↑s : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) ⊆
        (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) ∧
      (∀ U ∈ (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)),
        ∃ V ∈ s, ‖U - V‖ ≤ δ) ∧
      (s.card : ℝ) ≤ (2 / δ) ^ (2 ^ (4 * n)) := by
  have hε : 0 < δ / 2 := by positivity
  have hc : IsCompact (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :
      Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) :=
    Qatlib.Papers.Trainability23.HaarAverages.isCompact_unitaryGroup _
  obtain ⟨F, hF, hfin, hcover⟩ := hc.finite_cover_balls hε
  have hunit : (F : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) ⊆
      (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) := hF
  obtain ⟨s, hsF, hsep, hnet⟩ :=
    Qatlib.Foundations.MatrixGeometry.SphereNets.FiniteNet.finite_greedy_net
      hfin.toFinset (δ / 2) hε
  have hsU : (↑s : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) ⊆
      (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) := by
    intro x hx
    exact hunit (hfin.mem_toFinset.mp (hsF hx))
  refine ⟨s, hsU, ?_, ?_⟩
  · intro U hU
    obtain ⟨V, hV, hnear⟩ := Set.mem_iUnion₂.mp (hcover hU)
    obtain ⟨y, hy, hVy⟩ := hnet V (hfin.mem_toFinset.mpr hV)
    refine ⟨y, hy, ?_⟩
    have hUV : dist U V ≤ δ / 2 := by
      exact le_of_lt (by simpa only [mem_ball, dist_comm] using hnear)
    have hVy' : dist V y ≤ δ / 2 := hVy
    have hsum : dist U y ≤ δ := by
      calc dist U y ≤ dist U V + dist V y := dist_triangle _ _ _
        _ ≤ δ / 2 + δ / 2 := add_le_add hUV hVy'
        _ = δ := by ring
    simpa only [dist_eq_norm] using hsum
  · have hsep' : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ / 2 ≤ ‖x - y‖ := by
      intro x hx y hy hxy
      have hlt := hsep x hx y hy hxy
      simpa only [dist_eq_norm] using hlt.le
    have hnorm : ∀ x ∈ s, ‖x‖ ≤ 1 := by
      intro x hx
      have hxU := hsU hx
      have h1 : ‖x‖ = 1 := by
        have hx' : xᴴ * x = 1 := by
          simpa only [Matrix.star_eq_conjTranspose] using
            (Matrix.mem_unitaryGroup_iff'.mp hxU)
        have hmul : ‖x‖ * ‖x‖ = 1 := by
          rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hx', norm_one]
        nlinarith [norm_nonneg x]
      exact h1.le
    have hpack :=
      Qatlib.Foundations.MatrixGeometry.SphereNets.Packing.separated_card_bound
        s (δ / 2) hε hnorm hsep'
    have hfin : Module.finrank ℝ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) =
        2 * (2 ^ n) * (2 ^ n) := by
      rw [finrank_matrix_real]; ring
    rw [hfin] at hpack
    refine hpack.trans ?_
    have hratio : (1 + δ / 2 / 2) / (δ / 2 / 2) = 1 + 4 / δ := by
      field_simp
      ring
    rw [hratio]
    exact net_card_arithmetic n hn hδ0 hδ

end Qatlib.Papers.QCircApprox95.MainResults
