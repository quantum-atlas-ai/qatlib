/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.ReciprocalApproximation
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
import Qatlib.Concepts.QsvtCore.LinearSystems.PseudoinverseState
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Polynomial Matrix Filter
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Topology Matrix.Norms.L2Operator

def inverseEffectiveGap (δ : ℝ) : ℝ := min δ 1

noncomputable def inverseScale (n : ℕ) : ℝ := (2 * Real.sqrt (n : ℝ))⁻¹

noncomputable def normalizedInversePolynomial (n : ℕ) : Polynomial ℝ :=
  C ((Real.sqrt (n : ℝ))⁻¹) * reciprocalPolynomial n

theorem inverseScale_pos {n : ℕ} (hn : 0 < n) : 0 < inverseScale n := by
  unfold inverseScale
  exact inv_pos.mpr (mul_pos (by norm_num) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)))

theorem inverseScale_sq_div_four {n : ℕ} (hn : 0 < n) :
    inverseScale n ^ 2 / 4 = 1 / (16 * (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  unfold inverseScale
  rw [inv_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp
  ring

theorem normalizedInversePolynomial_half_eval (n : ℕ) (x : ℝ) :
    (normalizedInversePolynomial n).eval x / 2 =
      inverseScale n * (reciprocalPolynomial n).eval x := by
  simp only [normalizedInversePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    inverseScale, _root_.mul_inv_rev, div_eq_mul_inv]
  ring

theorem normalizedInversePolynomial_bounded {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) : |(normalizedInversePolynomial n).eval x| ≤ 1 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  simp only [normalizedInversePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    abs_mul, abs_of_pos (inv_pos.mpr hs)]
  calc
    _ ≤ (Real.sqrt (n : ℝ))⁻¹ * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left (reciprocalPolynomial_abs_le_sqrt n hx)
        (inv_nonneg.mpr hs.le)
    _ = 1 := inv_mul_cancel₀ hs.ne'

theorem normalizedInversePolynomial_natDegree {n : ℕ} (hn : 0 < n) :
    (normalizedInversePolynomial n).natDegree = 2 * n - 1 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [normalizedInversePolynomial, Polynomial.natDegree_C_mul (inv_ne_zero hs.ne'),
    reciprocalPolynomial_natDegree hn]

theorem normalizedInversePolynomial_comp_neg_X (n : ℕ) :
    (normalizedInversePolynomial n).comp (-X) = -normalizedInversePolynomial n := by
  simp [normalizedInversePolynomial, reciprocalPolynomial_comp_neg_X]

theorem exists_inverse_cutoff {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ n : ℕ, 0 < n ∧ reciprocalError (inverseEffectiveGap δ) n ≤ η / 2 := by
  have hd : 0 < inverseEffectiveGap δ := lt_min hδ (by norm_num)
  have hd1 : inverseEffectiveGap δ ≤ 1 := min_le_right _ _
  have he : ∀ᶠ n : ℕ in atTop, reciprocalError (inverseEffectiveGap δ) n < η / 2 :=
    (tendsto_order.mp (tendsto_reciprocalError hd hd1)).2 (η / 2) (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  refine ⟨max N 1, by omega, (hN _ (le_max_left _ _)).le⟩

theorem normalizedInversePolynomial_parity {n : ℕ} (hn : 0 < n) :
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2 * n - 1) (normalizedInversePolynomial n) := by
  have ho : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
  unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
  rw [normalizedInversePolynomial_comp_neg_X, ho.neg_one_pow]
  simp

theorem exists_inverse_phases {n : ℕ} (hn : 0 < n) :
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
      zs.length = 2 * n - 1 ∧
      ∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re =
        inverseScale n * (reciprocalPolynomial n).eval x := by
  have hd : (normalizedInversePolynomial n).degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) :=
    Polynomial.degree_le_of_natDegree_le (normalizedInversePolynomial_natDegree hn).le
  obtain ⟨base, zs, hb, hzs, hlen, _, hre⟩ :=
    Qatlib.Concepts.QspSimulation.Achievability.exists_phases_half_of_bounded hd
      (normalizedInversePolynomial_parity hn)
      (fun x hx => normalizedInversePolynomial_bounded hn hx)
  refine ⟨base, zs, hb, hzs, hlen, ?_⟩
  intro x
  have he := hre x
  have hh := normalizedInversePolynomial_half_eval n x
  linarith

section Encoding
variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

omit [Fintype I] [Fintype O] in

theorem projectedEncoding_average_lift {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} (h : ProjectedUnitaryEncoding A U L R) :
    ProjectedUnitaryEncoding A (averageCircuit U U) (averageFrame L) (averageFrame R) := by
  have he := average_projectedEncoding h h
  have hA : (2 : ℂ)⁻¹ • (A + A) = A := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  rwa [hA] at he

theorem realPart_pseudoinverse_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(((responseP base zs).eval (matrixSingularValues A i : ℂ)).re : ℂ) -
        (c : ℂ) / (matrixSingularValues A i : ℂ)‖ ≤ ε) :
    BlockEncoding ((c : ℂ) • matrixPseudoinverse A)
      (realPartQSVT U (rangeProjector R) (rangeProjector L) base zs)ᴴ
      (averageFrame R) (averageFrame L) 1 ε := by
  have he := realPartQSVT_odd_singularEncoding h hb zs hzs hodd
  have herr : ‖oddSingularTransform A (fun x => (c : ℂ) / (x : ℂ)) -
      oddSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ))‖ ≤ ε := by
    apply oddSingularTransform_error_le_positive A _ _ hε
    intro i hi
    simpa only [norm_sub_rev] using happrox i hi
  have hpert :=
      Qatlib.Concepts.BlockEncoding.Encoding.BlockEncoding.adjoint
      ((Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding he).perturb hε herr)
  simpa only [zero_add, inverseTransform_adjoint] using hpert

theorem constructivePseudoinverse_counted_encoding
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {δ η : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      δ ≤ matrixSingularValues A i) (hη : 0 < η) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × H))),
      0 < n ∧ reciprocalError (inverseEffectiveGap δ) n ≤ η / 2 ∧
      adjointQueryCount cs = 2 * n - 1 ∧ adjointGateCount cs = 2 * n ∧
      BlockEncoding ((inverseScale n : ℂ) • matrixPseudoinverse A)
        (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame L)
        1 (inverseScale n * η / 2) := by
  obtain ⟨n, hn, hcut⟩ := exists_inverse_cutoff hδ hη
  obtain ⟨base, zs, hb, hzs, hlen, hre⟩ := exists_inverse_phases hn
  have hc := inverseScale_pos hn
  have hd : 0 < inverseEffectiveGap δ := lt_min hδ (by norm_num)
  have hodd : zs.length % 2 = 1 := by rw [hlen]; omega
  have happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(((responseP base zs).eval (matrixSingularValues A i : ℂ)).re : ℂ) -
        (inverseScale n : ℂ) / (matrixSingularValues A i : ℂ)‖ ≤ inverseScale n * η / 2 := by
    intro i hi
    have hx : matrixSingularValues A i ∈ Set.Icc (inverseEffectiveGap δ) 1 :=
      ⟨(min_le_left δ 1).trans (hgap i hi), (encoded_singularValues_mem_unitInterval h i).2⟩
    have hs := scaledReciprocalPolynomial_error_le n (inverseScale n) hd hx
    rw [abs_of_pos hc] at hs
    have he : (((responseP base zs).eval (matrixSingularValues A i : ℂ)).re : ℂ) =
        (C (inverseScale n : ℂ) * complexReciprocalPolynomial n).eval
          (matrixSingularValues A i : ℂ) := by
      rw [hre]
      simp [complexReciprocalPolynomial_eval_real]
    rw [he]
    calc
      _ ≤ inverseScale n * reciprocalError (inverseEffectiveGap δ) n := hs
      _ ≤ inverseScale n * (η / 2) := mul_le_mul_of_nonneg_left hcut hc.le
      _ = inverseScale n * η / 2 := by ring
  have hW := realPart_pseudoinverse_approximation h hb zs hzs hodd
    (inverseScale n) (show 0 ≤ inverseScale n * η / 2 by positivity) happrox
  let cs := adjointCircuit (compileRealPartQSVT (rangeProjector R) (rangeProjector L) base zs)
  refine ⟨n, cs, hn, hcut, ?_, ?_, ?_⟩
  · dsimp only [cs]
    rw [adjointQueryCount_adjointCircuit, (counts_compileRealPartQSVT _ _ _ _).1, hlen]
  · dsimp only [cs]
    rw [adjointGateCount_adjointCircuit, (counts_compileRealPartQSVT _ _ _ _).2, hlen]
    omega
  · dsimp only [cs]
    rw [evaluate_adjointCircuit, evaluate_compileRealPartQSVT]
    exact hW

theorem constructivePseudoinverse_counted_output
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {δ η : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      δ ≤ matrixSingularValues A i) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × H))),
      0 < n ∧ reciprocalError (inverseEffectiveGap δ) n ≤ η / 2 ∧
      adjointQueryCount cs = 2 * n - 1 ∧ adjointGateCount cs = 2 * n ∧
      BlockEncoding ((inverseScale n : ℂ) • matrixPseudoinverse A)
        (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame L)
        1 (inverseScale n * η / 2) ∧
      ∀ b : QState O, Normalized b → (∃ z : QState I, A *ᵥ z = b) →
        1 / (16 * (n : ℝ)) ≤ postselectionProbability
          (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame L) b ∧
        0 < postselectionProbability
          (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame L) b ∧
        ∃ φ : QState I, postselectionOutput
          (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame L) b = some φ ∧
          IsMinimumNormSolutionState A b φ η := by
  obtain ⟨n, cs, hn, hcut, hqueries, hgates, hW⟩ :=
    constructivePseudoinverse_counted_encoding h hδ hgap hη
  refine ⟨n, cs, hn, hcut, hqueries, hgates, hW, ?_⟩
  intro b hb hrange
  have hc := inverseScale_pos hn
  have hehalf : inverseScale n * η / 2 ≤ inverseScale n / 2 := by nlinarith
  have hsmall : inverseScale n * η / 2 < inverseScale n := by linarith
  obtain ⟨hlower, hp, φ, hout, hspec⟩ := scaledPseudoinverse_postselection
    (projectedEncoding_average_lift h) hW hb hrange hsmall
  refine ⟨?_, hp, φ, hout, ?_⟩
  · calc
      1 / (16 * (n : ℝ)) = inverseScale n ^ 2 / 4 := (inverseScale_sq_div_four hn).symm
      _ = (inverseScale n / 2) ^ 2 := by ring
      _ ≤ (inverseScale n - inverseScale n * η / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ ≤ _ := hlower
  · have he : 2 * (inverseScale n * η / 2) / inverseScale n = η := by
      field_simp
    simpa only [he] using hspec

end Encoding
end Qatlib.Concepts.QsvtCore.LinearSystems
