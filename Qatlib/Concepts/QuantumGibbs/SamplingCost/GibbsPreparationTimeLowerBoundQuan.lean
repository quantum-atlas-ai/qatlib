/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.SamplingCost.GibbsPreparationTimeLowerBoundStat
public import Qatlib.Concepts.QuantumGibbs.SamplingCost.PurifiedGibbsReflectionLowerBoundQuan
public import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Foundations.QueryWordCore.HamiltonianQuery Qatlib.Concepts.ReferenceError.MixturePaths

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.CopyEvolution.Discriminate Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QuantumGibbs.SamplingCost
open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable def thermalZeroWeight (s : ℝ) : ℝ := 1 / (1 + Real.exp (-s))

/-- The zero diagonal entry of the two-level Gibbs state is `thermalZeroWeight`. -/
theorem gibbsTwoLevel_zero_entry (s : ℝ) :
    gibbsTwoLevel s 0 0 = (thermalZeroWeight s : ℂ) := by
  simp [gibbsTwoLevel, thermalZeroWeight, Fin.sum_univ_two]

/-- The norm of the zero diagonal entry of a two-dimensional matrix is at most its trace norm. -/
theorem thermal_zero_entry_le_traceNorm (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖M 0 0‖ ≤ Matrix.traceNorm M := by
  let E : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i = 0 then 1 else 0)
  have hn : ‖E‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    split <;> norm_num
  have ht : Matrix.trace (E * M) = M 0 0 := by
    simp [E, Matrix.trace, Matrix.diagonal_mul]
  calc
    _ = ‖Matrix.trace (E * M)‖ := congrArg norm ht.symm
    _ ≤ Matrix.traceNorm (E * M) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖E‖ * Matrix.traceNorm M := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1 * Matrix.traceNorm M := mul_le_mul_of_nonneg_right hn (Matrix.traceNorm_nonneg _)
    _ = _ := one_mul _

def thermalZeroEvent (A : ℕ) : Finset (Fin 2 × Fin A) :=
  Finset.univ.filter (fun a => a.1 = 0)

/-- The zero diagonal entry of a pure state's reduced density matrix is the probability of the
thermal zero event. -/
theorem thermal_marginal_zero_entry (A : ℕ) (ψ : QState (Fin 2 × Fin A)) :
    PartialTrace (pureDensity ψ) 0 0 = (MeasureProb ψ (thermalZeroEvent A) : ℂ) := by
  simp only [PartialTrace, pureDensity, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def, Complex.mul_conj']
  unfold MeasureProb thermalZeroEvent BornProb
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.reduceEq, ite_true, ite_false, Finset.sum_const_zero,
    add_zero]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]

/-- The operator norm distance between two lifted two-level Hamiltonians is at most the absolute
difference of their parameters. -/
theorem thermal_lift_distance_le (A : ℕ) (Δ Γ : ℝ) :
    ‖twoLevelHamiltonianLift A Δ - twoLevelHamiltonianLift A Γ‖ ≤ |Δ - Γ| :=
  reflection_lift_distance_le A Δ Γ

/-- For positive perturbations at most one, the increase in the thermal zero weight is at least
one quarter of the perturbation times the exponential of minus two. -/
theorem thermal_gibbs_sensitivity {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.exp (-2) * ε / 4 ≤ thermalZeroWeight (1 + ε) - thermalZeroWeight 1 := by
  let x := Real.exp (-1)
  let y := Real.exp (-ε)
  have hx : 0 < x := Real.exp_pos _
  have hy : 0 < y := Real.exp_pos _
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hy1 : y ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hyx : x ≤ y := Real.exp_le_exp.mpr (by linarith)
  have hey : y * Real.exp ε = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hgap : x * ε ≤ 1 - y := by
    calc
      _ ≤ y * ε := mul_le_mul_of_nonneg_right hyx hε.le
      _ ≤ y * (Real.exp ε - 1) := mul_le_mul_of_nonneg_left (by
        linarith [Real.add_one_le_exp ε]) hy.le
      _ = _ := by nlinarith [hey]
  have hxx : x * x = Real.exp (-2) := by
    rw [← Real.exp_add]; norm_num
  have hnum : Real.exp (-2) * ε ≤ x * (1 - y) := by
    rw [← hxx]
    nlinarith
  have hdenpos : 0 < (1 + x) * (1 + x * y) := by positivity
  have hxy : x * y ≤ 1 := (mul_le_mul hx1 hy1 hy.le zero_le_one).trans_eq (one_mul 1)
  have hden : (1 + x) * (1 + x * y) ≤ 4 := by nlinarith
  have he : Real.exp (-(1 + ε)) = x * y := by
    rw [show -(1 + ε) = -1 + -ε by ring, Real.exp_add]
  have hEq : thermalZeroWeight (1 + ε) - thermalZeroWeight 1 =
      x * (1 - y) / ((1 + x) * (1 + x * y)) := by
    unfold thermalZeroWeight
    rw [he]
    change 1 / (1 + x * y) - 1 / (1 + x) = _
    field_simp
    ring
  rw [hEq]
  calc
    _ ≤ x * (1 - y) / 4 := div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_left (by nlinarith) hdenpos hden

/-- Establishes the evolution-time lower bound for a valid query program preparing both nearby
two-level Gibbs states within the specified trace-norm error. -/
theorem gibbsPreparationTimeLowerBound : GibbsPreparationTimeLowerBound := by
  intro A β ε δ p ψ₀ hβ hε hε1 _hδ hp hψ h0 h1
  let H0 := twoLevelHamiltonianLift A (1 / β)
  let H1 := twoLevelHamiltonianLift A ((1 + ε) / β)
  let Φ0 := HamiltonianQueryRun H0 p ψ₀
  let Φ1 := HamiltonianQueryRun H1 p ψ₀
  let q0 := MeasureProb Φ0 (thermalZeroEvent A)
  let q1 := MeasureProb Φ1 (thermalZeroEvent A)
  have hb : 0 < β := by linarith
  have hH0 : H0.IsHermitian := twoLevelHamiltonianLift_hermitian _ _
  have hH1 : H1.IsHermitian := twoLevelHamiltonianLift_hermitian _ _
  have hnψ : ‖toEuclidean_fromVec ψ₀‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec _).mp hψ
  have hn0 : Normalized Φ0 := (normalized_iff_norm_toEuclidean_fromVec _).mpr (by
    change ‖toEuclidean_fromVec (HamiltonianQueryRun H0 p ψ₀)‖ = 1
    rw [norm_hamiltonianQueryRun H0 hH0 p hp, hnψ])
  have hn1 : Normalized Φ1 := (normalized_iff_norm_toEuclidean_fromVec _).mpr (by
    change ‖toEuclidean_fromVec (HamiltonianQueryRun H1 p ψ₀)‖ = 1
    rw [norm_hamiltonianQueryRun H1 hH1 p hp, hnψ])
  have hdist : ‖H0 - H1‖ ≤ ε / β := by
    have he : |1 / β - (1 + ε) / β| = ε / β := by
      rw [show 1 / β - (1 + ε) / β = -(ε / β) by ring, abs_neg, abs_of_pos (div_pos hε hb)]
    exact (thermal_lift_distance_le A (1 / β) ((1 + ε) / β)).trans_eq he
  have hhybrid : ‖toEuclidean_fromVec (Φ0 - Φ1)‖ ≤ HamiltonianEvolutionTime p * (ε / β) := by
    have h := norm_hamiltonianQueryRun_sub_le H0 H1 hH0 hH1 p hp ψ₀
    rw [hnψ, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdist (hamiltonianEvolutionTime_nonneg p))
  have hread : |q0 - q1| ≤ 2 * (HamiltonianEvolutionTime p * (ε / β)) :=
    (measureProb_sub_le_two_mul_l2 Φ0 Φ1 (thermalZeroEvent A) hn0 hn1).trans
      (mul_le_mul_of_nonneg_left hhybrid (by norm_num))
  have he0 : |q0 - thermalZeroWeight 1| ≤ δ := by
    have h :=
        (thermal_zero_entry_le_traceNorm (PartialTrace (pureDensity Φ0) - gibbsTwoLevel 1)).trans h0
    change ‖PartialTrace (pureDensity Φ0) 0 0 - gibbsTwoLevel 1 0 0‖ ≤ δ at h
    rw [thermal_marginal_zero_entry, gibbsTwoLevel_zero_entry, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have he1 : |q1 - thermalZeroWeight (1 + ε)| ≤ δ := by
    have h := (thermal_zero_entry_le_traceNorm
      (PartialTrace (pureDensity Φ1) - gibbsTwoLevel (1 + ε))).trans h1
    change ‖PartialTrace (pureDensity Φ1) 0 0 - gibbsTwoLevel (1 + ε) 0 0‖ ≤ δ at h
    rw [thermal_marginal_zero_entry, gibbsTwoLevel_zero_entry, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hupper : |thermalZeroWeight (1 + ε) - thermalZeroWeight 1| ≤
      δ + 2 * (HamiltonianEvolutionTime p * (ε / β)) + δ := by
    calc
      _ ≤ |thermalZeroWeight (1 + ε) - q1| + |q1 - q0| + |q0 - thermalZeroWeight 1| := by
        exact (abs_sub_le _ _ _).trans (by
          linarith [abs_sub_le q1 q0 (thermalZeroWeight 1)])
      _ ≤ _ := add_le_add (add_le_add (by simpa only [abs_sub_comm] using he1)
        (by simpa only [abs_sub_comm] using hread)) he0
  have hlower := thermal_gibbs_sensitivity hε hε1
  have habs := le_abs_self (thermalZeroWeight (1 + ε) - thermalZeroWeight 1)
  nlinarith

end Qatlib.Concepts.QuantumGibbs.SamplingCost
