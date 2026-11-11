/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorPair

/-!
# Correlation bounds for quantum Max Cut energy

`corr` and `tParam` express register Pauli correlations and the mean of the XX and YY
correlations. The two-qubit positivity inequality yields `edge_energy_upper` and, for
nonnegative edge weights, `qmc_energy_upper`; auxiliary Bloch inner-product bounds establish
nonnegativity of clipped mixtures.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `global_t_range`: places distinct-site transverse correlations in [−1, 1].
* `qmc_energy_upper`: bounds graph energy by a weighted sum of clipped correlations.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorPair
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Reduction
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch

/-- The real trace of the axis-`a` pair Pauli operator against the register matrix `ρ`. -/
noncomputable def corr {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (a : Fin 3) : ℝ :=
  (pairPauli i j a*ρ).trace.re

/-- The arithmetic mean of the XX and YY pair correlations at sites `i` and `j`. -/
noncomputable def tParam {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) : ℝ :=
  (corr ρ i j 0+corr ρ i j 1)/2

/-- The ZZ correlation of a positive semidefinite trace-one two-qubit matrix is at least −1. -/
theorem local_zz_lower (ρ : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) : -1≤Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.corrZZ ρ := by
  have h00 : 0≤(ρ (0,0) (0,0)).re := (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i:=(0,0)))).1
  have h11 : 0≤(ρ (1,1) (1,1)).re := (RCLike.nonneg_iff.mp (hρ.diag_nonneg (i:=(1,1)))).1
  have ht : (ρ (0,0) (0,0)).re+(ρ (0,1) (0,1)).re+
      (ρ (1,0) (1,0)).re+(ρ (1,1) (1,1)).re=1 := by
    simpa [Matrix.trace,Fintype.sum_prod_type,Fin.sum_univ_two,add_assoc] using
        congrArg Complex.re htr
  have hc : Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.corrZZ ρ = (ρ (0,0) (0,0)).re-(ρ (0,1) (0,1)).re-
      (ρ (1,0) (1,0)).re+(ρ (1,1) (1,1)).re := by
    simp [Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.corrZZ,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.expect,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.opZZ,
      Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.kron,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.pauliZ,Matrix.trace,Matrix.mul_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two]
    ring
  rw [hc]
  linarith

/-- The mean XX/YY correlation of a positive semidefinite trace-one two-qubit matrix lies in
[−1, 1]. -/
theorem local_t_range (ρ : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    -1≤Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.tParam ρ ∧ Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.tParam ρ≤1 := by
  have hu := Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.lemma3_zz_bound ρ hρ htr
  have hl := local_zz_lower ρ hρ htr
  apply abs_le.mp
  linarith

/-- For a physical register density matrix and distinct sites, `tParam ρ i j` lies in [−1, 1],
as in the correlation analysis of [CrostaSaubanereHuber2026]. -/
theorem global_t_range {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) : -1≤tParam ρ i j ∧ tParam ρ i j≤1 := by
  have hd := reduced_density i j hij ρ hρ htr
  have h := local_t_range (reduced i j hij ρ) hd.1 hd.2
  simpa only [tParam,corr,pair_eq_lift i j hij,local_xx,local_yy,lift_trace,
    Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.tParam,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.corrXX,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.corrYY,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.expect] using h

/-- Scaling a Hamiltonian by a real scalar scales its energy by the same scalar. -/
theorem energy_smul {I : Type*} [Fintype I] (c : ℝ) (H ρ : Matrix I I ℂ) :
    energy (c • H) ρ = c*energy H ρ := by simp [energy,Matrix.trace_smul]

/-- For a trace-one matrix, the expectation of `edgeOperator i j` equals one minus the sum of
the three pair Pauli correlations. -/
theorem energy_edge {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (htr : ρ.trace=1) (i j : Fin n) :
    energy (edgeOperator i j) ρ = 1-(corr ρ i j 0+corr ρ i j 1+corr ρ i j 2) := by
  simp [energy,edgeOperator,corr,Matrix.sub_mul,Matrix.trace_sub,Matrix.add_mul,Matrix.trace_add,
    htr,Fin.sum_univ_three]

/-- For a physical density matrix and distinct sites, the QMC edge energy is at most the minimum
of `tParam ρ i j` and zero. -/
theorem edge_energy_upper {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) :
    energy ((-1/4:ℝ) • edgeOperator i j) ρ ≤ min (tParam ρ i j) 0 := by
  rw [energy_smul,energy_edge ρ htr]
  have hz := tensor_zz_bound i j hij ρ hρ htr
  change corr ρ i j 2 ≤ 1-2*|tParam ρ i j| at hz
  have ht : corr ρ i j 0+corr ρ i j 1=2*tParam ρ i j := by dsimp [tParam];ring
  by_cases hb : 0≤tParam ρ i j
  · rw [min_eq_right hb]
    rw [abs_of_nonneg hb] at hz
    linarith
  · have hb' := le_of_not_ge hb
    rw [min_eq_left hb']
    rw [abs_of_nonpos hb'] at hz
    linarith

/-- The QMC energy is the weighted sum of the energies of its −1/4-scaled edge operators. -/
theorem qmc_energy_sum {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) :
    energy (qmcHamiltonian ends w) ρ =
      ∑ e, w e*energy ((-1/4:ℝ) • edgeOperator (ends e).1 (ends e).2) ρ := by
  simp only [qmcHamiltonian,energy,Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum,
    Matrix.smul_mul,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- For distinct-site edges with nonnegative weights, the QMC energy of a physical density
matrix is at most the weighted sum of `min (tParam ρ i j) 0`. This is the physical candidate
bound used in [CrostaSaubanereHuber2026]. -/
theorem qmc_energy_upper {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n)
    (hends : ∀ e, (ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0≤w e)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    energy (qmcHamiltonian ends w) ρ ≤ ∑ e, w e*min (tParam ρ (ends e).1 (ends e).2) 0 := by
  rw [qmc_energy_sum]
  exact Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left
    (edge_energy_upper ρ hρ htr _ _ (hends e)) (hw e))

/-- The inner product of two real three-dimensional vectors in the closed unit ball is at most
one. -/
theorem bloch_dot_le_one (u v : Fin 3 → ℝ) (hu : sqnorm u≤1) (hv : sqnorm v≤1) :
    (∑ a, u a*v a)≤1 := by
  simp only [sqnorm,Fin.sum_univ_three] at hu hv ⊢
  nlinarith [sq_nonneg (u 0-v 0),sq_nonneg (u 1-v 1),sq_nonneg (u 2-v 2)]

/-- For `p ∈ [0, 1]` and two Bloch-ball vectors, the clipped mixture `-4*p*min t 0 +
(1-p)*(1-u·v)` is nonnegative. -/
theorem clipped_mixed_nonneg (p t : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (u v : Fin 3 → ℝ) (hu : sqnorm u≤1) (hv : sqnorm v≤1) :
    0≤-4*p*min t 0+(1-p)*(1-∑ a, u a*v a) := by
  have ht : min t 0≤0 := min_le_right _ _
  have hprod := bloch_dot_le_one u v hu hv
  exact add_nonneg (mul_nonneg_of_nonpos_of_nonpos (by nlinarith) ht)
    (mul_nonneg (by linarith) (by linarith))
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
