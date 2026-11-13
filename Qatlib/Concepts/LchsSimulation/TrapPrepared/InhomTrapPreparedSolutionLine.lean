/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TrapPrepared.InhomTrapPreparedSolutionStat
import Qatlib.Concepts.LchsSimulation.TimeTrapezoid.InhomogeneousTrapezoidSourceQuadrature

/-!
# Correctness of unified trapezoidal LCHS preparation

The unified family separates into homogeneous and source labels, has an explicit
coefficient-mass factorization, and consists of unitary matrices under the preparation
hypotheses. `inhTrap_unified_raw_vector` identifies its action with the homogeneous quadrature
plus the source quadrature. `inhomogeneousTrapezoidPreparedSolution` transfers vector
approximation error to the density of every positive-success compiled output.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `inhTrap_unified_coefficient_mass`: factors the combined mass into Cauchy mass and source
  mass.
* `inhTrap_unified_raw_vector`: identifies the unified approximation vector.
* `inhomogeneousTrapezoidPreparedSolution`: proves the conditional output density bound.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.TrapPrepared
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- On a homogeneous label, the unified coefficient is the corresponding static Cauchy-grid
coefficient. -/
theorem inhTrap_coeff_homogeneous (b : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ) (j : Fin N) :
    inhTrapUnifiedCoeff b s t K N Mt (Fin.castAdd (N*(Mt+1)) j) = staticLchsCoeff K N j := by
  simp [inhTrapUnifiedCoeff, j.isLt]

omit [DecidableEq I] in

/-- On a source label, the unified coefficient is the product of the time trapezoid weight,
Cauchy-grid coefficient, and sampled source norm. -/
theorem inhTrap_coeff_source (b : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ)
    (p : Fin N × Fin (Mt+1)) :
    inhTrapUnifiedCoeff b s t K N Mt (Fin.natAdd N (finProdFinEquiv p)) =
      (inhTrapWeight Mt s t p.2 : ℂ)*staticLchsCoeff K N p.1*
        (‖toEuclidean_fromVec (b (inhTrapNode Mt s t p.2))‖ : ℂ) := by
  unfold inhTrapUnifiedCoeff
  rw [dif_neg (by simp only [Fin.val_natAdd]; omega)]
  simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, Fin.eta, Equiv.symm_apply_apply]

omit [DecidableEq I] in

/-- For `s ≤ t`, the unified coefficient mass equals the Cauchy coefficient mass times one plus
the trapezoid-weighted sum of source norms. -/
theorem inhTrap_unified_coefficient_mass (b : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ)
    (hst : s ≤ t) :
    coefficientMass (inhTrapUnifiedCoeff b s t K N Mt) =
      coefficientMass (staticLchsCoeff K N) *
        (1+∑ l : Fin (Mt+1), inhTrapWeight Mt s t l*
          ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖) := by
  unfold coefficientMass
  rw [Fin.sum_univ_add]
  simp_rw [inhTrap_coeff_homogeneous]
  have he := (finProdFinEquiv : Fin N × Fin (Mt+1) ≃ Fin (N*(Mt+1))).sum_comp
    (fun y => ‖inhTrapUnifiedCoeff b s t K N Mt (Fin.natAdd N y)‖)
  rw [← he]
  simp_rw [inhTrap_coeff_source, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inh_trap_weight_nonneg Mt s t hst _),
    Real.norm_of_nonneg (norm_nonneg _)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hinner : ∀ l : Fin (Mt+1),
      (∑ j : Fin N, inhTrapWeight Mt s t l*‖staticLchsCoeff K N j‖*
        ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖) =
      inhTrapWeight Mt s t l*‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖*
        (∑ j : Fin N, ‖staticLchsCoeff K N j‖) := by
    intro l
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  ring

omit [DecidableEq I] in

/-- The unified coefficient mass is positive for positive cutoff and node count on an ordered
time interval. -/
theorem inhTrap_unified_mass_pos (b : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ)
    (hst : s ≤ t) (hK : 0 < K) (hN : 0 < N) :
    0 < coefficientMass (inhTrapUnifiedCoeff b s t K N Mt) := by
  rw [inhTrap_unified_coefficient_mass b s t K N Mt hst]
  apply mul_pos (static_lchs_coefficient_mass_pos K N hK hN)
  have : 0 ≤ ∑ l : Fin (Mt+1), inhTrapWeight Mt s t l*
      ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖ :=
    Finset.sum_nonneg (fun _ _ =>
      mul_nonneg (inh_trap_weight_nonneg Mt s t hst _) (norm_nonneg _))
  linarith

/-- Every unified matrix is unitary when the generators have the stated continuity and
Hermiticity properties and all input and source preparation matrices are unitary. -/
theorem inhTrap_unified_unitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt+1) → Matrix I I ℂ)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    ∀ x, inhTrapUnifiedUnitary L H s t K N Mt B P x ∈ unitaryGroup I ℂ := by
  have hV (a z : ℝ) (j : Fin N) :
      orderedEvolution (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) a z ∈
        unitaryGroup I ℂ :=
    ordered_evolution_hermitian_unitary I (fun u => H u+staticLchsGrid K N j • L u)
      (by fun_prop)
      (fun u => (hHerm u).add ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all _))) a z
  intro x
  unfold inhTrapUnifiedUnitary
  split
  · exact hV _ _ _
  · exact (unitaryGroup I ℂ).mul_mem (hV _ _ _)
      ((unitaryGroup I ℂ).mul_mem (hP _) (Unitary.star_mem hB))

/-- On a homogeneous label, the unified matrix is the full-interval ordered Hamiltonian
propagator at that Cauchy-grid node. -/
theorem inhTrap_unitary_homogeneous (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt+1) → Matrix I I ℂ) (j : Fin N) :
    inhTrapUnifiedUnitary L H s t K N Mt B P (Fin.castAdd (N*(Mt+1)) j) =
      orderedEvolution (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t := by
  simp [inhTrapUnifiedUnitary, j.isLt]

/-- On a source label, the unified matrix is the source-time Hamiltonian propagator multiplied
by the source preparation and the conjugate transpose of the input preparation. -/
theorem inhTrap_unitary_source (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt+1) → Matrix I I ℂ) (p : Fin N × Fin (Mt+1)) :
    inhTrapUnifiedUnitary L H s t K N Mt B P (Fin.natAdd N (finProdFinEquiv p)) =
      inhTrapSourceKUnitary L H s t K N Mt p.1 p.2*(P p.2*Bᴴ) := by
  unfold inhTrapUnifiedUnitary
  rw [dif_neg (by simp only [Fin.val_natAdd]; omega)]
  simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, Fin.eta, Equiv.symm_apply_apply]

/-- If the source preparations load the normalized nonzero source vectors, applying the unified
linear combination to the prepared input gives the homogeneous quadrature vector plus the
trapezoidal source sum. -/
theorem inhTrap_unified_raw_vector (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K N Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt+1) → Matrix I I ℂ) (i₀ : I)
    (hB : B ∈ unitaryGroup I ℂ)
    (hprep : ∀ l : Fin (Mt+1), b (inhTrapNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ = ((‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
        b (inhTrapNode Mt s t l)) :
    (∑ x, inhTrapUnifiedCoeff b s t K N Mt x •
        inhTrapUnifiedUnitary L H s t K N Mt B P x) *ᵥ
        (B *ᵥ Ket i₀) =
      (∑ j : Fin N, staticLchsCoeff K N j •
        orderedEvolution (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t) *ᵥ
          (B *ᵥ Ket i₀)+inhTrapSourceSum L H b s t K N Mt := by
  have hundo : Bᴴ *ᵥ (B *ᵥ Ket i₀) = Ket i₀ := by
    have hBB : Bᴴ*B = 1 := Matrix.mem_unitaryGroup_iff'.mp hB
    rw [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
  rw [Fin.sum_univ_add, Matrix.add_mulVec]
  simp_rw [inhTrap_coeff_homogeneous, inhTrap_unitary_homogeneous]
  congr 1
  rw [Matrix.sum_mulVec]
  have he := (finProdFinEquiv : Fin N × Fin (Mt+1) ≃ Fin (N*(Mt+1))).sum_comp
    (fun y => (inhTrapUnifiedCoeff b s t K N Mt (Fin.natAdd N y) •
      inhTrapUnifiedUnitary L H s t K N Mt B P (Fin.natAdd N y)) *ᵥ (B *ᵥ Ket i₀))
  rw [← he]
  simp_rw [inhTrap_coeff_source, inhTrap_unitary_source, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hundo]
  have hnode (p : Fin N × Fin (Mt+1)) :
      ((inhTrapWeight Mt s t p.2 : ℂ)*staticLchsCoeff K N p.1*
        (‖toEuclidean_fromVec (b (inhTrapNode Mt s t p.2))‖ : ℂ)) •
        (inhTrapSourceKUnitary L H s t K N Mt p.1 p.2 *ᵥ (P p.2 *ᵥ Ket i₀)) =
      (inhTrapWeight Mt s t p.2 : ℂ) • (staticLchsCoeff K N p.1 •
        (inhTrapSourceKUnitary L H s t K N Mt p.1 p.2 *ᵥ b (inhTrapNode Mt s t p.2))) := by
    by_cases hz : b (inhTrapNode Mt s t p.2) = 0
    · simp [hz, toEuclidean_fromVec]
    · rw [hprep p.2 hz, Matrix.mulVec_smul, smul_smul, smul_smul]
      have hn : ‖toEuclidean_fromVec (b (inhTrapNode Mt s t p.2))‖ ≠ 0 := by
        apply norm_ne_zero_iff.mpr
        intro h
        apply hz
        exact (WithLp.toLp_injective 2)
            (by simpa only [toEuclidean_fromVec, WithLp.toLp_zero] using! h)
      rw [Complex.ofReal_inv, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn), mul_one]
  simp_rw [hnode]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.smul_sum, ← Matrix.smul_mulVec, ← Matrix.sum_mulVec]
  rfl

/-- Every positive-success compiled unified output has density trace norm error at most `4 * ε /
τ` when its raw approximation error is at most `ε ≤ τ / 2` and the forced output norm is at
least `τ` [AnLiuLin2023]. -/
theorem inhomogeneousTrapezoidPreparedSolution : InhomogeneousTrapezoidPreparedSolution := by
  intro I _ _ L H b s t ε τ K N Mt B P i₀ j₀ hL hH hPSD hHerm hst hB hP
    _hprep hK hN _hMt hε hτ hετ
  (try dsimp only)
  intro hτx he k hp
  let c := inhTrapUnifiedCoeff b s t K N Mt
  let V := inhTrapUnifiedUnitary L H s t K N Mt B P
  let x := orderedForcedSolution (fun u => L u+Complex.I • H u) b s (B *ᵥ Ket i₀) t
  let y := (∑ j, c j • V j) *ᵥ (B *ᵥ Ket i₀)
  have hα := inhTrap_unified_mass_pos b s t K N Mt hst hK hN
  have hV := inhTrap_unified_unitary L H s t K N Mt B P hL hH hPSD hHerm hB hP
  have herr := (static_lchs_output_density_error_of_vector_error x y ε τ hε hτ hετ hτx he).2
  have hi := static_lchs_actual_postselected_density_invariant I (N+N*(Mt+1)) c V B j₀ i₀ k
    hα hV hB hp
  have hr : (∑ j, (c j / (coefficientMass c : ℂ)) • V j) *ᵥ (B *ᵥ Ket i₀) =
      ((coefficientMass c : ℂ)⁻¹) • y := by
    rw [← static_lchs_actual_initial_data_branch I (N+N*(Mt+1)) c V B j₀ i₀ hα hV hB,
      static_lchs_initial_data_branch_raw I (N+N*(Mt+1)) c V B j₀ i₀ hα hV hB]
  have hα0 : (coefficientMass c : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hα.ne')
  rw [hi, hr, static_lchs_output_density_smul y _ hα0]
  exact herr

end Qatlib.Concepts.LchsSimulation.TrapPrepared
