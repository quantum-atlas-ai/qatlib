/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousPreparedSolutionStat
import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureLine

/-!
# Prepared solutions from a unified LCHS family

The unified coefficient and propagator family reproduces the sum of the homogeneous
approximation and `inhSourceSum`. The theorem `inhomogeneousPreparedSolution` transfers a
raw-vector error bound to a trace-norm bound for the successful compiled output. See
[AnLiuLin2023] for the mathematical setting.

## Main statements

* `inh_unified_raw_vector`: When `B` is unitary and `P` prepares the normalized nonzero source
  samples, the unified linear combination applied to the prepared input equals the homogeneous
  approximation plus `inhSourceSum`.
* `inhomogeneousPreparedSolution`: A raw-vector error at most `ε` and solution norm at least
  `τ`, with `ε ≤ τ / 2`, give trace-norm error at most `4 * ε / τ` on every successful compiled
  output. This realizes a prepared-solution consequence of the LCHS construction in
  [AnLiuLin2023].

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
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

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- On the homogeneous index block, `inhUnifiedCoeff` equals the static LCHS coefficient. -/
theorem inh_coeff_homogeneous (b : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ) (j : Fin N) :
    inhUnifiedCoeff b s t K N Mt (Fin.castAdd (N*Mt) j) = staticLchsCoeff K N j := by
  simp [inhUnifiedCoeff, j.isLt]

omit [DecidableEq I] in

/-- On a source index, `inhUnifiedCoeff` is the product of the time step, static coefficient,
and sampled source norm. -/
theorem inh_coeff_source (b : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ)
    (p : Fin N × Fin Mt) :
    inhUnifiedCoeff b s t K N Mt (Fin.natAdd N (finProdFinEquiv p)) =
      (inhStep Mt s t : ℂ)*staticLchsCoeff K N p.1*
        (‖toEuclidean_fromVec (b (inhNode Mt s t p.2))‖ : ℂ) := by
  unfold inhUnifiedCoeff
  rw [dif_neg (by simp only [Fin.val_natAdd]; omega)]
  simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, Fin.eta, Equiv.symm_apply_apply]

omit [DecidableEq I] in

/-- For `s ≤ t`, the unified coefficient mass equals the static mass times one plus the
left-grid sum of source norms. -/
theorem inh_unified_coefficient_mass (b : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ)
    (hst : s ≤ t) :
    coefficientMass (inhUnifiedCoeff b s t K N Mt) =
      coefficientMass (staticLchsCoeff K N) *
        (1+∑ l : Fin Mt, inhStep Mt s t*‖toEuclidean_fromVec (b (inhNode Mt s t l))‖) := by
  unfold coefficientMass
  rw [Fin.sum_univ_add]
  simp_rw [inh_coeff_homogeneous]
  have he := (finProdFinEquiv : Fin N × Fin Mt ≃ Fin (N*Mt)).sum_comp
    (fun y => ‖inhUnifiedCoeff b s t K N Mt (Fin.natAdd N y)‖)
  rw [← he]
  simp_rw [inh_coeff_source, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inh_step_nonneg Mt s t hst), Real.norm_of_nonneg (norm_nonneg _)]
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

omit [DecidableEq I] in

/-- For `s ≤ t` and positive `K` and `N`, the unified coefficient mass is positive. -/
theorem inh_unified_mass_pos (b : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ)
    (hst : s ≤ t) (hK : 0 < K) (hN : 0 < N) :
    0 < coefficientMass (inhUnifiedCoeff b s t K N Mt) := by
  rw [inh_unified_coefficient_mass b s t K N Mt hst]
  apply mul_pos (static_lchs_coefficient_mass_pos K N hK hN)
  have : 0 ≤ ∑ l : Fin Mt, inhStep Mt s t*‖toEuclidean_fromVec (b (inhNode Mt s t l))‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (inh_step_nonneg Mt s t hst) (norm_nonneg _))
  linarith

/-- For continuous positive semidefinite `L`, continuous Hermitian `H`, and unitary preparation
matrices, every member of `inhUnifiedUnitary` is unitary. -/
theorem inh_unified_unitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin Mt → Matrix I I ℂ)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    ∀ x, inhUnifiedUnitary L H s t K N Mt B P x ∈ unitaryGroup I ℂ := by
  have hV (a z : ℝ) (j : Fin N) :
      orderedEvolution (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) a z ∈
        unitaryGroup I ℂ :=
    ordered_evolution_hermitian_unitary I (fun u => H u+staticLchsGrid K N j • L u)
      (by fun_prop)
      (fun u => (hHerm u).add ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all _))) a z
  intro x
  unfold inhUnifiedUnitary
  split
  · exact hV _ _ _
  · exact (unitaryGroup I ℂ).mul_mem (hV _ _ _)
      ((unitaryGroup I ℂ).mul_mem (hP _) (Unitary.star_mem hB))

/-- The homogeneous block of `inhUnifiedUnitary` is the ordered evolution generated by
`Complex.I • (H u + staticLchsGrid K N j • L u)`. -/
theorem inh_unitary_homogeneous (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin Mt → Matrix I I ℂ) (j : Fin N) :
    inhUnifiedUnitary L H s t K N Mt B P (Fin.castAdd (N*Mt) j) =
      orderedEvolution (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t := by
  simp [inhUnifiedUnitary, j.isLt]

/-- The source block of `inhUnifiedUnitary` is the source propagator followed by the preparation
correction `P p.2 * Bᴴ`. -/
theorem inh_unitary_source (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin Mt → Matrix I I ℂ) (p : Fin N × Fin Mt) :
    inhUnifiedUnitary L H s t K N Mt B P (Fin.natAdd N (finProdFinEquiv p)) =
      inhSourceKUnitary L H s t K N Mt p.1 p.2*(P p.2*Bᴴ) := by
  unfold inhUnifiedUnitary
  rw [dif_neg (by simp only [Fin.val_natAdd]; omega)]
  simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, Fin.eta, Equiv.symm_apply_apply]

/-- When `B` is unitary and `P` prepares the normalized nonzero source samples, the unified
linear combination applied to the prepared input equals the homogeneous approximation plus
`inhSourceSum`. -/
theorem inh_unified_raw_vector (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K N Mt : ℕ) (B : Matrix I I ℂ) (P : Fin Mt → Matrix I I ℂ) (i₀ : I)
    (hB : B ∈ unitaryGroup I ℂ)
    (hprep : ∀ l : Fin Mt, b (inhNode Mt s t l) ≠ 0 →
      P l *ᵥ Ket i₀ = ((‖toEuclidean_fromVec (b (inhNode Mt s t l))‖⁻¹ : ℝ) : ℂ) •
        b (inhNode Mt s t l)) :
    (∑ x, inhUnifiedCoeff b s t K N Mt x • inhUnifiedUnitary L H s t K N Mt B P x) *ᵥ
        (B *ᵥ Ket i₀) =
      (∑ j : Fin N, staticLchsCoeff K N j •
        orderedEvolution (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t) *ᵥ
          (B *ᵥ Ket i₀)+inhSourceSum L H b s t K N Mt := by
  have hundo : Bᴴ *ᵥ (B *ᵥ Ket i₀) = Ket i₀ := by
    have hBB : Bᴴ*B = 1 := Matrix.mem_unitaryGroup_iff'.mp hB
    rw [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
  rw [Fin.sum_univ_add, Matrix.add_mulVec]
  simp_rw [inh_coeff_homogeneous, inh_unitary_homogeneous]
  congr 1
  rw [Matrix.sum_mulVec]
  have he := (finProdFinEquiv : Fin N × Fin Mt ≃ Fin (N*Mt)).sum_comp
    (fun y => (inhUnifiedCoeff b s t K N Mt (Fin.natAdd N y) •
      inhUnifiedUnitary L H s t K N Mt B P (Fin.natAdd N y)) *ᵥ (B *ᵥ Ket i₀))
  rw [← he]
  simp_rw [inh_coeff_source, inh_unitary_source, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hundo]
  have hnode (p : Fin N × Fin Mt) :
      ((inhStep Mt s t : ℂ)*staticLchsCoeff K N p.1*
        (‖toEuclidean_fromVec (b (inhNode Mt s t p.2))‖ : ℂ)) •
        (inhSourceKUnitary L H s t K N Mt p.1 p.2 *ᵥ (P p.2 *ᵥ Ket i₀)) =
      (inhStep Mt s t : ℂ) • (staticLchsCoeff K N p.1 •
        (inhSourceKUnitary L H s t K N Mt p.1 p.2 *ᵥ b (inhNode Mt s t p.2))) := by
    by_cases hz : b (inhNode Mt s t p.2) = 0
    · simp [hz, toEuclidean_fromVec]
    · rw [hprep p.2 hz, Matrix.mulVec_smul, smul_smul, smul_smul]
      have hn : ‖toEuclidean_fromVec (b (inhNode Mt s t p.2))‖ ≠ 0 := by
        apply norm_ne_zero_iff.mpr
        intro h
        apply hz
        exact (WithLp.toLp_injective 2)
            (by simpa only [toEuclidean_fromVec, WithLp.toLp_zero] using! h)
      rw [Complex.ofReal_inv, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn), mul_one]
  simp_rw [hnode]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.smul_sum, ← Matrix.smul_mulVec, ← Matrix.sum_mulVec]
  rw [Finset.smul_sum]
  rfl

/-- A raw-vector error at most `ε` and solution norm at least `τ`, with `ε ≤ τ / 2`, give
trace-norm error at most `4 * ε / τ` on every successful compiled output. This realizes a
prepared-solution consequence of the LCHS construction in [AnLiuLin2023]. -/
theorem inhomogeneousPreparedSolution : InhomogeneousPreparedSolution := by
  intro I _ _ L H b s t ε τ K N Mt B P i₀ j₀ hL hH hPSD hHerm hst hB hP
    _hprep hK hN _hMt hε hτ hετ
  (try dsimp only)
  intro hτx he k hp
  let c := inhUnifiedCoeff b s t K N Mt
  let V := inhUnifiedUnitary L H s t K N Mt B P
  let x := orderedForcedSolution (fun u => L u+Complex.I • H u) b s (B *ᵥ Ket i₀) t
  let y := (∑ j, c j • V j) *ᵥ (B *ᵥ Ket i₀)
  have hα := inh_unified_mass_pos b s t K N Mt hst hK hN
  have hV := inh_unified_unitary L H s t K N Mt B P hL hH hPSD hHerm hB hP
  have herr := (static_lchs_output_density_error_of_vector_error x y ε τ hε hτ hετ hτx he).2
  have hi := static_lchs_actual_postselected_density_invariant I (N+N*Mt) c V B j₀ i₀ k
    hα hV hB hp
  have hr : (∑ j, (c j / (coefficientMass c : ℂ)) • V j) *ᵥ (B *ᵥ Ket i₀) =
      ((coefficientMass c : ℂ)⁻¹) • y := by
    rw [← static_lchs_actual_initial_data_branch I (N+N*Mt) c V B j₀ i₀ hα hV hB,
      static_lchs_initial_data_branch_raw I (N+N*Mt) c V B j₀ i₀ hα hV hB]
  have hα0 : (coefficientMass c : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hα.ne')
  rw [hi, hr, static_lchs_output_density_smul y _ hα0]
  exact herr

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
