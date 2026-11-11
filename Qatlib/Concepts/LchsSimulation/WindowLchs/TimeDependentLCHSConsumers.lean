/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeLchs
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Forced time-dependent LCHS and compiled output bounds

The time-dependent Cauchy representation acts on an initial vector and on each source vector in
the Duhamel integral. `time_dependent_forced_lchs_double_integral` gives the resulting forced
representation. `time_dependent_lchs_actual_prepared_output` connects the finite quadrature with
an actual compiled circuit and bounds the initial selected branch and its normalized direction.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `time_dependent_forced_lchs_double_integral`: gives the homogeneous-plus-source Cauchy
  representation.
* `time_dependent_lchs_actual_prepared_output`: gives circuit counts, branch mass, and direction
  error.

## References

* [An et al., 2023][AnLiuLin2023]
-/

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Concepts.LchsSimulation.WindowLchs
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

/-- The Cauchy-weighted integral of ordered Hamiltonian evolutions applied to `v` equals the
nonunitary ordered evolution applied to `v` under the continuity and positivity hypotheses. -/
private theorem tdLchs_integral_action {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (s t : ℝ) (hst : s ≤ t) (v : QState I) :
    (∫ k : ℝ, (1/(Real.pi*(1+k^2))) •
      (orderedEvolution (fun u => Complex.I • (H u+k • L u)) s t *ᵥ v)) =
      orderedEvolution (fun u => L u+Complex.I • H u) s t *ᵥ v := by
  have h := time_dependent_lchs_entire_parameter I L H s t hL hH hPSD hHerm hst
  let F := fun z : ℂ => orderedEvolution (fun u => z • L u+Complex.I • H u) s t
  have hw : Integrable (fun k : ℝ => 1/(Real.pi*(1+k^2))) := by
    simpa [div_eq_mul_inv, _root_.mul_inv_rev, mul_comm] using!
      integrable_inv_one_add_sq.const_mul Real.pi⁻¹
  have hc : Continuous (fun k : ℝ => F ((k : ℂ)*Complex.I)) :=
    h.1.continuous.comp (Complex.continuous_ofReal.mul (continuous_const (y := Complex.I)))
  have hn (k : ℝ) : ‖F ((k : ℂ)*Complex.I)‖ ≤ 1 := h.2 _ (by simp)
  have hi := hw.smul_bdd 1 hc.aestronglyMeasurable (Filter.Eventually.of_forall hn)
  have hb (k : ℝ) : F ((k : ℂ)*Complex.I) =
      orderedEvolution (fun u => Complex.I • (H u+k • L u)) s t := by
    dsimp [F]
    congr 1
    funext u
    rw [smul_add, ← Complex.coe_smul, smul_smul, mul_comm]
    exact add_comm _ _
  let m : Matrix I I ℂ →L[ℝ] QState I :=
    (LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℂ ℂ).flip v)).restrictScalars ℝ
  have hm := m.integral_comp_comm hi
  have he := (time_dependent_lchs_cauchy_representation I L H s t hL hH hPSD hHerm hst).2
  change (∫ k : ℝ, m ((1/(Real.pi*(1+k^2))) • F ((k : ℂ)*Complex.I))) =
    m (∫ k : ℝ, (1/(Real.pi*(1+k^2))) • F ((k : ℂ)*Complex.I)) at hm
  simp only [hb] at hm
  rw [he] at hm
  have hmapply (X : Matrix I I ℂ) : m X = X *ᵥ v := rfl
  simpa only [hmapply, Matrix.smul_mulVec] using! hm

/-- The forced solution is the Cauchy-weighted Hamiltonian integral of the initial vector plus
the iterated time-and-parameter integral of propagated source vectors [An et al., Equation
(7)][AnLiuLin2023]. -/
theorem time_dependent_forced_lchs_double_integral :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
      (b : ℝ → QState I) (v : QState I) (s t : ℝ),
      Continuous L → Continuous H → Continuous b →
      (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s ≤ t →
      orderedForcedSolution (fun u => L u+Complex.I • H u) b s v t =
        (∫ k : ℝ, (1/(Real.pi*(1+k^2))) •
          (orderedEvolution (fun u => Complex.I • (H u+k • L u)) s t *ᵥ v)) +
        ∫ u in s..t, ∫ k : ℝ, (1/(Real.pi*(1+k^2))) •
          (orderedEvolution (fun x => Complex.I • (H x+k • L x)) u t *ᵥ b u) := by
  intro I _ _ L H b v s t hL hH _hb hPSD hHerm hst
  dsimp [orderedForcedSolution]
  congr 1
  · exact (tdLchs_integral_action L H hL hH hPSD hHerm s t hst v).symm
  · apply intervalIntegral.integral_congr
    intro u hu
    exact (tdLchs_integral_action L H hL hH hPSD hHerm u t
      ((Set.uIcc_of_le hst ▸ hu).2) (b u)).symm

/-- The compiled time-dependent quadrature circuit is unitary with `k` queries and word length
`10 * k + 4`, with exact input and selection counts; if quadrature error `η` is below target
norm `τ`, its initial selected branch has squared norm at least `((τ - η) / coefficientMass
c) ^ 2` and direction error at most `2 * η / τ` [AnLiuLin2023]. -/
theorem time_dependent_lchs_actual_prepared_output :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
      (s t : ℝ) (K N k : ℕ) (B : Matrix I I ℂ) (i₀ : I) (j₀ : Fin N),
      Continuous L → Continuous H → (∀ u, (L u).PosSemidef) →
      (∀ u, (H u).IsHermitian) → s ≤ t → 0 < K → 0 < N →
      B ∈ Matrix.unitaryGroup I ℂ →
      let c := staticLchsCoeff K N
      let V := fun j : Fin N => orderedEvolution
        (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
      let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
      let y := staticLchsDataBranch j₀
        (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0) (Ket (j₀,i₀)))
      let v := orderedEvolution (fun u => L u+Complex.I • H u) s t *ᵥ (B *ᵥ Ket i₀)
      let τ := ‖toEuclidean_fromVec v‖
      let η := 2/(Real.pi*K)+(2*(K : ℝ)/N)*(2/Real.pi+∫ u in s..t, ‖L u‖)
      IsUnitaryCircuit (staticLchsCompile c V B j₀ i₀ k) ∧
      QueryCount (staticLchsCompile c V B j₀ i₀ k) = k ∧
      (staticLchsWord k).count .inputF = k+1 ∧ (staticLchsWord k).count .inputB = k ∧
      (staticLchsWord k).count .selectF = k+1 ∧ (staticLchsWord k).count .selectB = k ∧
      (staticLchsWord k).length = 10*k+4 ∧
      (η < τ → ((τ-η)/coefficientMass c)^2 ≤ ‖toEuclidean_fromVec y‖^2 ∧
        ‖toEuclidean_fromVec (((‖toEuclidean_fromVec y‖⁻¹ : ℝ) : ℂ) • y -
          ((τ⁻¹ : ℝ) : ℂ) • v)‖ ≤ 2*η/τ) := by
  intro I _ _ L H s t K N k B i₀ j₀ hL hH hPSD hHerm hst hK hN hB
  (try dsimp only)
  let c := staticLchsCoeff K N
  let V := fun j : Fin N => orderedEvolution
    (fun u => Complex.I • (H u+staticLchsGrid K N j • L u)) s t
  let T := orderedEvolution (fun u => L u+Complex.I • H u) s t
  let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
  let y := staticLchsDataBranch j₀
    (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0) (Ket (j₀,i₀)))
  let ψ := B *ᵥ Ket i₀
  let v := T *ᵥ ψ
  let η := 2/(Real.pi*K)+(2*(K : ℝ)/N)*(2/Real.pi+∫ u in s..t, ‖L u‖)
  have hα : 0 < coefficientMass c := static_lchs_coefficient_mass_pos K N hK hN
  have hV (j : Fin N) : V j ∈ unitaryGroup I ℂ :=
    ordered_evolution_hermitian_unitary I (fun u => H u+staticLchsGrid K N j • L u)
      (by fun_prop)
      (fun u => (hHerm u).add ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all _))) s t
  obtain ⟨hC, _, hsf, hsb, hif, hib, _hcf, _hcb, hquery, hlen⟩ :=
    static_lchs_actual_expanded_prepare_select_amplification I N c V B j₀ i₀ k hα hV hB
  refine ⟨hC, hquery, hif, hib, hsf, hsb, hlen, ?_⟩
  intro hgap
  let w := (∑ j, c j • V j) *ᵥ ψ
  have hψ : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).mp (normalized_applyGate hB (normalized_ket i₀))
  have hq : ‖(∑ j, c j • V j)-T‖ ≤ η :=
    time_dependent_lchs_quadrature_error I L H s t K N hL hH hPSD hHerm hst hK hN
  have hclose : ‖toEuclidean_fromVec w-toEuclidean_fromVec v‖ ≤ η := by
    have hm := l2_norm_mulVec_fromVec_le ((∑ j, c j • V j)-T) ψ
    rw [hψ, mul_one] at hm
    have hm' : ‖toEuclidean_fromVec w-toEuclidean_fromVec v‖ ≤ ‖(∑ j, c j • V j)-T‖ := by
      simpa only [Matrix.sub_mulVec, toEuclidean_fromVec, WithLp.toLp_sub] using! hm
    exact hm'.trans hq
  have hy : toEuclidean_fromVec y = (coefficientMass c)⁻¹ • toEuclidean_fromVec w := by
    have he := static_lchs_initial_data_branch_raw I N c V B j₀ i₀ hα hV hB
    change y = ((coefficientMass c : ℂ)⁻¹) • w at he
    rw [he]
    simp only [toEuclidean_fromVec, WithLp.toLp_smul, ← Complex.ofReal_inv, Complex.coe_smul]
  have hnorm : ‖toEuclidean_fromVec v‖-η ≤ ‖toEuclidean_fromVec w‖ := by
    have hrev : ‖toEuclidean_fromVec v-toEuclidean_fromVec w‖ ≤ η := by
      rw [norm_sub_rev]
      exact hclose
    have hh := (le_abs_self (‖toEuclidean_fromVec v‖-‖toEuclidean_fromVec w‖)).trans
      ((abs_norm_sub_norm_le (toEuclidean_fromVec v) (toEuclidean_fromVec w)).trans hrev)
    linarith
  constructor
  · have hlow : (‖toEuclidean_fromVec v‖-η)/coefficientMass c ≤ ‖toEuclidean_fromVec y‖ := by
      rw [hy, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hα.le)]
      exact (div_le_div_of_nonneg_right hnorm hα.le).trans_eq (by ring)
    exact pow_le_pow_left₀ (by positivity) hlow 2
  · have herr := (normalize_error_of_gap hclose hgap).2
    have hn : NormedSpace.normalize (toEuclidean_fromVec y) =
        NormedSpace.normalize (toEuclidean_fromVec w) := by
      rw [hy, NormedSpace.normalize_smul_of_pos (inv_pos.mpr hα)]
    rw [← hn] at herr
    simpa only [NormedSpace.normalize, toEuclidean_fromVec, WithLp.toLp_sub,
      WithLp.toLp_smul, Complex.coe_smul] using! herr

end Qatlib.Concepts.LchsSimulation.WindowLchs
