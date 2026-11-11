/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticLCHSConsumers

/-!
# Discrete LCHS vector and preparation stability

`general_discrete_lchs_vector_stability` bounds the norm and normalized-vector error of a
discrete linear combination approximating a target vector. The prepared-output theorem transfers
these bounds to the actual compiled branch, including circuit and query identities, while
`lchs_two_term_combination_vector_bound` combines homogeneous and inhomogeneous approximation
errors. See [AnChildsLin2026] for the paper context.

## Main statements

* `general_discrete_lchs_vector_stability`: Under the stated unitary and coefficient-mass
  hypotheses, if the discrete vector is within `η < τ` of a target of norm `τ` and has positive
  norm, its norm is at least `τ - η` and the normalized vectors differ by at most `2 * η / τ`.
* `general_discrete_lchs_actual_prepared_output`: With positive coefficient mass `α`, unitary
  preparation and summands, and vector error at most `η < τ`, the zero-amplification compilation
  is unitary with zero queries and word length four; its selected branch has squared norm at
  least `((τ - η) / α) ^ 2` and normalized error at most `2 * η / τ`.
* `lchs_two_term_combination_vector_bound`: Combining a homogeneous approximation with error
  `η₁` on the normalized input and an inhomogeneous approximation with error `η₂` gives total
  vector error at most `‖x₀‖ * η₁ + η₂` and the corresponding lower bound on the reconstructed
  norm.

## References

* [An et al., 2026][AnChildsLin2026]
-/

set_option warningAsError false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Under the stated unitary and coefficient-mass hypotheses, if the discrete vector is within
`η < τ` of a target of norm `τ` and has positive norm, its norm is at least `τ - η` and the
normalized vectors differ by at most `2 * η / τ`. -/
theorem general_discrete_lchs_vector_stability :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (E : Matrix I I ℂ) (x₀ : QState I) (η : ℝ),
    (∀ j, V j ∈ 𝐔[I]) →
    let v := E.mulVec x₀
    let w := (∑ j, c j • V j).mulVec x₀
    let τ := ‖toEuclidean_fromVec v‖
    0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass c →
    η < τ →
    ‖toEuclidean_fromVec w - toEuclidean_fromVec v‖ ≤ η →
    0 < ‖toEuclidean_fromVec w‖ →
      τ - η ≤ ‖toEuclidean_fromVec w‖ ∧
      ‖toEuclidean_fromVec ((↑‖toEuclidean_fromVec w‖⁻¹) • w - (↑τ⁻¹) • v)‖ ≤
        2 * η / τ := by
  intro I _ _ N c V E x₀ η _
  (try dsimp only)
  intro _ hgap hclose _
  constructor
  · have hrev : ‖toEuclidean_fromVec (E.mulVec x₀) -
        toEuclidean_fromVec ((∑ j, c j • V j).mulVec x₀)‖ ≤ η := by
      rw [norm_sub_rev]
      exact hclose
    have hh := (le_abs_self _).trans
      ((abs_norm_sub_norm_le (toEuclidean_fromVec (E.mulVec x₀))
        (toEuclidean_fromVec ((∑ j, c j • V j).mulVec x₀))).trans hrev)
    linarith
  · simpa only [NormedSpace.normalize, toEuclidean_fromVec, WithLp.toLp_sub,
      WithLp.toLp_smul, Complex.coe_smul] using! (normalize_error_of_gap hclose hgap).2

/-- With positive coefficient mass `α`, unitary preparation and summands, and vector error at
most `η < τ`, the zero-amplification compilation is unitary with zero queries and word
length four; its selected branch has squared norm at least `((τ - η) / α) ^ 2` and
normalized error at most `2 * η / τ`. -/
theorem general_discrete_lchs_actual_prepared_output :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (i₀ : I) (j₀ : Fin N)
    (E : Matrix I I ℂ) (η : ℝ),
    0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass c →
    (∀ j, V j ∈ 𝐔[I]) → B ∈ 𝐔[I] →
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    let x₀ := B.mulVec (Ket i₀)
    let v := E.mulVec x₀
    let τ := ‖toEuclidean_fromVec v‖
    ‖toEuclidean_fromVec ((∑ j, c j • V j).mulVec x₀) - toEuclidean_fromVec v‖ ≤ η →
    η < τ →
      IsUnitaryCircuit (staticLchsCompile c V B j₀ i₀ 0) ∧
      QueryCount (staticLchsCompile c V B j₀ i₀ 0) = 0 ∧
      (staticLchsWord 0).length = 10 * 0 + 4 ∧
      ((τ - η) / Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass c) ^ 2 ≤
          ‖toEuclidean_fromVec (staticLchsDataBranch j₀
            (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0)
              (Ket (j₀, i₀))))‖ ^ 2 ∧
        ‖toEuclidean_fromVec
            ((↑‖toEuclidean_fromVec (staticLchsDataBranch j₀
                (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0)
                  (Ket (j₀, i₀))))‖⁻¹) • staticLchsDataBranch j₀
              (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0)
                (Ket (j₀, i₀))) -
              (↑τ⁻¹) • v)‖ ≤ 2 * η / τ := by
  intro I _ _ N c V B i₀ j₀ E η hα hV hB
  (try dsimp only)
  intro hclose hgap
  let x₀ := B.mulVec (Ket i₀)
  let v := E.mulVec x₀
  let w := (∑ j, c j • V j).mulVec x₀
  let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
  let y := staticLchsDataBranch j₀
    (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0) (Ket (j₀, i₀)))
  obtain ⟨hC, _, _, _, _, _, _, _, hquery, hlen⟩ :=
    static_lchs_actual_expanded_prepare_select_amplification I N c V B j₀ i₀ 0 hα hV hB
  have hy : toEuclidean_fromVec y = (coefficientMass c)⁻¹ • toEuclidean_fromVec w := by
    have he := static_lchs_initial_data_branch_raw I N c V B j₀ i₀ hα hV hB
    change y = ((coefficientMass c : ℂ)⁻¹) • w at he
    rw [he]
    simp only [toEuclidean_fromVec, WithLp.toLp_smul, ← Complex.ofReal_inv, Complex.coe_smul]
  have hw : 0 < ‖toEuclidean_fromVec w‖ :=
    norm_pos_iff.mpr (normalize_error_of_gap hclose hgap).1
  obtain ⟨hnorm, _⟩ := general_discrete_lchs_vector_stability I N c V E x₀ η hV hα hgap hclose hw
  refine ⟨hC, hquery, hlen, ?_, ?_⟩
  · have hlow : (‖toEuclidean_fromVec v‖ - η) / coefficientMass c ≤ ‖toEuclidean_fromVec y‖ := by
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

/-- Combining a homogeneous approximation with error `η₁` on the normalized input and an
inhomogeneous approximation with error `η₂` gives total vector error at most `‖x₀‖ * η₁ +
η₂` and the corresponding lower bound on the reconstructed norm. -/
theorem lchs_two_term_combination_vector_bound :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (N₁ N₂ : ℕ) (c : Fin N₁ → ℂ)
    (V : Fin N₁ → Matrix I I ℂ) (c' : Fin N₂ → ℂ) (b : Fin N₂ → QState I)
    (E : Matrix I I ℂ) (x₀ : QState I) (w₀ : QState I) (η₁ η₂ : ℝ),
    (∀ j, V j ∈ 𝐔[I]) →
    let xhat := ((‖toEuclidean_fromVec x₀‖⁻¹ : ℝ) : ℂ) • x₀
    let v₁ := (∑ j, c j • V j).mulVec xhat
    let w := ∑ j' : Fin N₂, c' j' • b j'
    let vCmb := (‖toEuclidean_fromVec x₀‖ : ℂ) • v₁ + w
    let u := E.mulVec x₀ + w₀
    ‖toEuclidean_fromVec v₁ - toEuclidean_fromVec (E.mulVec xhat)‖ ≤ η₁ →
    ‖toEuclidean_fromVec w - toEuclidean_fromVec w₀‖ ≤ η₂ →
      ‖toEuclidean_fromVec vCmb - toEuclidean_fromVec u‖ ≤
          ‖toEuclidean_fromVec x₀‖ * η₁ + η₂ ∧
        ‖toEuclidean_fromVec u‖ - (‖toEuclidean_fromVec x₀‖ * η₁ + η₂) ≤
          ‖toEuclidean_fromVec vCmb‖ := by
  intro I _ _ N₁ N₂ c V c' b E x₀ w₀ η₁ η₂ _
  (try dsimp only)
  intro h₁ h₂
  let r := ‖toEuclidean_fromVec x₀‖
  let xhat := ((r⁻¹ : ℝ) : ℂ) • x₀
  have hrecover : (r : ℂ) • xhat = x₀ := by
    have h := NormedSpace.norm_smul_normalize (toEuclidean_fromVec x₀)
    apply_fun WithLp.ofLp at h
    simpa only [NormedSpace.normalize, toEuclidean_fromVec, WithLp.ofLp_smul,
      WithLp.ofLp_toLp, Complex.coe_smul] using! h
  have hlin : (r : ℂ) • E.mulVec xhat = E.mulVec x₀ := by
    rw [← Matrix.mulVec_smul, hrecover]
  have heq :
      toEuclidean_fromVec ((r : ℂ) • (∑ j, c j • V j).mulVec xhat +
        (∑ j', c' j' • b j')) - toEuclidean_fromVec (E.mulVec x₀ + w₀) =
      (r : ℂ) • (toEuclidean_fromVec ((∑ j, c j • V j).mulVec xhat) -
        toEuclidean_fromVec (E.mulVec xhat)) +
      (toEuclidean_fromVec (∑ j', c' j' • b j') - toEuclidean_fromVec w₀) := by
    rw [← hlin]
    simp only [toEuclidean_fromVec, WithLp.toLp_add,
      WithLp.toLp_smul, smul_sub]
    abel
  have herr : ‖toEuclidean_fromVec ((r : ℂ) • (∑ j, c j • V j).mulVec xhat +
      (∑ j', c' j' • b j')) - toEuclidean_fromVec (E.mulVec x₀ + w₀)‖ ≤
      r * η₁ + η₂ := by
    rw [heq]
    refine (norm_add_le _ _).trans (add_le_add ?_ h₂)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left h₁ (norm_nonneg _)
  refine ⟨herr, ?_⟩
  have hrev := (le_abs_self _).trans ((abs_norm_sub_norm_le
    (toEuclidean_fromVec (E.mulVec x₀ + w₀))
    (toEuclidean_fromVec ((r : ℂ) • (∑ j, c j • V j).mulVec xhat +
      (∑ j', c' j' • b j')))))
  rw [norm_sub_rev] at hrev
  dsimp only [r, xhat] at herr hrev ⊢
  linarith only [herr, hrev]

end Qatlib.Papers.LinDynamics23.DiscreteObs
