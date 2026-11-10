/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.ExceptionalPhaseGradientTransportStat
import Qatlib.Concepts.GradientOracle.ReadoutTools.PureStateEventLipschitzOpti
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical

namespace ExceptionalPhaseGradientTransportAux

private noncomputable def gradientAdjWord (d M : ℕ) : Circuit (GradientGrid d M) :=
  (gradientQFTWord d M).reverse.map fun s => match s with
    | .gate U => .gate Uᴴ
    | .query => .query

private noncomputable def gradientUniformState (d M : ℕ) (hM : 0 < M) :
    QState (GradientGrid d M) :=
  gridProductState fun j => ApplyGate (QFTMatrix M) (Qatlib.Foundations.PureStateMath.Ket (gradientZero d M hM j))

private theorem norm_toEuclidean_applyGate {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (χ : QState I) :
    ‖toEuclidean_fromVec (ApplyGate U χ)‖ = ‖toEuclidean_fromVec χ‖ := by
  rw [← toEuclideanCLM_applyGate U χ]
  exact norm_toEuclideanCLM_of_mem_unitaryGroup hU _

private theorem norm_toEuclidean_run_le {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hgates : ∀ U : Matrix I I ℂ, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup I ℂ)
    (χ : QState I) :
    ‖toEuclidean_fromVec (Run O C χ)‖ ≤ ‖toEuclidean_fromVec χ‖ := by
  induction C generalizing χ with
  | nil => exact le_rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [run_gate]
      calc ‖toEuclidean_fromVec (Run O C (ApplyGate U χ))‖
          ≤ ‖toEuclidean_fromVec (ApplyGate U χ)‖ :=
            ih (fun V hV => hgates V (List.mem_cons_of_mem _ hV)) _
        _ = ‖toEuclidean_fromVec χ‖ := norm_toEuclidean_applyGate U
            (hgates U List.mem_cons_self) χ
    | query =>
      simp only [run_query]
      calc ‖toEuclidean_fromVec (Run O C (ApplyGate O χ))‖
          ≤ ‖toEuclidean_fromVec (ApplyGate O χ)‖ :=
            ih (fun V hV => hgates V (List.mem_cons_of_mem _ hV)) _
        _ = ‖toEuclidean_fromVec χ‖ := norm_toEuclidean_applyGate O hO χ

private theorem applyGate_sub {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (χ₁ χ₂ : QState I) :
    ApplyGate U (χ₁ - χ₂) = ApplyGate U χ₁ - ApplyGate U χ₂ := by
  funext i
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => mul_sub _ _ _

private theorem run_sub {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (χ₁ χ₂ : QState I) :
    Run O C (χ₁ - χ₂) = Run O C χ₁ - Run O C χ₂ := by
  induction C generalizing χ₁ χ₂ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp only [run_gate, applyGate_sub, ih]
    | query => simp only [run_query, applyGate_sub, ih]

private theorem gradientQFTWord_gates (d M : ℕ) :
    ∀ s ∈ gradientQFTWord d M, ∃ U : Matrix (GradientGrid d M) (GradientGrid d M) ℂ,
      s = Step.gate U := by
  intro s hs
  rw [gradientQFTWord] at hs
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hs
  exact ⟨coordinateQFT d M j, hj.symm⟩

private theorem gradientAdjWord_gates (d M : ℕ) :
    ∀ s ∈ gradientAdjWord d M, ∃ U : Matrix (GradientGrid d M) (GradientGrid d M) ℂ,
      s = Step.gate U := by
  intro s hs
  rw [gradientAdjWord] at hs
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hs
  obtain ⟨W, hW⟩ := gradientQFTWord_gates d M t (List.mem_reverse.mp ht)
  cases hW
  exact ⟨Wᴴ, hte.symm⟩

private theorem queryCount_of_all_gates {I : Type} (L : Circuit I)
    (hmem : ∀ s ∈ L, ∃ U : Matrix I I ℂ, s = Step.gate U) : QueryCount L = 0 := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    obtain ⟨U, hU⟩ := hmem s (by simp)
    subst hU
    exact ih fun s' hs' => hmem s' (by simp [hs'])

private theorem gradientAdjWord_unitary_gates (d M : ℕ) (hM : 0 < M) :
    ∀ U : Matrix (GradientGrid d M) (GradientGrid d M) ℂ,
      Step.gate U ∈ gradientAdjWord d M → U ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ := by
  intro U hU
  rw [gradientAdjWord] at hU
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hU
  have ht' : t ∈ gradientQFTWord d M := List.mem_reverse.mp ht
  rw [gradientQFTWord] at ht'
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp ht'
  rw [← hj] at hte
  have hUW : (coordinateQFT d M j)ᴴ = U := by injection hte with h
  rw [← hUW]
  exact adjoint_unitary (coordinateQFT_unitary d M j hM)

private theorem qft_ket_factor_sq (M : ℕ) (_hM : 0 < M) (q y : Fin M) :
    ‖ApplyGate (QFTMatrix M) (Qatlib.Foundations.PureStateMath.Ket q) y‖^2 = 1/(M : ℝ) := by
  have h : ApplyGate (QFTMatrix M) (Qatlib.Foundations.PureStateMath.Ket q) y
      = (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        Complex.exp (2*Real.pi*Complex.I*((((q.val : ℝ)*(y.val : ℝ))/(M : ℝ) : ℝ) : ℂ)) := by
    simp only [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, qftMatrix_apply,
      primRoot_zpow_eq_exp]
    congr 2
    push_cast
    ring
  have h1 : ‖Complex.exp (2*Real.pi*Complex.I*((((q.val : ℝ)*(y.val : ℝ))/(M : ℝ) : ℝ) : ℂ))‖
      = 1 := by
    simpa using! norm_exp_two_pi_I (((q.val : ℝ)*(y.val : ℝ))/(M : ℝ))
  have hsm : (Real.sqrt (M : ℝ)) * (Real.sqrt (M : ℝ)) = (M : ℝ) := by
    have h2 := Real.sq_sqrt (Nat.cast_nonneg M)
    rw [sq, mul_comm] at h2
    exact h2
  rw [h, norm_mul, h1, mul_one, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_ofReal, hsm, inv_eq_one_div]

private theorem gradient_uniform_run (d M : ℕ) (hM : 0 < M)
    (O : Matrix (GradientGrid d M) (GradientGrid d M) ℂ) :
    Run O (gradientQFTWord d M) (Qatlib.Foundations.PureStateMath.Ket (gradientZero d M hM))
      = gradientUniformState d M hM := by
  rw [← gridProductState_ket (gradientZero d M hM), run_gradientQFTWord_product]
  rfl

private theorem uniform_state_sq (d M : ℕ) (hM : 0 < M) (x : GradientGrid d M) :
    ‖gradientUniformState d M hM x‖^2 = 1/(M : ℝ)^d := by
  have hprod : ∀ j : Fin d,
      ‖ApplyGate (QFTMatrix M) (Qatlib.Foundations.PureStateMath.Ket (gradientZero d M hM j)) (x j)‖^2 = 1/(M : ℝ) :=
    fun j => qft_ket_factor_sq M hM _ _
  show ‖(∏ j : Fin d,
      ApplyGate (QFTMatrix M) (Qatlib.Foundations.PureStateMath.Ket (gradientZero d M hM j)) (x j))‖^2 = 1/(M : ℝ)^d
  rw [norm_prod, ← Finset.prod_pow, Finset.prod_congr rfl (fun j _ => hprod j),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ((1/(M : ℝ))^d) = 1/(M : ℝ)^d from by
    rw [one_div, inv_pow, inv_eq_one_div]]

end ExceptionalPhaseGradientTransportAux
open Qatlib.Concepts.GradientOracle.ReadoutTools.ExceptionalPhaseGradientTransportAux
set_option warningAsError false

theorem exceptionalPhaseGradientTransport : ExceptionalPhaseGradientTransport := by
  intro d M hM φ ψ S B η hB hη hcard hgood
  obtain ⟨hC, _, _⟩ := gradient_coordinate_qft_word_unitarity d M hM
  have hOφ := gradientPhase_unitary d M φ
  have hOψ := gradientPhase_unitary d M ψ
  have hnormφ : Normalized (gradientReadout d M hM φ) :=
    hC.normalized_run hOφ (normalized_ket _)
  have hnormψ : Normalized (gradientReadout d M hM ψ) :=
    hC.normalized_run hOψ (normalized_ket _)
  have hqcRest : QueryCount (gradientAdjWord d M) = 0 :=
    queryCount_of_all_gates _ (gradientAdjWord_gates d M)
  have hgatesRest := gradientAdjWord_unitary_gates d M hM
  have hsplit (χ : GradientGrid d M → ℝ) :
      gradientReadout d M hM χ = Run (gradientPhase d M χ) (gradientAdjWord d M)
        (ApplyGate (gradientPhase d M χ) (gradientUniformState d M hM)) := by
    show Run (gradientPhase d M χ) (gradientWord d M)
        (Qatlib.Foundations.PureStateMath.Ket (gradientZero d M hM)) = _
    rw [gradientWord, run_append, run_append, run_query, run_nil,
      gradient_uniform_run d M hM (gradientPhase d M χ)]
    rfl
  have hdiff : gradientReadout d M hM φ - gradientReadout d M hM ψ
      = Run (gradientPhase d M φ) (gradientAdjWord d M)
        (ApplyGate (gradientPhase d M φ) (gradientUniformState d M hM)
          - ApplyGate (gradientPhase d M ψ) (gradientUniformState d M hM)) := by
    rw [hsplit φ, hsplit ψ,
      run_eq_of_queryCount_eq_zero (gradientPhase d M ψ) (gradientPhase d M φ)
        (gradientAdjWord d M) hqcRest
        (ApplyGate (gradientPhase d M ψ) (gradientUniformState d M hM)),
      Qatlib.Concepts.LchsSimulation.StaticLchs.run_sub]
  have hpt : ∀ x : GradientGrid d M,
      (ApplyGate (gradientPhase d M φ) (gradientUniformState d M hM)
        - ApplyGate (gradientPhase d M ψ) (gradientUniformState d M hM)) x
      = (Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
          - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ)))
          * gradientUniformState d M hM x := by
    intro x
    simp only [ApplyGate, gradientPhase, Matrix.mulVec_diagonal, Pi.sub_apply]
    ring
  have hle := norm_toEuclidean_run_le (gradientPhase d M φ) hOφ (gradientAdjWord d M)
    hgatesRest (ApplyGate (gradientPhase d M φ) (gradientUniformState d M hM)
      - ApplyGate (gradientPhase d M ψ) (gradientUniformState d M hM))
  rw [← hdiff] at hle
  have hsqX : ‖toEuclidean_fromVec (ApplyGate (gradientPhase d M φ)
        (gradientUniformState d M hM)
        - ApplyGate (gradientPhase d M ψ) (gradientUniformState d M hM))‖^2
      = ∑ x : GradientGrid d M, ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
          - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
          * ‖gradientUniformState d M hM x‖^2 := by
    rw [norm_toEuclidean_fromVec_sq]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hpt x, norm_mul, mul_pow]
  have heφ (t : ℝ) : Complex.exp (2*Real.pi*Complex.I*((t : ℝ) : ℂ))
      = Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I) := by
    push_cast
    ring
  have hgood' : ∀ x ∈ S, ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
      - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2 ≤ (2*Real.pi*B)^2 := by
    intro x hx
    have h1 : ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
        - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖
        ≤ |2*Real.pi*(φ x) - 2*Real.pi*(ψ x)| := by
      rw [heφ (φ x), heφ (ψ x)]
      exact norm_exp_mul_I_sub_le _ _
    have h2 : |2*Real.pi*(φ x) - 2*Real.pi*(ψ x)| = 2*Real.pi*|φ x - ψ x| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
    have h3 : 2*Real.pi*|φ x - ψ x| ≤ 2*Real.pi*B :=
      mul_le_mul_of_nonneg_left (hgood x hx) (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) ((h2 ▸ h1).trans h3) 2
  have hbad' : ∀ x : GradientGrid d M, ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
      - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2 ≤ 4 := by
    intro x
    have h1 : ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
        - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖
        ≤ ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))‖
          + ‖Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖ := norm_sub_le _ _
    rw [norm_exp_two_pi_I, norm_exp_two_pi_I] at h1
    have h3 : ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
        - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖ ≤ 2 := by linarith
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    norm_num at h4
    exact h4
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMd : 0 < (M : ℝ)^d := pow_pos hMr _
  have hcardGood : (Finset.univ.filter (fun x : GradientGrid d M => x ∈ S)).card
      ≤ (Finset.univ : Finset (GradientGrid d M)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcardBad : ((Finset.univ.filter (fun x : GradientGrid d M => ¬ x ∈ S)).card : ℝ)
      ≤ η*(M : ℝ)^d := by
    rw [Finset.sdiff_eq_filter] at hcard
    exact hcard
  have hmass (F : Finset (GradientGrid d M)) :
      ∑ x ∈ F, ‖gradientUniformState d M hM x‖^2 = (F.card : ℝ)/(M : ℝ)^d := by
    rw [Finset.sum_congr rfl (fun x _ => uniform_state_sq d M hM x), Finset.sum_const]
    simp
    ring
  have hL2 : ‖toEuclidean_fromVec (gradientReadout d M hM φ
      - gradientReadout d M hM ψ)‖^2 ≤ (2*Real.pi*B)^2+4*η := by
    have hstep1 : ‖toEuclidean_fromVec (gradientReadout d M hM φ
        - gradientReadout d M hM ψ)‖^2
        ≤ ‖toEuclidean_fromVec (ApplyGate (gradientPhase d M φ)
            (gradientUniformState d M hM)
            - ApplyGate (gradientPhase d M ψ) (gradientUniformState d M hM))‖^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    have h1 : ∑ x ∈ Finset.univ.filter (fun x : GradientGrid d M => x ∈ S),
        (‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
          - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
          * ‖gradientUniformState d M hM x‖^2) ≤ (2*Real.pi*B)^2 := by
      have hfilt : ∀ x ∈ Finset.univ.filter (fun x : GradientGrid d M => x ∈ S),
          ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
            - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
            * ‖gradientUniformState d M hM x‖^2
          ≤ (2*Real.pi*B)^2 * ‖gradientUniformState d M hM x‖^2 := by
        intro x hx
        exact mul_le_mul_of_nonneg_right (hgood' x (Finset.mem_filter.mp hx).2)
          (by positivity : 0 ≤ ‖gradientUniformState d M hM x‖^2)
      have hcardUniv : ((Finset.univ : Finset (GradientGrid d M)).card : ℝ)
          = (M : ℝ)^d := by
        rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin]
        push_cast
        ring
      have hfrac : ((Finset.univ.filter (fun x : GradientGrid d M => x ∈ S)).card : ℝ)
          /(M : ℝ)^d ≤ 1 := by
        apply (div_le_iff₀ hMd).mpr
        have hle : ((Finset.univ.filter (fun x : GradientGrid d M => x ∈ S)).card : ℝ)
            ≤ (Finset.univ : Finset (GradientGrid d M)).card := by
          exact_mod_cast hcardGood
        rw [hcardUniv] at hle
        linarith
      calc ∑ x ∈ Finset.univ.filter (fun x : GradientGrid d M => x ∈ S),
          (‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
            - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
            * ‖gradientUniformState d M hM x‖^2)
          ≤ ∑ x ∈ Finset.univ.filter (fun x : GradientGrid d M => x ∈ S),
              (2*Real.pi*B)^2 * ‖gradientUniformState d M hM x‖^2 :=
            Finset.sum_le_sum hfilt
        _ = (2*Real.pi*B)^2 * ∑ x ∈ Finset.univ.filter
              (fun x : GradientGrid d M => x ∈ S),
              ‖gradientUniformState d M hM x‖^2 := (Finset.mul_sum _ _ _).symm
        _ = (2*Real.pi*B)^2 * (((Finset.univ.filter
              (fun x : GradientGrid d M => x ∈ S)).card : ℝ)/(M : ℝ)^d) := by
            rw [hmass _]
        _ ≤ (2*Real.pi*B)^2 * 1 :=
            mul_le_mul_of_nonneg_left hfrac (sq_nonneg _)
        _ = (2*Real.pi*B)^2 := by ring
    have h2 : ∑ x ∈ Finset.univ.filter (fun x : GradientGrid d M => ¬ x ∈ S),
        (‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
          - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
          * ‖gradientUniformState d M hM x‖^2) ≤ 4*η := by
      have hfilt : ∀ x ∈ Finset.univ.filter (fun x : GradientGrid d M => ¬ x ∈ S),
          ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
            - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
            * ‖gradientUniformState d M hM x‖^2
          ≤ 4 * ‖gradientUniformState d M hM x‖^2 := by
        intro x hx
        exact mul_le_mul_of_nonneg_right (hbad' x)
          (by positivity : 0 ≤ ‖gradientUniformState d M hM x‖^2)
      have hfrac : ((Finset.univ.filter (fun x : GradientGrid d M => ¬ x ∈ S)).card : ℝ)
          /(M : ℝ)^d ≤ η := by
        rw [div_le_iff₀ hMd]
        exact hcardBad
      calc ∑ x ∈ Finset.univ.filter (fun x : GradientGrid d M => ¬ x ∈ S),
          (‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
            - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
            * ‖gradientUniformState d M hM x‖^2)
          ≤ ∑ x ∈ Finset.univ.filter (fun x : GradientGrid d M => ¬ x ∈ S),
              4 * ‖gradientUniformState d M hM x‖^2 :=
            Finset.sum_le_sum hfilt
        _ = 4 * ∑ x ∈ Finset.univ.filter
              (fun x : GradientGrid d M => ¬ x ∈ S),
              ‖gradientUniformState d M hM x‖^2 := (Finset.mul_sum _ _ _).symm
        _ = 4 * (((Finset.univ.filter
              (fun x : GradientGrid d M => ¬ x ∈ S)).card : ℝ)/(M : ℝ)^d) := by
            rw [hmass _]
        _ ≤ 4 * η :=
            mul_le_mul_of_nonneg_left hfrac (by norm_num : 0 ≤ (4:ℝ))
    calc ‖toEuclidean_fromVec (gradientReadout d M hM φ
          - gradientReadout d M hM ψ)‖^2
        ≤ ∑ x : GradientGrid d M, ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
            - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
            * ‖gradientUniformState d M hM x‖^2 := hstep1.trans hsqX.le
      _ ≤ (2*Real.pi*B)^2+4*η := by
          have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun x : GradientGrid d M => x ∈ S) (fun x =>
              ‖Complex.exp (2*Real.pi*Complex.I*((φ x : ℝ) : ℂ))
                - Complex.exp (2*Real.pi*Complex.I*((ψ x : ℝ) : ℂ))‖^2
                * ‖gradientUniformState d M hM x‖^2)
          rw [← hsum]
          linarith
  refine ⟨hnormφ, hnormψ, hL2, ?_⟩
  intro E
  have h1 := pureStateEventLipschitz (GradientGrid d M)
    (gradientReadout d M hM φ) (gradientReadout d M hM ψ) hnormφ hnormψ E
  calc |MeasureProb (gradientReadout d M hM φ) E
        - MeasureProb (gradientReadout d M hM ψ) E|
      ≤ ‖toEuclidean_fromVec (gradientReadout d M hM φ
          - gradientReadout d M hM ψ)‖ := h1
    _ = Real.sqrt (‖toEuclidean_fromVec (gradientReadout d M hM φ
          - gradientReadout d M hM ψ)‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((2*Real.pi*B)^2+4*η) := Real.sqrt_le_sqrt hL2

end Qatlib.Concepts.GradientOracle.ReadoutTools
