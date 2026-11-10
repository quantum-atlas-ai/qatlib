/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RectangularPureDistance
import Qatlib.Concepts.Execution.KrausRefinement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance
open Matrix Qatlib
open scoped BigOperators InnerProductSpace
section InstrumentPureTV

def krausStackMatrix {O : Type} [Fintype O] {D E : ℕ} (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O D E) :
    Matrix ((O × (Fin E × Fin D)) × Fin E) (Fin D) ℂ :=
  fun ae j => Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I ae.1 ae.2 j

theorem krausStackMatrix_gram {O : Type} [Fintype O] {D E : ℕ}
    (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O D E) :
    (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I)ᴴ * Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I = 1 := by
  have hcomp := Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily_complete I
  ext i j
  have hentry : ((Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I)ᴴ * Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I) i j =
      (∑ a : O × (Fin E × Fin D), (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I a)ᴴ * Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I a) i j := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix, Fintype.sum_prod_type]
  rw [hentry, hcomp]

theorem instrumentProb_krausRefinement_outerProduct
    {O : Type} [Fintype O] {D E : ℕ}
    (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O D E) (ψ : Qatlib.Foundations.PureStateMath.QState (Fin D)) (a : O × (Fin E × Fin D)) :
    Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I) (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ) a =
      ∑ e : Fin E, Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I a *ᵥ ψ) e := by
  unfold Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb
  rw [Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement_branch, Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch_outerProduct, Qatlib.Foundations.PureStateMath.BornBridge.trace_outerProduct,
    Complex.ofReal_re]
  rfl

theorem instrumentProb_outerProduct_eq_sum_bornProb
    {O : Type} [Fintype O] {D E : ℕ}
    (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O D E) (ψ : Qatlib.Foundations.PureStateMath.QState (Fin D)) (o : O) :
    Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ) o =
      ∑ k : Fin E × Fin D, ∑ e : Fin E,
        Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ((o, k), e) := by
  rw [← Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement_sum_prob I o (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.instrumentProb_krausRefinement_outerProduct]
  rfl

theorem instrumentProb_outerProduct_eq_sum_prod
    {O : Type} [Fintype O] {D E : ℕ}
    (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O D E) (ψ : Qatlib.Foundations.PureStateMath.QState (Fin D)) (o : O) :
    Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ) o =
      ∑ ke : (Fin E × Fin D) × Fin E,
        Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ((o, ke.1), ke.2) := by
  rw [Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.instrumentProb_outerProduct_eq_sum_bornProb]
  exact (Fintype.sum_prod_type (fun ke : (Fin E × Fin D) × Fin E =>
    Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ((o, ke.1), ke.2))).symm

theorem instrument_pure_tv_le_sqrt_fidelity
    {O : Type} [Fintype O] [DecidableEq O] {D E : ℕ}
    (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O D E) (ψ φ : Qatlib.Foundations.PureStateMath.QState (Fin D))
    (hψ : Qatlib.Foundations.PureStateMath.Normalized ψ) (hφ : Qatlib.Foundations.PureStateMath.Normalized φ) :
    (1 / 2 : ℝ) * ∑ o : O,
      |Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ) o - Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct φ) o| ≤
      Real.sqrt (1 - ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ ^ 2) := by
  have ho (o : O) :
      |Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ) o - Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct φ) o| ≤
        ∑ k : Fin E × Fin D, ∑ e : Fin E,
          |Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ((o, k), e) -
            Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ φ) ((o, k), e)| := by
    rw [Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.instrumentProb_outerProduct_eq_sum_prod I ψ o,
      Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.instrumentProb_outerProduct_eq_sum_prod I φ o, ← Finset.sum_sub_distrib]
    calc
      |∑ ke : (Fin E × Fin D) × Fin E,
          (Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ((o, ke.1), ke.2) -
            Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ φ) ((o, ke.1), ke.2))|
        ≤ ∑ ke : (Fin E × Fin D) × Fin E,
            |Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ((o, ke.1), ke.2) -
              Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ φ) ((o, ke.1), ke.2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin E × Fin D, ∑ e : Fin E,
            |Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ((o, k), e) -
              Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ φ) ((o, k), e)| :=
          Fintype.sum_prod_type _
  have hsum :
      ∑ o : O, |Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ) o - Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct φ) o| ≤
        ∑ ae : (O × (Fin E × Fin D)) × Fin E,
          |Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ae - Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ φ) ae| := by
    calc
      ∑ o : O, |Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ) o - Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct φ) o|
        ≤ ∑ o : O, ∑ k : Fin E × Fin D, ∑ e : Fin E,
            |Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ((o, k), e) -
              Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ φ) ((o, k), e)| :=
          Finset.sum_le_sum fun o _ => ho o
      _ = ∑ ae : (O × (Fin E × Fin D)) × Fin E,
            |Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ae - Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ φ) ae| := by
          simp only [Fintype.sum_prod_type]
  have hcoarse :
      (1 / 2 : ℝ) * ∑ o : O,
        |Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ) o - Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct φ) o| ≤
      (1 / 2 : ℝ) * ∑ ae : (O × (Fin E × Fin D)) × Fin E,
        |Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ ψ) ae - Qatlib.Foundations.PureStateMath.BornProb (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I *ᵥ φ) ae| :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hx : ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec ψ‖ = 1 :=
    (Qatlib.Foundations.PureStateMath.BornBridge.normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hy : ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec φ‖ = 1 :=
    (Qatlib.Foundations.PureStateMath.BornBridge.normalized_iff_norm_toEuclidean_fromVec φ).mp hφ
  have hfine := Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.rectangular_born_tv_le_sqrt_fidelity
    (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix I) (Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.krausStackMatrix_gram I)
    (Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec ψ) (Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec φ) hx hy
  rw [Qatlib.Foundations.PureStateMath.BornBridge.inner_euclidean_fromVec] at hfine
  exact hcoarse.trans hfine

theorem instrument_euclidean_tv_le_sqrt_fidelity
    {Idx O : Type} [Fintype Idx] [DecidableEq Idx] [Fintype O] [DecidableEq O]
    {D E : ℕ} (e : Idx ≃ Fin D) (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O D E)
    (x y : EuclideanSpace ℂ Idx) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (1 / 2 : ℝ) * ∑ o : O,
      |Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.BornBridge.relabelState e x.ofLp)) o -
        Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.BornBridge.relabelState e y.ofLp)) o| ≤
      Real.sqrt (1 - ‖inner ℂ x y‖ ^ 2) := by
  have hx_norm : Qatlib.Foundations.PureStateMath.Normalized x.ofLp :=
    (Qatlib.Foundations.PureStateMath.BornBridge.normalized_iff_norm_toEuclidean_fromVec x.ofLp).mpr hx
  have hy_norm : Qatlib.Foundations.PureStateMath.Normalized y.ofLp :=
    (Qatlib.Foundations.PureStateMath.BornBridge.normalized_iff_norm_toEuclidean_fromVec y.ofLp).mpr hy
  have h := Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance.instrument_pure_tv_le_sqrt_fidelity I
    (Qatlib.Foundations.PureStateMath.BornBridge.relabelState e x.ofLp) (Qatlib.Foundations.PureStateMath.BornBridge.relabelState e y.ofLp)
    (Qatlib.Foundations.PureStateMath.BornBridge.normalized_relabelState e hx_norm) (Qatlib.Foundations.PureStateMath.BornBridge.normalized_relabelState e hy_norm)
  have hinner : Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.BornBridge.relabelState e x.ofLp) (Qatlib.Foundations.PureStateMath.BornBridge.relabelState e y.ofLp) = inner ℂ x y := by
    rw [Qatlib.Foundations.PureStateMath.BornBridge.inner_relabelState,
        ← Qatlib.Foundations.PureStateMath.BornBridge.inner_euclidean_fromVec]
    rfl
  rwa [hinner] at h

end InstrumentPureTV
end Qatlib.Concepts.MixedFidelity.FidelityMetric.InstrumentPureDistance
