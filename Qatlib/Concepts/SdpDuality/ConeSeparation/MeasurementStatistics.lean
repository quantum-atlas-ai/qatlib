/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Qatlib.Concepts.ShadowModels.UStatBackend.OrderedHigherUStatistic
import Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatisticsDefs
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Concepts.TensorRegisters.RegisterModel

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.TensorRegisters.RegisterModel Matrix
open scoped BigOperators ComplexOrder
set_option warningAsError false

def povmLaw {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ) : FinDist O :=
  ofPMF (instrumentPMF (Instrument.ofPOVM Λ) hρ)

theorem povmLaw_prob {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (o : O) :
    (povmLaw Λ ρ hρ).prob o = (Matrix.trace ((Λ.mats o).mat * ρ)).re := by
  change (instrumentPMF (Instrument.ofPOVM Λ) hρ o).toReal = _
  rw [instrumentPMF_apply, ENNReal.toReal_ofReal
    (instrumentProb_nonneg (Instrument.ofPOVM Λ) hρ.1 o), instrumentProb_ofPOVM]

theorem povmLaw_same_pmf {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    toPMF (povmLaw Λ ρ hρ) = instrumentPMF (Instrument.ofPOVM Λ) hρ := toPMF_ofPMF _

theorem povm_moment {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (f : O → ℝ) (c : ℝ) (k : ℕ) :
    (povmLaw Λ ρ hρ).expect (fun o => (f o - c)^k) =
      ∑ o, (Matrix.trace ((Λ.mats o).mat * ρ)).re * (f o - c)^k := by
  simp only [FinDist.expect, povmLaw_prob]

theorem povm_variance {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (f : O → ℝ) :
    (povmLaw Λ ρ hρ).variance f =
      ∑ o, (Matrix.trace ((Λ.mats o).mat * ρ)).re *
        (f o - (povmLaw Λ ρ hρ).expect f)^2 := povm_moment _ _ _ _ _ 2

theorem povm_ordered_u_unbiased {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (m r : ℕ) (h : List O → ℝ) (hr : r ≤ m) :
    (∑ ω : Fin m → O, (povmLaw Λ ρ hρ).probOf ω * (higherUCounted m r h ω).1) =
        higherUMean (povmLaw Λ ρ hρ) r h ∧
      (∀ ω : Fin m → O, (higherUCounted m 0 h ω).2 = 1) :=
  higher_u_asymmetric_unbiased_and_empty O (povmLaw Λ ρ hρ) m r h hr

theorem povm_ordered_u_variance {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (m r : ℕ) (h : List O → ℝ) (B : ℝ) (hm : 0 < m) (hr : r ≤ m)
    (hB : 0 ≤ B) (hb : ∀ xs : List O, xs.length = r → |h xs| ≤ B) :
    (∑ ω : Fin m → O, (povmLaw Λ ρ hρ).probOf ω *
        ((higherUCounted m r h ω).1 - higherUMean (povmLaw Λ ρ hρ) r h)^2) ≤
      4 * (r : ℝ)^2 * B^2 / m :=
  higher_u_overlap_covariance_and_variance O (povmLaw Λ ρ hρ) m r h B hm hr hB hb

theorem freshPovmDensity_density {m : ℕ} (d : Fin m → ℕ) (ρ : ∀ i, Operator (d i))
    (hρ : ∀ i, IsDensityOperator (ρ i)) : IsDensityOperator (freshPovmDensity d ρ) := by
  refine ⟨(productMatrix_psd ρ (fun i => (hρ i).1)).submatrix (flatten d).symm, ?_⟩
  change Matrix.trace ((productMatrix ρ).submatrix (flatten d).symm (flatten d).symm) = 1
  rw [Matrix.trace_submatrix, productMatrix_trace]
  have ht (i : Fin m) : Matrix.trace (ρ i) = 1 := (hρ i).2
  simp only [ht, Finset.prod_const_one]

theorem freshPovmKraus_complete {m : ℕ} (d : Fin m → ℕ)
    {O : Fin m → Type*} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) :
    (∑ ω : ∀ i, O i, (freshPovmKraus d Λ ω)ᴴ * freshPovmKraus d Λ ω) = 1 := by
  let F := Matrix.reindexAlgEquiv ℂ ℂ (flatten d)
  have hadj (A : Matrix (Labels d) (Labels d) ℂ) : (F A)ᴴ = F Aᴴ := rfl
  have hraw : (∑ ω : ∀ i, O i,
      (productMatrix (fun i => ((Λ i).mats (ω i) ^ (1/2 : ℝ)).mat))ᴴ *
        productMatrix (fun i => ((Λ i).mats (ω i) ^ (1/2 : ℝ)).mat)) = 1 := by
    simp only [productMatrix_adjoint, productMatrix_mul]
    rw [productMatrix_sum (fun i o =>
      (((Λ i).mats o ^ (1/2 : ℝ)).mat)ᴴ * ((Λ i).mats o ^ (1/2 : ℝ)).mat)]
    simp only [povm_sqrt_complete, productMatrix_one]
  change (∑ ω : ∀ i, O i,
    (F (productMatrix (fun i => ((Λ i).mats (ω i) ^ (1/2 : ℝ)).mat)))ᴴ *
      F (productMatrix (fun i => ((Λ i).mats (ω i) ^ (1/2 : ℝ)).mat))) = 1
  simp only [hadj, ← map_mul F]
  rw [← map_sum F, hraw, map_one]

def freshPovmInstrument {m : ℕ} (d : Fin m → ℕ)
    {O : Fin m → Type*} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) : Instrument (∀ i, O i) (∏ i, d i) (∏ i, d i) :=
  Instrument.ofKraus (freshPovmKraus d Λ) (freshPovmKraus_complete d Λ)

theorem freshPovm_record_mass {m : ℕ} (d : Fin m → ℕ)
    {O : Fin m → Type*} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) (ρ : ∀ i, Operator (d i))
    (hρ : ∀ i, IsDensityOperator (ρ i)) (ω : ∀ i, O i) :
    instrumentProb (freshPovmInstrument d Λ) (freshPovmDensity d ρ) ω =
      ∏ i, (povmLaw (Λ i) (ρ i) (hρ i)).prob (ω i) := by
  let F := Matrix.reindexAlgEquiv ℂ ℂ (flatten d)
  have hadj (A : Matrix (Labels d) (Labels d) ℂ) : (F A)ᴴ = F Aᴴ := rfl
  have ht (A : Matrix (Labels d) (Labels d) ℂ) : Matrix.trace (F A) = Matrix.trace A :=
    Matrix.trace_submatrix A (flatten d).symm
  have hb : (freshPovmInstrument d Λ).branch ω (freshPovmDensity d ρ) =
      F (productMatrix (fun i => (Instrument.ofPOVM (Λ i)).branch (ω i) (ρ i))) := by
    rw [freshPovmInstrument, Instrument.ofKraus_branch]
    change F (productMatrix (fun i => ((Λ i).mats (ω i) ^ (1/2 : ℝ)).mat)) *
        F (productMatrix ρ) * (F (productMatrix (fun i => ((Λ i).mats (ω i) ^ (1/2 : ℝ)).mat)))ᴴ = _
    rw [hadj, ← map_mul F, ← map_mul F, productMatrix_adjoint,
      productMatrix_mul, productMatrix_mul]
    rfl
  rw [instrumentProb, hb, ht, productMatrix_trace]
  have hr (i : Fin m) : Matrix.trace ((Instrument.ofPOVM (Λ i)).branch (ω i) (ρ i)) =
      (instrumentProb (Instrument.ofPOVM (Λ i)) (ρ i) (ω i) : ℂ) :=
    trace_branch_eq _ (hρ i).1 _
  simp only [hr, ← Complex.ofReal_prod, Complex.ofReal_re,
    povmLaw_prob, instrumentProb_ofPOVM]

def freshPovmLaw {m : ℕ} (d : Fin m → ℕ)
    {O : Fin m → Type*} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) (ρ : ∀ i, Operator (d i))
    (hρ : ∀ i, IsDensityOperator (ρ i)) : FinDist (∀ i, O i) :=
  ofPMF (instrumentPMF (freshPovmInstrument d Λ) (freshPovmDensity_density d ρ hρ))

theorem freshPovmLaw_prob {m : ℕ} (d : Fin m → ℕ)
    {O : Fin m → Type*} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) (ρ : ∀ i, Operator (d i))
    (hρ : ∀ i, IsDensityOperator (ρ i)) (ω : ∀ i, O i) :
    (freshPovmLaw d Λ ρ hρ).prob ω = ∏ i, (povmLaw (Λ i) (ρ i) (hρ i)).prob (ω i) := by
  change (instrumentPMF (freshPovmInstrument d Λ) (freshPovmDensity_density d ρ hρ) ω).toReal = _
  rw [instrumentPMF_apply, ENNReal.toReal_ofReal
    (instrumentProb_nonneg _ (freshPovmDensity_density d ρ hρ).1 ω), freshPovm_record_mass d Λ ρ hρ]

theorem freshPovmLaw_eq_independent {m : ℕ} (d : Fin m → ℕ)
    {O : Fin m → Type*} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) (ρ : ∀ i, Operator (d i))
    (hρ : ∀ i, IsDensityOperator (ρ i)) :
    freshPovmLaw d Λ ρ hρ = independent (fun i => povmLaw (Λ i) (ρ i) (hρ i)) := by
  apply FinDist.ext
  intro ω
  exact freshPovmLaw_prob d Λ ρ hρ ω

theorem freshPovm_weighted_variance {m : ℕ} (d : Fin m → ℕ)
    {O : Fin m → Type*} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) (ρ : ∀ i, Operator (d i))
    (hρ : ∀ i, IsDensityOperator (ρ i)) (w : Fin m → ℝ) (f : ∀ i, O i → ℝ) :
    (freshPovmLaw d Λ ρ hρ).variance (Qatlib.Concepts.ProbabilityCore.Concentration.weightedSum w f) =
      ∑ i, (w i)^2 * (povmLaw (Λ i) (ρ i) (hρ i)).variance (f i) := by
  simpa only [freshPovmLaw_eq_independent] using!
    ProbabilityInterfaces.independent_weighted_variance
      (fun i => povmLaw (Λ i) (ρ i) (hρ i)) w f

theorem freshPovm_weighted_hoeffding {m : ℕ} (d : Fin m → ℕ)
    {O : Fin m → Type*} [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)]
    (Λ : ∀ i, POVM (O i) (Fin (d i))) (ρ : ∀ i, Operator (d i))
    (hρ : ∀ i, IsDensityOperator (ρ i)) (w : Fin m → ℝ) (f : ∀ i, O i → ℝ)
    (a b : Fin m → ℝ) (u : ℝ) (hab : ∀ i, a i ≤ b i)
    (hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (hu : 0 < u)
    (hS : 0 < ∑ i, (w i)^2*(b i-a i)^2) :
    Qatlib.Concepts.ProbabilityCore.Concentration.eventMass (freshPovmLaw d Λ ρ hρ)
      (fun ω => u ≤ |Qatlib.Concepts.ProbabilityCore.Concentration.weightedSum w f ω-
        (freshPovmLaw d Λ ρ hρ).expect (Qatlib.Concepts.ProbabilityCore.Concentration.weightedSum w f)|) ≤
      2*Real.exp (-2*u^2/(∑ i, (w i)^2*(b i-a i)^2)) := by
  simpa only [freshPovmLaw_eq_independent] using!
    ProbabilityInterfaces.independent_weighted_hoeffding
      (fun i => povmLaw (Λ i) (ρ i) (hρ i)) w f a b u hab hf hu hS

theorem freshPovm_ordered_u_mean {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (m r : ℕ) (h : List O → ℝ) (hr : r ≤ m) :
    (∑ ω : Fin m → O,
      instrumentProb (freshPovmInstrument (fun _ : Fin m => D) (fun _ => Λ))
        (freshPovmDensity (fun _ : Fin m => D) (fun _ => ρ)) ω * (higherUCounted m r h ω).1) =
      higherUMean (povmLaw Λ ρ hρ) r h := by
  simp_rw [freshPovm_record_mass _ _ _ (fun _ => hρ)]
  exact (povm_ordered_u_unbiased Λ ρ hρ m r h hr).1

theorem freshPovm_ordered_u_variance {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (m r : ℕ) (h : List O → ℝ) (B : ℝ) (hm : 0 < m) (hr : r ≤ m)
    (hB : 0 ≤ B) (hb : ∀ xs : List O, xs.length = r → |h xs| ≤ B) :
    (∑ ω : Fin m → O,
      instrumentProb (freshPovmInstrument (fun _ : Fin m => D) (fun _ => Λ))
        (freshPovmDensity (fun _ : Fin m => D) (fun _ => ρ)) ω *
        ((higherUCounted m r h ω).1 - higherUMean (povmLaw Λ ρ hρ) r h)^2) ≤
      4 * (r : ℝ)^2 * B^2 / m := by
  simp_rw [freshPovm_record_mass _ _ _ (fun _ => hρ)]
  exact povm_ordered_u_variance Λ ρ hρ m r h B hm hr hB hb

end Qatlib.Concepts.SdpDuality.ConeSeparation
