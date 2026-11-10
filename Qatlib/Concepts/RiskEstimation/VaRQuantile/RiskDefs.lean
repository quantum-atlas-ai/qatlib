/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PayoffEncoding
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.SqEstimation.HierarchicalSQ.NativeCoefficientChoice
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxRecDepth 4096
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
namespace Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

def riskCDFPayoff {I : Type} (loss : I  → ℚ) (t : ℚ) (i : I) : ℝ := if loss i ≤ t then 1 else 0

def riskTailPayoff {I : Type} (loss : I  → ℚ) (t : ℚ) (i : I) : ℚ :=
    if loss i ≤ t then loss i else 0

noncomputable def riskCDF {I : Type} [Fintype I] (A : Matrix I I ℂ) (j : I) (loss : I  → ℚ) (t : ℚ) : ℝ :=
  ∑ i, BornProb (A*ᵥ Ket j) i*riskCDFPayoff loss t i

noncomputable def riskTailMean {I : Type} [Fintype I] (A : Matrix I I ℂ) (j : I) (loss : I  → ℚ) (t : ℚ) : ℝ :=
  (∑ i,BornProb (A*ᵥ Ket j) i*(riskTailPayoff loss t i:ℝ))/riskCDF A j loss t

noncomputable def riskCDFLaw {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (loss : I  → ℚ) (t : ℚ) (M : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) : FinDist (Fin M) :=
  meanLaw M A j (riskCDFPayoff loss t) hA (fun i => by
    dsimp [riskCDFPayoff]; split <;> norm_num) hM

noncomputable def riskNumeratorLaw {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (loss : I  → ℚ) (t : ℚ) (k M : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ)
    (hloss : ∀ i,0 ≤ loss i ∧loss i ≤ 1) (hM : 2 ≤ M) : FinDist (Fin M) :=
  meanLaw M A j (fun i => (rationalPayoffValue (riskTailPayoff loss t i) k:ℝ)) hA
    (fun i => by
      have hq : 0 ≤ riskTailPayoff loss t i ∧riskTailPayoff loss t i ≤ 1 := by
        dsimp [riskTailPayoff]; split <;> simp_all
      have h := (rationalPayoffCS_probability _ k hq.1 hq.2).2.2
      change (0:ℝ) ≤ (rationalPayoffValue (riskTailPayoff loss t i) k:ℝ) ∧
        (rationalPayoffValue (riskTailPayoff loss t i) k:ℝ) ≤ 1
      exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩) hM

noncomputable def riskMedianPMF {M : ℕ} (p : FinDist (Fin M)) (r : ℕ) : PMF ℝ :=
  (closurePMF ({
    prob := p.probOf
    nonneg := fun omega => Finset.prod_nonneg (fun i _ => p.nonneg (omega i))
    sum_one := p.sum_probOf (2*r+1)
    } : FinDist (Fin (2*r+1)  → Fin M))).map (meanMedian r M)

noncomputable def riskBisect (sample : ℚ  → PMF ℝ) (xs : List ℚ) (q : ℝ) : ℕ  → ℕ  → ℕ  → PMF (ℕ ×ℕ)
  | 0,lo,_ => PMF.pure (lo,0)
  | fuel+1,lo,hi => if hi ≤ lo then PMF.pure (lo,0) else
      let mid := (lo+hi)/2
      (sample (xs.getD mid 0)).bind (fun z =>
        (if q ≤ z then riskBisect sample xs q fuel lo mid else riskBisect sample xs q fuel (mid+1) hi).map
          (fun out => (out.1,out.2+1)))

noncomputable def riskVaR {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (loss : I  → ℚ) (xs : List ℚ) (q : ℝ) (M r : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ)
    (hM : 2 ≤ M) : PMF (ℕ ×ℕ) :=
  riskBisect (fun t => riskMedianPMF (riskCDFLaw A j loss t M hA hM) r) xs q
    (Nat.clog 2 xs.length+1) 0 (xs.length-1)

noncomputable def riskCVaR {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (loss : I  → ℚ) (xs : List ℚ) (q eps : ℝ) (k M r : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ)
    (hloss : ∀ i,0 ≤ loss i ∧loss i ≤ 1) (hM : 2 ≤ M) : PMF (ℕ ×ℝ ×ℕ) :=
  (riskVaR A j loss xs q M r hA hM).bind (fun z =>
    (riskMedianPMF (riskCDFLaw A j loss (xs.getD z.1 0) M hA hM) r).bind (fun phat =>
      (riskMedianPMF (riskNumeratorLaw A j loss (xs.getD z.1 0) k M hA hloss hM) r).map
        (fun muhat => (z.1,muhat/max eps phat,z.2+2))))

end Papers.QuantumRiskAnalysis2018
end Qatlib.Concepts.RiskEstimation.VaRQuantile

open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

theorem risk_event_mono {X : Type} (p : PMF X) {E F : X → Prop} (h : ∀ x, E x → F x) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p F := by
  classical
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_le_of_forall
  intro x
  by_cases hx : E x
  · simp only [if_pos hx, if_pos (h x hx), le_refl]
  · simp only [if_neg hx, zero_le]
end Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
