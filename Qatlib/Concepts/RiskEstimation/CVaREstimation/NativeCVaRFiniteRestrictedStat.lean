/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.NativeNumerics.LayeredMean.NativeSignedMeanConsumers
import Qatlib.Concepts.RiskEstimation.CVaREstimation.CVaRAlgorithmFiniteRestrictedQuan
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.RiskActualAccessLedgerFiniteQuan
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.CVaREstimation
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

def NativeCVaRFiniteRestricted : Prop :=
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
      (loss : I → ℚ) (xs : List ℚ) (q ε : ℚ) (rotationBits bits M r v : ℕ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M)
      (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1),
      xs ≠ [] → xs.SortedLE → (∀ i, loss i ∈ xs) → 0 < q → q < 1 → 0 < ε →
      v < xs.length →
      Real.pi/M+Real.pi^2/(M : ℝ)^2+64/(2 : ℝ)^rotationBits+(1/2 : ℝ)^bits ≤ (ε : ℝ) →
      (q : ℝ)+ε < riskCDF A j loss (xs.getD v 0) →
      (∀ u : ℕ, u < v → riskCDF A j loss (xs.getD u 0) < (q : ℝ)-ε) →
      2*(ε : ℝ) < riskCDF A j loss (xs.getD v 0) →
      let sample := fun p : FinDist (Fin M) =>
        (closurePMF ({
          prob := p.probOf
          nonneg := fun ω => Finset.prod_nonneg (fun z _ => p.nonneg (ω z))
          sum_one := p.sum_probOf (2*r+1) } : FinDist (Fin (2*r+1) → Fin M))).map
          (fun ω => (((List.ofFn (fun z => nativeAEDecode M bits (ω z))).mergeSort
            (fun a b => a ≤ b)).getD r 0))
      let bisect := fun (sampler : ℚ → PMF ℚ) (xs : List ℚ) (q : ℚ)
          (fuel lo hi : ℕ) =>
        Nat.rec (motive := fun _ => ℕ → ℕ → PMF (ℕ×ℕ))
          (fun lo _ => PMF.pure (lo,0))
          (fun _ rec lo hi => if hi ≤ lo then PMF.pure (lo,0) else
            let mid := (lo+hi)/2
            (sampler (xs.getD mid 0)).bind (fun z =>
              (if q ≤ z then rec lo mid else rec (mid+1) hi).map
                (fun out => (out.1,out.2+1)))) fuel lo hi
      let var := bisect (fun t => sample (riskCDFLaw A j loss t M hA hM)) xs q
        (Nat.clog 2 xs.length+1) 0 (xs.length-1)
      let cvar := var.bind (fun z =>
        (sample (riskCDFLaw A j loss (xs.getD z.1 0) M hA hM)).bind (fun phat =>
          (sample (riskNumeratorLaw A j loss (xs.getD z.1 0) rotationBits M hA hloss hM)).map
            (fun μhat => (z.1,μhat/max ε phat,z.2+2))))
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event cvar (fun z => z.1 ≠ v ∨
        4*(ε : ℝ)/riskCDF A j loss (xs.getD v 0) <
          |(z.2.1 : ℝ)-riskTailMean A j loss (xs.getD v 0)|) ≤
        ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r) ∧
      ∀ z ∈ cvar.support, z.2.2 ≤ Nat.clog 2 xs.length+3

end Qatlib.Concepts.RiskEstimation.CVaREstimation
