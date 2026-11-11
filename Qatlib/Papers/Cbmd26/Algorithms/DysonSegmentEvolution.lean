/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.RobustDysonSegmentBridge
import Qatlib.Foundations.CbmdAnalysis.Core.PiecewiseRepresentation

/-!
# Exact segments of piecewise Dyson evolution

`piecewiseEvolutionSegment` forms the relative propagator by multiplying an evolution matrix by
the adjoint at its starting time. For Hermitian `H` and positive semidefinite `L`, real sample
parameters give unitary segments satisfying a cocycle identity, an almost-everywhere evolution
equation, and absolute continuity.

`piecewiseEvolutionSegment_product` telescopes a finite sequence of segments to the full
propagator. These identities supply exact segment targets for the time-dependent algorithms of
[WangEtAl2026].

## Main statements

* `piecewiseEvolutionSegment_cocycle`: composes adjacent relative propagators.
* `piecewiseEvolutionSegment_product`: identifies the segment circuit with the full evolution.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- For continuous Hermitian coefficient families, the assembled Dyson evolution is unitary at
every real sample parameter and time. -/
theorem assembledDyson_real_unitary_all {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j))
    (hHherm : ∀ j u, (H j u).IsHermitian) (hLherm : ∀ j u, (L j u).IsHermitian)
    (τ : ℕ → ℝ) (n : ℕ) (x t : ℝ) :
    _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.assembledDyson H L τ n (x : ℂ) t ∈ Matrix.unitaryGroup I ℂ := by
  induction n with
  | zero => exact (Matrix.unitaryGroup I ℂ).one_mem
  | succ n ih =>
    unfold _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.assembledDyson
    split_ifs
    · exact ih
    · exact (Matrix.unitaryGroup I ℂ).mul_mem
        (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPropagator_real_unitary (H n) (L n) (hH n) (hL n)
          (hHherm n) (hLherm n) _ _ x)
        (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.dysonPiecewise_real_unitary H L hH hL hHherm hLherm τ n x)

section Piecewise
variable {I : Type} [Fintype I] [DecidableEq I]
variable {H L : ℝ → Matrix I I ℂ} {a b : ℝ}

/-- If `H` is Hermitian and `L` is positive semidefinite on the defining interval, the piecewise
evolution is unitary for every real parameter and time. -/
theorem piecewise_evolution_real_unitary_all
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian)
    (hL : ∀ t ∈ Icc a b, (L t).PosSemidef) (x t : ℝ) :
    P.evolution (x : ℂ) t ∈ Matrix.unitaryGroup I ℂ :=
  assembledDyson_real_unitary_all P.hPiece P.lPiece P.hPiece_continuous P.lPiece_continuous
    (P.hPiece_hermitian hH) (fun j u => (P.lPiece_positive hL j u).isHermitian)
    P.time P.count x t

/-- The relative evolution from `s` to `t`, defined as the evolution at `t` times the adjoint of
the evolution at `s`. -/
def piecewiseEvolutionSegment
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (x s t : ℝ) : Matrix I I ℂ := P.evolution (x : ℂ) t * (P.evolution (x : ℂ) s)ᴴ

/-- The relative evolution is unitary for real sample parameters when `H` is Hermitian and `L`
is positive semidefinite on the defining interval. -/
theorem piecewiseEvolutionSegment_unitary
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian)
    (hL : ∀ t ∈ Icc a b, (L t).PosSemidef) (x s t : ℝ) :
    piecewiseEvolutionSegment P x s t ∈ Matrix.unitaryGroup I ℂ :=
  (Matrix.unitaryGroup I ℂ).mul_mem (piecewise_evolution_real_unitary_all P hH hL x t)
    (adjoint_unitary (piecewise_evolution_real_unitary_all P hH hL x s))

/-- A relative evolution segment with equal endpoints is the identity under the Hermiticity and
positivity hypotheses. -/
theorem piecewiseEvolutionSegment_self
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian)
    (hL : ∀ t ∈ Icc a b, (L t).PosSemidef) (x s : ℝ) :
    piecewiseEvolutionSegment P x s s = 1 := by
  simpa only [piecewiseEvolutionSegment, Matrix.star_eq_conjTranspose] using!
    (piecewise_evolution_real_unitary_all P hH hL x s).2

/-- Almost everywhere on the defining interval, the segment satisfies the evolution equation
with derivative `-i (H(t) + x L(t))` times the segment. -/
theorem piecewiseEvolutionSegment_hasDerivAt_ae
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (x s : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Icc a b → HasDerivAt (piecewiseEvolutionSegment P x s)
      (-(Complex.I • (H t + (x : ℂ) • L t) * piecewiseEvolutionSegment P x s t)) t := by
  filter_upwards [P.evolution_hasDerivAt_ae (x : ℂ)] with t ht hmem
  convert! (ht hmem).mul_const (P.evolution (x : ℂ) s)ᴴ using 1
  simp only [piecewiseEvolutionSegment, neg_mul, mul_assoc]

/-- The relative evolution, as a function of its final time, is absolutely continuous on the
defining interval. -/
theorem piecewiseEvolutionSegment_absolutelyContinuous
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (x s : ℝ) : AbsolutelyContinuousOnInterval (piecewiseEvolutionSegment P x s) a b :=
  _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.absolutelyContinuous_mul (P.evolution_absolutelyContinuous (x : ℂ))
    ((show ContDiff ℝ 1 (fun _ : ℝ => (P.evolution (x : ℂ) s)ᴴ) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval)

/-- Under the Hermiticity and positivity hypotheses, multiplying the segment from `s` to `t` by
the segment from `r` to `s` gives the segment from `r` to `t`. -/
theorem piecewiseEvolutionSegment_cocycle
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian)
    (hL : ∀ t ∈ Icc a b, (L t).PosSemidef) (x r s t : ℝ) :
    piecewiseEvolutionSegment P x s t * piecewiseEvolutionSegment P x r s =
      piecewiseEvolutionSegment P x r t := by
  have hu : (P.evolution (x : ℂ) s)ᴴ * P.evolution (x : ℂ) s = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      (piecewise_evolution_real_unitary_all P hH hL x s).1
  simp only [piecewiseEvolutionSegment, mul_assoc]
  rw [← mul_assoc (P.evolution (x : ℂ) s)ᴴ, hu, one_mul]

end Piecewise

section Telescoping
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Evaluating a unitary-family word equals the list product of its selected matrices. -/
theorem unitaryFamilyEvaluate_eq_list_prod {m : ℕ} (V : Fin m → Matrix I I ℂ)
    (is : List (Fin m)) : unitaryFamilyEvaluate V is = (is.map V).prod := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [unitaryFamilyEvaluate, List.map_cons, List.prod_cons, ih]

/-- The ordered product of adjacent matrices `W i * (W (i + 1))ᴴ` telescopes to the first matrix
times the adjoint of the last when every `W i` is unitary. -/
theorem unitary_adjacent_product (m : ℕ) (W : Fin (m + 1) → Matrix I I ℂ)
    (hW : ∀ i, W i ∈ Matrix.unitaryGroup I ℂ) :
    (List.ofFn (fun i : Fin m => W i.castSucc * (W i.succ)ᴴ)).prod =
      W 0 * (W (Fin.last m))ᴴ := by
  induction m with
  | zero =>
    have hu : W 0 * (W 0)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using! (hW 0).2
    simpa using! hu.symm
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have ht := ih (fun i => W i.succ) (fun i => hW i.succ)
    simp only [Fin.succ_castSucc] at ht ⊢
    rw [ht]
    have hu : (W (0 : Fin (m + 1)).succ)ᴴ * W (0 : Fin (m + 1)).succ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using! (hW (0 : Fin (m + 1)).succ).1
    rw [mul_assoc, ← mul_assoc ((W (0 : Fin (m + 1)).succ)ᴴ), hu, one_mul]
    rfl

/-- A circuit of relative evolution segments whose first node is `b` and last node is `a`
evaluates to the piecewise propagator at `b`, under the stated Hermiticity and positivity
hypotheses. -/
theorem piecewiseEvolutionSegment_product {H L : ℝ → Matrix I I ℂ} {a b : ℝ}
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian)
    (hL : ∀ t ∈ Icc a b, (L t).PosSemidef) (x : ℝ) (m : ℕ)
    (nodes : Fin (m + 1) → ℝ) (hend : nodes 0 = b) (hstart : nodes (Fin.last m) = a) :
    unitaryFamilyEvaluate
      (fun i : Fin m => piecewiseEvolutionSegment P x (nodes i.succ) (nodes i.castSucc))
      (unitaryFamilyWord m) = P.evolution (x : ℂ) b := by
  rw [unitaryFamilyEvaluate_eq_list_prod]
  simp only [unitaryFamilyWord, List.map_ofFn, Function.comp_def, id_eq, piecewiseEvolutionSegment]
  rw [unitary_adjacent_product m (fun i => P.evolution (x : ℂ) (nodes i))
    (fun i => piecewise_evolution_real_unitary_all P hH hL x (nodes i))]
  rw [hend, hstart, P.evolution_initial, Matrix.conjTranspose_one, mul_one]

end Telescoping
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
