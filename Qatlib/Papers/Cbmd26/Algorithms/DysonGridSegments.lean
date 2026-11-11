/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DysonSegmentEvolution
import Qatlib.Papers.Cbmd26.Algorithms.PiecewiseGridFreeze

/-!
# Grouping Dyson grid evolution into segments

This module relates left-ordered matrix products to circuit evaluation and groups a uniform
Hamiltonian grid into equal blocks. `dysonGridSegment` is the product of the exact single-step
Hamiltonian evolutions in one block, and Hermitian samples make each segment unitary. These
identities connect segmented circuits to the supplied grid evolution used in the algorithms of
[WangEtAl2026].

## Main statements

* `piecewiseLeftProduct_blocks`: flattens products of consecutive blocks.
* `dysonGridSegment_product`: identifies the reversed segment circuit with the full uniform-grid
  evolution.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Enumerating a function on reversed finite indices produces the reverse of its original
enumeration. -/
private theorem list_ofFn_rev {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.rev, Fin.val_mk]
  omega

/-- Enumerating `f` on `Fin n` equals mapping `f` over `List.range n`. -/
private theorem list_ofFn_nat {α : Type*} (f : ℕ → α) (n : ℕ) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

section Product
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The left-ordered product of `n + m` factors splits into the product of the last `m` factors
followed by the first `n` factors. -/
theorem piecewiseLeftProduct_add (f : ℕ → Matrix I I ℂ) (n m : ℕ) :
    piecewiseLeftProduct f (n + m) =
      piecewiseLeftProduct (fun j => f (n + j)) m * piecewiseLeftProduct f n := by
  induction m with
  | zero => simp [piecewiseLeftProduct]
  | succ m ih =>
    rw [show n + (m+1) = (n+m)+1 by omega, piecewiseLeftProduct, ih,
      piecewiseLeftProduct, mul_assoc]

/-- Taking `S` consecutive left-ordered products of `M` factors equals the left-ordered product
of all `S * M` factors. -/
theorem piecewiseLeftProduct_blocks (f : ℕ → Matrix I I ℂ) (M S : ℕ) :
    piecewiseLeftProduct (fun i => piecewiseLeftProduct (fun j => f (i*M+j)) M) S =
      piecewiseLeftProduct f (S*M) := by
  induction S with
  | zero => simp [piecewiseLeftProduct]
  | succ S ih =>
    rw [piecewiseLeftProduct, ih, show (S+1)*M = S*M+M by ring,
      piecewiseLeftProduct_add]

/-- Evaluating the canonical word on a family indexed in reverse order gives its left-ordered
product. -/
theorem unitaryFamilyEvaluate_reverse_product (f : ℕ → Matrix I I ℂ) (S : ℕ) :
    unitaryFamilyEvaluate (fun i : Fin S => f i.rev.val) (unitaryFamilyWord S) =
      piecewiseLeftProduct f S := by
  rw [unitaryFamilyEvaluate_eq_list_prod]
  simp only [unitaryFamilyWord, List.map_ofFn, Function.comp_def, id_eq]
  rw [list_ofFn_rev (fun i : Fin S => f i.val), list_ofFn_nat,
    piecewiseLeftProduct_eq_reverse_prod]

/-- A finite left-ordered product of unitary matrices is unitary. -/
theorem piecewiseLeftProduct_unitary (f : ℕ → Matrix I I ℂ) (n : ℕ)
    (hf : ∀ j < n, f j ∈ Matrix.unitaryGroup I ℂ) :
    piecewiseLeftProduct f n ∈ Matrix.unitaryGroup I ℂ := by
  induction n with
  | zero => exact (Matrix.unitaryGroup I ℂ).one_mem
  | succ n ih =>
    exact (Matrix.unitaryGroup I ℂ).mul_mem
      (hf n (by omega)) (ih (fun j hj => hf j (by omega)))

/-- The left-ordered product of `M` Hamiltonian evolution steps of duration `h`, starting at
sample index `q * M`. -/
def dysonGridSegment (F : ℕ → Matrix I I ℂ) (h : ℝ) (M q : ℕ) : Matrix I I ℂ :=
  piecewiseLeftProduct (fun j => HamiltonianEvolution (F (q*M+j)) h) M

/-- A grid segment is unitary when its sample Hamiltonians are Hermitian and its segment index
is less than `S`. -/
theorem dysonGridSegment_unitary (F : ℕ → Matrix I I ℂ) (h : ℝ) (M S q : ℕ)
    (hq : q < S) (hF : ∀ j < S*M, (F j).IsHermitian) :
    dysonGridSegment F h M q ∈ Matrix.unitaryGroup I ℂ := by
  apply piecewiseLeftProduct_unitary
  intro j hj
  apply hamiltonianEvolution_unitary
  apply hF
  have hqM := Nat.mul_le_mul_right M (Nat.succ_le_of_lt hq)
  rw [Nat.succ_mul] at hqM
  omega

/-- Evolution on the uniform grid with spacing `h` equals the left-ordered product of the
corresponding Hamiltonian steps. -/
theorem suppliedGridEvolution_uniform (F : ℕ → Matrix I I ℂ) (h : ℝ) (N : ℕ) :
    suppliedGridEvolution (fun j => (j : ℝ)*h) F N =
      piecewiseLeftProduct (fun j => HamiltonianEvolution (F j) h) N := by
  unfold suppliedGridEvolution
  congr 1
  funext j
  congr 1
  push_cast
  ring

/-- Evaluating the `S` segments in reverse index order reproduces the supplied uniform-grid
evolution over `S * M` steps. -/
theorem dysonGridSegment_product (F : ℕ → Matrix I I ℂ) (h : ℝ) (M S : ℕ) :
    unitaryFamilyEvaluate (fun i : Fin S => dysonGridSegment F h M i.rev.val)
      (unitaryFamilyWord S) = suppliedGridEvolution (fun j => (j : ℝ)*h) F (S*M) := by
  rw [unitaryFamilyEvaluate_reverse_product, suppliedGridEvolution_uniform]
  exact piecewiseLeftProduct_blocks (fun j => HamiltonianEvolution (F j) h) M S

end Product
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
