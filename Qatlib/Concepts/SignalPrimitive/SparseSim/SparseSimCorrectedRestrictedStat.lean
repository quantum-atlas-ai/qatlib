/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationStat
import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedStat

/-!
# Sparse Simulation Eigenvector Contract

`SparseSimulationCorrectedRestricted` specifies a compressed-walk simulation guarantee for a
Hermitian matrix with at most `d` nonzero entries per row and column and entry norms at most
`b`. It assumes supplied isometries `L`, `R` encoding `H / (d * b)` and a Hermitian unitary swap
`S` carrying `L` to `R`, in the sparse simulation setting of [LowChuang2017].

For nonnegative time and `0 < ε ≤ 1 / 2`, the contract requests one phase list of length `2 *
(lcCorrectedQ (t * d * b) (ε / 8) - 1)`. On every normalized eigenvector, the compressed word
must have squared error at most `ε ^ 2` from the target phase evolution and output mass at least
`1 - 2 * ε`.

## Main statements

* `SparseSimulationCorrectedRestricted` defines the supplied-frame eigenvector approximation and
  output-mass guarantee.

## References

- [Low and Chuang, 2017][LowChuang2017], Theorem 3.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.QspSimulation.SparseWalk
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Concepts.SignalPrimitive.SparseSim

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open scoped Matrix.Norms.L2Operator

/-- The supplied-frame sparse simulation contract requiring a single corrected-degree phase list
to approximate the target phase on every normalized Hamiltonian eigenvector. Under the
stated encoding and swap hypotheses, it requires squared error at most `ε ^ 2` and output
mass at least `1 - 2 * ε` for nonnegative time and `0 < ε ≤ 1 / 2`. -/
def SparseSimulationCorrectedRestricted : Prop :=
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (H : Matrix I I ℂ) (d : ℕ) (b : ℝ),
    H.IsHermitian → 0 < d → 0 < b →
    (∀ o, (Finset.univ.filter fun i => H o i ≠ 0).card ≤ d) →
    (∀ i, (Finset.univ.filter fun o => H o i ≠ 0).card ≤ d) →
    (∀ o i, ‖H o i‖ ≤ b) →
    ∀ (L R : Matrix W I ℂ) (S : Matrix W W ℂ),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry R →
      L.conjTranspose * R = ((((d : ℝ) * b)⁻¹ : ℝ) : ℂ) • H →
      S ∈ Matrix.unitaryGroup W ℂ → S.conjTranspose = S → S * S = 1 →
      S * L = R →
      ∀ (t ε : ℝ), 0 ≤ t → 0 < ε → ε ≤ 1/2 →
        ∃ (phis : List ℝ),

          phis.length = 2 * (lcCorrectedQ (t * d * b) (ε/8) - 1) ∧
          ∀ (ψ : I → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) → ∀ (ev : ℝ), H *ᵥ ψ = (ev : ℂ) • ψ →

            let y := Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
              (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ

            (∑ i, ‖(y i - Complex.exp (Complex.I * (-(ev : ℂ) * t)) * ψ i)‖ ^ 2)
              ≤ ε ^ 2 ∧

            1 - 2 * ε ≤ ∑ i, ‖(y i)‖ ^ 2

end Qatlib.Concepts.SignalPrimitive.SparseSim
