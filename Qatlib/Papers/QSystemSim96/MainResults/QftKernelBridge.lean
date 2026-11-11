/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QftPreparation.LocalQft
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic
import Qatlib.Papers.QSystemSim96.MainResults.ShortTimeStepFactorization

/-!
# Bridging the local QFT and the lattice kernel

This module connects the local QFT circuit to the cyclic-grid Fourier kernel used in
[Zalka1998]. `zmodFourier`, `qftFinZmod`, and `latticeRegEquiv` relate Fourier matrices indexed
by finite integers, bit registers, and residue classes.

`diagonalQftSandwichRun` composes a local QFT with supplied pre- and post-circuits, and
`source_basis_map_qft_sandwich` identifies the short-step matrix with a normalized Fourier
sandwich when the lattice coefficient is `2 * Real.pi / N`.

## Main statements

* `qftFinZmod` identifies the relabeled finite QFT with `zmodFourier`.
* `diagonalQftSandwichRun` and `diagonalQftSandwichCosts` give the composite action and exact
  resources.
* `localQFT_lattice_matrix` identifies the local implementation under `latticeRegEquiv`.
* `source_basis_map_qft_sandwich` and `source_basis_map_unitary` specialize the short-step
  construction to the ordinary Fourier kernel.

## References

* [Zalka, 1998][Zalka1998]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QftPreparation.LocalQft
open Matrix
open scoped BigOperators
noncomputable section
namespace Qatlib.Papers.QSystemSim96.MainResults

/-- The normalized Fourier matrix on `ZMod M`, with entries `1 / sqrt M` times the standard
additive character of the product of the indices. -/
def zmodFourier (M : ℕ) [NeZero M] : Matrix (ZMod M) (ZMod M) ℂ :=
  fun a b => (Real.sqrt (M : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (a*b)

/-- The inverse finite-residue equivalence preserves the natural representative value of a
residue class. -/
theorem finZmodValue (M : ℕ) [NeZero M] (a : ZMod M) :
    ((ZMod.finEquiv M).symm a).val = a.val := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M => rfl

/-- Relabeling `QFTMatrix M` by the finite-residue equivalence gives `zmodFourier M`. -/
theorem qftFinZmod (M : ℕ) [NeZero M] :
    relabelGate (ZMod.finEquiv M).toEquiv (QFTMatrix M) = zmodFourier M := by
  ext a b
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, zmodFourier]
  change (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^
    ((((ZMod.finEquiv M).symm a).val : ℤ) * (((ZMod.finEquiv M).symm b).val : ℤ)) = _
  rw [finZmodValue, finZmodValue]
  have hab : a*b = (((a.val*b.val : ℕ) : ℤ) : ZMod M) := by
    push_cast
    simp
  rw [hab, ZMod.stdAddChar_coe, primRoot, ← Complex.exp_int_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- If the supplied pre- and post-circuits implement `Dpre` and `Dpost`, their composition
around the local QFT implements `Dpost * QFT * Dpre`, as in the Fourier-sandwich
construction of [Zalka1998]. -/
theorem diagonalQftSandwichRun (n : ℕ) (Cpre Cpost : Circuit (Reg n))
    (Dpre Dpost : Matrix (Reg n) (Reg n) ℂ)
    (hpre : ∀ψ, Run 1 Cpre ψ = ApplyGate Dpre ψ)
    (hpost : ∀ψ, Run 1 Cpost ψ = ApplyGate Dpost ψ) (ψ : QState (Reg n)) :
    Run 1 (Cpre ++ localProgramCircuit (localQFT n) ++ Cpost) ψ =
      ApplyGate (Dpost * relabelGate (bitVecEquiv n).symm (QFTMatrix (2^n)) * Dpre) ψ := by
  rw [run_append, run_append, hpre, (localDyadicProgram_run_adjoint_cost n (localQFT n) _).1,
    (localQFT_exact_positive_matrix n).1, hpost, applyGate_mul, applyGate_mul]

/-- The pre-QFT-post circuit has the sum of the endpoint gate counts and the exact local QFT
count, while its query count is the sum of the endpoint query counts, providing resource
accounting for [Zalka1998]. -/
theorem diagonalQftSandwichCosts (n : ℕ) (Cpre Cpost : Circuit (Reg n)) :
    GateCount (Cpre ++ localProgramCircuit (localQFT n) ++ Cpost) =
      GateCount Cpre + (n+n*(n-1)/2+n/2) + GateCount Cpost ∧
    QueryCount (Cpre ++ localProgramCircuit (localQFT n) ++ Cpost) =
      QueryCount Cpre + QueryCount Cpost := by
  rw [gateCount_append, gateCount_append, queryCount_append, queryCount_append,
    (aqLocalQFT_actual_matrix_and_cost n).2.1, (aqLocalQFT_actual_matrix_and_cost n).2.2]
  simp

/-- The equivalence from an `n`-bit register to `ZMod (2 ^ n)`, composed from `bitVecEquiv` and
the finite-residue equivalence. -/
def latticeRegEquiv (n : ℕ) : Reg n ≃ ZMod (2 ^ n) :=
  (bitVecEquiv n).trans (ZMod.finEquiv (2 ^ n)).toEquiv

/-- Relabeling the actual local QFT matrix by `latticeRegEquiv n` gives the normalized Fourier
matrix on the dyadic lattice, identifying the Fourier implementation used for [Zalka1998]. -/
theorem localQFT_lattice_matrix (n : ℕ) :
    relabelGate (latticeRegEquiv n) (localProgramMatrix (localQFT n)) =
      zmodFourier (2 ^ n) := by
  calc
    relabelGate (latticeRegEquiv n) (localProgramMatrix (localQFT n)) =
        relabelGate (ZMod.finEquiv (2 ^ n)).toEquiv (QFTMatrix (2 ^ n)) := by
      rw [(aqLocalQFT_actual_matrix_and_cost n).1]
      ext a b
      simp [relabelGate, latticeRegEquiv]
    _ = zmodFourier (2 ^ n) := qftFinZmod _

/-- When `m * Δx ^ 2 / Δt = 2 * Real.pi / N`, the source-oriented short-step matrix equals the
output diagonal, normalized cyclic Fourier matrix, and input diagonal product of
[Zalka1998]. -/
theorem source_basis_map_qft_sandwich (N : ℕ) [NeZero N]
    (m Δx Δt : ℝ) (V : ZMod N → ℝ)
    (hcond : m * Δx ^ 2 / Δt = 2 * Real.pi / (N : ℝ)) :
    stepMatrix N m Δx Δt V =
      diagonalRight N m Δx Δt * zmodFourier N * diagonalLeft N m Δx Δt V := by
  rw [stepMatrix_eq_smul_diagonal_mul_fourier_mul_diagonal,
    fourierMatrix_eq_twistedDFT N m Δx Δt 1 (by simpa using hcond)]
  have hnorm : zmodFourier N = stepNormalisation N • twistedDFT N 1 := by
    ext a b
    simp [zmodFourier, stepNormalisation, twistedDFT, Matrix.smul_apply]
  rw [hnorm, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Nat.cast_one]

/-- The short-step matrix is unitary under the lattice relation `m * Δx ^ 2 / Δt = 2 * Real.pi /
N`. -/
theorem source_basis_map_unitary (N : ℕ) [NeZero N]
    (m Δx Δt : ℝ) (V : ZMod N → ℝ)
    (hcond : m * Δx ^ 2 / Δt = 2 * Real.pi / (N : ℝ)) :
    stepMatrix N m Δx Δt V ∈ Matrix.unitaryGroup (ZMod N) ℂ :=
  stepMatrix_mem_unitaryGroup N m Δx Δt V 1 (by simp) (by simpa using hcond)

end Qatlib.Papers.QSystemSim96.MainResults
