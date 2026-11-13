/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.SignalProcessing
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

/-!
# Signal-processing word and Bessel definitions

This module fixes the matrix, phase, and series conventions used for quantum signal processing
in the setting of [LowChuang2017]. It defines equatorial-axis rotations, their words and
amplitudes, and a controlled-walk realization with ancilla phases.

It also supplies `lcBesselJ` as a factorial power series and `lcCorrectedQ` as an explicit
truncation cutoff.

## Main statements

* `lcAxisRotation`, `lcWord`, and `lcPlusAmp`: rotation words and amplitudes.
* `lcWalk`, `lcUhat`, and `lcSimWord`: walk and ancilla constructions.
* `lcBesselJ` and `lcCorrectedQ`: series coefficients and cutoff.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix

/-- The two-dimensional equatorial-axis rotation with azimuth `φ` and rotation angle `θ`. -/
noncomputable def lcAxisRotation (φ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Real.cos (θ/2),
     -Complex.I * Complex.exp (Complex.I * (-(φ : ℂ))) * (Real.sin (θ/2) : ℂ);
     -Complex.I * Complex.exp (Complex.I * (φ : ℂ)) * (Real.sin (θ/2) : ℂ),
     Real.cos (θ/2)]

/-- The product of axis rotations obtained by traversing the phase list in reverse order. -/
noncomputable def lcWord (phis : List ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (phis.reverse.map (fun φ => lcAxisRotation φ θ)).foldl (· * ·) 1

/-- The zero-azimuth axis rotation used as the signal step. -/
noncomputable def lcSignalStep (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  lcAxisRotation 0 θ

/-- The normalized two-dimensional Hadamard matrix. -/
noncomputable def lcHad : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) • !![(1 : ℂ), 1; 1, -(1 : ℂ)]

/-- The `(0, 0)` entry of the axis-rotation word conjugated by Hadamard matrices. -/
noncomputable def lcPlusAmp (phis : List ℝ) (θ : ℝ) : ℂ :=
  (lcHad * lcWord phis θ * lcHad) 0 0

/-- The list of half differences between consecutive angles. -/
noncomputable def lcHalfDiffs : List ℝ → List ℝ
  | [] => []
  | [_] => []
  | a :: b :: rest => ((a - b) / 2) :: lcHalfDiffs (b :: rest)

/-- The product of adjoint signal matrices followed by phase rotations from the list `qs`. -/
noncomputable def lcQspTilde (qs : List ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (qs.map (fun q => (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
    Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q)).foldl (· * ·) 1

/-- The `(0, 0)` amplitude of the Hadamard-framed signal word with endpoint phases `γ₀` and
`γ₁`. -/
noncomputable def lcRepoAmp (γ₀ γ₁ : ℝ) (qs : List ℝ) (x : ℝ) : ℂ :=
  (lcHad * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation γ₀ * lcQspTilde qs x *
    (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation γ₁ *
    lcHad) 0 0

/-- The `(0, 0)` amplitude of `QSPWord` conjugated by Hadamard matrices. -/
noncomputable def wordAmp (phis : List ℝ) (x : ℝ) : ℂ :=
  (lcHad * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.QSPWord phis x * lcHad) 0 0

/-- Half the sum of the four compressions of `V` between frames `L` and `R`, applied to `ψ`. -/
noncomputable def plusCorner {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] (V : Matrix W W ℂ) (L R : Matrix W I ℂ) (ψ : I → ℂ) : I → ℂ :=
  (1/2 : ℂ) • (Qatlib.Concepts.Execution.WorkspaceCP.compress L V R *ᵥ ψ +
    Qatlib.Concepts.Execution.WorkspaceCP.compress L V L *ᵥ ψ +
    Qatlib.Concepts.Execution.WorkspaceCP.compress R V R *ᵥ ψ +
    Qatlib.Concepts.Execution.WorkspaceCP.compress R V L *ᵥ ψ)

/-- The walk matrix `i * S * (2 * L * Lᴴ - 1)`. -/
noncomputable def lcWalk {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] (S : Matrix W W ℂ) (L : Matrix W I ℂ) : Matrix W W ℂ :=
  Complex.I • S * (2 • (L * L.conjTranspose) - 1)

/-- The block diagonal matrix acting as the identity on flag zero and as `V` on flag one. -/
noncomputable def lcControlledWalk {W : Type} [Fintype W] [DecidableEq W]
    (V : Matrix W W ℂ) : Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  Matrix.of fun ⟨a, w⟩ ⟨a', w'⟩ =>
    if a = a' then (if a = 0 then (if w = w' then 1 else 0) else V w w') else 0

/-- The Hadamard matrix acting on the ancilla and the identity on the workspace. -/
noncomputable def lcHadAncilla (W : Type) [Fintype W] [DecidableEq W] :
    Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  Matrix.of fun ⟨a, w⟩ ⟨a', w'⟩ => if w = w' then lcHad a a' else 0

/-- The angle phase rotation acting on the ancilla and the identity on the workspace. -/
noncomputable def lcPhaseAncilla (γ : ℝ) (W : Type) [Fintype W] [DecidableEq W] :
    Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  Matrix.of fun ⟨a, w⟩ ⟨a', w'⟩ => if w = w' then Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation γ a a' else 0

/-- The controlled-walk Hadamard sandwich conjugated by opposite half-angle ancilla phases. -/
noncomputable def lcUhat {W : Type} [Fintype W] [DecidableEq W] (φ : ℝ)
    (V : Matrix W W ℂ) : Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  lcPhaseAncilla (-(φ/2)) W *
    (lcHadAncilla W * lcControlledWalk V * lcHadAncilla W) * lcPhaseAncilla (φ/2) W

/-- The reversed phase-list product alternating between `lcUhat φ V` and the adjoint of `lcUhat
(φ + π) V`. -/
noncomputable def lcSimWord {W : Type} [Fintype W] [DecidableEq W]
    (V : Matrix W W ℂ) (phis : List ℝ) : Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  (phis.reverse.mapIdx (fun j φ =>
    if j % 2 = 0 then lcUhat φ V else (lcUhat (φ + Real.pi) V)ᴴ)).foldl (· * ·) 1

/-- The frame obtained by placing equal copies of `L`, scaled by `1 / sqrt 2`, in the two
ancilla sectors. -/
noncomputable def lcPlusFrame {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] (L : Matrix W I ℂ) : Matrix (Fin 2 × W) I ℂ :=
  Matrix.of fun ⟨_, w⟩ i => ((Real.sqrt 2)⁻¹ : ℝ) • L w i

/-- The order-`k` Bessel coefficient defined by its alternating factorial power series. -/
noncomputable def lcBesselJ (k : ℕ) (τ : ℝ) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j * (τ/2) ^ (2*j + k) /
    ((j.factorial : ℝ) * ((j + k).factorial : ℝ))

/-- Evaluates a real-coefficient polynomial at a complex argument after embedding its
coefficients in `ℂ`. -/
noncomputable def realEval (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  Polynomial.eval z (p.map Complex.ofRealHom)

/-- The corrected natural-number truncation cutoff formed from the stated time and logarithmic
error terms. -/
noncomputable def lcCorrectedQ (τ : ℝ) (ε : ℝ) : ℕ :=
  max (⌈3 * τ⌉₊ + 1)
    (max 4 (⌈3 * Real.log (32 / ε) /
      Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ + 1))

end Qatlib.Concepts.QsvtCore.PhaseExistence
