/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.SignalProcessing
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix

noncomputable def lcAxisRotation (φ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Real.cos (θ/2),
     -Complex.I * Complex.exp (Complex.I * (-(φ : ℂ))) * (Real.sin (θ/2) : ℂ);
     -Complex.I * Complex.exp (Complex.I * (φ : ℂ)) * (Real.sin (θ/2) : ℂ),
     Real.cos (θ/2)]

noncomputable def lcWord (phis : List ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (phis.reverse.map (fun φ => lcAxisRotation φ θ)).foldl (· * ·) 1

noncomputable def lcSignalStep (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  lcAxisRotation 0 θ

noncomputable def lcHad : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) • !![(1 : ℂ), 1; 1, -(1 : ℂ)]

noncomputable def lcPlusAmp (phis : List ℝ) (θ : ℝ) : ℂ :=
  (lcHad * lcWord phis θ * lcHad) 0 0

noncomputable def lcHalfDiffs : List ℝ → List ℝ
  | [] => []
  | [_] => []
  | a :: b :: rest => ((a - b) / 2) :: lcHalfDiffs (b :: rest)

noncomputable def lcQspTilde (qs : List ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (qs.map (fun q => (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
    Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q)).foldl (· * ·) 1

noncomputable def lcRepoAmp (γ₀ γ₁ : ℝ) (qs : List ℝ) (x : ℝ) : ℂ :=
  (lcHad * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation γ₀ * lcQspTilde qs x *
    (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation γ₁ *
    lcHad) 0 0

noncomputable def wordAmp (phis : List ℝ) (x : ℝ) : ℂ :=
  (lcHad * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.QSPWord phis x * lcHad) 0 0

noncomputable def plusCorner {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] (V : Matrix W W ℂ) (L R : Matrix W I ℂ) (ψ : I → ℂ) : I → ℂ :=
  (1/2 : ℂ) • (Qatlib.Concepts.Execution.WorkspaceCP.compress L V R *ᵥ ψ +
    Qatlib.Concepts.Execution.WorkspaceCP.compress L V L *ᵥ ψ +
    Qatlib.Concepts.Execution.WorkspaceCP.compress R V R *ᵥ ψ +
    Qatlib.Concepts.Execution.WorkspaceCP.compress R V L *ᵥ ψ)

noncomputable def lcWalk {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] (S : Matrix W W ℂ) (L : Matrix W I ℂ) : Matrix W W ℂ :=
  Complex.I • S * (2 • (L * L.conjTranspose) - 1)

noncomputable def lcControlledWalk {W : Type} [Fintype W] [DecidableEq W]
    (V : Matrix W W ℂ) : Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  Matrix.of fun ⟨a, w⟩ ⟨a', w'⟩ =>
    if a = a' then (if a = 0 then (if w = w' then 1 else 0) else V w w') else 0

noncomputable def lcHadAncilla (W : Type) [Fintype W] [DecidableEq W] :
    Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  Matrix.of fun ⟨a, w⟩ ⟨a', w'⟩ => if w = w' then lcHad a a' else 0

noncomputable def lcPhaseAncilla (γ : ℝ) (W : Type) [Fintype W] [DecidableEq W] :
    Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  Matrix.of fun ⟨a, w⟩ ⟨a', w'⟩ => if w = w' then Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation γ a a' else 0

noncomputable def lcUhat {W : Type} [Fintype W] [DecidableEq W] (φ : ℝ)
    (V : Matrix W W ℂ) : Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  lcPhaseAncilla (-(φ/2)) W *
    (lcHadAncilla W * lcControlledWalk V * lcHadAncilla W) * lcPhaseAncilla (φ/2) W

noncomputable def lcSimWord {W : Type} [Fintype W] [DecidableEq W]
    (V : Matrix W W ℂ) (phis : List ℝ) : Matrix (Fin 2 × W) (Fin 2 × W) ℂ :=
  (phis.reverse.mapIdx (fun j φ =>
    if j % 2 = 0 then lcUhat φ V else (lcUhat (φ + Real.pi) V)ᴴ)).foldl (· * ·) 1

noncomputable def lcPlusFrame {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] (L : Matrix W I ℂ) : Matrix (Fin 2 × W) I ℂ :=
  Matrix.of fun ⟨_, w⟩ i => ((Real.sqrt 2)⁻¹ : ℝ) • L w i

noncomputable def lcBesselJ (k : ℕ) (τ : ℝ) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j * (τ/2) ^ (2*j + k) /
    ((j.factorial : ℝ) * ((j + k).factorial : ℝ))

noncomputable def realEval (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  Polynomial.eval z (p.map Complex.ofRealHom)

noncomputable def lcCorrectedQ (τ : ℝ) (ε : ℝ) : ℕ :=
  max (⌈3 * τ⌉₊ + 1)
    (max 4 (⌈3 * Real.log (32 / ε) /
      Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ + 1))

end Qatlib.Concepts.QsvtCore.PhaseExistence
