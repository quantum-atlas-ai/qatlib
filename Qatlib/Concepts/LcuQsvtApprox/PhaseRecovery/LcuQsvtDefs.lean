/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.SignalProcessing
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

namespace Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery

open Matrix Polynomial Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

def Th3Pair (n : ℕ) (P Q : Polynomial ℂ) : Prop :=
  Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair n P Q

noncomputable def lqSignalRotation (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Complex.I * Real.sqrt (1 - x ^ 2);
     Complex.I * Real.sqrt (1 - x ^ 2), (x : ℂ)]

noncomputable def lqSignalReflection (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Real.sqrt (1 - x ^ 2);
     Real.sqrt (1 - x ^ 2), -(x : ℂ)]

noncomputable def lqZPhase (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![z, star z]

noncomputable def lqReflectionWord (x : ℝ) (Φ : List ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Φ.foldr (fun φ M => lqZPhase (anglePhase φ) * lqSignalReflection x * M) 1

noncomputable def lqSignalStep (x : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := M * lqSignalRotation x * lqZPhase z

noncomputable def lqSignalWord (x : ℝ) (z0 : ℂ) (zs : List ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  zs.foldl (lqSignalStep x) (lqZPhase z0)

noncomputable def lqEq3PairStep (w : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  (C w * (X * pq.1 - (1 - X ^ 2) * pq.2), C (star w) * (pq.1 + X * pq.2))

noncomputable def lqEq3Pair (z0 : ℂ) (zs : List ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  zs.foldl (fun pq z => lqEq3PairStep z pq) (C z0, 0)

noncomputable def lqSynthCount : ℕ → Polynomial ℂ → Polynomial ℂ → ℕ
  | 0, _, _ => 0
  | n + 1, P, Q =>
    let z := alignPhase (P.coeff (n + 1)) (Q.coeff n)
    12 + 8 * (max P.natDegree Q.natDegree + 1) +
      lqSynthCount n (inverseResponseP z P Q) (inverseResponseQ z P Q)

def lqSynthOpCount (n : ℕ) : ℕ := n * (8 * n + 28)

noncomputable def lqSynthWithCount (n : ℕ) (P Q : Polynomial ℂ) :
    (ℂ × List ℂ) × ℕ := (synthesizePair n P Q, lqSynthCount n P Q)

noncomputable def lqJaTerm (J : ℕ → ℝ) (θ : ℝ) (k : ℕ) : ℂ :=
  ((J k : ℝ) : ℂ) * Complex.exp (-(Complex.I * (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)))) +
    (if k = 0 then 0 else
      (-1 : ℂ) ^ k * ((J k : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ))))

noncomputable def lqJaTrunc (J : ℕ → ℝ) (θ : ℝ) (q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range q, lqJaTerm J θ k

def lqJaTruncOpCount (q : ℕ) : ℕ := q * 10 + 4

noncomputable def lqJaTruncWithCount (J : ℕ → ℝ) (θ : ℝ) (q : ℕ) : ℂ × ℕ :=
  (lqJaTrunc J θ q, lqJaTruncOpCount q)

def lqPhaseRecoveryOps (n : ℕ) : ℕ := 2048 * n * (Nat.clog 2 n + 5) ^ 2

noncomputable def lqIdealOp (h : ℝ → ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun b =>
    if b = 0 then Complex.exp (Complex.I * ((h θ : ℝ) : ℂ))
    else Complex.exp (Complex.I * (-((h θ : ℝ) : ℂ)))

noncomputable def lqHad : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) • !![(1 : ℂ), 1; 1, -(1 : ℂ)]

noncomputable def lqRepoWord (γ₀ γ₁ : ℝ) (qs : List ℝ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  lqHad * PhaseRotation γ₀ *
    (qs.map fun q => (SignalMatrix x).conjTranspose * PhaseRotation q).foldl (· * ·) 1 *
    (SignalMatrix x).conjTranspose * PhaseRotation γ₁ * lqHad

noncomputable def lqRepoAmpWord (γ₀ γ₁ : ℝ) (qs : List ℝ) (x : ℝ) : ℂ :=
  (lqRepoWord γ₀ γ₁ qs x) 0 0

structure LqSparseOracle (n d : ℕ) (b : ℝ) where
  H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  entries : Fin (2 ^ n) → List (Fin (2 ^ n) × ℂ)
  entries_complete : ∀ o i, H o i ≠ 0 → (i, H o i) ∈ entries o
  entries_sound : ∀ (o : Fin (2 ^ n)) (p : Fin (2 ^ n) × ℂ),
    p ∈ entries o → p.2 = H o p.1
  row_bound : ∀ o, (entries o).length ≤ d
  hermitian : H.IsHermitian
  entry_bound : ∀ o i, ‖H o i‖ ≤ b

def LqWalkFrame {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (c : ℝ) (H : Matrix I I ℂ) (L R : Matrix W I ℂ) (S : Matrix W W ℂ) : Prop :=
  Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L ∧ Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry R ∧
    L.conjTranspose * R = ((c : ℝ) : ℂ) • H ∧
    S ∈ Matrix.unitaryGroup W ℂ ∧ S.conjTranspose = S ∧ S * S = 1 ∧ S * L = R

end Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
