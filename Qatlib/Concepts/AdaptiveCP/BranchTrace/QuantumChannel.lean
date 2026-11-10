/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.AdaptiveCP.BranchTrace

open scoped ComplexOrder

variable {D E F : ℕ}

noncomputable def ChannelAmplification
    (T : Operator D →ₗ[ℂ] Operator E) (r : ℕ)
    (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    Matrix (Fin r × Fin E) (Fin r × Fin E) ℂ :=
  fun x y => T (fun i j => A (x.1, i) (y.1, j)) x.2 y.2

def CompletelyPositive (T : Operator D →ₗ[ℂ] Operator E) : Prop :=
  ∀ (r : ℕ) (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ),
    A.PosSemidef → (ChannelAmplification T r A).PosSemidef

def TracePreserving (T : Operator D →ₗ[ℂ] Operator E) : Prop :=
  ∀ A, Matrix.trace (T A) = Matrix.trace A

structure QuantumChannel (D E : ℕ) where
  map : Operator D →ₗ[ℂ] Operator E
  completelyPositive : CompletelyPositive map
  tracePreserving : TracePreserving map

noncomputable def InducedTraceNorm (T : Operator D →ₗ[ℂ] Operator E) : ℝ :=
  sSup {r : ℝ | ∃ A : Operator D, SchattenOne A = 1 ∧ r = SchattenOne (T A)}

theorem CompletelyPositive.positive {T : Operator D →ₗ[ℂ] Operator E}
    (hT : CompletelyPositive T) {A : Operator D} (hA : A.PosSemidef) :
    (T A).PosSemidef := by
  have h := hT 1 (A.submatrix Prod.snd Prod.snd) (hA.submatrix Prod.snd)
  simpa [ChannelAmplification] using! h.submatrix (fun i => ((0 : Fin 1), i))

theorem CompletelyPositive.comp {S : Operator E →ₗ[ℂ] Operator F}
    {T : Operator D →ₗ[ℂ] Operator E} (hS : CompletelyPositive S)
    (hT : CompletelyPositive T) : CompletelyPositive (S.comp T) := by
  intro r A hA
  simpa [ChannelAmplification] using! hS r (ChannelAmplification T r A) (hT r A hA)

noncomputable def QuantumChannel.id (D : ℕ) : QuantumChannel D D where
  map := LinearMap.id
  completelyPositive := by
    intro r A hA
    simpa [ChannelAmplification] using! hA
  tracePreserving := by intro A; rfl

noncomputable def QuantumChannel.comp (S : QuantumChannel E F)
    (T : QuantumChannel D E) : QuantumChannel D F where
  map := S.map.comp T.map
  completelyPositive := S.completelyPositive.comp T.completelyPositive
  tracePreserving := by
    intro A
    change Matrix.trace (S.map (T.map A)) = Matrix.trace A
    rw [S.tracePreserving, T.tracePreserving]

theorem QuantumChannel.preservesDensity (T : QuantumChannel D E)
    {ρ : Operator D} (hρ : IsDensityOperator ρ) : IsDensityOperator (T.map ρ) :=
  ⟨T.completelyPositive.positive hρ.1, (T.tracePreserving ρ).trans hρ.2⟩

end Qatlib.Concepts.AdaptiveCP.BranchTrace
