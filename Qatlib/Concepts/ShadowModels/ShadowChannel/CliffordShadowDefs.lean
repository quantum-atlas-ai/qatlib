/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordShadowContracts
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ShadowModels.ShadowChannel.FiniteEnsembleMeasurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.InstrumentCore.Measurement

open Matrix
open scoped Classical BigOperators

namespace Qatlib.Concepts.ShadowModels.ShadowChannel
def CliffordMomentHypothesisV2 (d : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d) : Prop :=
  ∀ Pp : Operator d, IsPureDensityOperator Pp → ∀ A : Operator d, A.IsHermitian →
    (∑ i, (μ.prob i * (Matrix.trace (A * ((Uf i)ᴴ * Pp * Uf i))).re) •
        ((Uf i)ᴴ * Pp * Uf i)) =
      ((Matrix.trace A).re / ((d : ℝ) * ((d : ℝ) + 1))) • 1 +
      (1 / ((d : ℝ) * ((d : ℝ) + 1))) • A
end Qatlib.Concepts.ShadowModels.ShadowChannel

set_option autoImplicit false
set_option maxHeartbeats 900000
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace Qatlib.Concepts.ShadowModels.ShadowChannel.HuangKuengPreskill2020
noncomputable section

theorem basisProjector_eq_projector {d : ℕ} (b : Fin d) :
    basisProjector b = Projector ({b} : Finset (Fin d)) := by
  ext i j
  simp only [basisProjector, Projector, Matrix.diagonal_apply, Finset.mem_singleton]
  split_ifs <;> simp_all
end
noncomputable section

theorem basisProjector_pure {d : ℕ} (b : Fin d) : IsPureDensityOperator (basisProjector b) := by
  rw [basisProjector_eq_projector]
  refine ⟨⟨?_, trace_projector_singleton b⟩, projector_mul_self _⟩
  have hp : (Projector ({b} : Finset (Fin d))) =
      (Projector ({b} : Finset (Fin d)))ᴴ*Projector ({b} : Finset (Fin d)) := by
    rw [projector_conjTranspose, projector_mul_self]
  rw [hp]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end
noncomputable section

theorem basis_born_trace_cycle {d : ℕ} (ρ U : Operator d) (b : Fin d) :
    Matrix.trace (basisProjector b*(U*ρ*Uᴴ)) =
      Matrix.trace (ρ*(Uᴴ*basisProjector b*U)) := by
  calc
    _ = Matrix.trace (basisProjector b*U*ρ*Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Uᴴ*basisProjector b*U*ρ) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (basisProjector b*U) ρ Uᴴ
    _ = _ := Matrix.trace_mul_comm _ _
end
end Qatlib.Concepts.ShadowModels.ShadowChannel.HuangKuengPreskill2020
