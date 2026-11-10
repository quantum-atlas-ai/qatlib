/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QuantumSVM13.PolyKernel

open Qatlib.Foundations.PureStateMath

variable {N d : ℕ}

noncomputable def tensorPow (ψ : QState (Fin N)) (d : ℕ) : QState (Fin d → Fin N) :=
  fun v => ∏ i, ψ (v i)

theorem tensorPow_inner (ψ φ : QState (Fin N)) (d : ℕ) :
    Inner (tensorPow ψ d) (tensorPow φ d) = (Inner ψ φ) ^ d := by
  rw [inner_apply, inner_apply]
  have hterm : ∀ v : Fin d → Fin N,
      (starRingEnd ℂ) (tensorPow ψ d v) * tensorPow φ d v
        = ∏ i, (starRingEnd ℂ) (ψ (v i)) * φ (v i) := by
    intro v
    unfold tensorPow
    rw [map_prod, Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [Fintype.sum_pow]

theorem card_featureSpace (N d : ℕ) [NeZero N] :
    Fintype.card (Fin d → Fin N) = N ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem log_featureSpace (N d : ℕ) (hN : 0 < N) :
    Real.log ((Fintype.card (Fin d → Fin N) : ℝ)) = d * Real.log N := by
  haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
  rw [card_featureSpace, Nat.cast_pow, Real.log_pow]

end Qatlib.Papers.QuantumSVM13.PolyKernel
