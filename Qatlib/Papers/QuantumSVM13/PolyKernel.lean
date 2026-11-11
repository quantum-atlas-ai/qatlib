/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Tensor-power polynomial kernels

Defines the tensor-power feature encoding of a quantum state and computes its inner products and
feature-space size. Tensor powers raise the original inner product to the polynomial degree,
while the logarithm of the feature-space cardinality scales linearly with that degree. See
[RebentrostMohseniLloyd2014].

## Main statements

* `tensorPow_inner`: identifies the tensor-power inner product with a power.
* `log_featureSpace`: computes the logarithm of the feature-space dimension.

## References

* [Rebentrost et al., 2014][RebentrostMohseniLloyd2014]
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QuantumSVM13.PolyKernel

open Qatlib.Foundations.PureStateMath

variable {N d : ℕ}

/-- The `d`-fold tensor-power amplitude encoding of `ψ`, indexed by functions from `Fin d` to
`Fin N`. -/
noncomputable def tensorPow (ψ : QState (Fin N)) (d : ℕ) : QState (Fin d → Fin N) :=
  fun v => ∏ i, ψ (v i)

/-- The inner product of two `d`-fold tensor-power encodings equals the `d`th power of their
original inner product [RebentrostMohseniLloyd2014]. -/
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

/-- For nonzero `N`, the tensor-power feature index type `Fin d → Fin N` has cardinality `N ^ d`
[RebentrostMohseniLloyd2014]. -/
theorem card_featureSpace (N d : ℕ) [NeZero N] :
    Fintype.card (Fin d → Fin N) = N ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- For positive `N`, the logarithm of the tensor-power feature-space cardinality is `d *
Real.log N` [RebentrostMohseniLloyd2014]. -/
theorem log_featureSpace (N d : ℕ) (hN : 0 < N) :
    Real.log ((Fintype.card (Fin d → Fin N) : ℝ)) = d * Real.log N := by
  haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
  rw [card_featureSpace, Nat.cast_pow, Real.log_pow]

end Qatlib.Papers.QuantumSVM13.PolyKernel
