/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QBoltzmann16.MainResults.VisibleSector

@[expose] public section

/-!
# Normalization of the conditional output law

For a family of outcome effects `Λ_y = V_y V_y†` on a `D`-dimensional finite Gibbs model that
resolves the identity, `∑ y, Λ_y = 1`, the trace-ratio probabilities
`Qatlib.Papers.QBoltzmann16.MainResults.conditionalProbability` form a probability distribution on
the outcome labels. This is the outcome-sum normalization behind the denominator convention of
Eq (41) and Eq (47) of [AminEtAl2018]: the trace of `exp(-H)` cancels against the trace-sum
identity, and the denominator is strictly positive for every Hermitian Hamiltonian in positive
dimension.

The result is a statement about sums of trace ratios. It does not assert the equality of the
global conditional law with the input-clamped law, nor does it require the data weights to be
normalized.

## Main statements

* `conditionalProbability_sum_eq_one`: trace-ratio probabilities of a resolution of the identity
  sum to one.

## References

* [Amin et al., 2018][AminEtAl2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.QBoltzmann16.MainResults

open Qatlib.Papers.QBoltzmann16.MainResults

/-- If the outcome effects `V y * (V y)ᴴ` resolve the identity, the finite Gibbs trace-ratio
probabilities of the outcome labels sum to one. The trace is linear over the finite label sum, so
the numerator sums to `Tr(exp(-H))` and cancels the positive partition function
[AminEtAl2018], Eq (41). -/
theorem conditionalProbability_sum_eq_one {Y : Type*} [Fintype Y] {D E : ℕ}
    (H : Operator D) (V : Y → Matrix (Fin D) (Fin E) ℂ) (hD : 0 < D) (hH : H.IsHermitian)
    (hV : ∑ y, V y * (V y)ᴴ = 1) :
    ∑ y, conditionalProbability D H (V y * (V y)ᴴ) = 1 := by
  have hsum :
      ∑ y, Matrix.trace ((V y * (V y)ᴴ)*NormedSpace.exp (-H)) =
        Matrix.trace (NormedSpace.exp (-H)) := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hV, Matrix.one_mul]
  have hr := congrArg Complex.re hsum
  rw [Complex.re_sum] at hr
  unfold conditionalProbability marginalizedProbability
  rw [← Finset.sum_div, hr]
  exact div_self (gibbsPartition_pos D H hD hH).ne'

end Qatlib.Papers.QBoltzmann16.MainResults
