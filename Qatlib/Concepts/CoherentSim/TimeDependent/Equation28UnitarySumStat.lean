/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TimeDependent.Equation28Stat

/-!
# Unitary sum specification for time dependent segments

`Equation28UnitarySum` specifies a finite unitary decomposition of `equation28Segment` for
Hamiltonians given by nonnegative combinations of fixed unitaries. Its total coefficient weight
is bounded above by a truncated exponential series and below by one.

The mathematical context is discussed in [BerryEtAl2015Taylor].

## Main statements

* `Equation28UnitarySum`: The positive unitary decomposition statement and its coefficient
  weight bounds.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.CoherentSim.TimeDependent

/-- The statement that a grid segment built from a Hamiltonian with nonnegative unitary
coefficients possesses a finite positive unitary representation whose total weight is
between one and ∑ k ≤ K, (Λτ)^k/k!. -/
def Equation28UnitarySum : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L : ℕ)
    (α : Fin L → ℝ → ℝ) (Hl : Fin L → Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (τ Λ : ℝ) (M K : ℕ),
    (∀ ℓ, Hl ℓ ∈ Matrix.unitaryGroup I ℂ) →
    (∀ (ℓ : Fin L) (u : ℝ), 0 ≤ α ℓ u) →
    (∀ u ∈ Set.Icc 0 τ, H u = ∑ ℓ, (α ℓ u : ℂ) • Hl ℓ) →
    (∀ u ∈ Set.Icc 0 τ, ∑ ℓ, α ℓ u ≤ Λ) → 0 < M → 0 ≤ τ →
    ∃ (D : Type) (_ : Fintype D) (_ : DecidableEq D) (β : D → ℝ) (V : D → Matrix I I ℂ),
      (∀ d, 0 ≤ β d) ∧ (∀ d, V d ∈ Matrix.unitaryGroup I ℂ) ∧
      equation28Segment H τ M K = ∑ d, (β d : ℂ) • V d ∧
      1 ≤ ∑ d, β d ∧
      ∑ d, β d ≤ ∑ k ∈ Finset.range (K + 1), (Λ * τ) ^ k / (((k.factorial : ℕ) : ℝ))

end Qatlib.Concepts.CoherentSim.TimeDependent
