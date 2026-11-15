/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

set_option autoImplicit false
namespace Qatlib.Concepts.NonNormalSpec.NumericalRange
open scoped BigOperators

noncomputable def finiteVectorPolynomial {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (K : ℕ) (c : Fin (K + 1) → E) (t : ℝ) : E :=
  ∑ i : Fin (K + 1), t ^ (i : ℕ) • c i

end Qatlib.Concepts.NonNormalSpec.NumericalRange
