/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid

/-!
# Discrete ordered-segment definitions

`gridIncrements` lists sampled Hamiltonian increments in reverse grid order, and
`equation28Segment` sums their sublist products up to a chosen order. These definitions give the
finite ordered expansion used to analyze the time-dependent Taylor extension
[BerryEtAl2015Taylor].

## Main statements

* `gridIncrements`: The reverse-ordered list of sampled evolution increments.
* `equation28Segment`: The sum of ordered sublist products through order `K`.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Concepts.CoherentSim.TimeDependent

/-- The reversed list of sampled increments `-(τ / M) • (I • H (τ * j / M))` over the `M`
time-grid indices. -/
noncomputable def gridIncrements {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (τ : ℝ) (M : ℕ) : List (Matrix I I ℂ) :=
  (List.ofFn (fun j : Fin M => -((τ / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (τ * (j : ℝ) / M)))).reverse

/-- The sum, for orders zero through `K`, of the products of all sublists of that length from
`gridIncrements`. -/
noncomputable def equation28Segment {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (τ : ℝ) (M K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K + 1), (((gridIncrements H τ M).sublistsLen k).map List.prod).sum
end Qatlib.Concepts.CoherentSim.TimeDependent
