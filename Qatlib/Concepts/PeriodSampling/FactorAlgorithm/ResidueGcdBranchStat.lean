/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.ResidueFactoringPrograms

/-!
# Residue gcd branch contract

Defines `ResidueGcdBranch`, the specification connecting classical gcd factors, coprime
residues, and modular units. The cardinality identity supplies the counting input for the
residue-based factoring probability model associated with [Shor1997].

## Main statements

* `ResidueGcdBranch`: Specifies factor soundness, residue-to-unit conversion, and the counting
  identity.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PopulationGap
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

/-- For `N ≥ 2`, requires sound classical residue factors, successful conversion of every
coprime residue to its unit, exact conversion of existing units, and equality between the
coprime-residue count and the unit count. -/
def ResidueGcdBranch : Prop :=
  ∀ (N : ℕ) [NeZero N], 2 ≤ N →
    (∀ (y : ZMod N) (d : ℕ), residueClassicalFactor N y = some d →
        1 < d ∧ d < N ∧ d ∣ N) ∧
    (∀ (y : ZMod N), Nat.Coprime y.val N →
        ∃ a : (ZMod N)ˣ, residueCoprimeUnit N y = some a ∧ (a : ZMod N) = y) ∧
    (∀ u : (ZMod N)ˣ, residueCoprimeUnit N (u : ZMod N) = some u) ∧
    ((Finset.univ.filter fun y : ZMod N => Nat.Coprime y.val N).card
        = Fintype.card (ZMod N)ˣ)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
