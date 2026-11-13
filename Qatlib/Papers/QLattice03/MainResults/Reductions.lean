/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Defs

/-!
# Solver predicates for lattice reductions

This module defines the solver predicates used in the lattice reductions of [Regev2004]. The
exponent `svpExponent` is 1/2 + 2f, while `ThetaUniqueSVP` and `PolyUniqueSVP` express
correctness for power-law uniqueness factors.

`SolvesDCPWithFailure` and `SolvesTwoPointWithFailure` attach a failure-parameter index to the
underlying correctness predicates; their definitions do not impose an additional
failure-probability bound.

## Main statements

* `HasDCPSolver`: Existence of a dihedral coset solver indexed by a failure parameter.
* `ThetaUniqueSVP`: Correctness for a uniqueness factor c n^e with c > 0.

## References

* [Regev, 2004][Regev2004]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

/-- The uniqueness exponent 1/2 + 2f associated with the DCP failure parameter in [Regev2004]. -/
noncomputable def svpExponent (f : ℝ) : ℝ := 1 / 2 + 2 * f

/-- The DCP correctness predicate indexed by a failure parameter `f`. This definition is
`SolvesDCP A` and does not impose a separate bound involving `f`. -/
def SolvesDCPWithFailure (_f : ℝ) (A : ∀ N : ℕ, DCPRegister N → ℤ) : Prop :=
  SolvesDCP A

/-- The two-point correctness predicate indexed by a failure parameter `f`. This definition is
`SolvesTwoPoint A` and does not impose a separate bound involving `f`. -/
def SolvesTwoPointWithFailure (_f : ℝ)
    (A : ∀ n M : ℕ, TwoPointRegister n M → (Fin n → ℤ)) : Prop :=
  SolvesTwoPoint A

/-- There exists a solver satisfying `SolvesDCPWithFailure f`. -/
def HasDCPSolver (f : ℝ) : Prop := ∃ A, SolvesDCPWithFailure f A

/-- There exists a solver satisfying `SolvesTwoPointWithFailure f`. -/
def HasTwoPointSolver (f : ℝ) : Prop := ∃ A, SolvesTwoPointWithFailure f A

/-- The solver `B` solves unique SVP with uniqueness factor c n^e for some positive real
constant c. -/
def ThetaUniqueSVP (e : ℝ)
    (B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ SolvesUniqueSVP (fun n => c * (n : ℝ) ^ e) B

/-- The solver `B` satisfies `ThetaUniqueSVP e B` for some positive real exponent e. -/
def PolyUniqueSVP (B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ)) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ThetaUniqueSVP e B

end Qatlib.Papers.QLattice03.MainResults
