/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs
import Qatlib.Papers.IsingPartit08.MainResults.ParityCollapse
import Qatlib.Papers.IsingPartit08.MainResults.Containment
import Qatlib.Papers.IsingPartit08.MainResults.GateExpansion
import Qatlib.Papers.IsingPartit08.MainResults.QWGT
import Qatlib.Papers.IsingPartit08.MainResults.Universality

/-!
# Numerical additive estimates for Ising sums

This module packages an objective and additive tolerance as `AdditiveProblem` and defines
`HasNumericalEstimate` as the existence of an estimator satisfying that tolerance. Given a
master correspondence and an amplitude estimate, it constructs such an estimator for the signed
Eulerian sum, expressing the numerical error-transfer consequence of Theorem 1 in [Geraci2008].

## Main statements

* `isingAdditiveProblem`: packages a fixed signed Eulerian sum as a one-instance estimation
  problem.
* `containment_problem`: constructs an estimator using an assumed positive normalizer.
* `containment_problem_normalizer`: specializes the construction to `normalizerOf`.

## References

* [Geraci, 2008][Geraci2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

/-- An additive estimation problem consisting of an instance type, a real objective, and a real
error tolerance for each instance. -/
structure AdditiveProblem where

  Inst : Type

  obj : Inst → ℝ

  acc : Inst → ℝ

/-- The existence of a real-valued estimator whose absolute error is at most the prescribed
tolerance on every instance. -/
def HasNumericalEstimate (P : AdditiveProblem) : Prop :=
  ∃ est : P.Inst → ℝ, ∀ x, |est x - P.obj x| ≤ P.acc x

/-- The one-instance additive estimation problem with objective `signedEulerianSum B CH lam` and
tolerance `acc`. -/
noncomputable def isingAdditiveProblem {R N : ℕ}
    (B : Matrix (Fin N) (Fin N) (ZMod 2)) (CH : Matrix (Fin R) (Fin N) (ZMod 2))
    (lam acc : ℝ) : AdditiveProblem where
  Inst := PUnit
  obj := fun _ => signedEulerianSum B CH lam
  acc := fun _ => acc

/-- Given a master correspondence with positive normalizer and an amplitude estimate of error
`ptest`, the associated signed Eulerian sum possesses a numerical estimate of error
`normalizer * ptest`. See [Geraci2008]. -/
theorem containment_problem {R N : ℕ} {B : Matrix (Fin N) (Fin N) (ZMod 2)}
    {CH : Matrix (Fin R) (Fin N) (ZMod 2)} {lam q normalizer ptest m : ℝ}
    (hN : 0 < normalizer)
    (hmaster : MasterCorrespondence q normalizer (signedEulerianSum B CH lam))
    (hm : HadamardTestEstimate q ptest m) :
    HasNumericalEstimate (isingAdditiveProblem B CH lam (normalizer * ptest)) := by
  refine ⟨fun _ => normalizer * m, ?_⟩
  intro x
  simpa [isingAdditiveProblem] using containment_additive hN hmaster hm

/-- Given the correspondence with `normalizerOf lam edges` and an amplitude estimate of error
`ptest`, the signed Eulerian sum possesses a numerical estimate with the scaled tolerance.
See [Geraci2008]. -/
theorem containment_problem_normalizer {R N : ℕ}
    {B : Matrix (Fin N) (Fin N) (ZMod 2)} {CH : Matrix (Fin R) (Fin N) (ZMod 2)}
    {lam q ptest m : ℝ} (edges : ℕ)
    (hmaster : MasterCorrespondence q (normalizerOf lam edges)
      (signedEulerianSum B CH lam))
    (hm : HadamardTestEstimate q ptest m) :
    HasNumericalEstimate
      (isingAdditiveProblem B CH lam (normalizerOf lam edges * ptest)) := by
  refine ⟨fun _ => normalizerOf lam edges * m, ?_⟩
  intro x
  simpa [isingAdditiveProblem] using
    containment_additive_normalizer lam edges hmaster hm

end Qatlib.Papers.IsingPartit08.MainResults
