/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OracleUseless11.MainResults.Theorem01CyclesInvolutions

@[expose] public section


set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.OracleUseless11.MainResults
open Qatlib.Papers.OracleUseless11.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

set_option autoImplicit false

attribute [local instance] Classical.propDecidable


/-- The explicit cycle answer model equals the pushforward of the uniform law on actual
full cycles. This connects its law to the source oracle rather than freely identifying models. -/
theorem cycleModel_law {N : ℕ}
    [Nonempty {π : Equiv.Perm (Fin N) // IsFullCycle π}]
    (hN : 2 ≤ N) (x : Fin N) :
    (cycleAnswerModel N hN).law x = classAnswerLaw (IsFullCycle (Y := Fin N)) x :=
  by simp [cycleAnswerModel]

/-- The explicit involution answer model equals the pushforward of the uniform law on
actual fixed-point-free involutions whenever that promise class is nonempty. -/
theorem involModel_law {N : ℕ}
    [Nonempty {π : Equiv.Perm (Fin N) // IsFixedPointFreeInvolution π}]
    (hN : 2 ≤ N) (x : Fin N) :
    (involutionAnswerModel N hN).law x =
      classAnswerLaw (IsFixedPointFreeInvolution (Y := Fin N)) x :=
  by simp [involutionAnswerModel]


/-- No deterministic adaptive classical decision rule distinguishes the actual nonempty
uniform cycle and involution classes under independent resampling at each query. -/
theorem class_no_solver (N : ℕ)
    [Nonempty {π : Equiv.Perm (Fin N) // IsFullCycle π}]
    [Nonempty {π : Equiv.Perm (Fin N) // IsFixedPointFreeInvolution π}]
    (hN : 2 ≤ N) :
    ¬ ∃ (k : ℕ) (A : AdaptiveClassicalAlg N) (D : (Fin k → Fin N) → Bool),
      1 / 2 < acceptProb ⟨classAnswerLaw (IsFullCycle (Y := Fin N))⟩ A k D ∧
        1 / 2 < 1 -
          acceptProb ⟨classAnswerLaw (IsFixedPointFreeInvolution (Y := Fin N))⟩ A k D := by
  rintro ⟨k, A, D, h1, h2⟩
  exact not_both_win
    (fun x => (cycleAnswerLaw_eq_uniform hN x).trans
      (involutionAnswerLaw_eq_uniform hN x).symm) A k D ⟨h1, h2⟩


end Qatlib.Papers.OracleUseless11.MainResults
