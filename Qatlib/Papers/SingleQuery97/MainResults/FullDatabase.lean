/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.RandomRecovery

/-!
# Full database recovery and capped randomized decoding

This module uses `identityQueries` to recover every database coordinate by a single quantum
query and defines an exact fallback decoder on an injective candidate family. The distribution
`capped` chooses between randomized recovery and this fallback, with the error bound
`capped_error` supporting the database retrieval constructions of [TerhalSmolin1998].

## Main statements

* `full_recovery`: Running the linear-code word for `identityQueries` places the complete
  database in the first register, resets the workspace, and leaves the answer register in its
  character state.
* `capped_error`: For an injective candidate family, the capped decoder has error probability at
  most `1 / 2^l`, as in the single-query recovery setting of [TerhalSmolin1998].

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.FullDatabase

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open LinearCodeProgram RandomRecovery

variable {A n k : ℕ} [NeZero A] [NeZero k]

/-- The coordinate query family with a `1` on the diagonal and `0` elsewhere. -/
def identityQueries (A n : ℕ) : Fin n → Fin n → ZMod A :=
  fun i j => if j=i then 1 else 0

omit [NeZero A] in

/-- The responses to `identityQueries` reproduce the database vector exactly. -/
theorem response_identity (y : Fin n → ZMod A) : response (identityQueries A n) y = y := by
  funext i
  simp [response, answer, identityQueries, ite_mul]

/-- Running the linear-code word for `identityQueries` places the complete database in the first
register, resets the workspace, and leaves the answer register in its character state. -/
theorem full_recovery (y : Fin n → ZMod A) :
    Run (oracle y) (word (identityQueries A n))
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1:ZMod A))) =
      TensorState (TensorState (Ket y) (Ket 0))
        (Qatlib.Concepts.QuditTeleport.TeleportCore.charState (1:ZMod A)) := by
  rw [run_word, response_identity]

/-- The candidate-label output law obtained by applying the inverse candidate map to the
full-coordinate recovery measurement. -/
noncomputable def fallback (candidates : Fin k → Fin n → ZMod A) (t : Fin k) : PMF (Fin k) :=
  (outputLaw (identityQueries A n) (candidates t)).map
    (fun p => Function.invFun candidates p.1.1)

/-- For an injective candidate family, the full-coordinate fallback decoder returns the true
label with probability one. -/
theorem fallback_exact (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) (t : Fin k) : fallback candidates t = PMF.pure t := by
  rw [fallback, outputLaw_decoded, response_identity, Function.leftInverse_invFun hinj]

/-- The output law that uses randomized recovery when `Nat.clog 2 k + l < n` and otherwise uses
exact full-coordinate recovery. -/
noncomputable def capped (candidates : Fin k → Fin n → ZMod A) (l : ℕ) (t : Fin k) : PMF (Fin k) :=
  if Nat.clog 2 k+l < n then
    experiment (m:=Nat.clog 2 k+l) candidates t else fallback candidates t

/-- For an injective candidate family, the capped decoder has error probability at most `1 /
2^l`, as in the single-query recovery setting of [TerhalSmolin1998]. -/
theorem capped_error (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) (l : ℕ) (t : Fin k) :
    (capped candidates l t).toOuterMeasure {out | out≠t} ≤ (1:ENNReal)/2^l := by
  classical
  unfold capped
  split_ifs
  · exact (general_recovery_error_bound candidates hinj t).trans (integer_redundancy_bound k l)
  · rw [fallback_exact candidates hinj t]
    simp only [PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq, ne_eq, not_true_eq_false, if_false]
    exact zero_le

end Qatlib.Papers.SingleQuery97.MainResults.FullDatabase
