/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.ResourceProgram
import Qatlib.Papers.SingleQuery97.MainResults.FullDatabase

/-!
# Resource bounds for randomized one-query recovery

This module realizes randomized database recovery with the sparse compiled program and
identifies its measured output with `RandomRecovery.experiment`. It bounds the realized time
expression by `2 + 2*m*n + T` and transfers prime-alphabet and general-alphabet error estimates
to this implementation of the construction in [TerhalSmolin1998].

## Main statements

* `realized_time`: The compiled random-code program has gate count plus query cost at most `2 +
  2*m*n + T`, a realized resource bound for the setting of [TerhalSmolin1998].
* `general_error_bound`: For an injective candidate family, the compiled experiment has error at
  most `(k - 1) / 2^m`, using the general-alphabet collision estimate for [TerhalSmolin1998].

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.RandomResource

open Qatlib.Foundations.QueryWordCore.Circuit
open LinearCodeProgram EncoderCircuit ResourceProgram RandomHashLaw RandomRecovery

variable {A m n k : ℕ} [NeZero A] [NeZero k]

/-- The compiled random-code program has gate count plus query cost at most `2 + 2*m*n + T`, a
realized resource bound for the setting of [TerhalSmolin1998]. -/
theorem realized_time (g : Fin m → Fin n → ZMod A) (T : ℕ) :
    GateCount (program g) + T*QueryCount (program g) ≤ 2+2*m*n+T := by
  have hs : (support g).card ≤ m*n := by
    have h := Finset.card_le_card (Finset.filter_subset (fun p : Fin m × Fin n => g p.1 p.2 ≠ 0)
      Finset.univ)
    simpa only [support, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using h
  rw [(program_resources _).1, (program_resources _).2, mul_one]
  rw [Nat.mul_assoc]
  omega

/-- The decoded output law obtained by sampling a uniform generator matrix and measuring the
sparse compiled program. -/
noncomputable def experiment (candidates : Fin k → Fin n → ZMod A) (t : Fin k) : PMF (Fin k) :=
  (matrixLaw A m n).bind fun g =>
    (measured g (candidates t)).map (fun p => decoder candidates g p.1.1)

/-- The compiled-program experiment has the same output law as `RandomRecovery.experiment`. -/
theorem experiment_eq (candidates : Fin k → Fin n → ZMod A) (t : Fin k) :
    experiment (m:=m) candidates t = RandomRecovery.experiment (m:=m) candidates t := by
  simp only [experiment, RandomRecovery.experiment, measured_eq]

/-- For an injective candidate family, the compiled experiment has error at most `(k - 1) /
2^m`, using the general-alphabet collision estimate for [TerhalSmolin1998]. -/
theorem general_error_bound (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) (t : Fin k) :
    (experiment (m:=m) candidates t).toOuterMeasure {out | out≠t} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/2^m) := by
  rw [experiment_eq]
  exact general_recovery_error_bound candidates hinj t

/-- Over a prime alphabet, the compiled experiment has error at most `(k - 1) / A^m` for an
injective candidate family, using the prime-alphabet collision law for [TerhalSmolin1998]. -/
theorem prime_error_bound [Fact (Nat.Prime A)] (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) (t : Fin k) :
    (experiment (m:=m) candidates t).toOuterMeasure {out | out≠t} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/A^m) := by
  rw [experiment_eq]
  exact recovery_error_bound candidates hinj t

end Qatlib.Papers.SingleQuery97.MainResults.RandomResource
