/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.ResourceProgram
import Qatlib.Papers.SingleQuery97.MainResults.FullDatabase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.RandomResource

open Qatlib.Foundations.QueryWordCore.Circuit
open LinearCodeProgram EncoderCircuit ResourceProgram RandomHashLaw RandomRecovery

variable {A m n k : ℕ} [NeZero A] [NeZero k]

theorem realized_time (g : Fin m → Fin n → ZMod A) (T : ℕ) :
    GateCount (program g) + T*QueryCount (program g) ≤ 2+2*m*n+T := by
  have hs : (support g).card ≤ m*n := by
    have h := Finset.card_le_card (Finset.filter_subset (fun p : Fin m × Fin n => g p.1 p.2 ≠ 0)
      Finset.univ)
    simpa only [support, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using h
  rw [(program_resources _).1, (program_resources _).2, mul_one]
  rw [Nat.mul_assoc]
  omega

noncomputable def experiment (candidates : Fin k → Fin n → ZMod A) (t : Fin k) : PMF (Fin k) :=
  (matrixLaw A m n).bind fun g =>
    (measured g (candidates t)).map (fun p => decoder candidates g p.1.1)

theorem experiment_eq (candidates : Fin k → Fin n → ZMod A) (t : Fin k) :
    experiment (m:=m) candidates t = RandomRecovery.experiment (m:=m) candidates t := by
  simp only [experiment, RandomRecovery.experiment, measured_eq]

theorem general_error_bound (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) (t : Fin k) :
    (experiment (m:=m) candidates t).toOuterMeasure {out | out≠t} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/2^m) := by
  rw [experiment_eq]
  exact general_recovery_error_bound candidates hinj t

theorem prime_error_bound [Fact (Nat.Prime A)] (candidates : Fin k → Fin n → ZMod A)
    (hinj : Function.Injective candidates) (t : Fin k) :
    (experiment (m:=m) candidates t).toOuterMeasure {out | out≠t} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/A^m) := by
  rw [experiment_eq]
  exact recovery_error_bound candidates hinj t

end Qatlib.Papers.SingleQuery97.MainResults.RandomResource
