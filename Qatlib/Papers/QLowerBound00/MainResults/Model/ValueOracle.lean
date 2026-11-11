/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Finite-alphabet value-query model

`InputD` represents words over a finite alphabet. The operation `addFin` supplies modular
addition, and `valueQuery` shifts the response-register argument on the selected query-index
sector. See [Ambainis2002] for the paper's setting.

## Main statements

* `InputD`: The type of length-`n` inputs with values in `Fin d`.
* `valueQuery`: The value-query action on amplitudes that shifts the response-register argument
  by `x i` modulo `d` on the query-index sector `i` and preserves other sectors.

## References

* [Ambainis, 2002][Ambainis2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.Model

/-- The type of length-`n` inputs with values in `Fin d`. -/
abbrev InputD (n d : ℕ) : Type := Fin n → Fin d

/-- Addition modulo the positive alphabet size `d`, written as an explicit operation on `Fin d`. -/
def addFin {d : ℕ} (hd : 0 < d) (a b : Fin d) : Fin d :=
  ⟨(a.val + b.val) % d, Nat.mod_lt _ hd⟩

/-- The value-query action on amplitudes that shifts the response-register argument by `x i`
modulo `d` on the query-index sector `i` and preserves other sectors. -/
def valueQuery {n d Z : ℕ} (hd : 0 < d) (i : Fin n)
    (φ : ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ) :
    ((Fin n × Fin d) × Fin Z) → InputD n d → ℂ :=
  fun iw x =>
    if iw.1.1 = i then φ ((iw.1.1, addFin hd iw.1.2 (x i)), iw.2) x else φ iw x

end Qatlib.Papers.QLowerBound00.MainResults.Model
