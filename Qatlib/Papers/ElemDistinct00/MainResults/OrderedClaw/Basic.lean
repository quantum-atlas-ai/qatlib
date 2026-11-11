/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Qatlib.Papers.ElemDistinct00.MainResults.Claw.OrReduction
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Ordered claw guarantees and singleton lower bounds

Claw-finding guarantees restrict from arbitrary inputs to inputs with a monotone first function,
and then to inputs with both functions monotone. The four guarantee-transfer lemmas express
these restrictions without changing the algorithm.

Every function on `Fin 1` is monotone, so the existing singleton claw lower bounds also apply to
the ordered problem. The results `orderedclaw_qe_lower_at_one` and `orderedclaw_q2_lower_at_one`
give explicit special cases relevant to Theorem 4 of [BuhrmanEtAl2005].

## Main statements

* `orderedClawBoundedError_of_clawBoundedError` and `orderedClawExact_of_clawExact`:
  unrestricted guarantees imply ordered guarantees.
* `bothOrderedClawBoundedError_of_orderedClawBoundedError` and
  `bothOrderedClawExact_of_orderedClawExact`: one ordered input suffices for the promise that
  both are ordered.
* `orderedclaw_qe_lower_at_one`: exact ordered claw finding with first domain `Fin 1` requires
  at least `M` queries for `M > 0`.
* `orderedclaw_q2_lower_at_one`: the corresponding bounded-error query count is at least `sqrt M
  / 8` when `6 ≤ M`.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005], *Quantum Algorithms for Element Distinctness*,
  arXiv:quant-ph/0007016 (2000 preprint).
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw

open Qatlib.Papers.ElemDistinct00.MainResults.Defs
open Qatlib.Papers.ElemDistinct00.MainResults.Claw
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

section Guarantees

variable {X Y Z W : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype W] [DecidableEq W] [Preorder X] [Preorder Y] [LinearOrder Z]

/-- A bounded-error claw-finding guarantee for arbitrary inputs also holds under the promise
that the first function is monotone. This transfers guarantees to the ordered setting of
[BuhrmanEtAl2005]. -/
theorem orderedClawBoundedError_of_clawBoundedError (A : ClawAlgorithm X Y Z W)
    (h : ClawBoundedError A) : OrderedClawBoundedError A :=
  fun f g _ hclaw => h f g hclaw

/-- An exact claw-finding guarantee for arbitrary inputs also holds under the promise that the
first function is monotone. This transfers guarantees to the ordered setting of
[BuhrmanEtAl2005]. -/
theorem orderedClawExact_of_clawExact (A : ClawAlgorithm X Y Z W)
    (h : ClawExact A) : OrderedClawExact A :=
  ⟨fun f g _ hclaw => h.1 f g hclaw, fun f g _ hnone => h.2 f g hnone⟩

/-- A bounded-error guarantee assuming the first function is monotone also holds when both
functions are required to be monotone. -/
theorem bothOrderedClawBoundedError_of_orderedClawBoundedError
    (A : ClawAlgorithm X Y Z W) (h : OrderedClawBoundedError A) :
    BothOrderedClawBoundedError A :=
  fun f g hf _ hclaw => h f g hf hclaw

/-- An exact guarantee assuming the first function is monotone also holds when both functions
are required to be monotone. -/
theorem bothOrderedClawExact_of_orderedClawExact (A : ClawAlgorithm X Y Z W)
    (h : OrderedClawExact A) : BothOrderedClawExact A :=
  ⟨fun f g hf _ hclaw => h.1 f g hf hclaw,
    fun f g hf _ hnone => h.2 f g hf hnone⟩

end Guarantees

/-- Every integer-valued function on `Fin 1` is monotone, since any two inputs are equal. -/
theorem monotone_fin_one (f : Fin 1 → ℤ) : Monotone f :=
  fun x y _ => le_of_eq (congrArg f (Subsingleton.elim x y))

/-- For positive `M`, an exact ordered claw algorithm with first domain `Fin 1` makes at least
`M` queries. This is a singleton-domain lower bound for the ordered problem in
[BuhrmanEtAl2005]. -/
theorem orderedclaw_qe_lower_at_one {M : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : ClawAlgorithm (Fin 1) (Fin M) ℤ W) (hE : OrderedClawExact A) (hM : 0 < M) :
    (M : ℝ) ≤ (QueryCount A.circuit : ℝ) :=
  claw_qe_lower_at_one A
    ⟨fun f g hh => hE.1 f g (monotone_fin_one f) hh,
      fun f g hh => hE.2 f g (monotone_fin_one f) hh⟩ hM

/-- For `6 ≤ M`, a bounded-error ordered claw algorithm with first domain `Fin 1` makes at least
`sqrt M / 8` queries. This is a singleton-domain lower bound for the ordered problem in
[BuhrmanEtAl2005]. -/
theorem orderedclaw_q2_lower_at_one {M : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : ClawAlgorithm (Fin 1) (Fin M) ℤ W) (hB : OrderedClawBoundedError A)
    (hM6 : 6 ≤ M) :
    Real.sqrt (M : ℝ) / 8 ≤ (QueryCount A.circuit : ℝ) :=
  claw_q2_lower_at_one A (fun f g hh => hB f g (monotone_fin_one f) hh) hM6

end Qatlib.Papers.ElemDistinct00.MainResults.OrderedClaw
