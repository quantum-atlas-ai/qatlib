/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrder
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Source model: notation of *A Theory of Trotter Error*

Childs--Su--Tran--Wiebe--Zhu, fixed arXiv:1912.08854v3.
PDF `prove/assets/1912.08854v3.pdf`,
plain text `prove/assets/1912.08854v3.txt`.

This module fixes the paper's vocabulary that is shared by the main body and
the appendices:

* `Op D` — the finite-dimensional operator space of Section 2.1 (complex
  square matrices, spectral norm);
* `OrderCondition` — Definition of Eq. (171), `F(τ) = O(τ^p)` near zero;
  this is the frozen `trotterOrder` predicate, so paper statements reuse the
  same radius/constant convention as the `Concepts.TrotterFormula` layer;
* `NestedCommutator` — the right-nested commutator
  `[H_{γ_{p+1}}, ··· [H_{γ_2}, H_{γ_1}]]` used in Theorem 11, Eq. (54);
* `BigOAtTop` — the paper's asymptotic `O(·)` in the system size `n → ∞`
  (Section 2.1), spelled as Mathlib's `IsBigO atTop`.

Boundary: this is a paper-layer model only.  It does not redefine or weaken
any frozen `Concepts.TrotterFormula` contract; frozen theorems are imported and
cited, not re-proved.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Matrix
open Filter Asymptotics
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.TrotterError19.MainResults

/-- The paper's operator space: complex square matrices with the spectral
norm (Section 2.1, "operators can be represented by complex square matrices"). -/
abbrev Op (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- The paper's order condition `F(τ) = O(τ^p)` near `τ = 0` (Eq. (171)).
This is definitionally the frozen `trotterOrder`, i.e. there are a positive
constant and radius with `‖F τ‖ ≤ c |τ|^p` on `|τ| ≤ t₀`. -/
abbrev OrderCondition {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (p : ℕ) : Prop :=
  Qatlib.Concepts.TrotterFormula.GeneralOrder.trotterOrder F p

/-- Right-nested commutators, innermost element first.  `NestedCommutator [A, B, C]`
is `[C, [B, A]]`, matching the paper's
`[H_{γ_{p+1}}, ··· [H_{γ_2}, H_{γ_1}]]` with the list read from the innermost
summand outwards (Theorem 11, Eq. (54)). -/
noncomputable def NestedCommutator {I : Type} [Fintype I] :
    List (Matrix I I ℂ) → Matrix I I ℂ
  | [] => 0
  | A :: rest => rest.foldl (fun acc X => X * acc - acc * X) A

/-- The `NestedCommutator_nil` result for the TrotterError19 paper model. -/
@[simp] theorem NestedCommutator_nil {I : Type} [Fintype I] :
    NestedCommutator ([] : List (Matrix I I ℂ)) = 0 := rfl

/-- The `NestedCommutator_singleton` result for the TrotterError19 paper model. -/
@[simp] theorem NestedCommutator_singleton {I : Type} [Fintype I]
    (A : Matrix I I ℂ) : NestedCommutator [A] = A := rfl

/-- The pair case `[B, A] = B·A − A·B`. -/
theorem NestedCommutator_pair {I : Type} [Fintype I]
    (A B : Matrix I I ℂ) : NestedCommutator [A, B] = B * A - A * B := rfl

/-- The paper's asymptotic notation `a(n) = O(b(n))` in the system size
(Section 2.1), i.e. Mathlib's `IsBigO atTop`. -/
def BigOAtTop (a b : ℕ → ℝ) : Prop := a =O[atTop] b

/-- The telescoping error of `r` repetitions of a one-step word (the standard
step from local to global Trotter error, used throughout Section 4 and the
appendices).  Kept as a named bound so the paper statements can share it. -/
theorem repeated_error_of_single {I : Type} [Fintype I] [DecidableEq I]
    (U V : Matrix I I ℂ) (r : ℕ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    ‖U ^ r - V ^ r‖ ≤ (r : ℝ) * ‖U - V‖ := by
  have := Qatlib.Concepts.TrotterFormula.LieStrang.pf_unitary_power_error U V hU hV r
  exact this

end Qatlib.Papers.TrotterError19.MainResults
