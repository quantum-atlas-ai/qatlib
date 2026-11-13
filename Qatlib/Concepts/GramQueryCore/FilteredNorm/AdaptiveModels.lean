/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Adaptive oracle trees and branch semantics

This module defines finite adaptive programs with known gates, forward or adjoint queries, and
branching instruments. It supplies legality, query counts, pure and density output semantics,
and auxiliary input and oracle encodings for state-conversion query models related to
[LeeEtAl2011].

## Main definitions

* `SourceAdaptive`: syntax of finite adaptive oracle trees.
* `sourceAdaptiveBranches`: the unnormalized terminal branch states.
* `sourceAdaptivePure` and `sourceAdaptiveDensity`: coherent branch recording and the sum of
  branch outer products.
* `sourceFractionalOracle`: a diagonal Boolean phase oracle with a fractional phase parameter.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- Finite adaptive oracle-tree syntax with termination, known matrix operations, forward or
adjoint queries, and finite instruments with outcome-dependent continuations. -/
inductive SourceAdaptive (H : Type) where
  | finish : SourceAdaptive H
  | known : Matrix H H ℂ → SourceAdaptive H → SourceAdaptive H
  | query : Bool → SourceAdaptive H → SourceAdaptive H
  | instrument : (m : ℕ) → (Fin m → Matrix H H ℂ) →
      (Fin m → SourceAdaptive H) → SourceAdaptive H

/-- The recursive legality condition requiring known operations to be unitary, each instrument's
Kraus completeness sum to be identity, and all continuations to be legal. -/
def sourceAdaptiveLegal {H : Type} [Fintype H] [DecidableEq H] : SourceAdaptive H → Prop
  | .finish => True
  | .known U next => U ∈ Matrix.unitaryGroup H ℂ ∧ sourceAdaptiveLegal next
  | .query _ next => sourceAdaptiveLegal next
  | .instrument m K next => (∑ i : Fin m, (K i)ᴴ * K i)=1 ∧
      ∀ i, sourceAdaptiveLegal (next i)

/-- The maximum number of oracle queries along a branch of an adaptive tree, taking the maximum
over instrument outcomes. -/
def sourceAdaptiveCalls {H : Type} : SourceAdaptive H → ℕ
  | .finish => 0
  | .known _ next => sourceAdaptiveCalls next
  | .query _ next => 1+sourceAdaptiveCalls next
  | .instrument _ _ next => (List.ofFn (fun i => sourceAdaptiveCalls (next i))).foldl max 0

/-- The number of terminal leaves of an adaptive tree, adding leaf counts across instrument
outcomes. -/
def sourceAdaptiveLeaves {H : Type} : SourceAdaptive H → ℕ
  | .finish => 1
  | .known _ next => sourceAdaptiveLeaves next
  | .query _ next => sourceAdaptiveLeaves next
  | .instrument _ _ next => (List.ofFn (fun i => sourceAdaptiveLeaves (next i))).sum

/-- The list of unnormalized terminal branch states obtained by executing known operations,
forward or adjoint oracle queries, and each instrument outcome. -/
def sourceAdaptiveBranches {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) : SourceAdaptive H → QState H → List (QState H)
  | .finish, ψ => [ψ]
  | .known U next, ψ => sourceAdaptiveBranches O next (U *ᵥ ψ)
  | .query adj next, ψ => sourceAdaptiveBranches O next ((if adj then Oᴴ else O) *ᵥ ψ)
  | .instrument _ K next, ψ =>
      (List.ofFn (fun i => sourceAdaptiveBranches O (next i) (K i *ᵥ ψ))).flatten

/-- The state that stores each terminal branch vector under its finite branch index, with zero
entries for unused indices in a register of size at least one. -/
def sourceAdaptivePure {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (ψ : QState H) :
    QState (Fin (max 1 (sourceAdaptiveLeaves T)) × H) :=
  fun p => ((sourceAdaptiveBranches O T ψ).getD p.1.val 0) p.2

/-- The sum of the outer products of all unnormalized terminal branch states. -/
def sourceAdaptiveDensity {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (ψ : QState H) : Matrix H H ℂ :=
  Matrix.of (fun p t => ((sourceAdaptiveBranches O T ψ).map
    (fun φ => φ p * star (φ t))).sum)

/-- The zero-one matrix preserving the query and symbol coordinates while encoding a record and
old workspace index as `record*old + index` in the new workspace. -/
def sourceTreeFrame {H : Type} [DecidableEq H] (n q old records new : ℕ) :
    Matrix (SourceSpace n q H new) (Fin records × SourceSpace n q H old) ℂ :=
  Matrix.of (fun p t => if p.1=t.2.1 ∧ p.2.1=t.2.2.1 ∧
    p.2.2.val=t.1.val*old+t.2.2.2.val then 1 else 0)

/-- The input formed from `m` independent instances by identifying a query index in `Fin (m*n)`
with an instance index and a coordinate index. -/
def sourceIndependentInput {X : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (m : ℕ) :
    (Fin m → X) → Fin (m*n) → Fin (q+1) :=
  fun xs j => input (xs (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

/-- The Boolean encoding in `Fin 2`, sending false to zero and true to one. -/
def sourceBooleanSymbol (b : Bool) : Fin 2 := if b then 1 else 0

/-- The diagonal oracle applying phase `exp (i*π*lam)` at an active index whose Boolean input is
true and phase one otherwise, independently of the symbol and workspace coordinates. -/
def sourceFractionalOracle {X W : Type} [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (x : X) (lam : ℝ) :
    Matrix ((Fin (n+1) × Fin 2) × W) ((Fin (n+1) × Fin 2) × W) ℂ :=
  Matrix.diagonal (fun p => Complex.exp (Complex.I * Real.pi * lam *
    (if h : p.1.1.val<n then if input x ⟨p.1.1.val,h⟩ then 1 else 0 else 0)))

end Qatlib.Concepts.GramQueryCore.FilteredNorm
