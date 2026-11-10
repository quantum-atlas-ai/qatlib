/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

inductive SourceAdaptive (H : Type) where
  | finish : SourceAdaptive H
  | known : Matrix H H ℂ → SourceAdaptive H → SourceAdaptive H
  | query : Bool → SourceAdaptive H → SourceAdaptive H
  | instrument : (m : ℕ) → (Fin m → Matrix H H ℂ) →
      (Fin m → SourceAdaptive H) → SourceAdaptive H

def sourceAdaptiveLegal {H : Type} [Fintype H] [DecidableEq H] : SourceAdaptive H → Prop
  | .finish => True
  | .known U next => U ∈ Matrix.unitaryGroup H ℂ ∧ sourceAdaptiveLegal next
  | .query _ next => sourceAdaptiveLegal next
  | .instrument m K next => (∑ i : Fin m, (K i)ᴴ * K i)=1 ∧
      ∀ i, sourceAdaptiveLegal (next i)

def sourceAdaptiveCalls {H : Type} : SourceAdaptive H → ℕ
  | .finish => 0
  | .known _ next => sourceAdaptiveCalls next
  | .query _ next => 1+sourceAdaptiveCalls next
  | .instrument _ _ next => (List.ofFn (fun i => sourceAdaptiveCalls (next i))).foldl max 0

def sourceAdaptiveLeaves {H : Type} : SourceAdaptive H → ℕ
  | .finish => 1
  | .known _ next => sourceAdaptiveLeaves next
  | .query _ next => sourceAdaptiveLeaves next
  | .instrument _ _ next => (List.ofFn (fun i => sourceAdaptiveLeaves (next i))).sum

def sourceAdaptiveBranches {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) : SourceAdaptive H → QState H → List (QState H)
  | .finish, ψ => [ψ]
  | .known U next, ψ => sourceAdaptiveBranches O next (U *ᵥ ψ)
  | .query adj next, ψ => sourceAdaptiveBranches O next ((if adj then Oᴴ else O) *ᵥ ψ)
  | .instrument _ K next, ψ =>
      (List.ofFn (fun i => sourceAdaptiveBranches O (next i) (K i *ᵥ ψ))).flatten

def sourceAdaptivePure {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (ψ : QState H) :
    QState (Fin (max 1 (sourceAdaptiveLeaves T)) × H) :=
  fun p => ((sourceAdaptiveBranches O T ψ).getD p.1.val 0) p.2

def sourceAdaptiveDensity {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (ψ : QState H) : Matrix H H ℂ :=
  Matrix.of (fun p t => ((sourceAdaptiveBranches O T ψ).map
    (fun φ => φ p * star (φ t))).sum)

def sourceTreeFrame {H : Type} [DecidableEq H] (n q old records new : ℕ) :
    Matrix (SourceSpace n q H new) (Fin records × SourceSpace n q H old) ℂ :=
  Matrix.of (fun p t => if p.1=t.2.1 ∧ p.2.1=t.2.2.1 ∧
    p.2.2.val=t.1.val*old+t.2.2.2.val then 1 else 0)

def sourceIndependentInput {X : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (m : ℕ) :
    (Fin m → X) → Fin (m*n) → Fin (q+1) :=
  fun xs j => input (xs (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

def sourceBooleanSymbol (b : Bool) : Fin 2 := if b then 1 else 0

def sourceFractionalOracle {X W : Type} [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (x : X) (lam : ℝ) :
    Matrix ((Fin (n+1) × Fin 2) × W) ((Fin (n+1) × Fin 2) × W) ℂ :=
  Matrix.diagonal (fun p => Complex.exp (Complex.I * Real.pi * lam *
    (if h : p.1.1.val<n then if input x ⟨p.1.1.val,h⟩ then 1 else 0 else 0)))

end Qatlib.Concepts.GramQueryCore.FilteredNorm
