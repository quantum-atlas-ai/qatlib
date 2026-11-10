/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorLCUProgram
import Qatlib.Concepts.CoherentSim.ResetDiscard.EffectiveTimeDependent
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.BlockEncoding.EncodingCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib
open Matrix
open scoped BigOperators

noncomputable def cubeNodeMass {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (j : Fin M) : ℝ :=
  ∑ m, |h (gridTime τ M j) m|

noncomputable def cubeLambda {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) : ℝ :=
  ∑ j, cubeNodeMass h τ M j

noncomputable def cubeScale {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) : ℝ :=
  cubeLambda h τ M / M

theorem cubeLambda_nonneg {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) :
    0 ≤ cubeLambda h τ M := by
  unfold cubeLambda
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun m _ => abs_nonneg _

abbrev CubeLabel (J : Type) (M K : ℕ) :=
  (Σ l : Fin (K + 1), Fin l.val → (Fin M × J)) ⊕ Bool

def cubeEmptyLabel (J : Type) (M K : ℕ) : CubeLabel J M K :=
  Sum.inl ⟨⟨0, by norm_num⟩, fun a => a.elim0⟩

noncomputable def cubeOrderMass {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (k : ℕ) : ℝ :=
  (|τ| * cubeScale h τ M) ^ k / k.factorial

noncomputable def cubeS0 {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (K : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (K + 1), cubeOrderMass h τ M l

noncomputable def cubeCoeff {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (K : ℕ) : CubeLabel J M K → ℂ :=
  fun x => match x with
    | Sum.inl w =>
        ((-Complex.I * (τ : ℂ)) ^ (w.1.val : ℕ) / ((w.1.val.factorial : ℕ) : ℂ)) *
          (∏ a, (h (gridTime τ M (w.2 a).1) (w.2 a).2 : ℂ) / (M : ℂ))
    | Sum.inr b =>
        if b then (2 - cubeS0 h τ M K) / 2
        else -(2 - cubeS0 h τ M K) / 2

noncomputable def cubeAmplitude {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) (x : CubeLabel J M K) : ℝ :=
  Real.sqrt (‖cubeCoeff h τ M K x‖ / 2)

noncomputable def cubePhaseGate {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) : Matrix (CubeLabel J M K) (CubeLabel J M K) ℂ := by
  classical
  exact Matrix.diagonal (fun x => coefficientPhase (cubeCoeff h τ M K x))

noncomputable def cubePrepare {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) : Matrix (CubeLabel J M K) (CubeLabel J M K) ℂ := by
  classical
  exact nonnegativePrepare (fun x => cubeAmplitude h τ M K x) (cubeEmptyLabel J M K)

end Qatlib.Concepts.CoherentSim.TaylorEncoding
