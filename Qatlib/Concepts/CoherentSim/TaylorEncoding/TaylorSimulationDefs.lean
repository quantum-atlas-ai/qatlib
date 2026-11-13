/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorLCUProgram
import Qatlib.Concepts.CoherentSim.ResetDiscard.EffectiveTimeDependent

/-!
# Grid-word coefficient and preparation definitions

This module defines coefficient masses and padded word labels for sampled time-dependent
Hamiltonian terms. `cubeCoeff`, `cubePhaseGate`, and `cubePrepare` supply coefficients and
preparation matrices for a grid-word LCU construction supporting time-dependent Taylor
simulation [BerryEtAl2015Taylor].

## Main statements

* `cubeCoeff`: Products of sampled coefficients with factorial weights and cancelling padding.
* `cubePrepare`: The preparation matrix built from coefficient magnitudes.
* `cubeLambda_nonneg`: Nonnegativity of the total sampled coefficient mass.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.BlockEncoding.EncodingCore

set_option autoImplicit false

namespace Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib
open Matrix
open scoped BigOperators

/-- The sum of absolute Hamiltonian coefficients at a specified time-grid point. -/
noncomputable def cubeNodeMass {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (j : Fin M) : ℝ :=
  ∑ m, |h (gridTime τ M j) m|

/-- The sum of the coefficient masses over all time-grid points. -/
noncomputable def cubeLambda {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) : ℝ :=
  ∑ j, cubeNodeMass h τ M j

/-- The total sampled coefficient mass divided by the grid size. -/
noncomputable def cubeScale {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) : ℝ :=
  cubeLambda h τ M / M

/-- The total sampled coefficient mass `cubeLambda` is nonnegative. -/
theorem cubeLambda_nonneg {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) :
    0 ≤ cubeLambda h τ M := by
  unfold cubeLambda
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun m _ => abs_nonneg _

/-- The type of words of length at most `K` in time-summand pairs, together with two Boolean
padding labels. -/
abbrev CubeLabel (J : Type) (M K : ℕ) :=
  (Σ l : Fin (K + 1), Fin l.val → (Fin M × J)) ⊕ Bool

/-- The label of the empty time-summand word. -/
def cubeEmptyLabel (J : Type) (M K : ℕ) : CubeLabel J M K :=
  Sum.inl ⟨⟨0, by norm_num⟩, fun a => a.elim0⟩

/-- The order-`k` exponential mass `( |τ| * cubeScale h τ M )^k / k!`. -/
noncomputable def cubeOrderMass {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (k : ℕ) : ℝ :=
  (|τ| * cubeScale h τ M) ^ k / k.factorial

/-- The sum of the grid-word exponential masses through order `K`. -/
noncomputable def cubeS0 {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (K : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (K + 1), cubeOrderMass h τ M l

/-- The grid-word coefficients formed from sampled Hamiltonian terms with Taylor phase, grid,
and factorial factors, together with two opposite padding coefficients. -/
noncomputable def cubeCoeff {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (K : ℕ) : CubeLabel J M K → ℂ :=
  fun x => match x with
    | Sum.inl w =>
        ((-Complex.I * (τ : ℂ)) ^ (w.1.val : ℕ) / ((w.1.val.factorial : ℕ) : ℂ)) *
          (∏ a, (h (gridTime τ M (w.2 a).1) (w.2 a).2 : ℂ) / (M : ℂ))
    | Sum.inr b =>
        if b then (2 - cubeS0 h τ M K) / 2
        else -(2 - cubeS0 h τ M K) / 2

/-- The nonnegative square root of half the norm of a grid-word coefficient. -/
noncomputable def cubeAmplitude {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) (x : CubeLabel J M K) : ℝ :=
  Real.sqrt (‖cubeCoeff h τ M K x‖ / 2)

/-- The diagonal matrix of phases of the grid-word coefficients. -/
noncomputable def cubePhaseGate {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) : Matrix (CubeLabel J M K) (CubeLabel J M K) ℂ := by
  classical
  exact Matrix.diagonal (fun x => coefficientPhase (cubeCoeff h τ M K x))

/-- The nonnegative preparation matrix for the grid-word amplitudes, based at the empty label. -/
noncomputable def cubePrepare {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) : Matrix (CubeLabel J M K) (CubeLabel J M K) ℂ := by
  classical
  exact nonnegativePrepare (fun x => cubeAmplitude h τ M K x) (cubeEmptyLabel J M K)

end Qatlib.Concepts.CoherentSim.TaylorEncoding
