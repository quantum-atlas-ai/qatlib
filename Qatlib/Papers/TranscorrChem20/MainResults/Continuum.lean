/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ImaginaryFlow.Continuum
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.ImaginaryFlow.Continuum

namespace Qatlib.Papers.TranscorrChem20.MainResults.Continuum

theorem electronic_tc_action (N : ℕ) (g V : (Fin (3*N) → ℝ) → ℝ)
    (f : (Fin (3*N) → ℝ) → ℂ) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin (3*N) → ℝ) :
    Real.exp (-g x) • schrodingerAction V (expMultiply g f) x =
      schrodingerAction V f x - ∑ j, correction g f j x :=
  actual_continuum_tc_action g V f hg hf x

theorem electronic_tc_bch (N : ℕ) (g V : (Fin (3*N) → ℝ) → ℝ)
    (f : (Fin (3*N) → ℝ) → ℂ) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin (3*N) → ℝ) :
    Real.exp (-g x) • schrodingerAction V (expMultiply g f) x =
      schrodingerAction V f x + firstCommutator g V f x +
        (1/2 : ℝ) • secondCommutator g V f x := actual_continuum_bch g V f hg hf x

theorem electronic_higher_commutator_zero (N : ℕ) (g V : (Fin (3*N) → ℝ) → ℝ)
    (f : (Fin (3*N) → ℝ) → ℂ) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (k : ℕ) (x : Fin (3*N) → ℝ) : iteratedCommutator g V (k+3) f x = 0 :=
  higherCommutator_zero g V f hg hf k x

end Qatlib.Papers.TranscorrChem20.MainResults.Continuum
