/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ImaginaryFlow.Continuum

/-!
# Continuum electronic transcorrelation

This module specializes continuum transcorrelation identities to electronic configuration space
with `3 * N` real coordinates. For twice continuously differentiable `g` and `f`, it gives the
pointwise action after exponential conjugation and the exact commutator expansion through second
order. See [McArdleTew2020].

## Main statements

* `electronic_tc_action`: the conjugated Schrödinger action equals the original action minus the
  coordinate corrections.
* `electronic_tc_bch`: the conjugated action is the sum of the original action, the first
  commutator, and half the second commutator.
* `electronic_higher_commutator_zero`: iterated commutators of order at least three vanish.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.ImaginaryFlow.Continuum

namespace Qatlib.Papers.TranscorrChem20.MainResults.Continuum

/-- For twice continuously differentiable `g` and `f` on electronic configuration space,
exponential conjugation of the Schrödinger action equals the original action minus the sum
of coordinate corrections. See [McArdleTew2020]. -/
theorem electronic_tc_action (N : ℕ) (g V : (Fin (3*N) → ℝ) → ℝ)
    (f : (Fin (3*N) → ℝ) → ℂ) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin (3*N) → ℝ) :
    Real.exp (-g x) • schrodingerAction V (expMultiply g f) x =
      schrodingerAction V f x - ∑ j, correction g f j x :=
  actual_continuum_tc_action g V f hg hf x

/-- For twice continuously differentiable `g` and `f`, the exponentially conjugated electronic
Schrödinger action equals the original action plus the first commutator and one half of the
second commutator. See [McArdleTew2020]. -/
theorem electronic_tc_bch (N : ℕ) (g V : (Fin (3*N) → ℝ) → ℝ)
    (f : (Fin (3*N) → ℝ) → ℂ) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin (3*N) → ℝ) :
    Real.exp (-g x) • schrodingerAction V (expMultiply g f) x =
      schrodingerAction V f x + firstCommutator g V f x +
        (1/2 : ℝ) • secondCommutator g V f x := actual_continuum_bch g V f hg hf x

/-- For twice continuously differentiable `g` and `f` on electronic configuration space, every
iterated commutator of order `k + 3` vanishes pointwise. See [McArdleTew2020]. -/
theorem electronic_higher_commutator_zero (N : ℕ) (g V : (Fin (3*N) → ℝ) → ℝ)
    (f : (Fin (3*N) → ℝ) → ℂ) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (k : ℕ) (x : Fin (3*N) → ℝ) : iteratedCommutator g V (k+3) f x = 0 :=
  higherCommutator_zero g V f hg hf k x

end Qatlib.Papers.TranscorrChem20.MainResults.Continuum
