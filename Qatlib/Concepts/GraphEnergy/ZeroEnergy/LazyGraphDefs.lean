/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphSpectralDefs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Lazy graph kernels and stationary energy

This module defines a lazy random-walk kernel with absorbing isolated vertices and a
degree-weighted stationary law, using uniform weights when graph volume is zero. It supplies
stationary means, variances, energy, cut mass and flow, and `weightedLaplacian` for subsequent
graph arguments. These finite Markov-chain objects provide background for [Szegedy2004].

## Main statements

* `kernel` and `stationary`: the lazy transition kernel and its stationary weights.
* `energy` and `weightedLaplacian`: the associated quadratic energy and matrix.
* `mass`, `flow`, and `centeredIndicator`: cut quantities.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.GraphEnergy.ZeroEnergy
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
/-- The degree of a vertex, expressed as a real sum of adjacency indicators. -/
def degree (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℝ :=
  ∑ y, if G.Adj x y then 1 else 0
/-- The sum of all real vertex degrees. -/
def volume (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := ∑ x, degree G x

/-- The lazy random-walk kernel, with holding probability one half at vertices of positive
degree and absorbing isolated vertices. -/
def kernel (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℝ :=
  if degree G x = 0 then (if x = y then 1 else 0)
  else (if x = y then 1/2 else 0) + (if G.Adj x y then 1/(2*degree G x) else 0)
/-- The degree divided by graph volume, with uniform weights when the volume is zero. -/
def stationary (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℝ :=
  if volume G = 0 then 1/(Fintype.card V : ℝ) else degree G x / volume G
/-- The mean of a real vertex function weighted by `stationary`. -/
def mean (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  ∑ x, stationary G x * f x
/-- The stationary weighted sum of squared deviations from the stationary mean. -/
def variance (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  ∑ x, stationary G x * (f x - mean G f)^2
/-- The stationary weighted pairing of a function with its difference from its one-step kernel
average. -/
def energy (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  ∑ x, stationary G x * f x * (f x - ∑ y, kernel G x y * f y)
/-- The total stationary weight of a finite vertex set. -/
def mass (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  ∑ x ∈ S, stationary G x
/-- The stationary transition weight from a finite vertex set to its complement. -/
def flow (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ Sᶜ, stationary G x * kernel G x y
/-- The membership indicator of a finite vertex set minus its stationary mass. -/
def centeredIndicator (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x : V) : ℝ :=
  (if x ∈ S then 1 else 0) - mass G S

/-- The matrix with entries `stationary G x * (δ(x, y) - kernel G x y)`. -/
def weightedLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun x y => stationary G x * ((if x=y then 1 else 0) - kernel G x y)
end Qatlib.Concepts.GraphEnergy.ZeroEnergy
