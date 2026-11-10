/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphSpectralDefs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.GraphEnergy.ZeroEnergy
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
def degree (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℝ :=
  ∑ y, if G.Adj x y then 1 else 0
def volume (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := ∑ x, degree G x

def kernel (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℝ :=
  if degree G x = 0 then (if x = y then 1 else 0)
  else (if x = y then 1/2 else 0) + (if G.Adj x y then 1/(2*degree G x) else 0)
def stationary (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℝ :=
  if volume G = 0 then 1/(Fintype.card V : ℝ) else degree G x / volume G
def mean (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  ∑ x, stationary G x * f x
def variance (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  ∑ x, stationary G x * (f x - mean G f)^2
def energy (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  ∑ x, stationary G x * f x * (f x - ∑ y, kernel G x y * f y)
def mass (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  ∑ x ∈ S, stationary G x
def flow (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ Sᶜ, stationary G x * kernel G x y
def centeredIndicator (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x : V) : ℝ :=
  (if x ∈ S then 1 else 0) - mass G S

def weightedLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun x y => stationary G x * ((if x=y then 1 else 0) - kernel G x y)
end Qatlib.Concepts.GraphEnergy.ZeroEnergy
