/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-layer algorithm models for ApproxSpan15

Ito--Jeffery, *Approximate Span Programs*, arXiv:1507.00432v1.

The source's algorithmic statements (Theorems 2.7–2.9, 3.8–3.12, 4.2–4.6,
B.1–B.3) are quantum algorithms with a stated query (and sometimes space) cost.
This layer is a paper-level *interface*: an algorithm is recorded by its output
(either a decision, a real estimate, or nothing) and by its per-input query and
space counts.  The circuit realising the estimate is built by phase estimation
on `U(P,x)` in the source; it is not modelled here, so the cost functions are
explicit witnesses supplied by the source construction.

`Estimates` is the source's "estimates `f` to accuracy `ε`", and `EstimatesRel`
its relative-accuracy version `|f̃ − f| ≤ ε f`.
-/


set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ApproxSpan15.MainResults

/-- Paper-level model of an algorithm that outputs a real estimate of a function
on `Ix`.  `queries x` is the number of oracle queries made on input `x`. -/
structure RealEstimator (Ix : Type*) where
  /-- The algorithm's real-valued estimate on input `x`. -/
  est : Ix → ℝ
  /-- The number of oracle queries made on input `x`. -/
  queries : Ix → ℕ

namespace RealEstimator

/-- The source's absolute-accuracy contract: the estimate is within `ε` of the
target on every input. -/
def Estimates {Ix : Type*} (alg : RealEstimator Ix) (f : Ix → ℝ) (eps : ℝ) : Prop :=
  ∀ x, |alg.est x - f x| ≤ eps

/-- The source's relative-accuracy contract (Theorem 3.9, Theorem 3.12,
Theorem 4.3): `|f̃(x) − f(x)| ≤ ε·f(x)`. -/
def EstimatesRel {Ix : Type*} (alg : RealEstimator Ix) (f : Ix → ℝ) (eps : ℝ) : Prop :=
  ∀ x, |alg.est x - f x| ≤ eps * f x

end RealEstimator

/-- Paper-level model of an algorithm with separate query and space costs, as
used for the time/space statements of Theorems 4.2, 4.3 and B.1–B.3. -/
structure SpaceBoundedAlgorithm (Ix : Type*) where
  /-- The algorithm's real-valued estimate on input `x` (junk when the task is
  not an estimation). -/
  est : Ix → ℝ
  /-- The number of oracle queries made on input `x`. -/
  queries : Ix → ℕ
  /-- The number of workspace qubits used on input `x`. -/
  space : Ix → ℕ

namespace SpaceBoundedAlgorithm

/-- Absolute-accuracy contract for an algorithm with a space cost. -/
def Estimates {Ix : Type*} (alg : SpaceBoundedAlgorithm Ix) (f : Ix → ℝ) (eps : ℝ) : Prop :=
  ∀ x, |alg.est x - f x| ≤ eps

/-- Relative-accuracy contract for an algorithm with a space cost. -/
def EstimatesRel {Ix : Type*} (alg : SpaceBoundedAlgorithm Ix) (f : Ix → ℝ) (eps : ℝ) : Prop :=
  ∀ x, |alg.est x - f x| ≤ eps * f x

end SpaceBoundedAlgorithm

/-- `maxOver X g = max_{x ∈ X} g x`, written as a supremum so that the empty
set and unbounded cases are handled by the usual real conventions. -/
noncomputable def maxOver {Ix : Type*} (X : Set Ix) (g : Ix → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ X, r = g x}

/-- `minOver X g = min_{x ∈ X} g x`, written as an infimum. -/
noncomputable def minOver {Ix : Type*} (X : Set Ix) (g : Ix → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ X, r = g x}

end Qatlib.Papers.ApproxSpan15.MainResults
