/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Theorem1DegreeLeLambdaSqDegr
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Theorem3DegreeLeQueryCountSqDegr
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Lemma9LambdaLeQueryCountRestrictedDegr
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Lemma26F2DegreeLeDegreeDegr

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Bridges to frozen sensitivity/degree results (ABKRT 2020)

Source: arXiv:2010.12629v1.  The paper's Theorem 1 (page 6), Lemma 9 (page 8),
Theorem 3 (page 8, restated in the introduction) and Lemma 26 (page 18) already
have frozen counterparts in `TriangleQuery.DegreeBounds`.
Each theorem below restates the paper claim with its own binders and delegates to
the frozen proof, recording the exact frozen fully-qualified name.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ApproxDegree20.MainResults.Bridges

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds
open Qatlib.Concepts.QueryComplexity.DegreeBounds
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open scoped Matrix.Norms.L2Operator

/-- **ABKRT 2020, Theorem 1 (page 6).**  For every total Boolean function
`f : {0,1}^n → {0,1}`, `deg(f) ≤ λ(f)^2`, where `deg` is the exact representing
degree and `λ` is the spectral sensitivity (paper Definition 7).

Bridge to the frozen proof
`TriangleQuery.DegreeBounds.theorem1DegreeLeLambdaSq`,
which implements Huang's argument through a top multilinear face, a nonzero
parity eigenvector and principal compression. -/
theorem theorem1_degree_le_lambda_sq
    (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool) :
    (exactDegree f : ℝ) ≤ (spectralSensitivity f) ^ 2 :=
  theorem1DegreeLeLambdaSq I f

/-- **ABKRT 2020, Lemma 26 (page 18).**  For every total Boolean function
`f : {0,1}^n → {0,1}`, `deg₂(f) ≤ deg(f)` (after O'Donnell, *Analysis of Boolean
Functions*, Proposition 6.23).

Bridge to the frozen proof
`TriangleQuery.DegreeBounds.lemma26F2DegreeLeDegree`,
which reduces the real multilinear representative modulo two. -/
theorem lemma26_gf2Degree_le_degree
    (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool) :
    gf2Degree f ≤ exactDegree f :=
  lemma26F2DegreeLeDegree I f

/-- **ABKRT 2020, Lemma 9 (page 8), restricted per-circuit form.**  For every
unitary bit-query circuit `C` over an arbitrary finite workspace that decides a
total Boolean function `f` with two-sided error `1/3` through the fixed readout
event `E`, `λ(f) ≤ 6 · (3 + 2√2) · QueryCount C`.  This is the quantitative
`SA(f) = O(Q(f))` half of the paper's `λ(f) ≤ SA(f) = O(Q(f))`.

Bridge to the frozen proof
`TriangleQuery.DegreeBounds.lemma9LambdaLeQueryCountRestricted`,
which takes the adversary matrix `Γ = A_f` in the negative-adversary bound. -/
theorem lemma9_lambda_le_queryCount_restricted
    (N : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit ((Fin N × Bool) × W)) (ψ : QState ((Fin N × Bool) × W))
    (E : Finset ((Fin N × Bool) × W)) (f : (Fin N → Bool) → Bool)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hs : ∀ g : Fin N → Bool,
      2 / 3 ≤ MeasureProb (Run (workspaceBitOracle (W := W) g) C ψ)
        (if f g then E else Eᶜ)) :
    spectralSensitivity f ≤ 6 * (3 + 2 * Real.sqrt 2) * (QueryCount C : ℝ) :=
  lemma9LambdaLeQueryCountRestricted N W C ψ E f hC hψ hs

/-- **ABKRT 2020, Theorem 3 (page 8, introduction page 3), restricted per-circuit
form.**  For every unitary bit-query circuit `C` over an arbitrary finite
workspace that decides a total Boolean function `f` with two-sided error `1/3`
through the fixed readout event `E`,
`deg(f) ≤ (6 · (3 + 2√2) · QueryCount C)^2`; equivalently
`QueryCount C ≥ √(deg f) / (6 · (3 + 2√2))`, the per-circuit content of
`deg(f) = O(Q(f)^2)`.

Bridge to the frozen proof
`TriangleQuery.DegreeBounds.theorem3DegreeLeQueryCountSq`,
which composes Theorem 1 with Lemma 9. -/
theorem theorem3_degree_le_queryCount_sq
    (N : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit ((Fin N × Bool) × W)) (ψ : QState ((Fin N × Bool) × W))
    (E : Finset ((Fin N × Bool) × W)) (f : (Fin N → Bool) → Bool)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hs : ∀ g : Fin N → Bool,
      2 / 3 ≤ MeasureProb (Run (workspaceBitOracle (W := W) g) C ψ)
        (if f g then E else Eᶜ)) :
    (exactDegree f : ℝ) ≤
      (6 * (3 + 2 * Real.sqrt 2) * (QueryCount C : ℝ)) ^ 2 :=
  theorem3DegreeLeQueryCountSq N W C ψ E f hC hψ hs

end Qatlib.Papers.ApproxDegree20.MainResults.Bridges
