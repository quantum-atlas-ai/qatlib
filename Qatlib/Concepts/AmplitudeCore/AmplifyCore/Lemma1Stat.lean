/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-!
# Specification of the Grover component action

`expected` states the action of the Grover iterate on the orthogonal good and bad parts of a
prepared basis state. The good subspace is the closed span of the basis vectors selected by the
marking predicate. See [BrassardEtAl2002] for background.

## Main statements

* `expected`: The proposition asserting the two good and bad component action formulas for the
  Grover iterate in [Brassard et al., Lemma 1][BrassardEtAl2002].

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma1Spec
/-- The proposition asserting the two good and bad component action formulas for the Grover
iterate in [Brassard et al., Lemma 1][BrassardEtAl2002]. -/
def expected : Prop :=
  (∀ (X : Set ℤ) (hzero : (0 : ℤ) ∈ X)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis X ℂ H) (χ : ℤ → Bool) (A : H ≃ₗᵢ[ℂ] H),
  let ket0 : H := basis ⟨0, hzero⟩;
  let G : Submodule ℂ H :=
    (Submodule.span ℂ
      (Set.image (fun i : X => basis i) {i : X | χ (i : ℤ) = true})).topologicalClosure;
  let P : H →L[ℂ] H := G.starProjection;
  let ψ : H := A ket0;
  let ψ₁ : H := P ψ;
  let ψ₀ : H := ψ - ψ₁;
  let a : ℝ := (inner ℂ ψ₁ ψ₁).re;
  let S₀ : H → H := fun v => v - (2 * inner ℂ ket0 v) • ket0;
  let Sχ : H → H := fun v => v - (2 : ℂ) • P v;
  let Q : H → H := fun v => -(A (S₀ (A.symm (Sχ v))));
  Q ψ₁ = (1 - 2 * (a : ℂ)) • ψ₁ - (2 * (a : ℂ)) • ψ₀ ∧
  Q ψ₀ = (2 * (1 - (a : ℂ))) • ψ₁ + (1 - 2 * (a : ℂ)) • ψ₀)
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma1Spec
