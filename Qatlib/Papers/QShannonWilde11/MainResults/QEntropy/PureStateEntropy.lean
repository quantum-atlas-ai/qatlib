/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ClassicalAux
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section


/-!
# Pure bipartite states: density operator and vanishing entropy

Paper version: **arXiv:1106.1445v8**, [Wilde2017], Theorem 11.2.1, Eqs. (11.23)–(11.24), fixed
PDF p. 325.
<https://arxiv.org/abs/1106.1445>

Theorem 11.2.1 states that a pure bipartite state `|φ⟩` has vanishing joint entropy,
`H(AB) = 0`, and that its two reduced states share one spectrum, so `H(A) = H(B)`.  This file
records the paper-model density operator `pureDensity` of a unit vector and proves that its
joint entropy vanishes and that it satisfies the paper's purity predicate.

The marginal equality `H(A) = H(B)` is *not* proved here.  The library reduces a marginal to
the partial trace of the Schmidt expansion
(`Qatlib.Concepts.FiniteLocc.LOCCProgram.g1`), but it has no statement identifying the
eigenvalues of a sum `Σ_k λ_k |u_k⟩⟨u_k|` of orthonormal rank-one terms, which is what the
spectral comparison of the two marginals needs.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QShannonWilde11.MainResults.QEntropy

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Papers.QShannonWilde11.MainResults.Model

noncomputable section

/-- The model's rank-one operator `|φ⟩⟨φ|` agrees with the library outer product. -/
theorem model_outerProduct_eq {I : Type} [Fintype I] [DecidableEq I] (φ : QState I) :
    Qatlib.Papers.QShannonWilde11.MainResults.Model.outerProduct φ =
      Reflection.outerProduct φ := by
  ext i j
  simp [Qatlib.Papers.QShannonWilde11.MainResults.Model.outerProduct, Reflection.outerProduct]

/-- The density operator `|φ⟩⟨φ|` of a unit vector, as a state of the paper model. -/
def pureDensity {I : Type} [Fintype I] [DecidableEq I] (φ : QState I) (hφ : IsUnitVec φ) :
    Dens I :=
  ⟨Reflection.outerProduct φ, (outerProduct_density hφ).1, (outerProduct_density hφ).2⟩

/-- The underlying matrix of `pureDensity` is the outer product `|φ⟩⟨φ|`. -/
theorem pureDensity_val {I : Type} [Fintype I] [DecidableEq I] (φ : QState I)
    (hφ : IsUnitVec φ) : (pureDensity φ hφ).val = Reflection.outerProduct φ := rfl

/-- `pureDensity` satisfies the paper's pure-state predicate `IsPureState` of §11.2. -/
theorem isPureState_pureDensity {I : Type} [Fintype I] [DecidableEq I] (φ : QState I)
    (hφ : IsUnitVec φ) : IsPureState (pureDensity φ hφ) :=
  ⟨φ, hφ, (pureDensity_val φ hφ).trans (model_outerProduct_eq φ).symm⟩

/-- The pure state of a unit vector is the paper model's density operator obtained from the
corresponding mixed state, so the entropy bridge applies to it. -/
theorem pureDensity_eq_localState_pure {I : Type} [Fintype I] [DecidableEq I] (φ : QState I)
    (hφ : IsUnitVec φ) :
    pureDensity φ hφ =
      localState (MState.pure (normalizedStateEquivKet I ⟨φ, hφ⟩)) := by
  refine Subtype.ext ?_
  rw [(entropy_density_bridge.2.1 I ⟨φ, hφ⟩).1]
  rfl

/-- **Theorem 11.2.1, Eq. (11.23)** — [Wilde2017], arXiv:1106.1445v8, fixed PDF p. 325.  The von Neumann
entropy of a pure bipartite state vanishes: `H(AB) = 0`. -/
theorem vnH_pureDensity {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (φ : A × B → ℂ) (hφ : IsUnitVec φ) : vnH (pureDensity φ hφ) = 0 := by
  show entropy (pureDensity φ hφ) = 0
  rw [pureDensity_eq_localState_pure φ hφ]
  exact (entropy_density_bridge.2.1 (A × B) ⟨φ, hφ⟩).2

end

end Qatlib.Papers.QShannonWilde11.MainResults.QEntropy
