/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QShannonWilde11.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Auxiliary vocabulary — classical entropies and structural predicates

Paper version: **arXiv:1106.1445v8**.  Binary entropy `h₂`, the `g₂` function of
the continuity bounds (§11.10), classical probability distributions, rank-one
POVMs (§11.1) and pure/mixed structural predicates used by the paper-layer
statements.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.Model

open Matrix
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open scoped BigOperators ComplexOrder ENNReal MatrixOrder

noncomputable section

/-- Binary entropy `h₂(t) = −t log t − (1−t) log(1−t)` (§11.10, Eq. 11.86). -/
def binEnt (t : ℝ) : ℝ := -t * Real.log t - (1 - t) * Real.log (1 - t)

/-- The `g₂(ε)` function of the AFW/continuity bounds (§11.10, Eq. 11.98):
`g₂(ε) = (2ε + (1−2ε)·log(1/ε))·log d`-free form `(1+2ε)log(1+2ε) − 2ε log(2ε)`. -/
def g2 (ε : ℝ) : ℝ :=
  (1 + 2 * ε) * Real.log (1 + 2 * ε) - 2 * ε * Real.log (2 * ε)

/-- A classical probability distribution on `X`. -/
def IsProb {X : Type} [Fintype X] (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∑ x, p x) = 1

/-- Shannon entropy `H(X) = −Σ_x p(x) log p(x)` (Ch. 10, Eq. 10.2). -/
def classicalEntropy {X : Type} [Fintype X] (p : X → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

/-- Classical relative entropy `D(p‖q) = Σ_x p(x) log(p(x)/q(x))` (Eq. 10.46). -/
def classicalRelEnt {X : Type} [Fintype X] (p q : X → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- Classical mutual information `I(X;Y) = H(X)+H(Y)−H(XY)` (Eq. 10.30). -/
def classicalMutualInfo {X Y : Type} [Fintype X] [Fintype Y]
    (p : X × Y → ℝ) : ℝ :=
  classicalEntropy (fun x => ∑ y, p (x, y)) +
    classicalEntropy (fun y => ∑ x, p (x, y)) - classicalEntropy p

/-- A rank-one operator: `M = |v⟩⟨v|` for a unit vector `v` (§11.1). -/
def IsRankOne {I : Type} [Fintype I] [DecidableEq I] (M : Op I) : Prop :=
  ∃ v : I → ℂ, IsUnitVec v ∧ M = outerProduct v

/-- A pure state: the density operator of a unit vector (§11.2, Eq. 11.19). -/
def IsPureState {I : Type} [Fintype I] [DecidableEq I] (ρ : Dens I) : Prop :=
  ∃ ψ : I → ℂ, IsUnitVec ψ ∧ ρ.val = outerProduct ψ

/-- `P` (a projector) projects onto the support of `ρ` restricted as needed in
the gentle-measurement / typicality arguments. -/
def projectsOnto {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (P : Matrix I I ℂ) (S : Matrix I J ℂ) : Prop :=
  P.PosSemidef ∧ P = P * P ∧ P * S = S

end

end Qatlib.Papers.QShannonWilde11.MainResults.Model
