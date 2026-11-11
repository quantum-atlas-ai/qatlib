/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Papers.PropTestGraph10.MainResults.Model.Graph
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# PropTestGraph10 source model: one-sided property testers and runtime predicates

Fixed source: arXiv:1012.3174v3. This module packages the paper's quantum
property-testing model (p. 3) on top of the library's fixed-space counted-query
circuit model (`QuantumAlgorithm.Concepts.QueryComplexity.DegreeMethod.Complexity`):
a `QuantumTester` holds a unitary oracle family for the graph, one unitary
fixed-gate circuit, one normalized start state, an instance-dependent accepting
set of basis states, and the accounted time. `acceptProb` is the acceptance
probability of the measured output.

The paper's algorithmic claims (Theorems 1, 10, 13, Lemma 12) quantify over such
algorithms and bound either their query complexity or their accounted time. The
paper derives its running times by charging `poly(log N / ε)` work per oracle
query; `query_le_time` records the corresponding lower relation (each query is
one accounted step), so a time bound is at least as strong as the query bound.

Also defined here are the asymptotic cost predicates used verbatim by the
statements: `O(N^{1/3} poly(log N / ε))`, `O(N^{1/3+3μ} poly(log N) · …)`, and
the lower-bound shape `Ω(N^{1/4} / log N)`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.Model

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix

/-- A quantum property tester in the paper's adjacency-list oracle model. The
oracle family `oracle G` is the black box `|v,i,z⟩ ↦ |v,i,z ⊕ f_G(v,i)⟩`
(p. 2); `circuit` is one fixed unitary circuit applied to `start`; `accepting G`
is the set of final basis states that decode to "true on `G`". `timeCost` is the
accounted running time, at least the query count. -/
structure QuantumTester (N d : ℕ) where
  /-- The finite basis of the algorithm's workspace. -/
  I : Type
  [fintypeI : Fintype I]
  [decEqI : DecidableEq I]
  /-- Unitarily implemented adjacency-list oracle for every graph. -/
  oracle : BoundedDegreeGraph N d → Matrix I I ℂ
  oracle_unitary : ∀ G, oracle G ∈ Matrix.unitaryGroup I ℂ
  /-- The fixed unitary circuit (instance-independent). -/
  circuit : Circuit I
  circuit_unitary : IsUnitaryCircuit circuit
  /-- The normalized, instance-independent start state. -/
  start : QState I
  start_normalized : Normalized start
  /-- Final basis states that output "true". -/
  accepting : BoundedDegreeGraph N d → Finset I
  /-- Accounted running time of the algorithm on `N`-vertex inputs. -/
  timeCost : ℕ
  /-- Querying costs at least one accounted time step each. -/
  query_le_time : QueryCount circuit ≤ timeCost

/-- Acceptance probability of the tester on `G`: the output "true" mass. -/
def QuantumTester.acceptProb {N d : ℕ} (T : QuantumTester N d)
    (G : BoundedDegreeGraph N d) : ℝ :=
  letI := T.fintypeI
  letI := T.decEqI
  MeasureProb (Run (T.oracle G) T.circuit T.start) (T.accepting G)

/-- Query complexity of the tester (machine-counted oracle calls). -/
def QuantumTester.queryCost {N d : ℕ} (T : QuantumTester N d) : ℕ :=
  QueryCount T.circuit

/-- The tester "always returns true" when `G` is bipartite and rejects with
constant probability `c` when `G` is `ε`-far from bipartite (Theorem 1 /
Theorem 10, pp. 3 and 15). -/
def TestsBipartiteness {N d : ℕ} (T : QuantumTester N d) (ε c : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧
    (∀ G : BoundedDegreeGraph N d, IsBipartite G → T.acceptProb G = 1) ∧
    (∀ G : BoundedDegreeGraph N d, FarFromBipartite ε G → T.acceptProb G ≤ 1 - c)

/-- The tester accepts `α`-expanders with probability at least `2/3` and rejects
graphs `ε`-far from every `α'`-expander of degree at most `d` with probability at
least `2/3` (the constant-error expansion-testing promise used by Theorem 2 and
Theorem 13). -/
def TestsExpansion {N d : ℕ} (T : QuantumTester N d) (ε α α' : ℝ) : Prop :=
  (∀ G : BoundedDegreeGraph N d, IsExpander α G → (2 / 3 : ℝ) ≤ T.acceptProb G) ∧
    (∀ G : BoundedDegreeGraph N d, FarFromExpanders ε α' G → T.acceptProb G ≤ (1 / 3 : ℝ))

/-- `T = O(N^{1/3} poly(log N / ε))` along `N ≥ 1`, the running time of Theorem 1
and Theorem 10 (pp. 3 and 15). -/
def IsN13PolyLog (T : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ j : ℕ, ∀ N : ℕ, 1 ≤ N →
    T N ≤ C * (N : ℝ) ^ (1 / 3 : ℝ) * (Real.log N / ε) ^ j

/-- `T = Ω(N^{1/4} / log N)` along `N ≥ 2`, the query lower bound of Theorem 2
(p. 4). -/
def IsOmegaN14Log (T : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → c * (N : ℝ) ^ (1 / 4 : ℝ) / Real.log N ≤ T N

/-- `T = O(M log M · |X|^{2/3} · poly(log |Y|))`, the running time of Algorithm 4
(Lemma 12, p. 15). -/
def IsMlogMX23PolyLogY (T : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ j : ℕ, ∀ M X Y : ℕ, 2 ≤ M → 2 ≤ X → 2 ≤ Y →
    T M X Y ≤ C * (M : ℝ) * Real.log M * (X : ℝ) ^ (2 / 3 : ℝ) * (Real.log Y) ^ j

/-- `T = O(N^{1/3+3μ} poly(log N) · (d² / (ε α²)) · log(d/α))`, the running time
of Algorithm 5 (Theorem 13, p. 16). -/
def IsN13MuPolyLog (T : ℕ → ℝ) (μ ε α : ℝ) (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ j : ℕ, ∀ N : ℕ, 2 ≤ N →
    T N ≤ C * (N : ℝ) ^ (1 / 3 + 3 * μ : ℝ) * (Real.log N) ^ j *
      ((d : ℝ) ^ 2 / (ε * α ^ 2)) * Real.log ((d : ℝ) / α)

end Qatlib.Papers.PropTestGraph10.MainResults.Model
