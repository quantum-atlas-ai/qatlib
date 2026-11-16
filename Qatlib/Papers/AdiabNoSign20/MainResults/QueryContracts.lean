/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# AdiabNoSign20 — query-model support structures and legacy contract defects

Source: M. B. Hastings, *The Power of Adiabatic Quantum Computation with No
Sign Problem*, arXiv:2005.03791v2, Sections 2-3 and 6.

This module preserves the closed query-model support structures of the
original development of this material (`IsSection3Path`, `GraphDistinguisher`,
`IsAryTree`, `IsPathBase`, `IsHeightDecoration`) and records, as
machine-checked theorems, two defects of the legacy paper-layer contracts:

* `reachHard_never` — the legacy `ReachHard` predicate quantifies over
  `GraphQueryAlgorithm` records whose `reachProb` field is an arbitrary
  function with no semantic tie to reachability; a record with
  `reachProb := fun _ _ _ => p + 1` refutes the bound for every `p`, so
  `ReachHard` is unsatisfiable.  Consequently Lemma 6 parts 1-2 (which
  *conclude* `ReachHard`) and Lemma 7 (whose conclusion conjoins it) are
  false as literally stated, and Lemma 5 (which *hypothesises* it) is only
  vacuously satisfiable.  `lemma7_conclusion_refuted` spells out the
  refutation of Lemma 7's conclusion.
* `noAlgorithmBeats_modified_unsat` — `NoAlgorithmBeatsInModel` quantifies
  over algorithms on *every* finite computational-basis type `ι`, including
  the empty type, where no `AdNSPInstance` exists (the endpoint condition
  requires a basis state) and `SolvesEveryInstance` holds vacuously; so the
  lower-bound statement of Theorem 1 is refuted by an empty-basis algorithm.
  The corrected contract needs an inhabitedness/existence assumption on the
  instance family, which the legacy model does not carry.

The original targets are retained verbatim in the project history; these
theorems are the evidence that
they cannot be admitted as-is, and mark the precise model boundary that any
faithful completion must first repair.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabNoSign20.MainResults.QueryContracts

open Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel

/-- The path `P̂` of Section 3 (p. 10-11), abstractly: it is built from `N`
copies of the `C`/`D` graph Hamiltonians, and its endpoint condition holds
because the transverse field is ramped up at the end. -/
structure IsSection3Path {ι : Type} [Fintype ι] [DecidableEq ι]
    (params : AdNSPParameters) (N : ℕ) (V : Type) (C D : SimpleGraph V)
    (startC : V) (Hhat : ℝ → Hamiltonian ι) (a b : ℝ) : Prop where
  /-- the endpoint condition holds: the ramp `Q` ends in a computational
  basis state (Section 3, p. 11) -/
  endpoint : SatisfiesEndpoint Hhat a b

/-- A classical algorithm trying to distinguish two graphs in the modified
query model (§6, p. 17).  `successProb G G'` is the probability of correctly
answering `G` when the true graph is `G` and the alternative is `G'`;
`mutualInfo G G'` is the mutual information between the choice of graph and
the query responses (conditioned on the algorithm's randomness). -/
structure GraphDistinguisher (V : Type) where
  /-- number of queries made by the algorithm -/
  queryCount : ℕ
  /-- probability of guessing the true graph `G` when the alternative is `G'` -/
  successProb : SimpleGraph V → SimpleGraph V → ℝ
  /-- mutual information between the graph choice and the query responses -/
  mutualInfo : SimpleGraph V → SimpleGraph V → ℝ

/-- `IsAryTree T root arity height`: `T` is the perfect `arity`-ary tree
`T_{arity,height}` of §6 rooted at `root`, whose leaves are at distance
`height` from the root.  Only the acyclicity is recorded; the degree and
height structure is documented rather than formalised. -/
structure IsAryTree {V : Type} (T : SimpleGraph V) (root : V) (arity height : ℕ) :
    Prop where
  acyclic : T.IsAcyclic

/-- `IsPathBase T L n`: `T` is the base path graph `P_{L,(n+1)/2}` of §5.2. -/
structure IsPathBase {V : Type} (T : SimpleGraph V) (L n : ℕ) : Prop where
  acyclic : T.IsAcyclic

/-- `IsHeightDecoration base G hs`: `G` is obtained from `base` by the sequence
of decorations with the height sequence `hs` (§6, p. 18); in particular `base`
is an induced subgraph of `G`. -/
structure IsHeightDecoration {V : Type} [Fintype V] (base G : SimpleGraph V)
    (hs : List ℕ) : Prop where
  sub : ∀ a b, base.Adj a b → G.Adj a b

/-- The legacy `ReachHard` predicate is unsatisfiable: `reachProb` is an
unconstrained field of `GraphQueryAlgorithm`, so a record returning `p + 1`
on the target triple violates the bound `≤ p`.  This machine-checks the
model-contract defect behind Lemma 5 (hypothesis), Lemma 6 parts 1-2
(conclusion) and Lemma 7 (conclusion) of the original development of this
material; see the module docstring. -/
theorem reachHard_never {V : Type} (G : SimpleGraph V) (start : V) (S : Set V)
    (p : ℝ) (q : ℕ) : ¬ ReachHard G start S p q := by
  intro h
  have h0 : (0 : ℕ) ≤ q := Nat.zero_le q
  have := h ⟨0, fun _ _ _ => p + 1⟩ h0
  linarith

/-- The conclusion of Lemma 7 (§7, p. 21) of the original development of
this material is refuted in the legacy model: its last conjunct is a
`ReachHard` statement, which `reachHard_never` refutes for every parameter
choice.  The corrected contract must constrain `reachProb` to genuine reach
probabilities. -/
theorem lemma7_conclusion_refuted {V : Type} {D : SimpleGraph V} {startD : V}
    {Δ : Set V} {N : ℕ} :
    ¬ ∃ (P : ℝ) (Q : ℕ),
      (∃ c : ℝ, 0 < c ∧ Real.exp (-(c * (N : ℝ))) ≤ P) ∧
      (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        Real.exp (c₁ * (Real.log (N : ℝ)) ^ 2) ≤ (Q : ℝ) ∧
        (Q : ℝ) ≤ Real.exp (c₂ * (Real.log (N : ℝ)) ^ 2)) ∧
      ReachHard D startD Δ P Q := by
  rintro ⟨P, Q, -, -, hR⟩
  exact reachHard_never D startD Δ P Q hR

/-- The legacy `NoAlgorithmBeatsInModel` statement of Theorem 1 (§1.1, p. 4)
is unsatisfiable: on the empty computational
basis `ι = Empty` no `AdNSPInstance` exists (the endpoint condition requires
a basis state), so `SolvesEveryInstance` holds vacuously and the negated
success condition fails for the zero-query algorithm.  The corrected
contract must require an inhabited instance family. -/
theorem noAlgorithmBeats_modified_unsat :
    ¬ NoAlgorithmBeatsInModel QueryModelKind.modified := by
  rintro ⟨params, c, K, hc, hK, hN⟩
  have hinst :
      ∀ inst : AdNSPInstance Empty params 2, False := by
    intro inst
    obtain ⟨⟨i₀, _⟩, _⟩ := inst.endpoint
    exact i₀.elim
  have hq : (0 : ℝ) ≤ Real.exp (K * (Real.log (2 : ℝ)) ^ 2) :=
    le_trans (le_of_eq (by norm_num)) (Real.exp_nonneg _)
  have hcontra := hN 2 le_rfl Empty Unit
    ⟨QueryModelKind.modified, 0, fun _ inst => (hinst inst).elim, True⟩ rfl
    (by simpa using hq)
  apply hcontra
  intro inst
  exact (hinst inst).elim

end Qatlib.Papers.AdiabNoSign20.MainResults.QueryContracts
