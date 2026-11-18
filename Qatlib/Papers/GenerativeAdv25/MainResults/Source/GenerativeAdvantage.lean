/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GenerativeAdv25.MainResults.Model.Complexity

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# GenerativeAdv25 — generative-advantage theorems

Fixed paper version: arXiv:2509.09033v1.

The paper's advantage theorems are stated against complexity classes that the repository
does not formalize (BPP, BQP, the non-uniform polynomial hierarchy, and the IDQNN of
Definition 17).  They are therefore recorded on the sampling interface of
`Model/Complexity.lean`:

* `QuantumlyEasy p` — a polynomial-size quantum sampler generates the family `p`;
* `ClassicallyHard p` — no polynomial-size classical sampler does;
* `Conjecture1` — existence of such a family (the paper's Conjecture 1);
* `BPPEqBQP` — every quantumly sampleable family is classically sampleable, the sampling
  analogue of `BPP = BQP`;
* `PolynomialHierarchyCollapses` — the sampling analogue used in Proposition 4;
* `RepFindingFamily` — a family of circuit descriptions that is quantumly easy and
  classically hard (the output of the paper's circuit-compression tasks).

The proofs below are logical consequences of these sampling definitions. They do not
construct the paper's circuit-compression reductions or identify complexity classes.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.GenerativeAdv25.MainResults

namespace Qatlib.Papers.GenerativeAdv25.MainResults.Source
open Qatlib.Papers.GenerativeAdv25.MainResults

/-- Sampling analogue of `BPP = BQP`: every polynomially quantum-sampleable
conditional-law family is also polynomially classically sampleable. -/
def BPPEqBQP : Prop :=
  ∀ (m : ℕ) (p : ∀ n, CondLaw n m), QuantumlyEasy p → ClassicallyEasy p

/-- Sampling analogue of a collapse of the non-uniform polynomial hierarchy: the same
separation failure as `BPPEqBQP`, used in Proposition 4. -/
def PolynomialHierarchyCollapses : Prop :=
  ∀ (m : ℕ) (p : ∀ n, CondLaw n m), QuantumlyEasy p → ClassicallyEasy p

/-- A family of circuit descriptions that is quantumly easy and classically hard: the
output form of the paper's circuit-compression tasks (Theorems 2 and 14). -/
def RepFindingFamily : Prop :=
  ∃ (_m r : ℕ) (desc : ∀ n, CondLaw n r), QuantumlyEasy desc ∧ ClassicallyHard desc

/-- Extract the quantumly easy, classically hard sampling family assumed by `Conjecture1`.
**Theorem 13** (arXiv:2509.09033v1): learning
generative instantaneously-deep QNNs is quantumly easy but classically hard under
Conjecture 1.  On the sampling interface, Conjecture 1 *is* the existence of such a family,
so the implication is the identity; the IDQNN-specific instantiation (Definition 17) is not
modelled in this repository. -/
theorem exists_sampling_separation_of_conjecture (h : Conjecture1) :
    ∃ (m : ℕ) (p : ∀ n, CondLaw n m), QuantumlyEasy p ∧ ClassicallyHard p :=
  h

/-- Extract a hard conditional-law family from the sampling conjecture.
**Theorem 1** (arXiv:2509.09033v1): under standard
complexity-theoretic conjectures there exist conditionals `p(y|x)` that a quantum computer
learns to generate from classical samples but no classical computer can generate.  Recorded
at the sampling interface; the learning algorithm itself is not modelled. -/
theorem exists_hard_conditional_law_of_conjecture (h : Conjecture1) :
    ∃ (m : ℕ) (p : ∀ n, CondLaw n m), QuantumlyEasy p ∧ ClassicallyHard p :=
  h

/-- Failure of the sampling equality yields a hard description family.
**Theorem 2** (arXiv:2509.09033v1): given a polynomial-size
circuit promised to have a constant-depth representation, finding that representation is
not classically efficient unless `BPP = BQP`.


This declaration concerns only the sampling or existential interface above. -/
theorem rep_finding_family_of_not_bpp_eq_bqp (h : ¬ BPPEqBQP) : RepFindingFamily := by
  classical
  by_contra hc
  apply h
  intro m p hq
  by_contra hp
  exact hc ⟨m, m, p, hq, hp⟩

/-- Failure of the sampling hierarchy-collapse predicate implies the sampling conjecture.
**Proposition 4** (arXiv:2509.09033v1): assuming the non-uniform
polynomial hierarchy does not collapse, Conjecture 1 holds.


This declaration concerns only the sampling or existential interface above. -/
theorem conjecture_of_not_sampling_hierarchy_collapse (h : ¬ PolynomialHierarchyCollapses) : Conjecture1 := by
  classical
  by_contra hc
  apply h
  intro m p hq
  by_contra hp
  exact hc ⟨m, p, hq, hp⟩

/-- Reuse a conjectured sampling separation as a hard description family.
**Theorem 12** (arXiv:2509.09033v1): learning generative
tomographically-complete shallow QNNs is quantumly easy and classically hard under
Conjecture 1.  On the sampling interface this is the identity implication; the
tomographic-completeness property of the shallow ansatz is not modelled. -/
theorem rep_finding_family_of_conjecture (h : Conjecture1) : RepFindingFamily := by
  obtain ⟨m, p, hq, hh⟩ := h
  exact ⟨m, m, p, hq, hh⟩

/-- The sampling inequality supplies an existential hard description family.
**Theorem 14** (arXiv:2509.09033v1): under `BPP ≠ BQP`,
generating a more efficient constant-depth circuit `C'` for an input circuit `C` is
efficiently solvable on a quantum computer but classically intractable.


This declaration concerns only the sampling or existential interface above. -/
theorem exists_hard_description_family_of_not_bpp_eq_bqp (h : ¬ BPPEqBQP) : RepFindingFamily := by
  exact rep_finding_family_of_not_bpp_eq_bqp h

end Qatlib.Papers.GenerativeAdv25.MainResults.Source
