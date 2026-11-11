/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Theorems 2 and 5, Corollaries 1 and 2: classical hardness of local
expectation values

Fixed version: arXiv:2608.15545v1 (2026-08-16): Theorem 2 (p.4), Theorem 5
(p.15), Corollary 1 (p.4-5), Corollary 2 (p.5), and the guiding reductions of
Appendix E (p.23-25).  Paper: *Quantum Advantage with Adaptive Shallow
Circuits*.

Theorem 2 asserts that some CRAS circuit has local output expectation values
that no efficient classical algorithm can estimate within constant additive
error.  Its formal proof (Theorem 4, Appendix E) is a reduction: a
polynomial-time classical estimator for the local expectation values of an
explicit DLP-based CRAS family would solve the prime-field discrete logarithm
problem in randomized polynomial time, contradicting `DLP ∉ BPP`.

* **Theorem 2** — the unrestricted-architecture family.
* **Corollary 1** — the same family compiled onto the 2D nearest-neighbour
  dynamic architecture via Lemma 4 and Lemmas 10-11.
* **Corollary 2** — the 2D family's states obey the entanglement area law,
  yet one fixed single-qubit observable remains classically hard.
* **Theorem 5** — the observable is a fixed one-local `Z` on one output qubit
  and the additive error is exactly `1/100`.

This file sets up the paper-layer vocabulary (families of local-expectation
tasks, polynomial-time classical estimators, the additive-error criterion)
and proves the logical shape of these statements, including monotonicity in
the error parameter.  The Appendix E reduction itself enters as the explicit
hypothesis `hReduction`; the structural facts (membership in CRAS, 2D layout,
area law) enter as witness fields of `LocalExpectationFamily`, exactly as in
the paper's proof of each corollary.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.ClassicalHardness

/-- Architecture on which a circuit family is implemented.  Theorem 2 only
requires the unrestricted architecture; Corollary 1 refines it to the
two-dimensional nearest-neighbour architecture. -/
inductive Architecture where
  /-- Arbitrary connectivity, as in the definition of CRAS. -/
  | arbitrary
  /-- Two-dimensional nearest-neighbour dynamic architecture. -/
  | twoDimensional
  deriving DecidableEq, Repr

/-- A family of local-expectation tasks.  `index` is the set of instances
`(p, g, y)`; `value` is the expectation `μ_{p,g,y}` of the fixed one-qubit
readout `Z` on the output qubit of the corresponding CRAS circuit.  The
provenance fields record the paper's structural requirements (membership in
CRAS, 2D layout for Corollary 1, and the entanglement area law for
Corollary 2). -/
structure LocalExpectationFamily where
  /-- Instance set of the family (the paper's `(p, g, y) ∈ I`). -/
  index : Type
  /-- Expectation value of the fixed output observable, per instance. -/
  value : index → ℝ
  /-- Architecture on which the family is implemented. -/
  architecture : Architecture
  /-- The circuits belong to CRAS (with the paper's depth/feedback budget). -/
  hasCrasCircuits : Prop
  /-- Witness that the family is in CRAS. -/
  cras_witness : hasCrasCircuits
  /-- The prepared states obey the entanglement area law (Corollary 2). -/
  obeysAreaLaw : Prop
  /-- Witness of the area law. -/
  areaLaw_witness : obeysAreaLaw

/-- A classical estimator for a family of expectation values, with additive
error `δ`.  `polyTime` is the paper's randomized polynomial-time predicate;
it is kept abstract because this paper layer does not formalize Turing
machines or the BPP class. -/
structure ClassicalEstimator (F : LocalExpectationFamily) (δ : ℝ) where
  /-- The estimated values, one per instance. -/
  estimate : F.index → ℝ
  /-- The estimator is randomized polynomial time (the paper's BPP). -/
  polyTime : Prop
  /-- Every estimate is within additive error `δ`. -/
  error_le : ∀ i, |estimate i - F.value i| ≤ δ

/-- **Theorem 2's notion of efficient estimation.**  The family is classically
estimable within additive error `δ` if some polynomial-time classical
estimator achieves error `≤ δ` on every instance. -/
def ClassicallyEstimable (F : LocalExpectationFamily) (δ : ℝ) : Prop :=
  ∃ E : ClassicalEstimator F δ, E.polyTime

/-- **Error monotonicity.**  An estimator with error `δ` is also an estimator
with any larger error `δ'`; in particular hardness at constant `δ` implies
hardness at every smaller error. -/
theorem classicallyEstimable_mono {F : LocalExpectationFamily} {δ δ' : ℝ}
    (h : δ ≤ δ') (hE : ClassicallyEstimable F δ) :
    ClassicallyEstimable F δ' := by
  obtain ⟨E, hPoly⟩ := hE
  refine ⟨⟨E.estimate, E.polyTime, fun i => ?_⟩, hPoly⟩
  exact le_trans (E.error_le i) h

/-- **Theorem 2, reduction form.**  Assume the family is implemented in CRAS
and that a polynomial-time classical estimator for its local expectation
values (within additive error `δ`) would put the prime-field discrete
logarithm in BPP.  Then, if DLP is not in BPP, the family's expectation
values are not classically estimable within `δ`. -/
theorem classical_hardness_of_DLP
    (F : LocalExpectationFamily) (δ : ℝ) (DLPinBPP : Prop)
    (hHard : ¬ DLPinBPP)
    (hReduction : ClassicallyEstimable F δ → DLPinBPP) :
    F.hasCrasCircuits ∧ ¬ ClassicallyEstimable F δ :=
  ⟨F.cras_witness, fun hEst => hHard (hReduction hEst)⟩

/-- **Theorem 2 (Classical hardness).**  Let `DLP ∉ BPP` and let `F` be an
explicit CRAS family whose local expectation values reduce DLP to classical
estimation, as constructed in Appendix E (Theorem 4).  Then there is a CRAS
family — namely `F` — whose local output expectation values cannot be
efficiently estimated classically within constant additive error `δ`.

The existential form matches the paper's "there exists a quantum circuit in
CRAS"; the family `F` is the explicit DLP-based construction of Appendix E,
supplied by the caller together with its CRAS witness and the reduction
`hReduction`. -/
theorem theorem2_classical_hardness
    (DLPinBPP : Prop) (hHard : ¬ DLPinBPP)
    (F : LocalExpectationFamily) (δ : ℝ)
    (hReduction : ClassicallyEstimable F δ → DLPinBPP) :
    ∃ F' : LocalExpectationFamily,
      F'.hasCrasCircuits ∧ ¬ ClassicallyEstimable F' δ :=
  ⟨F, classical_hardness_of_DLP F δ DLPinBPP hHard hReduction⟩

/-- **Corollary 1 (Classical hardness with 2D structure).**  Let `DLP ∉ BPP`
and let `F` be a CRAS family implemented on a two-dimensional architecture
whose local expectation values reduce DLP to classical estimation (the 2D
compilation is Lemma 4 together with Lemmas 10-11).  Then there is an
explicit 2D CRAS family whose output expectation values cannot be efficiently
estimated classically within constant additive error. -/
theorem corollary1_classical_hardness_2d
    (DLPinBPP : Prop) (hHard : ¬ DLPinBPP)
    (F : LocalExpectationFamily) (δ : ℝ)
    (hArch : F.architecture = Architecture.twoDimensional)
    (hReduction : ClassicallyEstimable F δ → DLPinBPP) :
    ∃ F' : LocalExpectationFamily,
      F'.architecture = Architecture.twoDimensional ∧
        F'.hasCrasCircuits ∧ ¬ ClassicallyEstimable F' δ := by
  refine ⟨F, hArch, ?_⟩
  exact classical_hardness_of_DLP F δ DLPinBPP hHard hReduction

/-- **Corollary 2 (Entanglement area-law hardness).**  Let `DLP ∉ BPP` and
let `F` be a 2D CRAS family whose prepared states obey the entanglement area
law and whose local expectation values reduce DLP to classical estimation.
Then there is an explicit 2D CRAS family that obeys the area law while one
fixed single-qubit observable is classically hard in the worst case. -/
theorem corollary2_area_law_hardness
    (DLPinBPP : Prop) (hHard : ¬ DLPinBPP)
    (F : LocalExpectationFamily) (δ : ℝ)
    (hArch : F.architecture = Architecture.twoDimensional)
    (hArea : F.obeysAreaLaw)
    (hReduction : ClassicallyEstimable F δ → DLPinBPP) :
    ∃ F' : LocalExpectationFamily,
      F'.architecture = Architecture.twoDimensional ∧
        F'.obeysAreaLaw ∧ F'.hasCrasCircuits ∧
          ¬ ClassicallyEstimable F' δ := by
  refine ⟨F, hArch, hArea, ?_⟩
  exact classical_hardness_of_DLP F δ DLPinBPP hHard hReduction

/-- The absolute additive error of Theorem 5. -/
noncomputable def theorem5Error : ℝ := 1 / 100

/-- The error of Theorem 5 is strictly positive. -/
theorem theorem5Error_pos : 0 < theorem5Error := by
  unfold theorem5Error
  norm_num

/-- **Theorem 5 (Conditional hardness with a fixed observable).**  Assume
`DLP ∉ BPP` in the worst case, and let `F` be the explicit CRAS family of
Appendix E together with a reduction from classical estimation of its fixed
one-local `Z` observable (to additive error `1/100`) to DLP in BPP.  Then
there is an explicit CRAS family with a fixed one-local observable such that
no randomized classical polynomial-time algorithm estimates it to additive
error `1/100` on every valid input. -/
theorem theorem5_fixed_observable_hardness
    (DLPinBPP : Prop) (hHard : ¬ DLPinBPP)
    (F : LocalExpectationFamily)
    (hReduction : ClassicallyEstimable F theorem5Error → DLPinBPP) :
    ∃ F' : LocalExpectationFamily,
      F'.hasCrasCircuits ∧ ¬ ClassicallyEstimable F' theorem5Error :=
  theorem2_classical_hardness DLPinBPP hHard F theorem5Error hReduction

/-- **Theorem 5, error monotonicity consequence.**  Hardness at the fixed
error `1/100` implies hardness at every smaller additive error `δ ≤ 1/100`:
an estimator with a smaller error would in particular be an estimator with
error `1/100`. -/
theorem theorem5_hardness_at_smaller_error
    (F : LocalExpectationFamily) (δ : ℝ) (hδ : δ ≤ theorem5Error)
    (hHard : ¬ ClassicallyEstimable F theorem5Error) :
    ¬ ClassicallyEstimable F δ := by
  intro hEst
  exact hHard (classicallyEstimable_mono hδ hEst)

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.ClassicalHardness
