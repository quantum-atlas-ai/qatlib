/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAPerfect26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# QMAPerfect26 — class-level results

Fixed paper: Grewal–Rudolph, *QMA has perfect completeness*, arXiv:2609.13032v1.

This file fixes the promise-problem / verifier model and states the class-level
claims: Corollaries 1.2–1.5 and 1.7 as conditional bridges, with the class equality
of Theorem 1.1 (and Corollary 1.6) as an explicit hypothesis.  Theorem 1.1,
Corollary 1.6, and Lemma 3.1 themselves are not formalised; their statements are
preserved in the branch history of this file (real-simulation transport, the
constructive verifier of §3.3, parallel-repetition amplification, and the
relativised circuit pass are the open gaps).

Modelling boundary. A `Verifier` bundles the per-instance acceptance operator `E_x`.
Following Definition 2.1 (p.6) the class predicates record the spectral conditions on
`E_x` (`Complete`/`Sound`); polynomial-time uniformity and the concrete gate-word
encoding are represented by the `QMA1_S2` *dyadic normal form* (the consequence of
compiling into `𝓢₂`, Corollary 3.2), not by an unstated computability oracle. The
external completeness results of Gosset–Nagaj, Ma–Natarajan, Crichigno–Kohler,
King–Kohler, Hayakawa, Bostanci et al. are taken as explicit hypotheses with their
bibliographic identifiers, exactly as the paper composes them with Theorem 1.1.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMAPerfect26.MainResults

/-- A promise problem: a type of instances with YES/NO promises. -/
structure PromiseProblem where
  Inst : Type
  isYes : Inst → Prop
  isNo : Inst → Prop

/-- A promise-preserving many-one reduction `P ≤ L`. -/
structure Reduction (P L : PromiseProblem) where
  toFun : P.Inst → L.Inst
  yes_to_yes : ∀ x, P.isYes x → L.isYes (toFun x)
  no_to_no : ∀ x, P.isNo x → L.isNo (toFun x)

/-- A quantum verifier family: for each instance `x`, an acceptance operator on
`dim x` proof qubits (Definition 2.1, Eq. (1), p.6). -/
structure Verifier (P : PromiseProblem) where
  dim : P.Inst → ℕ
  accept : (x : P.Inst) → ProofMat (dim x)

/-- Completeness `c`: every YES instance admits a normalised proof with acceptance
probability at least `c` (Definition 2.1(i), p.6). -/
def Verifier.Complete {P : PromiseProblem} (V : Verifier P) (c : ℝ) : Prop :=
  ∀ x, P.isYes x →
    ∃ ψ : Idx (V.dim x) → ℝ, ψ ⬝ᵥ ψ = 1 ∧ c ≤ ψ ⬝ᵥ (V.accept x *ᵥ ψ)

/-- Soundness `s`: every proof on a NO instance has acceptance probability at most `s`
(Definition 2.1(ii), p.6). -/
def Verifier.Sound {P : PromiseProblem} (V : Verifier P) (s : ℝ) : Prop :=
  ∀ x, P.isNo x → ∀ ψ : Idx (V.dim x) → ℝ,
    ψ ⬝ᵥ (V.accept x *ᵥ ψ) ≤ s * (ψ ⬝ᵥ ψ)

/-- `QMA(c,s)` (Definition 2.1). -/
def InQMA (P : PromiseProblem) (c s : ℝ) : Prop :=
  ∃ V : Verifier P, V.Complete c ∧ V.Sound s

/-- `QMA = QMA(2/3, 1/3)`. -/
def QMA (P : PromiseProblem) : Prop := InQMA P (2 / 3) (1 / 3)

/-- `QMA₁ = QMA(1, 1/2)` (perfect completeness). -/
def QMA1 (P : PromiseProblem) : Prop := InQMA P 1 (1 / 2)

/-- `QMA^{𝓢₂}` normal form: a verifier whose acceptance operator is dyadic
(`2^h E` integral, Corollary 3.2, p.7). This is the invariant the paper extracts from
compilation into `𝓢₂ = {X, CNOT, Toffoli, H⊗H}`. -/
def InQMAS2 (P : PromiseProblem) (c s : ℝ) : Prop :=
  ∃ V : Verifier P, V.Complete c ∧ V.Sound s ∧ ∃ h, ∀ x, IsDyadicMat h (V.accept x)

/-- `QMA^{𝓢₂}(2/3, 1/3)`. -/
def QMAdyadicS2 (P : PromiseProblem) : Prop := InQMAS2 P (2 / 3) (1 / 3)

/-- `QMA^{𝓢₂}_1 = QMA^{𝓢₂}(1, 1/2)`. -/
def QMA1_S2 (P : PromiseProblem) : Prop := InQMAS2 P 1 (1 / 2)

/-- `L` is hard for a class `C` under promise-preserving reductions. -/
def HardFor (L : PromiseProblem) (C : PromiseProblem → Prop) : Prop :=
  ∀ P : PromiseProblem, C P → Nonempty (Reduction P L)

/-- `L` is QMA-complete. -/
def QMAComplete (L : PromiseProblem) : Prop := QMA L ∧ HardFor L QMA

/-- `L` is `QMA^{𝓢₂}_1`-complete. -/
def QMA1_S2Complete (L : PromiseProblem) : Prop := QMA1_S2 L ∧ HardFor L QMA1_S2

/-! ## Corollary 1.2: exact simulation of `𝓢₂` -/

/-- A gate set `S` (represented by the predicate "operator `E` is realisable exactly
over `S`, possibly with `|0⟩` ancillas that return to `|0⟩`") implements every gate of
`𝓢₂` exactly. -/
def SimulatesS2 (S : ∀ m : ℕ, ProofMat m → Prop) : Prop :=
  ∀ m (E : ProofMat m), (∃ h, IsDyadicMat h E) → S m E
/-! ## Corollary 1.6: relativisation to classical oracles -/

/-- A classical oracle access model, abstracted to the two class predicates it
induces. XOR-access oracles are its own inverse permutation, which is what preserves
the construction's arithmetic (Corollary 1.6 proof, p.11). -/
structure ClassicalOracle where
  QMAO : PromiseProblem → Prop
  QCMAO : PromiseProblem → Prop
  QMA1_S2O : PromiseProblem → Prop

/-! ## Theorem 1.1 and Lemma 3.1 (statements retired)

Theorem 1.1 (`QMA = QMA^{S2}_1`) and Lemma 3.1 (`QMA = QMA^{S2}(2/3, 1/3)`) require the
real-simulation transport, the constructive verifier of §3.3 assembled from
`lemma34_yes`/`lemma36_ratio`/`lemma37`, and parallel-repetition amplification; those
statements are preserved in the branch history of this file. The corollaries below record
the paper's *composition* content with the class equality as an explicit hypothesis. -/

/-- Corollary 1.2 (p.2), `QMA ⊆ QMAˢ₁` half: if `S` implements every `𝓢₂` gate exactly
and the Theorem 1.1 class equality holds (explicit hypothesis `h11`), then every `QMA`
problem has a perfect-completeness `S`-verifier with soundness `1/2`.

The reverse inclusion `QMAˢ₁ ⊆ QMA` needs amplification of the `(1, 1/2)` verifier to
`(2/3, 1/3)`; that step is not formalised here (Definition 2.1 discussion, p.6). -/
theorem cor12 (S : ∀ m : ℕ, ProofMat m → Prop) (hS : SimulatesS2 S)
    (h11 : ∀ P : PromiseProblem, QMA P ↔ QMA1_S2 P) :
    ∀ P : PromiseProblem, QMA P →
      ∃ V : Verifier P, V.Complete 1 ∧ V.Sound (1 / 2) ∧
        ∀ x, S (V.dim x) (V.accept x) := by
  intro P hQ
  obtain ⟨V, hc, hs, h, hd⟩ := (h11 P).mp hQ
  exact ⟨V, hc, hs, fun x => hS _ _ ⟨h, hd x⟩⟩

/-- Corollary 1.3 (p.2): quantum 3-SAT is QMA-complete. The Gosset–Nagaj completeness
(arXiv:1302.0290) enters as `hL`; Theorem 1.1's class equality enters as the explicit
hypothesis `h11`. -/
theorem cor13 (L : PromiseProblem) (hL : QMA1_S2Complete L)
    (h11 : ∀ P : PromiseProblem, QMA P ↔ QMA1_S2 P) : QMAComplete L := by
  obtain ⟨hmem, hhard⟩ := hL
  refine ⟨(h11 L).mpr hmem, ?_⟩
  intro P hP
  exact hhard P ((h11 P).mp hP)

/-- Corollary 1.4 (p.2): `XZ`-quantum 6-SAT is QMA-complete, by the same upgrade as
Corollary 1.3 (external `QMA^{𝓢₂}_1`-completeness as `hL`). -/
theorem cor14 (L : PromiseProblem) (hL : QMA1_S2Complete L)
    (h11 : ∀ P : PromiseProblem, QMA P ↔ QMA1_S2 P) : QMAComplete L :=
  cor13 L hL h11

/-- Corollary 1.5 (p.3): gapped clique homology is QMA-complete for weighted and
unweighted graphs (external completeness results as `hW`/`hU`; class equality as `h11`). -/
theorem cor15 (Hw Hu : PromiseProblem) (hW : QMA1_S2Complete Hw)
    (hU : QMA1_S2Complete Hu)
    (h11 : ∀ P : PromiseProblem, QMA P ↔ QMA1_S2 P) :
    QMAComplete Hw ∧ QMAComplete Hu :=
  ⟨cor13 Hw hW h11, cor13 Hu hU h11⟩

/-- Corollary 1.7 (p.3): a classical oracle separating `QCMA` from `QMA` (explicit
separation hypothesis `hsep`, cf. Bostanci–Haferkott–Nirkhe–Zhandry and
Bostanci–Huang–Vaikuntanathan) separates `QCMA` from `QMA^{𝓢₂,O}_1`, given the
relativised class equality of Corollary 1.6 as the explicit hypothesis `h16`.

Corollary 1.6 itself (the relativised circuit construction) is not formalised; its
statement is preserved in the branch history of this file. -/
theorem cor17 (O : ClassicalOracle) (h16 : ∀ P : PromiseProblem, O.QMAO P ↔ O.QMA1_S2O P)
    (hsep : (∀ P, O.QCMAO P → O.QMAO P) ∧ ¬ (∀ P, O.QMAO P → O.QCMAO P)) :
    (∀ P, O.QCMAO P → O.QMA1_S2O P) ∧ ¬ (∀ P, O.QMA1_S2O P → O.QCMAO P) := by
  obtain ⟨hsub, hnot⟩ := hsep
  refine ⟨fun P hP => (h16 P).mp (hsub P hP), ?_⟩
  intro hall
  exact hnot (fun P hP => hall P ((h16 P).mp hP))
end Qatlib.Papers.QMAPerfect26.MainResults
