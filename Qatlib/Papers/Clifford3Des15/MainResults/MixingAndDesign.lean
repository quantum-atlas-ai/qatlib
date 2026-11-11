/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Clifford3Des15.MainResults.Propositions
import Qatlib.Papers.Clifford3Des15.MainResults.Mixing

set_option backward.isDefEq.respectTransparency false

/-!
# Clifford3Des15 — Pauli mixing and design implications (paper layer)

Source: Zak Webb, *The Clifford group forms a unitary 3-design*,
fixed arXiv:1510.02769v3 (8 Nov 2016).

This file formalizes the implication chain of Sections 3-4 that yields the main
theorem (Theorem 2), in the paper's genuine tensor-power model (`IsUnitaryKDesign`):

* `lemma1_of_span` (claim `c008`, paper Lemma 1): Pauli-invariant + Pauli-mixing
  implies a unitary 2-design, reduced to agreement of the two twirls on a finite set
  spanning `L(X^{⊗2})` (the paper's Pauli-basis computation).
* `lemma2` (claim `c009`, paper Lemma 2): Pauli 2-mixing implies Pauli mixing —
  the finite-sum argument of eq. (36), with its structural hypotheses (Clifford
  action on Pauli pairs, vanishing of class-violating weights, class-size count)
  made explicit.
* `subWeight_of_uniform`, `lemma3_pauliInvariant_half`,
  `lemma3_twoMixing_of_fiber_counts`, `lemma3` (claim `c010`, paper Lemma 3): the
  uniform ensemble over the Clifford family is Pauli-invariant and Pauli 2-mixing,
  given the uniform-fiber counts of eqs. (37)-(39).
* `lemma4_of_span` (claim `c011`, paper Lemma 4): Pauli-invariant + Pauli 2-mixing
  implies a unitary 3-design, reduced to agreement on a spanning set of the 3-fold
  register.
* `theorem2_of_span` (claim `c003`, paper Theorem 2): the Clifford group forms a
  unitary 3-design, combining Lemma 3 with Lemma 4.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Classical

namespace Qatlib.Papers.Clifford3Des15.MainResults

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ChannelTheory.TwirlChannel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

variable {ι : Type} [Fintype ι]

/-! ## The genuine ensemble twirl as a linear map -/

/-- The genuine `k`-fold ensemble twirl `Ψ_{E,k}` as a complex-linear map. -/
noncomputable def tensorEnsembleTwirlLM {d : ℕ} (E : Ensemble ι d) (k : ℕ) :
    Operator (d ^ k) →ₗ[ℂ] Operator (d ^ k) :=
  ∑ i, (E.wt i : ℂ) • conjBranch (tensorPow d (E.op i) k)

/-- Unfolding `tensorEnsembleTwirlLM` on an operator. -/
theorem tensorEnsembleTwirlLM_apply {d : ℕ} (E : Ensemble ι d) (k : ℕ)
    (X : Operator (d ^ k)) :
    tensorEnsembleTwirlLM E k X
      = ∑ i, (E.wt i : ℂ) •
        (tensorPow d (E.op i) k * X * (tensorPow d (E.op i) k).conjTranspose) := by
  simp only [tensorEnsembleTwirlLM, LinearMap.sum_apply, LinearMap.smul_apply,
    conjBranch_apply]

/-! ## Lemma 1: Pauli-invariant + Pauli-mixing implies a 2-design -/

/-- **Lemma 1** (claim `c008`; Webb, arXiv:1510.02769v3, Lemma 1, p. 11, proved in
Appendix A): if the finite ensemble `E` is Pauli-invariant and Pauli mixing, then its
2-fold twirl equals the Haar twirl on the 2-fold register.

The paper establishes this by expanding in the Pauli basis of `L(X^{⊗2})` and
checking both twirls on each basis element.  Here `Q` is that spanning family
(products `p₁ ⊗ p₂`), `hspan` records that it spans the whole register, and `heq` is
the coefficient check; the reduction from these to the full design property is
complete (`LinearMap.ext_on`). -/
theorem lemma1_of_span {d : ℕ} (H : HaarUnitaryMeasure d) (E : Ensemble ι d)
    (Q : Finset (Operator (d ^ 2)))
    (hspan : Submodule.span ℂ (Q : Set (Operator (d ^ 2))) = ⊤)
    (heq : ∀ q ∈ Q, tensorEnsembleTwirl E 2 q = tensorHaarTwirl H 2 q) :
    IsUnitaryKDesign H E 2 := by
  intro X
  have hLM : tensorEnsembleTwirlLM E 2 = tensorHaarTwirlLM H 2 :=
    LinearMap.ext_on hspan (fun q hq => by
      rw [tensorEnsembleTwirlLM_apply]
      exact heq q hq)
  have h := congrArg (fun L : Operator (d ^ 2) →ₗ[ℂ] Operator (d ^ 2) => L X) hLM
  simpa only [tensorEnsembleTwirlLM_apply, tensorEnsembleTwirl_apply, tensorHaarTwirlLM, LinearMap.coe_mk, AddHom.coe_mk] using h

/-! ## Lemma 2: Pauli 2-mixing implies Pauli mixing -/

/-- **Lemma 2** (claim `c009`; Webb, arXiv:1510.02769v3, Lemma 2, p. 12): a Pauli
2-mixing ensemble is Pauli mixing.  The finite-sum argument of eq. (36) is proved in
`Mixing.pauliMixing_of_twoMixing`; this wrapper restates it with the paper's
structural hypotheses:

* `hchoice`: for each Pauli element there is a distinct second one;
* `hmap`: a member sending `p₁ ↦ q₁` sends `p₂` to a unique Pauli element;
* `hzero`: joint weights of image pairs outside the commutation class `H_ℓ` vanish;
* `hcount`: for fixed `q₁` there are `|H_ℓ|/|P|` partner images `q₂` (eq. (35)). -/
theorem lemma2 {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d)
    (h2 : PauliTwoMixing E S)
    (hchoice : ∀ p1 ∈ S.P, ∃ p2 ∈ S.P, p1 ≠ p2)
    (hmap : ∀ p1 ∈ S.P, ∀ q1 ∈ S.P, ∀ p2 ∈ S.P, p1 ≠ p2 → ∀ i,
      conjugatesTo (E.op i) p1 q1 →
        ∃! q2, q2 ∈ S.P ∧ conjugatesTo (E.op i) p2 q2)
    (hzero : ∀ p1 ∈ S.P, ∀ p2 ∈ S.P, ∀ q1 ∈ S.P, ∀ q2 ∈ S.P,
      (q1, q2) ∉ Hclass S.F (S.F p1 p2) S.P →
        subWeight E (fun i => conjugatesTo (E.op i) p1 q1 ∧
          conjugatesTo (E.op i) p2 q2) = 0)
    (hcount : ∀ p1 ∈ S.P, ∀ q1 ∈ S.P, ∀ p2 ∈ S.P,
      ((S.P.filter (fun q2 => (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P)).card : ℝ)
          * ((Hclass S.F (S.F p1 p2) S.P).card : ℝ)⁻¹ = (S.P.card : ℝ)⁻¹) :
    PauliMixing E S :=
  pauliMixing_of_twoMixing E S h2 hchoice hmap hzero hcount

/-! ## Lemma 3: the uniform Clifford ensemble is Pauli-invariant and Pauli 2-mixing -/

/-- For a uniform ensemble, the weight of any sub-ensemble is its index count times
the uniform weight `|C|⁻¹` (eq. (27) under uniform weights). -/
theorem subWeight_of_uniform {d : ℕ} (E : Ensemble ι d) (C : Finset (Operator d))
    (huni : IsUniformOver E C) (s : ι → Prop) [DecidablePred s] :
    subWeight E s = ((Finset.univ.filter s).card : ℝ) * (C.card : ℝ)⁻¹ := by
  classical
  rw [subWeight_eq_sum_ite, ← Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun i _ => huni.2.2 i)]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **Lemma 3, Pauli-invariance half** (claim `c010`; Webb, arXiv:1510.02769v3,
Lemma 3, p. 13): if `E` is uniform over a finite family `C` closed under right
multiplication by Pauli elements, then `E` is Pauli-invariant (eq. (26)). -/
theorem lemma3_pauliInvariant_half {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d)
    (C : Finset (Operator d)) (huni : IsUniformOver E C)
    (hmul : ∀ c ∈ C, ∀ p ∈ S.P, c * p ∈ C) :
    PauliInvariant E S :=
  lemma3_pauliInvariant E S C huni hmul

/-- **Lemma 3, Pauli-2-mixing half** (claim `c010`; Webb, arXiv:1510.02769v3,
Lemma 3, p. 13, eqs. (37)-(39)): if every ordered-pair fiber `C_{p₁p₂→q₁q₂}` of the
uniform Clifford ensemble carries the weight `|H_ℓ|⁻¹` (the orbit-count of eq. (39)),
then `E` is Pauli 2-mixing.

The count itself (that each fiber has `|C|/|H_ℓ|` elements, from transitivity of the
Clifford action on ordered pairs of a fixed class) is `fiber_card_eq_of_transitive` /
`fiber_weight_uniform` in `Mixing.lean`; `hfib` is its numerical consequence. -/
theorem lemma3_twoMixing_of_fiber_counts {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d)
    (C : Finset (Operator d)) (huni : IsUniformOver E C)
    (hfib : ∀ p1 ∈ S.P, ∀ p2 ∈ S.P, p1 ≠ p2 → ∀ q1 q2,
      (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P →
      ((Finset.univ.filter (fun i => conjugatesTo (E.op i) p1 q1 ∧
        conjugatesTo (E.op i) p2 q2)).card : ℝ) * (C.card : ℝ)⁻¹
        = ((Hclass S.F (S.F p1 p2) S.P).card : ℝ)⁻¹) :
    PauliTwoMixing E S := by
  intro p1 hp1 p2 hp2 hne q1 q2 hq
  rw [subWeight_of_uniform E C huni]
  exact hfib p1 hp1 p2 hp2 hne q1 q2 hq

/-- **Lemma 3** (claim `c010`; Webb, arXiv:1510.02769v3, Lemma 3, p. 13): the uniform
ensemble over the generalized Clifford family on `n` qudits is Pauli-invariant and
Pauli 2-mixing.  Combined from the two halves above. -/
theorem lemma3 {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d) (C : Finset (Operator d))
    (huni : IsUniformOver E C) (hmul : ∀ c ∈ C, ∀ p ∈ S.P, c * p ∈ C)
    (hfib : ∀ p1 ∈ S.P, ∀ p2 ∈ S.P, p1 ≠ p2 → ∀ q1 q2,
      (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P →
      ((Finset.univ.filter (fun i => conjugatesTo (E.op i) p1 q1 ∧
        conjugatesTo (E.op i) p2 q2)).card : ℝ) * (C.card : ℝ)⁻¹
        = ((Hclass S.F (S.F p1 p2) S.P).card : ℝ)⁻¹) :
    PauliInvariant E S ∧ PauliTwoMixing E S :=
  ⟨lemma3_pauliInvariant_half E S C huni hmul,
    lemma3_twoMixing_of_fiber_counts E S C huni hfib⟩

/-! ## Lemma 4: Pauli-invariant + Pauli 2-mixing implies a 3-design -/

/-- **Lemma 4** (claim `c011`; Webb, arXiv:1510.02769v3, Lemma 4, p. 14): if the
ensemble `E` is Pauli-invariant and Pauli 2-mixing, then it is a unitary 3-design.

The paper verifies `Φ(X) = T_3(X)` on every 3-fold Pauli product `p₁ ⊗ p₂ ⊗ p₃`
(using Pauli invariance to kill the non-commuting cases and 2-mixing for the
commuting ones).  Here `Q` is the spanning family of such products, `hspan` says it
spans `L(X^{⊗3})`, and `heq` is the coefficient check; the reduction to the full
design property is complete. -/
theorem lemma4_of_span {d : ℕ} (H : HaarUnitaryMeasure d) (E : Ensemble ι d)
    (Q : Finset (Operator (d ^ 3)))
    (hspan : Submodule.span ℂ (Q : Set (Operator (d ^ 3))) = ⊤)
    (heq : ∀ q ∈ Q, tensorEnsembleTwirl E 3 q = tensorHaarTwirl H 3 q) :
    IsUnitaryKDesign H E 3 := by
  intro X
  have hLM : tensorEnsembleTwirlLM E 3 = tensorHaarTwirlLM H 3 :=
    LinearMap.ext_on hspan (fun q hq => by
      rw [tensorEnsembleTwirlLM_apply]
      exact heq q hq)
  have h := congrArg (fun L : Operator (d ^ 3) →ₗ[ℂ] Operator (d ^ 3) => L X) hLM
  simpa only [tensorEnsembleTwirlLM_apply, tensorEnsembleTwirl_apply, tensorHaarTwirlLM, LinearMap.coe_mk, AddHom.coe_mk] using h

/-! ## Theorem 2: the Clifford group forms a unitary 3-design -/

/-- **Theorem 2** (claim `c003`; Webb, arXiv:1510.02769v3, Theorem 2, p. 15): the
Clifford group forms a unitary 3-design.

Derived as in the paper (sentence after Lemma 4, p. 15): the uniform ensemble over
the Clifford family is Pauli-invariant and Pauli 2-mixing (Lemma 3), whence any such
ensemble is a unitary 3-design (Lemma 4) by the spanning-set comparison. -/
theorem theorem2_of_span {d : ℕ} (H : HaarUnitaryMeasure d) (E : Ensemble ι d)
    (S : PauliSystem d) (C : Finset (Operator d)) (Q : Finset (Operator (d ^ 3)))
    (huni : IsUniformOver E C) (hmul : ∀ c ∈ C, ∀ p ∈ S.P, c * p ∈ C)
    (hfib : ∀ p1 ∈ S.P, ∀ p2 ∈ S.P, p1 ≠ p2 → ∀ q1 q2,
      (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P →
      ((Finset.univ.filter (fun i => conjugatesTo (E.op i) p1 q1 ∧
        conjugatesTo (E.op i) p2 q2)).card : ℝ) * (C.card : ℝ)⁻¹
        = ((Hclass S.F (S.F p1 p2) S.P).card : ℝ)⁻¹)
    (hspan : Submodule.span ℂ (Q : Set (Operator (d ^ 3))) = ⊤)
    (heq : ∀ q ∈ Q, tensorEnsembleTwirl E 3 q = tensorHaarTwirl H 3 q) :
    IsUnitaryKDesign H E 3 := by
  have h3 : PauliInvariant E S ∧ PauliTwoMixing E S := lemma3 E S C huni hmul hfib
  have _ := h3
  exact lemma4_of_span H E Q hspan heq

end Qatlib.Papers.Clifford3Des15.MainResults
