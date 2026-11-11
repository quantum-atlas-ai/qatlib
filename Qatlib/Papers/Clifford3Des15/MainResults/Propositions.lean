/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Clifford3Des15.MainResults.Tensor

set_option backward.isDefEq.respectTransparency false

/-!
# Clifford3Des15 — Section 2 propositions (paper layer)

Source: Zak Webb, *The Clifford group forms a unitary 3-design*,
fixed arXiv:1510.02769v3 (8 Nov 2016).

This file formalizes the three propositions of Section 2:

* `proposition1` (claim `c005`, paper Proposition 1): the Haar `k`-fold twirl `T_k`
  is a projection onto the fixed points of every finite ensemble twirl,
  `T_k(X) = T_k(Ψ_{E,k}(X))`.  The paper's own tensor-power version is
  `proposition1_tensor` in `Tensor.lean`.
* `proposition2` (claim `c006`, paper Proposition 2): the permutation operators
  `W_π` are fixed by the `k`-fold twirl, `T_k(W_π) = W_π`.  The genuine tensor-power
  version is `proposition2_tensor` in `Tensor.lean`.
* `proposition3` (claim `c007`, paper Proposition 3): `T_k(X)` expands as a linear
  combination of permutation operators `∑_π α_π(X) W_π`, reduced here to the
  double-commutant span statement of the paper's Theorem 1.

`haarTwirlLM` packages the Haar twirl as a complex-linear map; it is the object used
in the linear-algebra reductions of Lemmas 1 and 4 (`MixingAndDesign.lean`).
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

/-! ## Proposition 1 (claim c005) — `T_k` is a projection onto the twirl's fixed points -/

/-- **Proposition 1** (claim `c005`; Webb, arXiv:1510.02769v3, Proposition 1, p. 8):
for every finite unitary ensemble `E` and every `X`, the Haar `k`-fold twirl
`T_k = HaarTwirl H` satisfies `T_k(X) = T_k(Ψ_{E,k}(X))`.

Here `X` is an operator of the register `L(X^{⊗k})` (dimension `d`), `E` is the
finite ensemble on that register, and `Ψ_{E,k} = ensembleTwirl E`.  The proof pushes
`T_k` through the weighted average (linearity) and uses that each `U X U†` has the
same `T_k`-image as `X` (Haar unitary-invariance). -/
theorem proposition1 {d : ℕ} (H : HaarUnitaryMeasure d) (E : Ensemble ι d)
    (X : Operator d) :
    HaarTwirl H X = HaarTwirl H (ensembleTwirl E X) := by
  rw [ensembleTwirl_apply]
  -- Linearity: `T_k(∑ i, α_i • U_i X U_i†) = ∑ i, α_i • T_k(U_i X U_i†)`.
  rw [show HaarTwirl H (∑ i, (E.wt i : ℂ) • (E.op i * X * (E.op i).conjTranspose))
        = ∑ i, (E.wt i : ℂ) • HaarTwirl H (E.op i * X * (E.op i).conjTranspose) from by
      simpa using haarTwirl_finset_sum H (Finset.univ : Finset ι)
        (fun i => (E.wt i : ℂ)) (fun i => E.op i * X * (E.op i).conjTranspose)]
  -- Each conjugated summand has the same `T_k`-image as `X`.
  have hinv : ∀ i : ι,
      HaarTwirl H (E.op i * X * (E.op i).conjTranspose) = HaarTwirl H X :=
    fun i => haarTwirl_conj_invariant H (E.op i) X (E.op_unitary i)
  simp only [hinv]
  -- `∑ i, α_i • T_k(X) = (∑ i, α_i) • T_k(X) = 1 • T_k(X) = T_k(X)`.
  rw [← Finset.sum_smul]
  have hw : (∑ i, (E.wt i : ℂ)) = 1 := by
    have h1 : ((∑ i, E.wt i : ℝ) : ℂ) = 1 := by rw [E.wt_sum_one]; norm_num
    rw [← h1]; push_cast; ring
  rw [hw, one_smul]

/-! ## Proposition 2 (claim c006) — permutation operators are twirl fixed points -/

/-- **Proposition 2** (claim `c006`; Webb, arXiv:1510.02769v3, Proposition 2, p. 8):
the permutation operator `W_π ∈ L(X^{⊗k})` satisfies `T_k(W_π) = W_π`.

We state the `k`-fold twirl abstractly as the uniform finite-family twirl
`FamilyTwirl V` where `V` ranges over the (tensor-power) unitaries `U^{⊗k}` of the
ensemble; the hypothesis `hcomm` is exactly eq. (9)'s tensor-power commutation
`U^{⊗k} · W_π = W_π · U^{⊗k}`.  Under `hcomm` each conjugated summand reduces to
`W_π`, and the weights sum to one, giving the fixed-point identity.

The genuine tensor-power version (with `T_k` the average over the base space and
`hcomm` discharged by `permOp_commute_tensorPow`) is `proposition2_tensor`. -/
theorem proposition2 {J : Type} [Fintype J] [Nonempty J] {D : ℕ}
    (V : J → Operator D) (hV : ∀ j, IsUnitaryMatrix (V j))
    (W : Operator D) (hcomm : ∀ j, V j * W = W * V j) :
    FamilyTwirl V W = W := by
  rw [familyTwirl_apply]
  have hterm : ∀ j : J, V j * W * (V j).conjTranspose = W := by
    intro j
    calc V j * W * (V j).conjTranspose
        = W * V j * (V j).conjTranspose := by rw [hcomm j]
      _ = W * (V j * (V j).conjTranspose) := by rw [Matrix.mul_assoc]
      _ = W * 1 := by rw [(hV j).2]
      _ = W := by rw [Matrix.mul_one]
  have hsum : (∑ j : J, V j * W * (V j).conjTranspose) = (Fintype.card J : ℂ) • W := by
    simp only [hterm]
    exact sum_const_card_smul W
  rw [hsum, smul_smul]
  have hc : (Fintype.card J : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr inferInstance
    have hne : Fintype.card J ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    exact_mod_cast hne
  rw [inv_mul_cancel₀ hc, one_smul]

/-! ## Proposition 3 (claim c007) — expansion in permutation operators -/

/-- **Proposition 3** (claim `c007`; Webb, arXiv:1510.02769v3, Proposition 3, p. 9,
equation (24)): for every `X ∈ L(X^{⊗k})`, `T_k(X)` is a complex linear combination
of the permutation operators `W_π = permOp d k π`, `π ∈ S_k`.

The hypothesis `hspan` is the paper's Theorem 1 (double commutant / Wedderburn): the
commutant of the tensor-power unitary action is spanned by the permutation operators.
The paper obtains `T_k(X) ∈` commutant from Haar invariance; that step is
`proposition3_of_commutant_span` in `Core.lean`, whose tensor-power form is
`proposition3_tensor_of_commutant_span` in `Tensor.lean`. -/
theorem proposition3 {d k : ℕ} (H : HaarUnitaryMeasure (d ^ k)) (X : Operator (d ^ k))
    (hspan : ∀ T : Operator (d ^ k),
      (∀ A : Operator (d ^ k), IsUnitaryMatrix A → A * T * A.conjTranspose = T) →
      T ∈ Submodule.span ℂ (Set.range (permOp d k))) :
    ∃ α : Equiv.Perm (Fin k) → ℂ,
      HaarTwirl H X = ∑ π : Equiv.Perm (Fin k), α π • permOp d k π :=
  proposition3_of_commutant_span H X hspan

/-! ## The Haar twirl as a linear map -/

/-- The Haar twirl `T_k` as a complex-linear map (linearity from
`haarTwirl_add`/`haarTwirl_smul`). -/
def haarTwirlLM {D : ℕ} (H : HaarUnitaryMeasure D) : Operator D →ₗ[ℂ] Operator D where
  toFun := HaarTwirl H
  map_add' := haarTwirl_add H
  map_smul' := haarTwirl_smul H

/-- The genuine `k`-fold twirl `T_k` as a complex-linear map. -/
def tensorHaarTwirlLM {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ) :
    Operator (d ^ k) →ₗ[ℂ] Operator (d ^ k) where
  toFun := tensorHaarTwirl H k
  map_add' := tensorHaarTwirl_add H k
  map_smul' := tensorHaarTwirl_smul H k

end Qatlib.Papers.Clifford3Des15.MainResults
