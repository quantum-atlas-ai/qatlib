/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationCommBound

/-!
# Qudit branch marginals and outcome counts

The lemmas establish linearity and positivity of `qdBranchMarginal`, and expand pure-resource
branches into row Kraus operators `qdRowKraus`. Perfect recovery with unitary corrections forces
each corrected row Kraus operator to be scalar.

These identities yield `qdCard_le_of_perfect`, bounding the number of outcomes below by `n²`,
together with communication bounds for single and composite qudit systems. These results develop
resource and communication properties of teleportation [BennettEtAl1993Teleportation].

## Main statements

* `qdBranchMarginal_outerProduct_kraus`: For a pure resource, the branch marginal is the sum of
  conjugation branches associated with all row Kraus operators.
* `qdRowKraus_scalar`: In nonzero dimension, perfect teleportation of a pure resource with
  unitary corrections makes every corrected row Kraus operator a scalar multiple of the
  identity.
* `qdCard_le_of_perfect`: In nonzero dimension, perfect teleportation with a pure resource and
  unitary corrections requires at least `n²` outcomes [BennettEtAl1993Teleportation].
* `clause4_clause2`: Perfect teleportation with a normalized pure resource and unitary
  corrections gives outcome and bit-count bounds, and message consistency forces equal
  conjugation maps for equal messages [BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped ComplexOrder

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel
open Matrix
open scoped BigOperators ComplexOrder

/-- The inverse Bob-first register equivalence sends `(i, finProdFinEquiv x)` to `(x, i)`. -/
private theorem qdBobFirst_symm_apply {n : ℕ} (i : Fin n) (x : Fin n × Fin n) :
    (qdBobFirstEquiv n).symm (i, finProdFinEquiv x) = (x, i) := by
  have h : qdBobFirstEquiv n (x, i) = (i, finProdFinEquiv x) := rfl
  rw [← h]
  exact (qdBobFirstEquiv n).symm_apply_apply _

/-- The Bob-first partial trace has entry `(i, j)` equal to the sum of `X (x, i) (x, j)` over
Alice's register pair. -/
private theorem qdBobFirst_sum {n : ℕ}
    (X : Matrix ((Fin n × Fin n) × Fin n) ((Fin n × Fin n) × Fin n) ℂ) (i j : Fin n) :
    PartialTrace (relabelGate (qdBobFirstEquiv n) X) i j
      = ∑ x : Fin n × Fin n, X (x, i) (x, j) := by
  simp only [PartialTrace, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [← (finProdFinEquiv (m := n) (n := n)).sum_comp]
  simp only [qdBobFirst_symm_apply]

/-- Complex conjugation distributes through a conditional expression. -/
private theorem star_ite' {c : Prop} [Decidable c] (a b : ℂ) :
    star (if c then a else b) = if c then star a else star b := by
  by_cases hc : c <;> simp [hc]

/-- An entry of `qdBranchMarginal` expands as the finite sum of the measurement, input,
resource, and conjugate-measurement entries. -/
theorem qdBranchMarginal_apply {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ : Operator n) (i j : Fin n) :
    qdBranchMarginal K ω ρ i j =
      ∑ x : Fin n, ∑ x_1 : Fin n, ∑ x_2 : Fin n, ∑ x_3 : Fin n,
        (∑ x_4 : Fin n, ∑ x_5 : Fin n,
          K (x, x_1) (x_4, x_5) * (ρ x_4 x_2 * ω (x_5, i) (x_3, j)))
          * star (K (x, x_1) (x_2, x_3)) := by
  have h0 : qdBranchMarginal K ω ρ =
      PartialTrace (relabelGate (qdBobFirstEquiv n)
        (TensorGate K (1 : Operator n) *
          relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm (TensorGate ρ ω) *
          (TensorGate K (1 : Operator n)).conjTranspose)) := rfl
  rw [h0, qdBobFirst_sum]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [tensorGate_apply, Matrix.one_apply, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Equiv.prodAssoc_apply]
  simp only [mul_ite, mul_one, mul_zero, star_ite', star_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The branch marginal is additive in its input operator. -/
theorem qdBranchMarginal_add {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (A B : Operator n) :
    qdBranchMarginal K ω (A + B)
      = qdBranchMarginal K ω A + qdBranchMarginal K ω B := by
  simp only [qdBranchMarginal, TensorGate, Matrix.add_kronecker, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_add, Pi.add_apply,
    Matrix.mul_add, Matrix.add_mul, partialTrace_add]

/-- The branch marginal commutes with complex scalar multiplication of its input operator. -/
theorem qdBranchMarginal_smul {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (c : ℂ) (A : Operator n) :
    qdBranchMarginal K ω (c • A) = c • qdBranchMarginal K ω A := by
  simp only [qdBranchMarginal, TensorGate, Matrix.smul_kronecker, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_smul, Pi.smul_apply,
    Matrix.mul_smul, Matrix.smul_mul, partialTrace_smul]

/-- A positive semidefinite resource and positive semidefinite input produce a positive
semidefinite branch marginal. -/
theorem qdBranchMarginal_positive {n : ℕ}
    (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (ρ : Operator n) (hρ : ρ.PosSemidef) :
    (qdBranchMarginal K ω ρ).PosSemidef := by
  apply partialTrace_posSemidef
  apply converse_relabel_positive
  have hj := converse_relabel_positive (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm _
    (Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hρ hω)
  simpa only [Matrix.conjTranspose_conjTranspose] using
    hj.conjTranspose_mul_mul_same (TensorGate K (1 : Operator n))ᴴ

/-- Conjugating a branch marginal by `U` preserves additivity in the input operator. -/
theorem qdCorrectedBranch_add {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (U : Operator n) (A B : Operator n) :
    U * qdBranchMarginal K ω (A + B) * U.conjTranspose
      = U * qdBranchMarginal K ω A * U.conjTranspose
        + U * qdBranchMarginal K ω B * U.conjTranspose := by
  rw [qdBranchMarginal_add, Matrix.mul_add, Matrix.add_mul]

/-- Conjugating a branch marginal by `U` preserves compatibility with complex scalar
multiplication of the input. -/
theorem qdCorrectedBranch_smul {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (U : Operator n) (c : ℂ) (A : Operator n) :
    U * qdBranchMarginal K ω (c • A) * U.conjTranspose
      = c • (U * qdBranchMarginal K ω A * U.conjTranspose) := by
  rw [qdBranchMarginal_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- Conjugating the branch marginal of a positive semidefinite resource and input by any matrix
`U` preserves positive semidefiniteness. -/
theorem qdCorrectedBranch_positive {n : ℕ}
    (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (U : Operator n) (ρ : Operator n) (hρ : ρ.PosSemidef) :
    (U * qdBranchMarginal K ω ρ * U.conjTranspose).PosSemidef := by
  have h := (qdBranchMarginal_positive K ω hω ρ hρ).conjTranspose_mul_mul_same U.conjTranspose
  simpa only [Matrix.conjTranspose_conjTranspose] using h

/-- Multiplication by `outerProduct φ` sends `v` to `(star φ ⬝ᵥ v) • φ`. -/
private theorem outerProduct_mulVec {I : Type} [Fintype I] [DecidableEq I] (φ : QState I)
    (v : I → ℂ) : outerProduct φ *ᵥ v = (star φ ⬝ᵥ v) • φ := by
  ext i
  simp only [Matrix.mulVec, dotProduct, outerProduct_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_assoc, ← Finset.mul_sum]
  exact mul_comm _ _

/-- If both `A` and `outerProduct φ - A` are positive semidefinite, then `A` is a complex scalar
multiple of `outerProduct φ`. -/
theorem psd_le_outerProduct {I : Type} [Fintype I] [DecidableEq I] (φ : QState I)
    (A : Matrix I I ℂ) (hA : A.PosSemidef) (hB : (outerProduct φ - A).PosSemidef) :
    ∃ c : ℂ, A = c • outerProduct φ := by
  have hker : ∀ v : I → ℂ, star φ ⬝ᵥ v = 0 → A *ᵥ v = 0 := by
    intro v hv
    have hAB : (star v ⬝ᵥ ((outerProduct φ - A) *ᵥ v)).re = -(star v ⬝ᵥ (A *ᵥ v)).re := by
      rw [Matrix.sub_mulVec, outerProduct_mulVec, hv, zero_smul, zero_sub]
      simp only [dotProduct, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      exact Complex.neg_re _
    have hB0 : 0 ≤ (star v ⬝ᵥ ((outerProduct φ - A) *ᵥ v)).re :=
      (Complex.nonneg_iff.mp (hB.dotProduct_mulVec_nonneg v)).1
    have hA0 : 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re :=
      (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1
    have hre : (star v ⬝ᵥ (A *ᵥ v)).re = 0 := by linarith
    have him : (star v ⬝ᵥ (A *ᵥ v)).im = 0 :=
      ((Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).2).symm
    have hz : star v ⬝ᵥ (A *ᵥ v) = 0 := by
      apply Complex.ext <;> simp [hre, him]
    exact hA.dotProduct_mulVec_zero_iff.mp hz
  have hpar : ∀ i j k : I, star (φ j) * A k i = star (φ i) * A k j := by
    intro i j k
    have hv : star φ ⬝ᵥ (star (φ j) • Qatlib.Foundations.PureStateMath.Ket i - star (φ i) • Qatlib.Foundations.PureStateMath.Ket j) = 0 := by
      simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Qatlib.Foundations.PureStateMath.Ket,
        mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      show star (φ i) * star (φ j) - star (φ j) * star (φ i) = 0
      ring
    have h0 := congrFun (hker _ hv) k
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Qatlib.Foundations.PureStateMath.Ket, Pi.zero_apply, mul_sub, Finset.sum_sub_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h0
    have h1 : A k i * star (φ j) = A k j * star (φ i) := sub_eq_zero.mp h0
    exact (mul_comm _ _).trans (h1.trans (mul_comm _ _))
  by_cases hz : ∀ i : I, φ i = 0
  · refine ⟨0, ?_⟩
    have hA0 : ∀ i j : I, A i j = 0 := by
      intro i j
      have h := congrFun (hker (Qatlib.Foundations.PureStateMath.Ket j) (by
        simp only [dotProduct]
        exact Finset.sum_eq_zero fun k _ => by simp [hz])) i
      simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, Pi.zero_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      exact h
    ext i j
    simp [hA0]
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hz
    have hi₀s : star (φ i₀) ≠ 0 := by
      intro h
      have h' := congrArg star h
      simp only [star_star, star_zero] at h'
      exact hi₀ h'
    have hn0 : φ i₀ * star (φ i₀) ≠ 0 := mul_ne_zero hi₀ hi₀s
    have hherm : ∀ a b : I, A a b = star (A b a) := by
      intro a b
      have h := congrArg (fun M : Matrix I I ℂ => M a b) hA.1.eq
      simp only [Matrix.conjTranspose_apply] at h
      exact h.symm
    have hdiag : star (A i₀ i₀) = A i₀ i₀ := (hherm i₀ i₀).symm
    refine ⟨A i₀ i₀ / (φ i₀ * star (φ i₀)), ?_⟩
    ext k j
    have e1 : star (φ j) * A k i₀ = star (φ i₀) * A k j := hpar i₀ j k
    have e2 : star (φ i₀) * A i₀ k = star (φ k) * A i₀ i₀ := hpar k i₀ i₀
    have eQ : A k i₀ * φ i₀ = A i₀ i₀ * φ k := by
      have hs := congrArg star e2
      simp only [star_mul, star_star] at hs
      rw [hdiag] at hs
      rw [hherm k i₀]
      exact hs
    have eP : A k j * (φ i₀ * star (φ i₀)) = A i₀ i₀ * φ k * star (φ j) := by
      have h := congrArg (fun z : ℂ => z * φ i₀) e1
      simp only [mul_assoc] at h
      rw [eQ] at h
      simp only [mul_assoc, mul_comm] at h
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h.symm
    have hfinal : A k j = A i₀ i₀ / (φ i₀ * star (φ i₀)) * φ k * star (φ j) := by
      have h := congrArg (fun z : ℂ => z / (φ i₀ * star (φ i₀))) eP
      simp only [mul_assoc] at h
      rw [mul_div_cancel_right₀ _ hn0] at h
      field_simp [hn0] at h ⊢
      ring_nf at h ⊢
      exact h
    rw [hfinal]
    simp only [Matrix.smul_apply, smul_eq_mul, outerProduct_apply]
    exact mul_assoc _ _ _

/-- In a perfect protocol with unitary corrections and a positive semidefinite resource, each
corrected branch on a pure input is a scalar multiple of that input's outer product. -/
theorem qdBranch_parallel {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hω : ω.PosSemidef) (hperf : QdLoccPerfect P ω)
    (k : κ) (φ : QState (Fin n)) :
    ∃ c : ℂ,
      U k * qdBranchMarginal (P.kraus k) ω (outerProduct φ) * (U k).conjTranspose
        = c • outerProduct φ := by
  classical
  let A : κ → Operator n := fun j =>
    U j * qdBranchMarginal (P.kraus j) ω (outerProduct φ) * (U j).conjTranspose
  have hsum : ∑ j, A j = outerProduct φ := by
    have h := hperf (outerProduct φ)
    have hkey : (∑ j, P.corr j (qdBranchMarginal (P.kraus j) ω (outerProduct φ))) = ∑ j, A j :=
      Finset.sum_congr rfl (fun j _ => hU.2 j _)
    exact hkey.symm.trans h
  have hpos : ∀ j, (A j).PosSemidef := fun j =>
    qdCorrectedBranch_positive (P.kraus j) ω hω (U j) (outerProduct φ)
      (outerProduct_posSemidef φ)
  have hrest : (outerProduct φ - A k).PosSemidef := by
    have h := Matrix.posSemidef_sum (Finset.univ.erase k) (fun j _ => hpos j)
    have he : ∑ j ∈ Finset.univ.erase k, A j = outerProduct φ - A k := by
      have h1 : (∑ j ∈ Finset.univ.erase k, A j) + A k = outerProduct φ := by
        rw [Finset.sum_erase_add (s := Finset.univ) (f := A) (a := k) (Finset.mem_univ k), hsum]
      calc ∑ j ∈ Finset.univ.erase k, A j
          = (∑ j ∈ Finset.univ.erase k, A j) + A k - A k := by abel
        _ = outerProduct φ - A k := by rw [h1]
    rw [← he]
    exact h
  exact psd_le_outerProduct φ (A k) (hpos k) hrest
open Matrix
open scoped BigOperators ComplexOrder
open scoped BigOperators

/-- The coefficient matrix of a bipartite vector, with entry `(i, a)` equal to `v (a, i)`. -/
noncomputable def qdMatW {n : ℕ} (v : Fin n × Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i a => v (a, i)

/-- The matrix obtained from row `u` of `K`, with entry `(a, c)` equal to `K u (c, a)`. -/
noncomputable def qdMatA {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (u : Fin n × Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun a c => K u (c, a)

/-- The row Kraus operator `qdMatW Ψ * qdMatA K u` associated with resource vector `Ψ` and
measurement row `u`. -/
noncomputable def qdRowKraus {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (Ψ : QState (Fin n × Fin n)) (u : Fin n × Fin n) : Operator n :=
  qdMatW Ψ * qdMatA K u

/-- Reordering the complex factors in a pure-resource branch summand puts the resource
amplitudes next to the corresponding measurement entries. -/
private theorem qd_ac1 {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (Ψ : QState (Fin n × Fin n)) (ρ : Operator n) (i j x x1 x2 x3 x4 x5 : Fin n) :
    K (x, x1) (x4, x5) * (ρ x4 x2 * (Ψ (x5, i) * (starRingEnd ℂ) (Ψ (x3, j))))
        * star (K (x, x1) (x2, x3))
      = Ψ (x5, i) * K (x, x1) (x4, x5) * ρ x4 x2
          * (star (K (x, x1) (x2, x3)) * star (Ψ (x3, j))) := by
  have h : (starRingEnd ℂ) (Ψ (x3, j)) = star (Ψ (x3, j)) := rfl
  rw [h]
  ac_rfl

/-- The six-index complex sum expressing entry `(i, j)` of a pure-resource branch marginal in
row Kraus form. -/
private noncomputable def qdMaster {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (Ψ : QState (Fin n × Fin n)) (ρ : Operator n) (i j : Fin n) : ℂ :=
  ∑ x : Fin n, ∑ x1 : Fin n, ∑ x2 : Fin n, ∑ x3 : Fin n, ∑ x4 : Fin n, ∑ x5 : Fin n,
    Ψ (x5, i) * K (x, x1) (x4, x5) * ρ x4 x2
      * (star (K (x, x1) (x2, x3)) * star (Ψ (x3, j)))

/-- For a pure resource, the branch marginal is the sum of conjugation branches associated with
all row Kraus operators. -/
theorem qdBranchMarginal_outerProduct_kraus {n : ℕ}
    (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (Ψ : QState (Fin n × Fin n))
    (ρ : Operator n) :
    qdBranchMarginal K (outerProduct Ψ) ρ =
      ∑ u : Fin n × Fin n, conjBranch (qdRowKraus K Ψ u) ρ := by
  classical
  have hpt : ∀ i j : Fin n,
      qdBranchMarginal K (outerProduct Ψ) ρ i j =
        (∑ u : Fin n × Fin n, conjBranch (qdRowKraus K Ψ u) ρ) i j := by
    intro i j
    have hL : qdBranchMarginal K (outerProduct Ψ) ρ i j = qdMaster K Ψ ρ i j := by
      rw [qdBranchMarginal_apply]
      simp only [outerProduct_apply, Finset.sum_mul, qd_ac1]
      rfl
    have hR : (∑ u : Fin n × Fin n, conjBranch (qdRowKraus K Ψ u) ρ) i j
        = qdMaster K Ψ ρ i j := by
      have he : ∀ u : Fin n × Fin n,
          conjBranch (qdRowKraus K Ψ u) ρ i j =
            ∑ x2 : Fin n, ∑ x3 : Fin n, ∑ x4 : Fin n, ∑ x5 : Fin n,
              Ψ (x5, i) * K u (x4, x5) * ρ x4 x2
                * (star (K u (x2, x3)) * star (Ψ (x3, j))) := by
        intro u
        simp only [conjBranch_apply, qdRowKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
          qdMatW, qdMatA, star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Matrix.sum_apply]
      simp only [he]
      rw [Fintype.sum_prod_type]
      rfl
    rw [hL, hR]
  ext i j
  exact hpt i j

/-- In nonzero dimension, perfect teleportation of a pure resource with unitary corrections
makes every corrected row Kraus operator a scalar multiple of the identity. -/
theorem qdRowKraus_scalar {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (Ψ : QState (Fin n × Fin n))
    (hperf : QdLoccPerfect P (outerProduct Ψ)) :
    ∀ (k : κ) (u : Fin n × Fin n),
      ∃ z : ℂ, U k * qdRowKraus (P.kraus k) Ψ u = z • (1 : Operator n) := by
  classical
  set A : κ × (Fin n × Fin n) → Operator n :=
    fun w => U w.1 * qdRowKraus (P.kraus w.1) Ψ w.2
  have hsum : ∀ ρ : Operator n,
      (∑ w : κ × (Fin n × Fin n), conjBranch (A w) ρ) = ρ := by
    intro ρ
    rw [Fintype.sum_prod_type]
    show (∑ k : κ, ∑ u : Fin n × Fin n,
        conjBranch (U k * qdRowKraus (P.kraus k) Ψ u) ρ) = ρ
    have h2 : ∀ k : κ,
        (∑ u : Fin n × Fin n, conjBranch (U k * qdRowKraus (P.kraus k) Ψ u) ρ)
          = U k * qdBranchMarginal (P.kraus k) (outerProduct Ψ) ρ * (U k)ᴴ := by
      intro k
      have hx : ∀ u : Fin n × Fin n,
          conjBranch (U k * qdRowKraus (P.kraus k) Ψ u) ρ
            = U k * conjBranch (qdRowKraus (P.kraus k) Ψ u) ρ * (U k)ᴴ := by
        intro u
        simp only [conjBranch_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [Finset.sum_congr rfl (fun u _ => hx u)]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← qdBranchMarginal_outerProduct_kraus]
    simp only [h2]
    have h3 : (∑ k : κ, U k * qdBranchMarginal (P.kraus k) (outerProduct Ψ) ρ * (U k)ᴴ)
        = ∑ k : κ, P.corr k (qdBranchMarginal (P.kraus k) (outerProduct Ψ) ρ) :=
      Finset.sum_congr rfl (fun k _ => (hU.2 k _).symm)
    rw [h3]
    exact hperf ρ
  have hsum' : ∀ ρ : Operator n, (∑ w, conjBranch (A w) ρ) = (1 : ℂ) • ρ := by
    intro ρ
    rw [one_smul]
    exact hsum ρ
  have hsc := Qatlib.Concepts.QuditTeleport.CommLowerBound.comm_kraus_scalar_of_identity A 1 hsum'
  intro k u
  obtain ⟨z, hz⟩ := hsc (k, u)
  exact ⟨z, hz⟩

/-- If a unitary correction sends a row Kraus operator to `z • 1`, the row Kraus operator equals
`z` times the correction's adjoint. -/
theorem qdRowKraus_eq {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (Ψ : QState (Fin n × Fin n)) (k : κ) (u : Fin n × Fin n) (z : ℂ)
    (h : U k * qdRowKraus (P.kraus k) Ψ u = z • (1 : Operator n)) :
    qdRowKraus (P.kraus k) Ψ u = z • (U k)ᴴ := by
  have hu : (U k)ᴴ * U k = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (hU.1 k)
  have hL : (U k)ᴴ * (U k * qdRowKraus (P.kraus k) Ψ u) = qdRowKraus (P.kraus k) Ψ u := by
    rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hR : (U k)ᴴ * (z • (1 : Operator n)) = z • (U k)ᴴ := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  calc qdRowKraus (P.kraus k) Ψ u
      = (U k)ᴴ * (U k * qdRowKraus (P.kraus k) Ψ u) := hL.symm
    _ = (U k)ᴴ * (z • (1 : Operator n)) := congrArg _ h
    _ = z • (U k)ᴴ := hR

/-- In nonzero dimension, perfect teleportation with a pure resource and unitary corrections
requires at least `n²` outcomes [BennettEtAl1993Teleportation]. -/
theorem qdCard_le_of_perfect {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (Ψ : QState (Fin n × Fin n))
    (hperf : QdLoccPerfect P (outerProduct Ψ)) :
    n * n ≤ Fintype.card κ := by
  classical
  have hscal := qdRowKraus_scalar P U hU Ψ hperf
  choose z hz using hscal
  have hne : ∃ k u, z k u ≠ 0 := by
    by_contra hc
    have hc' : ∀ k u, z k u = 0 := by
      intro k u
      by_contra hne0
      exact hc ⟨k, u, hne0⟩
    have hB : ∀ k u, qdRowKraus (P.kraus k) Ψ u = 0 := by
      intro k u
      have h2 := qdRowKraus_eq P U hU Ψ k u (z k u) (hz k u)
      rw [hc' k u, zero_smul] at h2
      exact h2
    have hM : ∀ k ρ, qdBranchMarginal (P.kraus k) (outerProduct Ψ) ρ = 0 := by
      intro k ρ
      rw [qdBranchMarginal_outerProduct_kraus]
      simp only [hB, conjBranch_apply, Matrix.zero_mul, Finset.sum_const_zero]
    haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
    have hz2 : qdLoccOutput P (outerProduct Ψ) (1 : Operator n) = 0 := by
      show (∑ k, P.corr k (qdBranchMarginal (P.kraus k) (outerProduct Ψ) (1 : Operator n))) = 0
      simp only [hM, map_zero, Finset.sum_const_zero]
    have hone := hperf (1 : Operator n)
    rw [hz2] at hone
    exact zero_ne_one hone
  obtain ⟨k0, u0, hz0⟩ := hne
  have hprod : ∀ k u, qdMatW Ψ * qdMatA (P.kraus k) u = z k u • (U k)ᴴ :=
    fun k u => qdRowKraus_eq P U hU Ψ k u (z k u) (hz k u)
  have hWdet : IsUnit (qdMatW Ψ).det := by
    have hu0 : (U k0)ᴴ * U k0 = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff'.mp (hU.1 k0)
    have hdet1 : (U k0)ᴴ.det * (U k0).det = 1 := by
      have h := congrArg Matrix.det hu0
      rw [Matrix.det_mul, Matrix.det_one] at h
      exact h
    have hdetU : (U k0).det ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at hdet1
      exact zero_ne_one hdet1
    have hdetU' : (U k0)ᴴ.det ≠ 0 := by
      rw [Matrix.det_conjTranspose]
      exact star_ne_zero.mpr hdetU
    have hdetP : ((z k0 u0 • (U k0)ᴴ : Operator n)).det ≠ 0 := by
      rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hz0) hdetU'
    have hmul := congrArg Matrix.det (hprod k0 u0)
    rw [Matrix.det_mul] at hmul
    exact IsUnit.mk0 _ (left_ne_zero_of_mul (hmul ▸ hdetP))
  have hW : IsUnit (qdMatW Ψ) := (Matrix.isUnit_iff_isUnit_det (qdMatW Ψ)).mpr hWdet
  let G : κ → Operator n := fun k => (qdMatW Ψ)⁻¹ * (U k)ᴴ
  have hG : ∀ k u, qdMatA (P.kraus k) u = z k u • G k := by
    intro k u
    have h := hprod k u
    have hinv : (qdMatW Ψ)⁻¹ * (qdMatW Ψ * qdMatA (P.kraus k) u) = qdMatA (P.kraus k) u := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWdet, Matrix.one_mul]
    calc qdMatA (P.kraus k) u
        = (qdMatW Ψ)⁻¹ * (qdMatW Ψ * qdMatA (P.kraus k) u) := hinv.symm
      _ = (qdMatW Ψ)⁻¹ * (z k u • (U k)ᴴ) := congrArg _ h
      _ = z k u • ((qdMatW Ψ)⁻¹ * (U k)ᴴ) := by rw [Matrix.mul_smul]
      _ = z k u • G k := rfl
  have hrow : ∀ k u c a, P.kraus k u (c, a) = z k u * G k a c := by
    intro k u c a
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a c) (hG k u)
    simpa only [qdMatA, Matrix.smul_apply, smul_eq_mul] using h
  set b : κ → (Fin n × Fin n) → ℂ := fun k p => G k p.2 p.1
  have hk : ∀ k i p, P.kraus k i p = z k i * b k p := by
    intro k i p
    rw [hrow k i p.1 p.2]
  have hcomp : ∀ p q : Fin n × Fin n, (∑ k, (∑ i, star (z k i) * z k i) * star (b k p) * b k q)
      = (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) p q := by
    intro p q
    have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M p q) P.krausComplete
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    simp only [hk] at h
    have h2 : ∀ k, (∑ i, star (z k i * b k p) * (z k i * b k q))
        = (∑ i, star (z k i) * z k i) * star (b k p) * b k q := by
      intro k
      have hp : ∀ i, star (z k i * b k p) * (z k i * b k q)
          = star (b k p) * b k q * (star (z k i) * z k i) := by
        intro i
        simp only [star_mul]
        ac_rfl
      simp only [hp, ← Finset.mul_sum]
      ac_rfl
    simp only [h2] at h
    exact h
  set t : κ → ℂ := fun k => (Real.sqrt (∑ i, Complex.normSq (z k i)) : ℂ)
  have ht : ∀ k, star (t k) * t k = ∑ i, star (z k i) * z k i := by
    intro k
    have hst : star (t k) = t k := by
      simp only [t, Complex.star_def, Complex.conj_ofReal]
    rw [hst]
    show (Real.sqrt (∑ i, Complex.normSq (z k i)) : ℂ)
        * (Real.sqrt (∑ i, Complex.normSq (z k i)) : ℂ) = ∑ i, star (z k i) * z k i
    rw [← Complex.ofReal_mul,
      Real.mul_self_sqrt (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (z k i))),
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Complex.normSq_eq_conj_mul_self
  set V : Matrix κ (Fin n × Fin n) ℂ := fun k p => t k * b k p
  have hV : V.conjTranspose * V = 1 := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V]
    have h3 : ∀ k, star (t k * b k p) * (t k * b k q)
        = (star (t k) * t k) * star (b k p) * b k q := by
      intro k
      simp only [star_mul]
      ac_rfl
    simp only [h3, ht]
    exact hcomp p q
  have h1 : (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ).rank = n * n := by
    rw [Matrix.rank_one, Fintype.card_prod, Fintype.card_fin]
  have h2 : (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ).rank = V.rank := by
    rw [← hV, Matrix.rank_conjTranspose_mul_self]
  have h3 : V.rank ≤ Fintype.card κ := Matrix.rank_le_card_height V
  calc n * n = (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ).rank := h1.symm
    _ = V.rank := h2
    _ ≤ Fintype.card κ := h3

/-- No vector indexed by an empty finite type is normalized. -/
private theorem qdNormalized_false_empty {I : Type} [Fintype I] [DecidableEq I] [IsEmpty I]
    (Ψ : QState I) : ¬ Normalized Ψ := by
  intro h
  have hz : ∑ i : I, ‖Ψ i‖ ^ 2 = 0 :=
    Finset.sum_eq_zero (fun i _ => (IsEmpty.false i).elim)
  have h1 : (∑ i : I, ‖Ψ i‖ ^ 2) = 1 := h
  rw [hz] at h1
  exact zero_ne_one h1

/-- Perfect teleportation with a normalized pure resource and unitary corrections gives outcome
and bit-count bounds, and message consistency forces equal conjugation maps for equal
messages [BennettEtAl1993Teleportation]. -/
theorem clause4_clause2 : ∀ (n : ℕ) (κ : Type) (_hκ : Fintype κ) (P : QdLoccTeleport n κ)
    (U : κ → Operator n) (Ψ : QState (Fin n × Fin n)),
    Normalized Ψ → QdLoccUnitaryCorr P U → QdLoccPerfect P (outerProduct Ψ) →
    (QdLoccMsgConsistent P → ∀ k k' : κ, P.msgCode k = P.msgCode k' →
      QdSameConjugation n (U k) (U k')) ∧
    n * n ≤ Fintype.card κ ∧ n * n ≤ 2 ^ qdMessageBits κ ∧
    (Function.Injective P.msgCode → n * n ≤ 2 ^ (qdCommCost P + 1)) := by
  intro n κ hκ P U Ψ hΨ hU hperf
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : IsEmpty (Fin 0 × Fin 0) := ⟨fun p => Fin.elim0 p.1⟩
    exact absurd hΨ (qdNormalized_false_empty Ψ)
  · haveI : NeZero n := ⟨ne_of_gt hn⟩
    have hcard := qdCard_le_of_perfect P U hU Ψ hperf
    exact ⟨clause4_clause2_msgConsistent n κ hκ P U Ψ hΨ hU hperf, hcard,
      clause4_clause2_counting_reduce n κ hcard,
      qdCommCost_of_card P hcard⟩

/-- For dimension `n ^ k` with `k ≥ 1`, perfect teleportation with a normalized pure resource
and unitary corrections gives the corresponding squared-dimension outcome and bit-count
bounds [BennettEtAl1993Teleportation]. -/
theorem clause4_clause5 : ∀ (n k : ℕ) (_hk : 1 ≤ k) (κc : Type) (_hc : Fintype κc)
    (P : QdLoccTeleport (n ^ k) κc) (U : κc → Operator (n ^ k))
    (Ψ : QState (Fin (n ^ k) × Fin (n ^ k))),
    Normalized Ψ → QdLoccUnitaryCorr P U →
      QdLoccPerfect P (outerProduct Ψ) →
    n ^ k * n ^ k ≤ Fintype.card κc ∧ n ^ k * n ^ k ≤ 2 ^ qdMessageBits κc ∧
    (Function.Injective P.msgCode → n ^ k * n ^ k ≤ 2 ^ (qdCommCost P + 1)) := by
  intro n k hk κc hc P U Ψ hΨ hU hperf
  rcases Nat.eq_zero_or_pos (n ^ k) with hd | hd
  · haveI : IsEmpty (Fin (n ^ k) × Fin (n ^ k)) := by
      rw [hd]
      exact ⟨fun p => Fin.elim0 p.1⟩
    exact absurd hΨ (qdNormalized_false_empty Ψ)
  · haveI : NeZero (n ^ k) := ⟨ne_of_gt hd⟩
    have hcard := qdCard_le_of_perfect P U hU Ψ hperf
    exact ⟨hcard, clause4_clause2_counting_reduce (n ^ k) κc hcard,
      qdCommCost_of_card P hcard⟩
end Qatlib.Concepts.QuditTeleport.QdLoccModel
