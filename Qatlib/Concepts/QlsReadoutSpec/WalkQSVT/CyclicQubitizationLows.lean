/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.CyclicQubitizationStat
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec

/-!
# Cyclic subspaces for qubitization

This module proves the cyclic-subspace structure associated with a Hermitian compression of a
unitary through an isometry. Under the compressed-square identity, an embedded eigenvector
generates a one- or two-dimensional invariant subspace, according to whether its eigenvalue has
absolute value one or less than one. Related mathematical background is given in [LowSu2026].

## Main statements

* `Clause11CyclicQubitization_answer`: Cyclic-subspace, dimension, and invariance identities
  from Lemma 17.

## References

* [Low and Su, 2026, Lemma 17][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
  Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The squared vector norm is the sum of squared coordinate norms. -/
private theorem normVec_sq {H : Type} [Fintype H] (v : H → ℂ) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  show ‖toEuclidean_fromVec v‖ ^ 2 = _
  exact norm_toEuclidean_fromVec_sq v

/-- A normalized state has vector norm one. -/
private theorem normVec_eq_one_of_normalized {I : Type} [Fintype I]
    {φ : QState I} (hφ : Normalized φ) : normVec φ = 1 := by
  have h2 : normVec φ ^ 2 = 1 := by
    rw [normVec_sq, hφ]
  have hn : 0 ≤ normVec φ := norm_nonneg _
  nlinarith

/-- An isometric matrix preserves the vector norm. -/
private theorem normVec_isometry {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] {L : Matrix H I ℂ} (hL : IsIsometry L) (v : QState I) :
    normVec (L *ᵥ v) = normVec v := by
  show ‖toEuclidean_fromVec (L *ᵥ v)‖ = ‖toEuclidean_fromVec v‖
  exact isometry_mulVec_norm hL v

/-- A unitary matrix preserves the vector norm. -/
private theorem normVec_unitary {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) (v : QState H) :
    normVec (U *ᵥ v) = normVec v := by
  have hUHU : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  exact normVec_isometry (L := U) hUHU v

/-- The vector norm of a complex scalar multiple is the scalar norm times the vector norm. -/
private theorem normVec_smul {H : Type} [Fintype H] (c : ℂ) (v : QState H) :
    normVec (c • v) = ‖c‖ * normVec v := by
  show ‖toEuclidean_fromVec (c • v)‖ = ‖c‖ * normVec v
  have h : toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := rfl
  rw [h, norm_smul]
  rfl

/-- A state with vector norm zero is the zero state. -/
private theorem normVec_eq_zero {H : Type} [Fintype H] {v : QState H}
    (h : normVec v = 0) : v = 0 := by
  have h2 : ∑ i, ‖v i‖ ^ 2 = 0 := by
    rw [← normVec_sq, h]
    norm_num
  have h4 : ∀ i, v i = 0 := by
    intro i
    have hi : ‖v i‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    rw [h2] at hi
    have hn : ‖v i‖ = 0 := by nlinarith [norm_nonneg (v i)]
    exact norm_eq_zero.mp hn
  exact funext h4

/-- The pure-state inner product is complex-linear in its second argument under scalar
multiplication. -/
private theorem inner_smul_right' {I : Type} [Fintype I] (c : ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (c • φ) = c * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul, smul_eq_mul]

/-- The pure-state inner product is conjugate-linear in its first argument under scalar
multiplication. -/
private theorem inner_smul_left' {I : Type} [Fintype I] (c : ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (c • ψ) φ = (starRingEnd ℂ) c * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, star_smul, smul_dotProduct, smul_eq_mul,
      RCLike.star_def]

/-- The pure-state inner product distributes over subtraction in its second argument. -/
private theorem inner_sub_right' {I : Type} [Fintype I] (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (φ - χ) = Qatlib.Foundations.PureStateMath.Inner ψ φ - Qatlib.Foundations.PureStateMath.Inner ψ χ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_sub]

/-- For a Hermitian compression of a unitary through an isometry, the compressed-square identity
gives the stated cyclic-span, eigenvalue, dimension, and invariance properties. See [Low and
Su, Lemma 17][LowSu2026]. -/
theorem Clause11CyclicQubitization_answer : Clause11CyclicQubitization := by
  intro H I _fH _dH _fI _dI U G hU hGiso hHerm
  have hUU : U * Uᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUHU : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hGG : Gᴴ * G = 1 := hGiso
  have hU2unit : (U ^ 2)ᴴ * U ^ 2 = 1 := by
    rw [pow_two, Matrix.conjTranspose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U U, hUHU, Matrix.one_mul]
    exact hUHU

  have part1 : Gᴴ * (U ^ 2) * G = 1 ↔ U ^ 2 * G = G := by
    constructor
    · intro h
      have hexp : ((U ^ 2 * G - G : Matrix H I ℂ)ᴴ * (U ^ 2 * G - G) : Matrix I I ℂ) = 0 := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.mul_sub]
        have a1 : (Gᴴ * (U ^ 2)ᴴ) * (U ^ 2 * G) = 1 := by
          conv_lhs => rw [Matrix.mul_assoc, ← Matrix.mul_assoc (U ^ 2)ᴴ (U ^ 2) G,
            hU2unit, Matrix.one_mul]
          exact hGG
        have a2 : (Gᴴ * (U ^ 2)ᴴ) * G = 1 := by
          have : (Gᴴ * (U ^ 2)ᴴ) * G = (Gᴴ * U ^ 2 * G)ᴴ := by
            conv_rhs => rw [Matrix.mul_assoc, Matrix.conjTranspose_mul,
              Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          rw [this, h, Matrix.conjTranspose_one]
        have a3 : Gᴴ * (U ^ 2 * G) = 1 := by
          conv_lhs => rw [← Matrix.mul_assoc]
          exact h
        rw [a1, a2, a3, hGG]
        abel
      exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp hexp)
    · intro h
      conv_lhs => rw [Matrix.mul_assoc]
      rw [h, hGG]
  constructor
  exact part1
  intro hU2G φ lam hφ hlam v w
  have hv : v = G *ᵥ φ := rfl
  have hw : w = U *ᵥ v := rfl

  have hU2G' : U ^ 2 * G = G := part1.mp hU2G
  have hU2v : (U ^ 2) *ᵥ v = v := by
    conv_lhs => rw [hv]
    calc U ^ 2 *ᵥ (G *ᵥ φ) = (U ^ 2 * G) *ᵥ φ := Matrix.mulVec_mulVec φ (U ^ 2) G
      _ = G *ᵥ φ := by rw [hU2G']
      _ = v := hv.symm
  have hUw : U *ᵥ w = v := by
    conv_lhs => rw [hw]
    calc U *ᵥ (U *ᵥ v) = (U * U) *ᵥ v := Matrix.mulVec_mulVec v U U
      _ = (U ^ 2) *ᵥ v := by rw [← pow_two]
      _ = v := hU2v
  have hUHv : Uᴴ *ᵥ v = w := by
    conv_lhs => rw [← hUw]
    calc Uᴴ *ᵥ (U *ᵥ w) = (Uᴴ * U) *ᵥ w := Matrix.mulVec_mulVec w Uᴴ U
      _ = w := by rw [hUHU, Matrix.one_mulVec]
  have hUHw : Uᴴ *ᵥ w = v := by
    conv_lhs => rw [hw]
    calc Uᴴ *ᵥ (U *ᵥ v) = (Uᴴ * U) *ᵥ v := Matrix.mulVec_mulVec v Uᴴ U
      _ = v := by rw [hUHU, Matrix.one_mulVec]
  have hGGv : (G * Gᴴ) *ᵥ v = v := by
    conv_lhs => rw [hv]
    calc (G * Gᴴ) *ᵥ (G *ᵥ φ) = G *ᵥ (Gᴴ *ᵥ (G *ᵥ φ)) :=
        (Matrix.mulVec_mulVec (G *ᵥ φ) G Gᴴ).symm
      _ = G *ᵥ ((Gᴴ * G) *ᵥ φ) := by rw [(Matrix.mulVec_mulVec φ Gᴴ G).symm]
      _ = G *ᵥ φ := by rw [hGG, Matrix.one_mulVec]
      _ = v := hv.symm
  have hGGw : (G * Gᴴ) *ᵥ w = (lam : ℂ) • v := by
    conv_lhs => rw [hw, hv]
    have hkey : (G * Gᴴ) *ᵥ (U *ᵥ (G *ᵥ φ)) = G *ᵥ ((Gᴴ * U * G) *ᵥ φ) := by
      calc (G * Gᴴ) *ᵥ (U *ᵥ (G *ᵥ φ)) = G *ᵥ (Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ))) :=
          (Matrix.mulVec_mulVec (U *ᵥ (G *ᵥ φ)) G Gᴴ).symm
        _ = G *ᵥ ((Gᴴ * U * G) *ᵥ φ) := by
          congr 1
          calc Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ)) = (Gᴴ * U) *ᵥ (G *ᵥ φ) :=
              Matrix.mulVec_mulVec (G *ᵥ φ) Gᴴ U
            _ = ((Gᴴ * U) * G) *ᵥ φ := Matrix.mulVec_mulVec φ (Gᴴ * U) G
            _ = (Gᴴ * U * G) *ᵥ φ := rfl
    rw [hkey, hlam, Matrix.mulVec_smul]

  have hInner_vw : Qatlib.Foundations.PureStateMath.Inner v w = (lam : ℂ) := by
    conv_lhs => rw [hw, hv]
    rw [Inner_mulVec]
    have hkey : Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ)) = (Gᴴ * U * G) *ᵥ φ := by
      calc Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ)) = (Gᴴ * U) *ᵥ (G *ᵥ φ) :=
          Matrix.mulVec_mulVec (G *ᵥ φ) Gᴴ U
        _ = ((Gᴴ * U) * G) *ᵥ φ := Matrix.mulVec_mulVec φ (Gᴴ * U) G
        _ = (Gᴴ * U * G) *ᵥ φ := rfl
    rw [hkey, hlam, inner_smul_right', inner_self_eq_one hφ, mul_one]
  have hInner_vv : Qatlib.Foundations.PureStateMath.Inner v v = 1 := by
    rw [hv, (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.inner_mulVec hGiso),
        inner_self_eq_one hφ]
  have hnorm_v : normVec v = 1 := by
    rw [hv, normVec_isometry hGiso, normVec_eq_one_of_normalized hφ]
  have hnorm_w : normVec w = 1 := by
    rw [hw, normVec_unitary hU, hnorm_v]
  have habs_le : |lam| ≤ 1 := by
    have h1 : normVec ((Gᴴ * U * G) *ᵥ φ) = ‖((lam : ℂ))‖ * normVec φ := by
      rw [hlam, normVec_smul]
    have h2 : ‖((lam : ℂ))‖ = |lam| := by simp
    have h3 : normVec ((Gᴴ * U * G) *ᵥ φ) = |lam| * normVec φ := by rw [h1, h2]
    have h4 : (Gᴴ * U * G) *ᵥ φ = Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ)) := by
      calc (Gᴴ * U * G) *ᵥ φ = ((Gᴴ * U) * G) *ᵥ φ := rfl
        _ = (Gᴴ * U) *ᵥ (G *ᵥ φ) := (Matrix.mulVec_mulVec φ (Gᴴ * U) G).symm
        _ = Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ)) := (Matrix.mulVec_mulVec (G *ᵥ φ) Gᴴ U).symm
    have h5 : normVec (Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ))) ≤ normVec (U *ᵥ (G *ᵥ φ)) := by
      have hGH : ‖(Gᴴ : Matrix I H ℂ)‖ ≤ 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact Qatlib.Concepts.BlockEncoding.EncodingCore.isometry_norm_le hGiso
      have hle := stateVector_mulVec_norm_le Gᴴ (U *ᵥ (G *ᵥ φ))
      have hcast : ‖stateVector (Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ)))‖
          = normVec (Gᴴ *ᵥ (U *ᵥ (G *ᵥ φ))) := rfl
      have hcast2 : ‖stateVector (U *ᵥ (G *ᵥ φ))‖ = normVec (U *ᵥ (G *ᵥ φ)) := rfl
      rw [hcast, hcast2] at hle
      have : ‖(Gᴴ : Matrix I H ℂ)‖ * normVec (U *ᵥ (G *ᵥ φ))
          ≤ 1 * normVec (U *ᵥ (G *ᵥ φ)) :=
        mul_le_mul_of_nonneg_right hGH (norm_nonneg _)
      rw [one_mul] at this
      exact le_trans hle this
    have h6 : normVec (U *ᵥ (G *ᵥ φ)) = 1 := by
      rw [normVec_unitary hU, normVec_isometry hGiso, normVec_eq_one_of_normalized hφ]
    have h7 : |lam| * normVec φ ≤ 1 := by
      rw [← h3, h4]
      exact le_trans h5 (by rw [h6])
    rw [normVec_eq_one_of_normalized hφ, mul_one] at h7
    exact h7
  have hneg1 : -1 ≤ lam := (abs_le.mp habs_le).1
  have hpos1 : lam ≤ 1 := (abs_le.mp habs_le).2

  have item9 : |lam| = 1 → w = (lam : ℂ) • v := by
    intro habs
    set u : QState H := w - (lam : ℂ) • v with hu
    have hdecomp : w = (lam : ℂ) • v + u := by
      rw [hu]
      module
    have hIn : Qatlib.Foundations.PureStateMath.Inner v u = 0 := by
      rw [hu, inner_sub_right', inner_smul_right',
        hInner_vw, hInner_vv, mul_one]
      ring
    have hIn2 : Qatlib.Foundations.PureStateMath.Inner ((lam : ℂ) • v) u = 0 := by
      rw [inner_smul_left', hIn, mul_zero]
    have hpyth : ‖stateVector w‖ ^ 2
        = ‖stateVector ((lam : ℂ) • v)‖ ^ 2 + ‖stateVector u‖ ^ 2 := by
      rw [hdecomp]
      exact stateVector_norm_sq_add_of_inner_eq_zero hIn2
    have hw1 : ‖stateVector w‖ = 1 := by
      show ‖toEuclidean_fromVec w‖ = 1
      exact hnorm_w
    have hv1 : ‖stateVector v‖ = 1 := by
      show ‖toEuclidean_fromVec v‖ = 1
      exact hnorm_v
    have hlamnorm : ‖stateVector ((lam : ℂ) • v)‖ = |lam| * ‖stateVector v‖ := by
      rw [show stateVector ((lam : ℂ) • v) = (lam : ℂ) • stateVector v from rfl,
        norm_smul, show ‖((lam : ℂ))‖ = |lam| from by
          rw [show ‖((lam : ℂ))‖ = Real.sqrt (Complex.normSq (lam : ℂ)) from rfl,
            Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]]
    rw [hlamnorm, hv1, mul_one, habs, one_pow, hw1, one_pow] at hpyth
    have hu0 : ‖stateVector u‖ ^ 2 = 0 := by linarith
    have hu0' : u = 0 := by
      have : normVec u = 0 := by
        show ‖toEuclidean_fromVec u‖ = 0
        have : ‖toEuclidean_fromVec u‖ ^ 2 = 0 := hu0
        nlinarith [norm_nonneg (toEuclidean_fromVec u)]
      exact normVec_eq_zero this
    rw [hu, sub_eq_zero] at hu0'
    exact hu0'

  have mem_closure : ∀ ψ ∈ Submodule.span ℂ ({v, w} : Set (QState H)),
      U *ᵥ ψ ∈ Submodule.span ℂ {v, w} ∧
      Uᴴ *ᵥ ψ ∈ Submodule.span ℂ {v, w} ∧
      (G * Gᴴ) *ᵥ ψ ∈ Submodule.span ℂ {v, w} := by
    intro ψ hψ
    have hsp : ({v, w} : Set (QState H)) = insert v {w} := rfl
    rw [hsp, Submodule.mem_span_insert] at hψ
    obtain ⟨c1, y, hy, hψ⟩ := hψ
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c2, rfl⟩ := hy

    have hv_mem : v ∈ Submodule.span ℂ ({v, w} : Set (QState H)) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hw_mem : w ∈ Submodule.span ℂ ({v, w} : Set (QState H)) :=
      Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [hψ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw.symm, hUw]
      exact Submodule.add_mem _ (Submodule.smul_mem _ c1 hw_mem)
        (Submodule.smul_mem _ c2 hv_mem)
    · rw [hUHv, hUHw]
      exact Submodule.add_mem _ (Submodule.smul_mem _ c1 hw_mem)
        (Submodule.smul_mem _ c2 hv_mem)
    · rw [hGGv, hGGw]
      rw [smul_smul, ← add_smul]
      exact Submodule.smul_mem _ _ hv_mem
  have pow_mem : ∀ k : ℕ, (U ^ k) *ᵥ v ∈ Submodule.span ℂ ({v, w} : Set (QState H)) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Matrix.one_mulVec]
      exact Submodule.subset_span (Set.mem_insert _ _)
    | succ k ih =>
      have h : (U ^ (k + 1)) *ᵥ v = U *ᵥ ((U ^ k) *ᵥ v) := by
        rw [pow_succ']
        exact (Matrix.mulVec_mulVec v U (U ^ k)).symm
      rw [h]
      exact (mem_closure _ ih).1
  have powH_mem : ∀ k : ℕ, (Uᴴ ^ k) *ᵥ v ∈ Submodule.span ℂ ({v, w} : Set (QState H)) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Matrix.one_mulVec]
      exact Submodule.subset_span (Set.mem_insert _ _)
    | succ k ih =>
      have h : (Uᴴ ^ (k + 1)) *ᵥ v = Uᴴ *ᵥ ((Uᴴ ^ k) *ᵥ v) := by
        rw [pow_succ']
        exact (Matrix.mulVec_mulVec v Uᴴ (Uᴴ ^ k)).symm
      rw [h]
      exact (mem_closure _ ih).2.1
  have cyclic_eq : cyclic U v = Submodule.span ℂ ({v, w} : Set (QState H)) := by
    apply le_antisymm
    · show cyclic U v ≤ _
      unfold cyclic
      rw [Submodule.span_le]
      rintro ψ (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact pow_mem k
      · exact powH_mem k
    · rw [Submodule.span_le]
      rintro ψ (rfl | rfl)
      · apply Submodule.subset_span
        left
        exact ⟨0, by rw [pow_zero, Matrix.one_mulVec]⟩
      · apply Submodule.subset_span
        left
        exact ⟨1, by rw [pow_one]⟩

  have hv_ne : v ≠ 0 := by
    intro hz
    have h0 : normVec (0 : QState H) = 0 := by
      show ‖toEuclidean_fromVec (0 : QState H)‖ = 0
      rw [show toEuclidean_fromVec (0 : QState H) = 0 from rfl]
      exact norm_zero
    rw [hz, h0] at hnorm_v
    norm_num at hnorm_v
  have hfinrank_span_v : Module.finrank ℂ (Submodule.span ℂ ({v} : Set (QState H))) = 1 :=
    finrank_span_singleton hv_ne
  have hspan_mono_v : Submodule.span ℂ ({v} : Set (QState H))
      ≤ Submodule.span ℂ ({v, w} : Set (QState H)) := by
    apply Submodule.span_mono
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert _ _
  have hw_eq_smul_of_finrank1 : Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set (QState H))) = 1
      → w = (lam : ℂ) • v := by
    intro hfin
    have heq : Submodule.span ℂ ({v} : Set (QState H))
        = Submodule.span ℂ ({v, w} : Set (QState H)) :=
      Submodule.eq_of_le_of_finrank_eq hspan_mono_v (by rw [hfinrank_span_v, hfin])
    have hw_in : w ∈ Submodule.span ℂ ({v} : Set (QState H)) := by
      rw [heq]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hw_in
    have hGGc : (G * Gᴴ) *ᵥ w = c • ((G * Gᴴ) *ᵥ v) := by
      rw [← hc, Matrix.mulVec_smul]
    rw [hGGw, hGGv] at hGGc
    have hclam : c = (lam : ℂ) := by
      have : (c - (lam : ℂ)) • v = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact hGGc.symm
      rcases smul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv_ne
    rw [← hc, hclam]
  have hfinrank1_of_abs : |lam| = 1
      → Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set (QState H))) = 1 := by
    intro habs
    have hsmul : w = (lam : ℂ) • v := item9 habs
    have hle : Submodule.span ℂ ({v, w} : Set (QState H))
        ≤ Submodule.span ℂ ({v} : Set (QState H)) := by
      apply Submodule.span_le.mpr
      rintro x (rfl | rfl)
      · exact Submodule.subset_span (Set.mem_singleton _)
      · rw [hsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    have heq : Submodule.span ℂ ({v, w} : Set (QState H))
        = Submodule.span ℂ ({v} : Set (QState H)) :=
      le_antisymm hle hspan_mono_v
    rw [heq, hfinrank_span_v]
  have hsmul_of_finrank1 : Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set (QState H))) = 1
      → |lam| = 1 := by
    intro hfin
    have hw' := hw_eq_smul_of_finrank1 hfin
    have hnorm : normVec w = ‖((lam : ℂ))‖ * normVec v := by
      rw [hw', normVec_smul]
    rw [hnorm_v, hnorm_w, mul_one] at hnorm
    have : ‖((lam : ℂ))‖ = |lam| := by simp
    rw [this] at hnorm
    exact hnorm.symm
  have hfinrank_iff1 : Module.finrank ℂ (cyclic U v) = 1 ↔ |lam| = 1 := by
    rw [cyclic_eq]
    exact ⟨hsmul_of_finrank1, hfinrank1_of_abs⟩
  have hfinrank_pos : 1 ≤ Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set (QState H))) := by
    have := Submodule.finrank_mono hspan_mono_v
    rw [hfinrank_span_v] at this
    exact this
  have hfinrank_le2 : Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set (QState H))) ≤ 2 := by
    have hspan : Submodule.span ℂ ({v, w} : Set (QState H))
        = Submodule.span ℂ {v} ⊔ Submodule.span ℂ {w} := by
      have hset : ({v, w} : Set (QState H)) = {v} ∪ {w} := by
        ext x; simp [or_comm]
      rw [hset, Submodule.span_union]
    rw [hspan]
    have h1 : Module.finrank ℂ (Submodule.span ℂ ({v} : Set (QState H))) ≤ 1 := by
      by_cases hv0 : v = 0
      · rw [hv0, show Submodule.span ℂ ({(0 : QState H)} : Set _) = ⊥ from
          Submodule.span_singleton_eq_bot.mpr rfl]
        norm_num
      · exact (finrank_span_singleton hv0).le
    have h2 : Module.finrank ℂ (Submodule.span ℂ ({w} : Set (QState H))) ≤ 1 := by
      by_cases hw0 : w = 0
      · rw [hw0, show Submodule.span ℂ ({(0 : QState H)} : Set _) = ⊥ from
          Submodule.span_singleton_eq_bot.mpr rfl]
        norm_num
      · exact (finrank_span_singleton hw0).le
    have := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℂ ({v} : Set (QState H))) (Submodule.span ℂ ({w} : Set (QState H)))
    have hinf : 0 ≤ Module.finrank ℂ ↥(Submodule.span ℂ ({v} : Set (QState H)) ⊓
      Submodule.span ℂ ({w} : Set (QState H))) := Nat.zero_le _
    linarith
  have hfinrank_iff2 : Module.finrank ℂ (cyclic U v) = 2 ↔ |lam| < 1 := by
    rw [cyclic_eq]
    constructor
    · intro hfin
      by_contra hnl
      have hge1 : 1 ≤ |lam| := le_of_not_gt hnl
      have habs : |lam| = 1 := le_antisymm habs_le hge1
      have h1 : Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set (QState H))) = 1 :=
        hfinrank1_of_abs habs
      omega
    · intro hlt
      by_contra hne
      have hlt2 : Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set (QState H))) < 2 :=
        lt_of_le_of_ne hfinrank_le2 hne
      have hfin1 : Module.finrank ℂ (Submodule.span ℂ ({v, w} : Set (QState H))) = 1 :=
        le_antisymm (Nat.lt_succ_iff.mp hlt2) hfinrank_pos
      have habs : |lam| = 1 := hsmul_of_finrank1 hfin1
      rw [habs] at hlt
      norm_num at hlt

  have item10 : ∀ ψ : QState H, ψ ∈ cyclic U v →
      (U *ᵥ ψ ∈ cyclic U v) ∧ (Uᴴ *ᵥ ψ ∈ cyclic U v) ∧ ((G * Gᴴ) *ᵥ ψ ∈ cyclic U v) := by
    intro ψ hψ
    rw [cyclic_eq] at hψ ⊢
    exact mem_closure ψ hψ

  refine ⟨hneg1, hpos1, cyclic_eq, hfinrank_iff1, hfinrank_iff2, hUw, hGGv, hGGw, item9, item10⟩

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
