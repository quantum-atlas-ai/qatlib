/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Clifford3Des15.MainResults.Core

set_option backward.isDefEq.respectTransparency false

/-!
# Clifford3Des15 — tensor-power register and the genuine `k`-fold twirl

Source: Zak Webb, *The Clifford group forms a unitary 3-design*,
fixed arXiv:1510.02769v3 (8 Nov 2016).

The paper's `k`-fold register is `L(X^{⊗k})` and its `k`-fold twirl `T_k` averages
`X ↦ U^{⊗k} X (U^{⊗k})†` over unitaries `U` of the *base* space `X = ℂ^d` (not over all
unitaries of the `k`-fold space).  This module supplies that missing tensor structure:

* `tensorPow d A k`: the `k`-fold tensor power `A^{⊗k}`, a `Operator (d^k)` whose
  entries are products over the `k` register coordinates (via `regEquiv`).
* `tensorPow_mul`, `tensorPow_conjTranspose`, `tensorPow_one`, `tensorPow_unitary`:
  the tensor power is a unital `*`-monoid homomorphism into matrices.
* `tensorPow_entry_norm_le_one` and `measurable_tensorPow_entry`: the boundedness and
  measurability facts that make the entrywise Bochner integral meaningful.
* `tensorHaarTwirl H k`: the genuine `k`-fold twirl `T_k(X) = E_U[U^{⊗k} X (U^{⊗k})†]`.
* `tensorHaarTwirl_of_central`: Proposition 2's core for the genuine twirl.
* `tensorHaarTwirl_conj_invariant`: `T_k` is invariant under `U^{⊗k}`-conjugation.
* `tensorEnsembleTwirl` and `proposition1_tensor`: Proposition 1 for the genuine
  tensor-power ensembles, `T_k(X) = T_k(Ψ_{E,k}(X))`.
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

attribute [local instance] operatorMeasurableSpace

variable {ι : Type} [Fintype ι]

/-! ## The tensor power `A^{⊗k}` on the `k`-fold register -/

/-- The `k`-fold tensor power `A^{⊗k}` of a base-space operator `A`, viewed as an
operator on the `k`-fold register `X^{⊗k}` (indexed by `Fin (d^k)` through
`regEquiv`).  Its `(i,j)` entry is the product of the corresponding entries of `A`
over the `k` register coordinates. -/
def tensorPow (d : ℕ) (A : Operator d) (k : ℕ) : Operator (d ^ k) :=
  Matrix.of fun i j => ∏ t : Fin k, A ((regEquiv d k).symm i t) ((regEquiv d k).symm j t)

/-- Entry form of the tensor power. -/
theorem tensorPow_apply (d : ℕ) (A : Operator d) (k : ℕ) (i j : Fin (d ^ k)) :
    tensorPow d A k i j
      = ∏ t : Fin k, A ((regEquiv d k).symm i t) ((regEquiv d k).symm j t) := rfl

/-- The tensor power is multiplicative: `(AB)^{⊗k} = A^{⊗k} B^{⊗k}`. -/
theorem tensorPow_mul (d : ℕ) (A B : Operator d) (k : ℕ) :
    tensorPow d A k * tensorPow d B k = tensorPow d (A * B) k := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [tensorPow_apply]
  have hstep : ∀ m : Fin (d ^ k),
      (∏ t : Fin k, A ((regEquiv d k).symm i t) ((regEquiv d k).symm m t)) *
      (∏ t : Fin k, B ((regEquiv d k).symm m t) ((regEquiv d k).symm j t))
      = ∏ t : Fin k, (A ((regEquiv d k).symm i t) ((regEquiv d k).symm m t) *
          B ((regEquiv d k).symm m t) ((regEquiv d k).symm j t)) := by
    intro m
    rw [Finset.prod_mul_distrib]
  simp_rw [hstep]
  have hsum := Fintype.sum_equiv (regEquiv d k)
      (fun x : Fin k → Fin d => ∏ t : Fin k,
        (A ((regEquiv d k).symm i t) (x t) * B (x t) ((regEquiv d k).symm j t)))
      (fun m : Fin (d ^ k) => ∏ t : Fin k,
        (A ((regEquiv d k).symm i t) ((regEquiv d k).symm m t) *
          B ((regEquiv d k).symm m t) ((regEquiv d k).symm j t)))
      (fun x => by simp)
  rw [← hsum]
  rw [show (∑ x : Fin k → Fin d, ∏ t : Fin k,
        (A ((regEquiv d k).symm i t) (x t) * B (x t) ((regEquiv d k).symm j t)))
      = ∑ x ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset (Fin d))),
          ∏ t : Fin k,
            (A ((regEquiv d k).symm i t) (x t) * B (x t) ((regEquiv d k).symm j t))
        from by simp only [Fintype.piFinset_univ]]
  rw [← Finset.prod_univ_sum
    (t := fun _ : Fin k => (Finset.univ : Finset (Fin d)))
    (f := fun t y => A ((regEquiv d k).symm i t) y * B y ((regEquiv d k).symm j t))]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [Matrix.mul_apply]

/-- The conjugate transpose of a tensor power is the tensor power of the conjugate
transpose. -/
theorem tensorPow_conjTranspose (d : ℕ) (A : Operator d) (k : ℕ) :
    (tensorPow d A k).conjTranspose = tensorPow d A.conjTranspose k := by
  ext i j
  simp only [Matrix.conjTranspose_apply, tensorPow_apply]
  rw [star_prod]

/-- The tensor power of the identity is the identity. -/
theorem tensorPow_one (d : ℕ) (k : ℕ) :
    tensorPow d (1 : Operator d) k = 1 := by
  ext i j
  simp only [tensorPow_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : (regEquiv d k).symm i ≠ (regEquiv d k).symm j := by
      intro h
      exact hij ((regEquiv d k).symm.injective h)
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hne
    rw [Matrix.one_apply, if_neg hij]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by rw [Matrix.one_apply, if_neg ht])

/-- A unitary tensor power: `A^{⊗k}` is unitary whenever `A` is. -/
theorem tensorPow_unitary (d : ℕ) (A : Operator d) (k : ℕ) (hA : IsUnitaryMatrix A) :
    IsUnitaryMatrix (tensorPow d A k) := by
  constructor
  · rw [tensorPow_conjTranspose, tensorPow_mul, hA.1, tensorPow_one]
  · rw [tensorPow_conjTranspose, tensorPow_mul, hA.2, tensorPow_one]

/-- Each entry of a unitary tensor power has norm at most one. -/
theorem tensorPow_entry_norm_le_one {d : ℕ} (k : ℕ) {A : Operator d}
    (hA : IsUnitaryMatrix A) (i j : Fin (d ^ k)) : ‖tensorPow d A k i j‖ ≤ 1 := by
  rw [tensorPow_apply]
  have hbound : ∀ t : Fin k,
      ‖A ((regEquiv d k).symm i t) ((regEquiv d k).symm j t)‖ ≤ 1 :=
    fun t => unitary_entry_norm_le_one hA _ _
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, norm_mul]
      calc ‖A ((regEquiv d k).symm i a) ((regEquiv d k).symm j a)‖ *
            ‖∏ x ∈ s, A ((regEquiv d k).symm i x) ((regEquiv d k).symm j x)‖
          ≤ 1 * 1 := by
            refine mul_le_mul (hbound a) ih
              (norm_nonneg _) (by norm_num)
        _ = 1 := by ring

/-- Each entry of the tensor power is a measurable function of the base operator. -/
theorem measurable_tensorPow_entry (d k : ℕ) (i j : Fin (d ^ k)) :
    Measurable (fun A : Operator d => tensorPow d A k i j) := by
  have h : (fun A : Operator d => tensorPow d A k i j)
      = fun A => ∏ t : Fin k, A ((regEquiv d k).symm i t) ((regEquiv d k).symm j t) := rfl
  rw [h]
  exact Finset.measurable_prod _ (fun t _ => measurable_operator_entry _ _)

/-- Each entry of the conjugated sandwich `U^{⊗k} X (U^{⊗k})†` is measurable in `U`. -/
theorem measurable_tensorPow_conjEntry (d k : ℕ) (X : Operator (d ^ k))
    (i j : Fin (d ^ k)) :
    Measurable (fun A : Operator d =>
      (tensorPow d A k * X * (tensorPow d A k).conjTranspose) i j) := by
  have h : (fun A : Operator d =>
        (tensorPow d A k * X * (tensorPow d A k).conjTranspose) i j)
      = fun A => ∑ p : Fin (d ^ k), ∑ q : Fin (d ^ k),
          tensorPow d A k i q * X q p * star (tensorPow d A k j p) := by
    funext A
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [h]
  refine Finset.measurable_sum _ (fun p _ => Finset.measurable_sum _ (fun q _ => ?_))
  exact ((measurable_tensorPow_entry d k i q).mul measurable_const).mul
    (continuous_star.measurable.comp (measurable_tensorPow_entry d k j p))

/-- Every entry of the tensor-conjugated sandwich is integrable against Haar measure
on the base space, bounded by the entrywise `ℓ¹` norm of `X`. -/
theorem tensorHaarEntry_integrable {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (X : Operator (d ^ k)) (i j : Fin (d ^ k)) :
    MeasureTheory.Integrable
      (fun A : Operator d =>
        (tensorPow d A k * X * (tensorPow d A k).conjTranspose) i j) H.μ := by
  haveI : MeasureTheory.IsProbabilityMeasure H.μ := H.isProb
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun A : Operator d =>
        (tensorPow d A k * X * (tensorPow d A k).conjTranspose) i j) H.μ :=
    (measurable_tensorPow_conjEntry d k X i j).stronglyMeasurable.aestronglyMeasurable
  refine MeasureTheory.Integrable.of_bound hmeas
    (∑ a : Fin (d ^ k), ∑ b : Fin (d ^ k), ‖X a b‖) ?_
  filter_upwards [haar_ae_unitary H] with A hA
  have hform : (tensorPow d A k * X * (tensorPow d A k).conjTranspose) i j
      = ∑ p : Fin (d ^ k), ∑ q : Fin (d ^ k),
          tensorPow d A k i q * X q p * star (tensorPow d A k j p) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [hform]
  calc ‖∑ p : Fin (d ^ k), ∑ q : Fin (d ^ k),
          tensorPow d A k i q * X q p * star (tensorPow d A k j p)‖
      ≤ ∑ p : Fin (d ^ k), ‖∑ q : Fin (d ^ k),
          tensorPow d A k i q * X q p * star (tensorPow d A k j p)‖ := norm_sum_le _ _
    _ ≤ ∑ p : Fin (d ^ k), ∑ q : Fin (d ^ k),
          ‖tensorPow d A k i q * X q p * star (tensorPow d A k j p)‖ :=
        Finset.sum_le_sum fun p _ => norm_sum_le _ _
    _ ≤ ∑ p : Fin (d ^ k), ∑ q : Fin (d ^ k), ‖X q p‖ := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul, norm_mul, norm_star]
        have h1 : ‖tensorPow d A k i q‖ ≤ 1 := tensorPow_entry_norm_le_one k hA i q
        have h2 : ‖tensorPow d A k j p‖ ≤ 1 := tensorPow_entry_norm_le_one k hA j p
        have hz : 0 ≤ ‖X q p‖ := norm_nonneg _
        have h3 : ‖tensorPow d A k i q‖ * ‖X q p‖ ≤ ‖X q p‖ := by
          simpa using mul_le_mul_of_nonneg_right h1 hz
        have h4 : ‖X q p‖ * ‖tensorPow d A k j p‖ ≤ ‖X q p‖ := by
          simpa using mul_le_mul_of_nonneg_left h2 hz
        calc ‖tensorPow d A k i q‖ * ‖X q p‖ * ‖tensorPow d A k j p‖
            ≤ ‖X q p‖ * ‖tensorPow d A k j p‖ :=
              mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ ≤ ‖X q p‖ := h4
    _ = ∑ a : Fin (d ^ k), ∑ b : Fin (d ^ k), ‖X a b‖ := Finset.sum_comm

/-! ## The genuine `k`-fold twirl `T_k` -/

/-- The genuine `k`-fold Haar twirl `T_k(X) = E_{U∈U(d)}[U^{⊗k} X (U^{⊗k})†]`,
averaging over the base space `X = ℂ^d` (paper §2.1, eqs. (21)-(22)). -/
noncomputable def tensorHaarTwirl {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (X : Operator (d ^ k)) : Operator (d ^ k) :=
  Matrix.of fun i j => MeasureTheory.integral H.μ
    fun A : Operator d => (tensorPow d A k * X * (tensorPow d A k).conjTranspose) i j

/-- Entrywise unfolding of the genuine `k`-fold twirl. -/
theorem tensorHaarTwirl_apply {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (X : Operator (d ^ k)) (i j : Fin (d ^ k)) :
    tensorHaarTwirl H k X i j = MeasureTheory.integral H.μ
      fun A : Operator d =>
        (tensorPow d A k * X * (tensorPow d A k).conjTranspose) i j := rfl

/-- The `k`-fold twirl of the zero operator is zero. -/
theorem tensorHaarTwirl_zero {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ) :
    tensorHaarTwirl H k (0 : Operator (d ^ k)) = 0 := by
  ext i j
  rw [tensorHaarTwirl_apply]
  have hz : (fun A : Operator d =>
        (tensorPow d A k * (0 : Operator (d ^ k)) * (tensorPow d A k).conjTranspose) i j)
      = fun _ => (0 : ℂ) := by
    funext A; simp
  rw [hz, MeasureTheory.integral_zero]
  simp

/-- The `k`-fold twirl is additive. -/
theorem tensorHaarTwirl_add {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (ρ σ : Operator (d ^ k)) :
    tensorHaarTwirl H k (ρ + σ) = tensorHaarTwirl H k ρ + tensorHaarTwirl H k σ := by
  ext i j
  rw [tensorHaarTwirl_apply, Matrix.add_apply, tensorHaarTwirl_apply, tensorHaarTwirl_apply]
  have hpt : (fun A : Operator d =>
        (tensorPow d A k * (ρ + σ) * (tensorPow d A k).conjTranspose) i j)
      = fun A => (tensorPow d A k * ρ * (tensorPow d A k).conjTranspose) i j
          + (tensorPow d A k * σ * (tensorPow d A k).conjTranspose) i j := by
    funext A
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  rw [hpt]
  exact MeasureTheory.integral_add (tensorHaarEntry_integrable H k ρ i j)
    (tensorHaarEntry_integrable H k σ i j)

/-- The `k`-fold twirl is complex-homogeneous. -/
theorem tensorHaarTwirl_smul {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (c : ℂ) (ρ : Operator (d ^ k)) :
    tensorHaarTwirl H k (c • ρ) = c • tensorHaarTwirl H k ρ := by
  ext i j
  rw [tensorHaarTwirl_apply, Matrix.smul_apply, tensorHaarTwirl_apply]
  have hpt : (fun A : Operator d =>
        (tensorPow d A k * (c • ρ) * (tensorPow d A k).conjTranspose) i j)
      = fun A => c * ((tensorPow d A k * ρ * (tensorPow d A k).conjTranspose) i j) := by
    funext A
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [hpt, MeasureTheory.integral_const_mul, smul_eq_mul]

/-- The `k`-fold twirl is additive over a finite scalar-weighted sum. -/
theorem tensorHaarTwirl_finset_sum {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (s : Finset ι) (c : ι → ℂ) (ρ : ι → Operator (d ^ k)) :
    tensorHaarTwirl H k (∑ i ∈ s, c i • ρ i)
      = ∑ i ∈ s, c i • tensorHaarTwirl H k (ρ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensorHaarTwirl_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, tensorHaarTwirl_add,
        tensorHaarTwirl_smul, ih]

/-! ## Fixed points of the genuine twirl (Proposition 2's core) -/

/-- **Proposition 2 core for the genuine twirl** (eq. (23)): any operator `W` on the
`k`-fold register that is fixed by conjugation with every `U^{⊗k}` is fixed by the
genuine `k`-fold twirl `T_k`. -/
theorem tensorHaarTwirl_of_central {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (W : Operator (d ^ k))
    (hW : ∀ A : Operator d, IsUnitaryMatrix A →
      tensorPow d A k * W * (tensorPow d A k).conjTranspose = W) :
    tensorHaarTwirl H k W = W := by
  ext i j
  rw [tensorHaarTwirl_apply]
  have hcongr : (fun A : Operator d =>
        (tensorPow d A k * W * (tensorPow d A k).conjTranspose) i j)
      =ᵐ[H.μ] fun _ : Operator d => W i j := by
    filter_upwards [haar_ae_unitary H] with A hA
    exact congrArg (fun M : Operator (d ^ k) => M i j) (hW A hA)
  rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_const]
  change (H.μ).real Set.univ • W i j = W i j
  rw [haar_prob_real_univ H, one_smul]

/-! ## Invariance of the genuine twirl under tensor-power conjugation -/

/-- Regrouping identity: `P (Q X Q†) P† = (P Q) X (P Q)†`. -/
theorem tensor_mul_conj_conj_assoc {D : ℕ} (P Q X : Operator D) :
    P * (Q * X * Q.conjTranspose) * P.conjTranspose
      = (P * Q) * X * (P * Q).conjTranspose := by
  rw [Matrix.conjTranspose_mul]
  simp only [← Matrix.mul_assoc]

/-- **Invariance of the genuine `k`-fold twirl** (`k`-fold analogue of
`haarTwirl_conj_invariant`): conjugating by a tensor power `V^{⊗k}` does not change
the twirl, `T_k(V^{⊗k} X (V^{⊗k})†) = T_k(X)`. -/
theorem tensorHaarTwirl_conj_invariant {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (V : Operator d) (hV : IsUnitaryMatrix V) (X : Operator (d ^ k)) :
    tensorHaarTwirl H k (tensorPow d V k * X * (tensorPow d V k).conjTranspose)
      = tensorHaarTwirl H k X := by
  ext i j
  show MeasureTheory.integral H.μ
        (fun A : Operator d => (tensorPow d A k *
          (tensorPow d V k * X * (tensorPow d V k).conjTranspose) *
          (tensorPow d A k).conjTranspose) i j)
    = MeasureTheory.integral H.μ
        (fun A : Operator d =>
          (tensorPow d A k * X * (tensorPow d A k).conjTranspose) i j)
  have hA : (fun A : Operator d => (tensorPow d A k *
        (tensorPow d V k * X * (tensorPow d V k).conjTranspose) *
        (tensorPow d A k).conjTranspose) i j)
      = fun A => ((tensorPow d A k * tensorPow d V k) * X *
          (tensorPow d A k * tensorPow d V k).conjTranspose) i j :=
    funext fun A => congrArg (fun M : Operator (d ^ k) => M i j)
      (tensor_mul_conj_conj_assoc (tensorPow d A k) (tensorPow d V k) X)
  rw [hA]
  have hval : (fun A : Operator d => ((tensorPow d A k * tensorPow d V k) * X *
        (tensorPow d A k * tensorPow d V k).conjTranspose) i j)
      = fun A => (tensorPow d (A * V) k * X * (tensorPow d (A * V) k).conjTranspose) i j := by
    funext A
    rw [tensorPow_mul]
  rw [hval]
  have hmap : MeasureTheory.Measure.map (fun A : Operator d => A * V) H.μ = H.μ :=
    H.rightInvariant V hV
  conv_rhs => rw [← hmap]
  exact (MeasureTheory.integral_map_of_stronglyMeasurable
    (measurable_operator_mul_right V)
    (Measurable.stronglyMeasurable (measurable_tensorPow_conjEntry d k X i j))).symm

/-! ## Permutation operators commute with tensor powers (eq. (9)) -/

/-- **Equation (9) core**: every tensor power `U^{⊗k}` commutes with every permutation
operator `W_π`, `π ∈ S_k`.  This is the commutativity that makes `W_π` a fixed point
of the genuinely `k`-fold twirl (Proposition 2).

Entrywise, the left product selects the register index `(regEquiv d k) (v_i ∘ π)` and
the right product selects `(regEquiv d k) (v_j ∘ π⁻¹)`, and the two entries agree
after reindexing the defining product along `π`. -/
theorem permOp_commute_tensorPow (d k : ℕ) (π : Equiv.Perm (Fin k)) (A : Operator d) :
    permOp d k π * tensorPow d A k = tensorPow d A k * permOp d k π := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : (∑ m : Fin (d ^ k), permOp d k π i m * tensorPow d A k m j)
      = tensorPow d A k (regEquiv d k ((regEquiv d k).symm i ∘ ⇑π)) j := by
    have hzero : ∀ m : Fin (d ^ k), m ≠ regEquiv d k ((regEquiv d k).symm i ∘ ⇑π) →
        permOp d k π i m * tensorPow d A k m j = 0 := by
      intro m hm
      have hz : permOp d k π i m = 0 := by
        rw [permOp_apply]
        have hne : ¬ ((regEquiv d k).symm m = (regEquiv d k).symm i ∘ ⇑π) := by
          intro h
          apply hm
          calc m = regEquiv d k ((regEquiv d k).symm m) :=
                (Equiv.apply_symm_apply (regEquiv d k) m).symm
            _ = regEquiv d k ((regEquiv d k).symm i ∘ ⇑π) := by rw [h]
        simp [hne]
      rw [hz, zero_mul]
    rw [Finset.sum_eq_single (regEquiv d k ((regEquiv d k).symm i ∘ ⇑π))
      (fun m _ hm => hzero m hm) (fun h => absurd (Finset.mem_univ _) h)]
    rw [show permOp d k π i (regEquiv d k ((regEquiv d k).symm i ∘ ⇑π)) = 1 by
      rw [permOp_eq_one_iff]; simp, one_mul]
  have hR : (∑ m : Fin (d ^ k), tensorPow d A k i m * permOp d k π m j)
      = tensorPow d A k i (regEquiv d k ((regEquiv d k).symm j ∘ ⇑π.symm)) := by
    have hzero : ∀ m : Fin (d ^ k), m ≠ regEquiv d k ((regEquiv d k).symm j ∘ ⇑π.symm) →
        tensorPow d A k i m * permOp d k π m j = 0 := by
      intro m hm
      have hz : permOp d k π m j = 0 := by
        rw [permOp_apply]
        have hne : ¬ ((regEquiv d k).symm j = (regEquiv d k).symm m ∘ ⇑π) := by
          intro h
          apply hm
          have hsymm : (regEquiv d k).symm m = (regEquiv d k).symm j ∘ ⇑π.symm := by
            funext x
            have hx := congrFun h (π.symm x)
            simpa [Function.comp_apply] using hx.symm
          calc m = regEquiv d k ((regEquiv d k).symm m) :=
                (Equiv.apply_symm_apply (regEquiv d k) m).symm
            _ = regEquiv d k ((regEquiv d k).symm j ∘ ⇑π.symm) := by rw [hsymm]
        simp [hne]
      rw [hz, mul_zero]
    rw [Finset.sum_eq_single (regEquiv d k ((regEquiv d k).symm j ∘ ⇑π.symm))
      (fun m _ hm => hzero m hm) (fun h => absurd (Finset.mem_univ _) h)]
    rw [show permOp d k π (regEquiv d k ((regEquiv d k).symm j ∘ ⇑π.symm)) j = 1 by
      rw [permOp_eq_one_iff]
      funext x
      simp, mul_one]
  rw [hL, hR]
  simp only [tensorPow_apply, Equiv.symm_apply_apply]
  have hprod : (∏ t : Fin k,
        A (((regEquiv d k).symm i ∘ ⇑π) t) ((regEquiv d k).symm j t))
      = ∏ t : Fin k,
        A ((regEquiv d k).symm i t) (((regEquiv d k).symm j ∘ ⇑π.symm) t) := by
    have h := Equiv.prod_comp π (fun t : Fin k =>
      A ((regEquiv d k).symm i t) (((regEquiv d k).symm j ∘ ⇑π.symm) t))
    simpa [Function.comp_apply] using h
  exact hprod

/-- **Proposition 2 for the genuine `k`-fold twirl** (claim `c006`; Webb,
arXiv:1510.02769v3, Proposition 2, p. 8): for every `π ∈ S_k`, the permutation
operator `W_π` is a fixed point of `T_k`, `T_k(W_π) = W_π`. -/
theorem proposition2_tensor {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (π : Equiv.Perm (Fin k)) :
    tensorHaarTwirl H k (permOp d k π) = permOp d k π := by
  refine tensorHaarTwirl_of_central H k (permOp d k π) (fun A hA => ?_)
  calc tensorPow d A k * permOp d k π * (tensorPow d A k).conjTranspose
      = permOp d k π * tensorPow d A k * (tensorPow d A k).conjTranspose := by
        rw [← permOp_commute_tensorPow d k π A]
    _ = permOp d k π * (tensorPow d A k * (tensorPow d A k).conjTranspose) := by
        rw [Matrix.mul_assoc]
    _ = permOp d k π * 1 := by rw [(tensorPow_unitary d A k hA).2]
    _ = permOp d k π := Matrix.mul_one _

/-- **Proposition 3 for the genuine `k`-fold twirl** (claim `c007`; Webb,
arXiv:1510.02769v3, Proposition 3, p. 9, eq. (24)): if the commutant of the tensor
power action is contained in the span of the permutation operators, and `T_k(X)` is
in that commutant, then `T_k(X)` is a complex linear combination of the `permOp`.

The two hypotheses are exactly the paper's two proof steps: `hfix` is the Haar
invariance statement (the `k`-fold analogue of `haarTwirl_unitary_conj_fixed`) and
`hspan` is the paper's Theorem 1 (double-commutant / Wedderburn span theorem). -/
theorem proposition3_tensor_of_commutant_span {d k : ℕ} (H : HaarUnitaryMeasure d)
    (X : Operator (d ^ k))
    (hfix : ∀ A : Operator d, IsUnitaryMatrix A →
      tensorPow d A k * tensorHaarTwirl H k X * (tensorPow d A k).conjTranspose
        = tensorHaarTwirl H k X)
    (hspan : ∀ T : Operator (d ^ k),
      (∀ A : Operator d, IsUnitaryMatrix A →
        tensorPow d A k * T * (tensorPow d A k).conjTranspose = T) →
      T ∈ Submodule.span ℂ (Set.range (permOp d k))) :
    ∃ α : Equiv.Perm (Fin k) → ℂ,
      tensorHaarTwirl H k X = ∑ π : Equiv.Perm (Fin k), α π • permOp d k π := by
  have hmem : tensorHaarTwirl H k X ∈ Submodule.span ℂ (Set.range (permOp d k)) :=
    hspan _ hfix
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  exact ⟨α, hα.symm⟩

/-! ## Genuine ensemble twirl and Proposition 1 -/

/-- The genuine `k`-fold ensemble twirl `Ψ_{E,k}(X) = ∑_i α_i U_i^{⊗k} X (U_i^{⊗k})†`
of eq. (21). -/
noncomputable def tensorEnsembleTwirl {d : ℕ} (E : Ensemble ι d) (k : ℕ)
    (X : Operator (d ^ k)) : Operator (d ^ k) :=
  ∑ i, ((E.wt i : ℂ)) •
    (tensorPow d (E.op i) k * X * (tensorPow d (E.op i) k).conjTranspose)

/-- Unfolding the genuine ensemble twirl. -/
theorem tensorEnsembleTwirl_apply {d : ℕ} (E : Ensemble ι d) (k : ℕ)
    (X : Operator (d ^ k)) :
    tensorEnsembleTwirl E k X
      = ∑ i, ((E.wt i : ℂ)) •
        (tensorPow d (E.op i) k * X * (tensorPow d (E.op i) k).conjTranspose) := rfl

/-- Definition 1 in the paper's tensor model: `E` is a unitary `k`-design when the
genuinely `k`-fold ensemble twirl equals the genuinely `k`-fold Haar twirl on the
whole `k`-fold register `L(X^{⊗k})` (paper eq. (21)/(28)). -/
def IsUnitaryKDesign {ι : Type} [Fintype ι] {d : ℕ} (H : HaarUnitaryMeasure d)
    (E : Ensemble ι d) (k : ℕ) : Prop :=
  ∀ X : Operator (d ^ k), tensorEnsembleTwirl E k X = tensorHaarTwirl H k X

/-- **Proposition 1 for the genuine tensor-power twirl** (claim `c005`;
Webb, arXiv:1510.02769v3, Proposition 1, p. 8): for every finite unitary ensemble `E`
and every `X` on the `k`-fold register,
`T_k(X) = T_k(Ψ_{E,k}(X))`.

The proof is the paper's: push `T_k` through the weighted average using linearity, and
use the invariance `tensorHaarTwirl_conj_invariant` to see each summand has the same
`T_k`-image as `X`. -/
theorem proposition1_tensor {d : ℕ} (H : HaarUnitaryMeasure d) (k : ℕ)
    (E : Ensemble ι d) (X : Operator (d ^ k)) :
    tensorHaarTwirl H k X = tensorHaarTwirl H k (tensorEnsembleTwirl E k X) := by
  rw [tensorEnsembleTwirl_apply]
  rw [show tensorHaarTwirl H k
        (∑ i, (E.wt i : ℂ) •
          (tensorPow d (E.op i) k * X * (tensorPow d (E.op i) k).conjTranspose))
      = ∑ i, (E.wt i : ℂ) •
          tensorHaarTwirl H k
            (tensorPow d (E.op i) k * X * (tensorPow d (E.op i) k).conjTranspose) from by
      simpa using tensorHaarTwirl_finset_sum H k (Finset.univ : Finset ι)
        (fun i => (E.wt i : ℂ))
        (fun i => tensorPow d (E.op i) k * X * (tensorPow d (E.op i) k).conjTranspose)]
  have hinv : ∀ i : ι, tensorHaarTwirl H k
      (tensorPow d (E.op i) k * X * (tensorPow d (E.op i) k).conjTranspose)
        = tensorHaarTwirl H k X :=
    fun i => tensorHaarTwirl_conj_invariant H k (E.op i) (E.op_unitary i) X
  simp only [hinv]
  rw [← Finset.sum_smul]
  have hw : (∑ i, (E.wt i : ℂ)) = 1 := by
    have h1 : ((∑ i, E.wt i : ℝ) : ℂ) = 1 := by rw [E.wt_sum_one]; norm_num
    rw [← h1]; push_cast; ring
  rw [hw, one_smul]

end Qatlib.Papers.Clifford3Des15.MainResults
