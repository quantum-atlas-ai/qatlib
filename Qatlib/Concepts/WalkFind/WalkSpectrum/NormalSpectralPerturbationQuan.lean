/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.NormalSpectralPerturbationStat
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Mathlib.Combinatorics.Hall.Finite
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkFind.SearchAlgorithm

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.WalkSpectrum
open Matrix
open scoped BigOperators InnerProductSpace

theorem frobeniusSq_unitary_left (m n : ℕ) (U : Matrix (Fin m) (Fin m) ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    frobeniusSq (U*A) = frobeniusSq A := by
  unfold frobeniusSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖A i j‖^2)]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (fun x : ℝ => x^2)
    (norm_applyGate_of_mem_unitaryGroup hU (fun i => A i j))
  simpa only [norm_toEuclidean_fromVec_sq, ApplyGate, Matrix.mulVec, dotProduct,
    Matrix.mul_apply] using! h

theorem normal_euclidean_eigenbasis (m : ℕ) (U : Matrix (Fin m) (Fin m) ℂ)
    (hu : Uᴴ*U = U*Uᴴ) :
    ∃ (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (μ : Fin m → ℂ),
      ∀ j, U.toEuclideanLin (b j) = μ j • b j := by
  classical
  let f : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := U.toEuclideanLin
  have hf : star f * f = f * star f := by
    change U.toEuclideanLin.adjoint * U.toEuclideanLin =
      U.toEuclideanLin * U.toEuclideanLin.adjoint
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using!
      congrArg Matrix.toEuclideanLin hu
  let H : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := (1 / 2 : ℂ) • (f + star f)
  let K : Module.End ℂ (EuclideanSpace ℂ (Fin m)) := (-Complex.I / 2) • (f - star f)
  have hH : H.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    change star H = H
    simp [H, star_smul, add_comm]
  have hK : K.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    change star K = K
    simp only [K, star_smul, star_sub, star_star]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp]
    rw [← neg_sub f (star f), smul_neg, ← neg_smul]
    rw [neg_smul, neg_div]
    exact (neg_smul _ _).symm
  have hc : Commute f (star f) := by
    show f * star f = star f * f
    exact hf.symm
  have hHK : Commute H K :=
    (((Commute.refl f).sub_right hc).add_left
      (hc.symm.sub_right (Commute.refl (star f)))).smul_left (1 / 2 : ℂ)
        |>.smul_right (-Complex.I / 2)
  let ι := {i : ℂ × ℂ // H.eigenspace i.2 ⊓ K.eigenspace i.1 ≠ ⊥}
  let embed : ι → Module.End.Eigenvalues H × Module.End.Eigenvalues K :=
    fun i => (⟨i.1.2, ne_bot_of_le_ne_bot i.2 inf_le_left⟩,
      ⟨i.1.1, ne_bot_of_le_ne_bot i.2 inf_le_right⟩)
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p => p.2.val) hij) (congrArg (fun p => p.1.val) hij)
  letI : Finite ι := Finite.of_injective embed hembed
  letI : Fintype ι := Fintype.ofFinite ι
  have horth := (hH.orthogonalFamily_eigenspace_inf_eigenspace hK).comp
    (Subtype.coe_injective : Function.Injective (Subtype.val : ι → ℂ × ℂ))
  have hdecomp : DirectSum.IsInternal (fun i : ι => H.eigenspace i.1.2 ⊓ K.eigenspace i.1.1) := by
    apply horth.isInternal_iff.mpr
    rw [iSup_ne_bot_subtype]
    rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
    exact hH.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hK hHK
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := by simp
  let b := hdecomp.subordinateOrthonormalBasis hn horth
  let χ := fun j => hdecomp.subordinateOrthonormalBasisIndex hn j horth
  let μ := fun j => (χ j).1.2 + Complex.I * (χ j).1.1
  have hparts : H + Complex.I • K = f := by
    have hIK : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
      norm_num
    simp only [H, K, smul_smul, hIK]
    module
  have heig (j : Fin m) : f (b j) = μ j • b j := by
    have hj := hdecomp.subordinateOrthonormalBasis_subordinate hn j horth
    have hHj := Module.End.mem_eigenspace_iff.mp hj.1
    have hKj := Module.End.mem_eigenspace_iff.mp hj.2
    rw [← hparts, LinearMap.add_apply]
    change H (b j) + Complex.I • K (b j) = _
    rw [hHj, hKj, smul_smul, ← add_smul]
  exact ⟨b, μ, heig⟩

theorem normal_matrix_eigenbasis (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Aᴴ*A = A*Aᴴ) :
    ∃ (E : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ),
      E ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ A*E = E*Matrix.diagonal μ := by
  classical
  obtain ⟨b, μ, hb⟩ := normal_euclidean_eigenbasis n A hA
  let E := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix b.toBasis
  have hE : E ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  refine ⟨E, μ, hE, ?_⟩
  ext i j
  have h := congrArg WithLp.ofLp (hb j)
  change A *ᵥ (fun i => E i j) = μ j • (fun i => E i j) at h
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using! congrFun h i

theorem balanced_positive_permutation (n : ℕ) (W : Matrix (Fin n) (Fin n) ℝ)
    (s : ℝ) (hs : 0 < s) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = s) (hcol : ∀ j, ∑ i, W i j = s) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, 0 < W i (σ i) := by
  classical
  let neighbors : Fin n → Finset (Fin n) := fun i => Finset.univ.filter (fun j => 0 < W i j)
  have hhall (S : Finset (Fin n)) : S.card ≤ (S.biUnion neighbors).card := by
    let T := S.biUnion neighbors
    have hnoleak (i j : Fin n) (hi : i ∈ S) (hj : j ∉ T) : W i j = 0 := by
      apply le_antisymm _ (hW i j)
      apply le_of_not_gt
      intro hp
      apply hj
      exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [neighbors, hp]⟩
    have hmass : (S.card : ℝ)*s ≤ (T.card : ℝ)*s := by
      calc
        (S.card : ℝ)*s = ∑ i ∈ S, ∑ j, W i j := by simp [hrow]
        _ = ∑ j ∈ T, ∑ i ∈ S, W i j := by
          rw [Finset.sum_comm]
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          exact Finset.sum_eq_zero fun i hi => hnoleak i j hi hj
        _ ≤ ∑ j ∈ T, s := by
          apply Finset.sum_le_sum
          intro j _
          rw [← hcol j]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hW i j)
        _ = (T.card : ℝ)*s := by simp
    exact_mod_cast (mul_le_mul_iff_left₀ hs).mp hmass
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hhall
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  exact ⟨σ, fun i => (Finset.mem_filter.mp (hmem i)).2⟩

theorem balanced_permutation_cost (n : ℕ) (W cost : Matrix (Fin n) (Fin n) ℝ)
    (s : ℝ) (hs : 0 < s) (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = s) (hcol : ∀ j, ∑ i, W i j = s) :
    ∃ σ : Equiv.Perm (Fin n), s*(∑ i, cost i (σ i)) ≤ ∑ i, ∑ j, W i j*cost i j := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨Equiv.refl _, by simp⟩
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  let support (M : Matrix (Fin n) (Fin n) ℝ) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter (fun z => 0 < M z.1 z.2)
  have main : ∀ m : ℕ, ∀ M : Matrix (Fin n) (Fin n) ℝ, (support M).card = m →
      ∀ t : ℝ, 0 < t → (∀ i j, 0 ≤ M i j) →
      (∀ i, ∑ j, M i j = t) → (∀ j, ∑ i, M i j = t) →
      ∃ σ : Equiv.Perm (Fin n), t*(∑ i, cost i (σ i)) ≤ ∑ i, ∑ j, M i j*cost i j := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro M hm t ht hM hr hc
      obtain ⟨σ, hσ⟩ := balanced_positive_permutation n M t ht hM hr hc
      by_cases hcheap : t*(∑ i, cost i (σ i)) ≤ ∑ i, ∑ j, M i j*cost i j
      · exact ⟨σ, hcheap⟩
      obtain ⟨i0, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => M i (σ i))
        Finset.univ_nonempty
      let δ := M i0 (σ i0)
      have hδ : 0 < δ := hσ i0
      have hδle (i : Fin n) : δ ≤ M i (σ i) := hmin i (Finset.mem_univ _)
      have hδt : δ ≤ t := by
        calc
          δ ≤ M i0 (σ i0) := le_rfl
          _ ≤ ∑ j, M i0 j := Finset.single_le_sum (fun j _ => hM i0 j) (Finset.mem_univ _)
          _ = t := hr i0
      let M' : Matrix (Fin n) (Fin n) ℝ := fun i j => M i j - if j = σ i then δ else 0
      have hM' (i j : Fin n) : 0 ≤ M' i j := by
        dsimp [M']
        split_ifs with h
        · subst j; exact sub_nonneg.mpr (hδle i)
        · simpa using! hM i j
      have hr' (i : Fin n) : ∑ j, M' i j = t-δ := by
        simp [M', Finset.sum_sub_distrib, hr]
      have hc' (j : Fin n) : ∑ i, M' i j = t-δ := by
        have heq (i : Fin n) : j = σ i ↔ i = σ.symm j := by
          constructor
          · intro h; simpa using! (congrArg σ.symm h).symm
          · intro h; simp [h]
        simp [M', Finset.sum_sub_distrib, hc, heq]
      have hweight : (∑ i, ∑ j, M' i j*cost i j) =
          (∑ i, ∑ j, M i j*cost i j) - δ*(∑ i, cost i (σ i)) := by
        simp [M', sub_mul, Finset.sum_sub_distrib, ite_mul, ← Finset.mul_sum]
      have hsub : support M' ⊆ support M := by
        intro z hz
        have hz' := (Finset.mem_filter.mp hz).2
        have hle : M' z.1 z.2 ≤ M z.1 z.2 := by
          dsimp [M']; split_ifs <;> linarith
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hz' hle⟩
      have hne : support M' ≠ support M := by
        intro heq
        have hmem : (i0, σ i0) ∈ support M := by simp [support, hσ]
        rw [← heq] at hmem
        simp [support, M', δ] at hmem
      have hlt : (support M').card < m := by
        rw [← hm]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      have hremaining : 0 < t-δ := by
        by_contra h
        have heq : t-δ = 0 := le_antisymm (le_of_not_gt h) (sub_nonneg.mpr hδt)
        have hz (i j : Fin n) : M' i j = 0 := by
          have hsum : ∑ j, M' i j = 0 := (hr' i).trans heq
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hM' i j)).mp hsum j
              (Finset.mem_univ _)
        have hw : (∑ i, ∑ j, M' i j*cost i j) = 0 := by simp [hz]
        rw [hw] at hweight
        have htd : t = δ := sub_eq_zero.mp heq
        apply hcheap
        rw [htd]
        linarith
      obtain ⟨τ, hτ⟩ := ih (support M').card hlt M' rfl (t-δ) hremaining hM' hr' hc'
      refine ⟨τ, ?_⟩
      rw [hweight] at hτ
      have h1 := mul_le_mul_of_nonneg_left hτ ht.le
      have h2 := mul_pos hδ (sub_pos.mpr (lt_of_not_ge hcheap))
      have h3 : 0 ≤ (t-δ)*( (∑ i, ∑ j, M i j*cost i j) - t*(∑ i, cost i (τ i))) := by
        nlinarith only [h1, h2]
      exact (mul_nonneg_iff_of_pos_left hremaining).mp h3 |> sub_nonneg.mp
  exact main (support W).card W rfl s hs hW hrow hcol

private theorem spectral_adjoint_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  simpa only [Matrix.star_eq_conjTranspose] using! hU.2

theorem frobeniusSq_adjoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    frobeniusSq Aᴴ = frobeniusSq A := by
  unfold frobeniusSq
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

theorem frobeniusSq_unitary_right (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    frobeniusSq (A*U) = frobeniusSq A := by
  calc
    _ = frobeniusSq (A*U)ᴴ := (frobeniusSq_adjoint _).symm
    _ = frobeniusSq (Uᴴ*Aᴴ) := by rw [Matrix.conjTranspose_mul]
    _ = frobeniusSq Aᴴ := frobeniusSq_unitary_left n m Uᴴ Aᴴ (spectral_adjoint_unitary hU)
    _ = frobeniusSq A := frobeniusSq_adjoint A

theorem unitary_squared_entries_balanced (n : ℕ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (∀ i, ∑ j, ‖P i j‖^2 = 1) ∧ (∀ j, ∑ i, ‖P i j‖^2 = 1) := by
  have hleft : Pᴴ*P = 1 := by simpa only [Matrix.star_eq_conjTranspose] using!
    Matrix.mem_unitaryGroup_iff'.mp hP
  have hright : P*Pᴴ = 1 := by simpa only [Matrix.star_eq_conjTranspose] using!
    Matrix.mem_unitaryGroup_iff.mp hP
  have hprod (z : ℂ) : (starRingEnd ℂ) z*z = ((‖z‖^2 : ℝ) : ℂ) := by
    change star z*z = _
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hprod' (z : ℂ) : z*(starRingEnd ℂ) z = ((‖z‖^2 : ℝ) : ℂ) := by
    rw [mul_comm]
    exact hprod z
  constructor
  · intro i
    apply Complex.ofReal_injective
    have h := congrArg (fun A => A i i) hright
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      hprod', Complex.ofReal_sum] using! h
  · intro j
    apply Complex.ofReal_injective
    have h := congrArg (fun A => A j j) hleft
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      hprod, Complex.ofReal_sum] using! h

theorem normal_spectral_matching (n : ℕ) (C D : Matrix (Fin n) (Fin n) ℂ)
    (hC : Cᴴ*C = C*Cᴴ) (hD : Dᴴ*D = D*Dᴴ) :
    ∃ (E F : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n → ℂ) (σ : Equiv.Perm (Fin n)),
      E ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ F ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      C*E = E*Matrix.diagonal c ∧ D*F = F*Matrix.diagonal d ∧
      (∑ i, ‖c i-d (σ i)‖^2) ≤ frobeniusSq (C-D) := by
  classical
  obtain ⟨E, c, hE, hCE⟩ := normal_matrix_eigenbasis n C hC
  obtain ⟨F, d, hF, hDF⟩ := normal_matrix_eigenbasis n D hD
  have hEl : Eᴴ*E = 1 := by simpa only [Matrix.star_eq_conjTranspose] using!
    Matrix.mem_unitaryGroup_iff'.mp hE
  have hEr : E*Eᴴ = 1 := by simpa only [Matrix.star_eq_conjTranspose] using!
    Matrix.mem_unitaryGroup_iff.mp hE
  let P := Eᴴ*F
  have hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (Matrix.unitaryGroup (Fin n) ℂ).mul_mem (spectral_adjoint_unitary hE) hF
  obtain ⟨hrow, hcol⟩ := unitary_squared_entries_balanced n P hP
  obtain ⟨σ, hσ⟩ := balanced_permutation_cost n (fun i j => ‖P i j‖^2)
    (fun i j => ‖c i-d j‖^2) 1 (by norm_num) (fun _ _ => sq_nonneg _) hrow hcol
  have hEC : Eᴴ*C = Matrix.diagonal c*Eᴴ := by
    calc
      _ = (Eᴴ*(C*E))*Eᴴ := by simp [Matrix.mul_assoc, hEr]
      _ = (Eᴴ*(E*Matrix.diagonal c))*Eᴴ := by rw [hCE]
      _ = _ := by simp [← Matrix.mul_assoc, hEl]
  have htransport : Eᴴ*(C-D)*F = Matrix.diagonal c*P - P*Matrix.diagonal d := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hEC, Matrix.mul_assoc Eᴴ D F, hDF]
    simp [P, Matrix.mul_assoc]
  have hcost : (∑ i, ∑ j, ‖P i j‖^2*‖c i-d j‖^2) = frobeniusSq (C-D) := by
    have hnorm : frobeniusSq (Eᴴ*(C-D)*F) = frobeniusSq (C-D) := by
      rw [frobeniusSq_unitary_right n n _ F hF,
        frobeniusSq_unitary_left n n Eᴴ _ (spectral_adjoint_unitary hE)]
    rw [htransport] at hnorm
    rw [← hnorm]
    unfold frobeniusSq
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    change ‖P i j‖^2*‖c i-d j‖^2 = ‖c i*P i j - P i j*d j‖^2
    rw [show c i*P i j-P i j*d j = (c i-d j)*P i j by ring, norm_mul, mul_pow, mul_comm]
  refine ⟨E, F, c, d, σ, hE, hF, hCE, hDF, ?_⟩
  simpa [hcost] using! hσ

theorem frobeniusSq_eigenvalue_distance (n : ℕ) (A E : Matrix (Fin n) (Fin n) ℂ)
    (μ : Fin n → ℂ) (hE : E ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hAE : A*E = E*Matrix.diagonal μ) :
    frobeniusSq (A-1) = ∑ i, ‖μ i-1‖^2 := by
  have hEl : Eᴴ*E = 1 := by simpa only [Matrix.star_eq_conjTranspose] using!
    Matrix.mem_unitaryGroup_iff'.mp hE
  have htransport : Eᴴ*(A-1)*E = Matrix.diagonal (fun i => μ i-1) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_assoc Eᴴ A E, hAE, ← Matrix.mul_assoc, hEl, Matrix.one_mul]
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  calc
    _ = frobeniusSq (Eᴴ*(A-1)*E) := by
      rw [frobeniusSq_unitary_right n n _ E hE,
        frobeniusSq_unitary_left n n Eᴴ _ (spectral_adjoint_unitary hE)]
    _ = frobeniusSq (Matrix.diagonal (fun i => μ i-1)) := by rw [htransport]
    _ = _ := by simp [frobeniusSq, Matrix.diagonal, apply_ite]

private theorem spectral_unitary_normal {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ*U = U*Uᴴ := by
  have hL : Uᴴ*U = 1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  have hR : U*Uᴴ = 1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.2
  rw [hL, hR]

theorem normalSpectralPerturbation_answer : NormalSpectralPerturbation := by
  refine ⟨frobeniusSq_unitary_left, normal_spectral_matching, ?_⟩
  intro n A B hA hB
  obtain ⟨E, a, hE, hAE⟩ := normal_matrix_eigenbasis n A (spectral_unitary_normal hA)
  have hAB := (Matrix.unitaryGroup (Fin n) ℂ).mul_mem hA hB
  obtain ⟨F, G, b, ab, σ, hF, hG, hBF, hABG, hmatch⟩ :=
    normal_spectral_matching n B (A*B) (spectral_unitary_normal hB)
      (spectral_unitary_normal hAB)
  refine ⟨E, F, G, a, b, ab, σ, hE, hF, hG, hAE, hBF, hABG, ?_⟩
  have hbound : frobeniusSq (B-A*B) = ∑ i, ‖a i-1‖^2 := by
    calc
      _ = frobeniusSq ((1-A)*B) := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = frobeniusSq (1-A) := frobeniusSq_unitary_right n n (1-A) B hB
      _ = frobeniusSq (A-1) := by
        rw [show 1-A = -(A-1) by abel]
        simp only [frobeniusSq, Matrix.neg_apply, norm_neg]
      _ = _ := frobeniusSq_eigenvalue_distance n A E a hE hAE
  rw [hbound] at hmatch
  exact hmatch

end Qatlib.Concepts.WalkFind.WalkSpectrum
