/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem4QuadraticSpeedupWithKnownAQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem16Stat
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-!
# Exact search under a cardinality promise

`bhmt_theorem16_promise_exact` proves the bounded cardinality-promise formulation of exact
search from [BrassardEtAl2002]. The proof identifies the Fourier-prepared marked mass and
verifies normalization and program costs; `not_bhmt_theorem16_contract` also refutes the
unrestricted contract.

## Main statements

* `not_bhmt_theorem16_contract`: failure of the contract without a bound on the promised
  cardinality.
* `bhmt_theorem16_promise_exact`: exact search for promised cardinality between one and `N`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16

/-- The unrestricted promise-search specification `Theorem16Spec.expected` is false. -/
theorem not_bhmt_theorem16_contract :
    ¬ Theorem16Spec.expected := by
  intro h
  obtain ⟨design,c,C,C₂,hc,hC,_hC₂,hspec⟩ := h
  obtain ⟨t₀,ht₀⟩ := exists_nat_gt (C^2)
  have htpos : (0:ℝ)<t₀ := lt_of_le_of_lt (sq_nonneg C) ht₀
  have ht₀pos : 0<t₀ := by exact_mod_cast htpos
  have hroot : 0<Real.sqrt (t₀:ℝ) := Real.sqrt_pos.mpr htpos
  have hCroot : C<Real.sqrt (t₀:ℝ) := by
    nlinarith [Real.sq_sqrt htpos.le]
  have hb := hspec 1 (by decide) (∅:Finset (Fin 1)) t₀ ht₀pos (Or.inl rfl)
  dsimp only at hb
  simp only [Nat.cast_one, div_one] at hb
  obtain ⟨_hr0,_hr1,_hnorm,_hgood,_hzero,hlo,hup,_hcost⟩ := hb
  let k := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (design (t₀:ℝ)).2
  have hk0 : (0:ℝ)<k := (div_pos hc hroot).trans_le hlo
  have hkn : 0<k := by exact_mod_cast hk0
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hkn
  have hklt : (k:ℝ)<1 := hup.trans_lt ((div_lt_one hroot).mpr hCroot)
  linarith

set_option autoImplicit false

/-- The exact-amplification program with iteration parameter `m` contains exactly `m`
instructions with label five. -/
theorem promise_program_marks (m : ℕ) :
    marksCount (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m) = m := by
  induction m with
  | zero => simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program, marksCount]
  | succ m ih =>
    simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program, marksCount,
      List.filter_append, List.length_append, List.replicate_succ, List.flatten_cons] at *
    norm_num at *
    omega

/-- The marked-instruction count plus one is bounded by the call count of the
exact-amplification program. -/
theorem promise_program_mark_budget (m : ℕ) :
    marksCount (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m) + 1 ≤
      Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program m) := by
  rw [promise_program_marks,
      Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program_calls]
  omega

/-- The marked-instruction count plus one is bounded by the call count of the program chosen by
the exact-amplification design. -/
theorem promise_design_mark_budget (a : ℝ) :
    marksCount (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design a).2 + 1 ≤
      Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design a).2 := by
  unfold Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design
  split
  · norm_num [marksCount, Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls]
  · exact promise_program_mark_budget _

/-- If `0 < t₀ ≤ N`, the marked fraction `t₀ / N` lies in `(0, 1]`. -/
theorem promise_probability_domain (N t₀ : ℕ) (hN : 0 < N) (ht : 0 < t₀)
    (hbound : t₀ ≤ N) : 0 < (t₀ : ℝ)/(N : ℝ) ∧ (t₀ : ℝ)/(N : ℝ) ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · exact div_pos (by exact_mod_cast ht) hNr
  · exact (div_le_one hNr).mpr (by exact_mod_cast hbound)

/-- The marked projection associated with an empty marked set is zero. -/
theorem promise_empty_projection (N : ℕ) :
    Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ))
      (markLabels N ∅) = 0 := by
  simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection, markLabels]

/-- For an empty marked set, every promise-search program has zero marked mass. -/
theorem promise_zero_good_mass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hS : S.card = 0) (r : ℝ) (prog : List (Fin 6)) :
    promiseGoodMass hN S r prog = 0 := by
  have hs := Finset.card_eq_zero.mp hS
  subst S
  simp [promiseGoodMass, promise_empty_projection]

section Generic

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Equality of the sums of self-inner-products of two vector pairs implies equality of their
total squared norms. -/
private lemma inner_norm_pair (z w x y : H)
    (h : inner ℂ z z + inner ℂ w w = inner ℂ x x + inner ℂ y y) :
    ‖z‖^2 + ‖w‖^2 = ‖x‖^2 + ‖y‖^2 := by
  have hc : RCLike.re (inner ℂ z z + inner ℂ w w)
      = RCLike.re (inner ℂ x x + inner ℂ y y) := by rw [h]
  rw [(RCLike.re (K := ℂ)).map_add, (RCLike.re (K := ℂ)).map_add] at hc
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact hc

/-- Expands the self-inner-product of a real linear combination of two vectors into diagonal and
cross terms. -/
private lemma combo_inner (r₁ r₂ : ℝ) (x y : H) :
    inner ℂ ((r₁:ℂ) • x + (r₂:ℂ) • y) ((r₁:ℂ) • x + (r₂:ℂ) • y) =
      ((r₁:ℂ))^2 * inner ℂ x x + ((r₂:ℂ))^2 * inner ℂ y y +
      ((r₁:ℂ))*((r₂:ℂ)) * (inner ℂ x y + inner ℂ y x) := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  ring

/-- The Householder reflection about a unit vector preserves self-inner-products. -/
private lemma householder_inner (e x : H) (he : ‖e‖ = 1) :
    inner ℂ (-x + (2 * inner ℂ e x) • e) (-x + (2 * inner ℂ e x) • e) = inner ℂ x x := by
  have hee : inner ℂ e e = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  have hxe : inner ℂ x e = starRingEnd ℂ (inner ℂ e x) := (_root_.inner_conj_symm x e).symm
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_neg_left, inner_neg_right, hee, hxe, map_mul, map_ofNat]
  norm_num
  ring

/-- The reflection defined by an orthogonal projection preserves self-inner-products. -/
private lemma star_reflection_inner (K : Submodule ℂ H) [K.HasOrthogonalProjection] (x : H) :
    inner ℂ (x - (2:ℂ) • K.starProjection x) (x - (2:ℂ) • K.starProjection x)
      = inner ℂ x x := by
  have h0 : inner ℂ (x - K.starProjection x) (K.starProjection x) = 0 :=
    (Submodule.mem_orthogonal' K _).1 (Submodule.sub_starProjection_mem_orthogonal x) _
      (Submodule.starProjection_apply_mem K x)
  have h0' : inner ℂ (K.starProjection x) (x - K.starProjection x) = 0 := by
    rw [show inner ℂ (K.starProjection x) (x - K.starProjection x)
        = starRingEnd ℂ (inner ℂ (x - K.starProjection x) (K.starProjection x)) from
      (_root_.inner_conj_symm _ _).symm, h0, map_zero]
  have hbx : inner ℂ (K.starProjection x) x
      = inner ℂ (K.starProjection x) (K.starProjection x) := by
    calc inner ℂ (K.starProjection x) x
        = inner ℂ (K.starProjection x) ((x - K.starProjection x) + K.starProjection x) := by
          rw [sub_add_cancel]
      _ = inner ℂ (K.starProjection x) (x - K.starProjection x)
            + inner ℂ (K.starProjection x) (K.starProjection x) := inner_add_right _ _ _
      _ = inner ℂ (K.starProjection x) (K.starProjection x) := by rw [h0', zero_add]
  calc inner ℂ (x - (2:ℂ) • K.starProjection x) (x - (2:ℂ) • K.starProjection x)
      = inner ℂ ((x - K.starProjection x) - K.starProjection x)
          ((x - K.starProjection x) - K.starProjection x) := by
        rw [show x - (2:ℂ) • K.starProjection x
          = (x - K.starProjection x) - K.starProjection x from by module]
    _ = inner ℂ ((x - K.starProjection x) + K.starProjection x)
          ((x - K.starProjection x) + K.starProjection x) := by
        simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, h0, hbx]
        ring
    _ = inner ℂ x x := by rw [sub_add_cancel]

/-- Each exact-amplification instruction preserves the sum of self-inner-products of the two
state components when `r ∈ [0, 1]`. -/
private lemma step_inner_sq (A : H ≃ₗᵢ[ℂ] H) (e : H) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (r : ℝ) (he : ‖e‖ = 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (k : Fin 6) (v : H × H) :
    inner ℂ (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v).1
        (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v).1 +
      inner ℂ (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v).2
        (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v).2 =
      inner ℂ v.1 v.1 + inner ℂ v.2 v.2 := by
  have hcs : (Real.sqrt (1-r))^2 + (Real.sqrt r)^2 = 1 := by
    have h₁ := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
    have h₂ := Real.sq_sqrt hr
    linarith
  have hc2 : ((Real.sqrt (1-r) : ℝ) : ℂ)^2 + ((Real.sqrt r : ℝ) : ℂ)^2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, hcs]
    norm_num
  rcases k with ⟨n, hn⟩
  interval_cases n
  · simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step]
    rw [A.inner_map_map, A.inner_map_map]
  · simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step]
    rw [A.symm.inner_map_map, A.symm.inner_map_map]
  · simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step]
    rw [sub_eq_add_neg, ← neg_smul, ← Complex.ofReal_neg,
      combo_inner (Real.sqrt (1-r)) (-(Real.sqrt r)) v.1 v.2,
      combo_inner (Real.sqrt r) (Real.sqrt (1-r)) v.1 v.2, Complex.ofReal_neg]
    linear_combination hc2 * (inner ℂ v.1 v.1 + inner ℂ v.2 v.2)
  · simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step]
    rw [← Complex.ofReal_neg,
      combo_inner (Real.sqrt (1-r)) (Real.sqrt r) v.1 v.2,
      combo_inner (-(Real.sqrt r)) (Real.sqrt (1-r)) v.1 v.2, Complex.ofReal_neg]
    linear_combination hc2 * (inner ℂ v.1 v.1 + inner ℂ v.2 v.2)
  · simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step]
    rw [householder_inner e v.1 he]
    simp only [inner_neg_left, inner_neg_right, neg_neg]
  · simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step]
    rw [star_reflection_inner]

/-- An exact-amplification run starting from a unit vector has total squared norm one when `r ∈
[0, 1]`. -/
private theorem run_total_norm_sq (A : H ≃ₗᵢ[ℂ] H) (e : H) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (r : ℝ) (he : ‖e‖ = 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (prog : List (Fin 6)) :
    ‖(Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e K.starProjection r prog).1‖^2 +
      ‖(Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e K.starProjection r prog).2‖^2 = 1 := by
  have hind : ∀ (l : List (Fin 6)) (v : H × H),
      inner ℂ (l.foldl (fun v k => Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v) v).1
          (l.foldl (fun v k => Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v) v).1 +
        inner ℂ (l.foldl (fun v k => Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v) v).2
          (l.foldl (fun v k => Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v) v).2 =
        inner ℂ v.1 v.1 + inner ℂ v.2 v.2 := by
    intro l
    induction l with
    | nil => intro v; rfl
    | cons k l ih =>
      intro v
      rw [List.foldl_cons,
          ih (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e K.starProjection r k v)]
      exact step_inner_sq A e K r he hr hr1 k v
  have hrun := hind prog (e, 0)
  simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run] at hrun ⊢
  have h2 := inner_norm_pair _ _ e (0:H) (by simpa using! hrun)
  rw [h2]
  simp [he]

end Generic

section Euclidean
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh16

/-- The canonical finite Hilbert basis vector is the corresponding coordinate single vector. -/
private lemma finEB_single (N : ℕ) (i : Fin N) :
    finEB N i = EuclideanSpace.single i (1:ℂ) := by
  have h : finEB N = (EuclideanSpace.basisFun (Fin N) ℂ).toHilbertBasis := rfl
  rw [h]
  exact (congrFun (OrthonormalBasis.coe_toHilbertBasis
    (EuclideanSpace.basisFun (Fin N) ℂ)) i).trans (by simp)

/-- The integer-label marked predicate holds on coordinate `i` exactly when `i ∈ S`. -/
private lemma markLabels_iff (N : ℕ) (S : Finset (Fin N)) (i : Fin N) :
    markLabels N S (i.val : ℤ) = true ↔ i ∈ S := by
  simp only [markLabels, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp h
    have hjq : j = i := Fin.val_inj.mp (by exact_mod_cast hval)
    rwa [hjq] at hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Projecting the sum of all coordinate basis vectors onto the marked subspace gives the sum
over marked coordinates. -/
private lemma proj_sum_marked (N : ℕ) (S : Finset (Fin N)) :
    (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
        {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)})).topologicalClosure.starProjection
      (∑ i : Fin N, finEB N i) = ∑ i ∈ S, finEB N i := by
  classical
  have hspan : ∀ i ∈ S, finEB N i ∈ Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
      {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)}) := by
    intro i hi
    exact Submodule.subset_span ⟨i, (markLabels_iff N S i).mpr hi, rfl⟩
  have hw : (∑ i ∈ S, finEB N i) ∈ (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
      {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)})).topologicalClosure :=
    (Submodule.le_topologicalClosure _) (Submodule.sum_mem _ (fun i hi => hspan i hi))
  have hd : (∑ i : Fin N, finEB N i) - ∑ i ∈ S, finEB N i = ∑ i ∈ Finset.univ \ S, finEB N i := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S)]
    abel
  have horth : ∀ j ∈ S, inner ℂ (∑ i ∈ Finset.univ \ S, finEB N i) (finEB N j) = 0 := by
    intro j hj
    rw [sum_inner]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hne : i ≠ j := fun h => (Finset.mem_sdiff.mp hi).2 (h ▸ hj)
    exact (finEB N).orthonormal.2 hne
  have hdKorth : ∑ i ∈ Finset.univ \ S, finEB N i ∈ (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
      {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)}))ᗮ := by
    have key : ∀ y : EuclideanSpace ℂ (Fin N), y ∈ (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
        {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)})) →
        inner ℂ (∑ i ∈ Finset.univ \ S, finEB N i) y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, hj, hxj⟩ := (Set.mem_image _ _ _).mp hx
        rw [← hxj]
        exact horth j ((markLabels_iff N S j).mp hj)
      | zero => simp
      | add x y _ _ ihx ihy => rw [inner_add_right, ihx, ihy, add_zero]
      | smul a x _ ih => rw [inner_smul_right, ih, mul_zero]
    exact (Submodule.mem_orthogonal' _ _).2 key
  refine Submodule.eq_starProjection_of_mem_orthogonal hw ?_
  rw [hd]
  rw [show (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
      {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)})).topologicalClosureᗮ
      = (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
      {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)}))ᗮ from by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.triorthogonal_eq_orthogonal]]
  exact hdKorth

/-- The Fourier transform sends the zero coordinate basis vector to the normalized uniform
superposition. -/
private lemma qft_uniform (N : ℕ) (hN : 0 < N) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)) (finEB N ⟨0, hN⟩)
      = ((Real.sqrt (N:ℝ) : ℝ) : ℂ)⁻¹ • ∑ i : Fin N, finEB N i := by
  have hsum : ∑ i : Fin N, finEB N i = WithLp.toLp 2 (fun _ : Fin N => (1:ℂ)) := by
    refine (WithLp.ofLp_injective 2).eq_iff.mp ?_
    rw [WithLp.ofLp_sum, WithLp.ofLp_toLp]
    funext j
    simp only [Finset.sum_apply, finEB_single, PiLp.ofLp_single, Pi.single_apply]
    simp
  have he0 : WithLp.ofLp (finEB N ⟨0, hN⟩) = Qatlib.Foundations.PureStateMath.Ket (⟨0, hN⟩ : Fin N) := by
    rw [finEB_single N ⟨0, hN⟩, PiLp.ofLp_single]
    funext j
    simp [Qatlib.Foundations.PureStateMath.Ket, Pi.single_apply]
  have hA : (Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
      (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)) (finEB N ⟨0, hN⟩)
      = WithLp.toLp 2 (fun _ : Fin N => ((Real.sqrt (N:ℝ) : ℝ) : ℂ)⁻¹) := by
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean_apply]
    refine (WithLp.toLp_injective 2).eq_iff.mp ?_
    rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, he0,
      show (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N).mulVec (Qatlib.Foundations.PureStateMath.Ket (⟨0, hN⟩ : Fin N))
        = Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
          (Qatlib.Foundations.PureStateMath.Ket (⟨0, hN⟩ : Fin N)) from rfl,
      Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_ket_zero N hN]
  have hsm : ((Real.sqrt (N:ℝ) : ℝ) : ℂ)⁻¹ • ∑ i : Fin N, finEB N i
      = WithLp.toLp 2 (fun _ : Fin N => ((Real.sqrt (N:ℝ) : ℝ) : ℂ)⁻¹) := by
    refine (WithLp.ofLp_injective 2).eq_iff.mp ?_
    rw [WithLp.ofLp_smul, hsum, WithLp.ofLp_toLp]
    funext j
    simp
  rw [hA, hsm]

/-- The squared norm of a sum of distinct vectors from a Hilbert basis equals the number of
summands. -/
private lemma orth_norm_sum_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} [Fintype ι] (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    ‖∑ i ∈ s, b i‖^2 = (s.card : ℝ) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have h1 : ∑ i ∈ s, b i = ∑ i ∈ s, (1:ℂ) • b i := by simp
  have h2 : inner ℂ (∑ i ∈ s, (1:ℂ) • b i) (∑ i ∈ s, (1:ℂ) • b i)
      = ∑ i ∈ s, starRingEnd ℂ ((1:ℂ)) * (1:ℂ) := b.orthonormal.inner_sum _ _ s
  rw [h1, h2]
  simp

/-- The marked mass of the Fourier-prepared zero basis vector is `S.card / N`. -/
private theorem qft_mark_mass (N : ℕ) (hN : 0 < N) (S : Finset (Fin N)) :
    ‖(Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ)) (markLabels N S))
      ((Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)) (finEB N ⟨0, hN⟩))‖^2
      = (S.card : ℝ)/(N : ℝ) := by
  have hn : ‖((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹‖^2 = (N : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by exact_mod_cast hN.le)]
  rw [show Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ))
      (markLabels N S)
      = (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
        {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)})).topologicalClosure.starProjection
      from rfl,
    qft_uniform N hN, map_smul, proj_sum_marked N S, norm_smul, mul_pow, hn,
    orth_norm_sum_sq]
  rw [div_eq_inv_mul]

end Euclidean

/-- Establishes exact search for the promise that the marked cardinality is zero or a known `t₀`
with `0 < t₀ ≤ N`, including normalization and inverse-square-root call bounds [Brassard et
al., Theorem 16][BrassardEtAl2002]. -/
theorem bhmt_theorem16_promise_exact : BHMTTh16.Theorem16 := by
  refine ⟨Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design, 1, Real.pi/2+2, Real.pi/2+2,
    by norm_num, by positivity, by positivity, ?_⟩
  intro N hN S t₀ ht₀ htN _hor
  obtain ⟨ha0, ha1⟩ := promise_probability_domain N t₀ hN ht₀ htN
  have he : ‖finEB N ⟨0, hN⟩‖ = 1 := (finEB N).orthonormal.1 ⟨0, hN⟩
  have hA1 : ‖(Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
      (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)) (finEB N ⟨0, hN⟩)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact he
  have hK : (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ))
      (markLabels N S))
      = (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
        {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)})).topologicalClosure.starProjection :=
    rfl
  have hmass := qft_mark_mass N hN S
  have hproj := Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.projection
    (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
      {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)})).topologicalClosure
    ((Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
      (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)) (finEB N ⟨0, hN⟩)) hA1
  have hnorm : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ prog : List (Fin 6),
      ‖(promiseRun hN S r prog).1‖^2 + ‖(promiseRun hN S r prog).2‖^2 = 1 := by
    intro r hr hr1 prog
    have h := run_total_norm_sq
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)) (finEB N ⟨0, hN⟩)
      (Submodule.span ℂ ((fun i : Fin N => finEB N i) ''
        {i : Fin N | markLabels N S ((i : Fin N).val : ℤ)})).topologicalClosure
      r he hr hr1 prog
    rw [← hK] at h
    simpa [promiseRun] using! h
  (try dsimp only)
  set a : ℝ := (t₀:ℝ)/(N:ℝ) with hadef
  by_cases ha1eq : a = 1
  · have hdesign : Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design a = (0, [0]) := by
      simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design, ha1eq]
    have hbud := promise_design_mark_budget a
    rw [hdesign] at hbud
    have hc1 : Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls [0] = 1 := by
      simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls]
    rw [hc1] at hbud
    rw [hdesign]
    (try dsimp only)
    rw [ha1eq]
    simp only [Real.sqrt_one, div_one]
    refine ⟨by norm_num, by norm_num, hnorm 0 (by norm_num) (by norm_num) [0], ?_,
      fun h0 => promise_zero_good_mass hN S h0 0 [0], by rw [hc1]; norm_num, ?_, ?_⟩
    · intro hcard
      simp only [promiseGoodMass, promiseRun, Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run, List.foldl_cons,
        List.foldl_nil, Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step, Fin.val_zero, map_zero, norm_zero]
      rw [hmass, hcard]
      have hz : (0:ℝ)^2 = 0 := by norm_num
      rw [hz, add_zero, ← hadef]
      exact ha1eq
    · rw [hc1]
      norm_num
      linarith [Real.pi_pos]
    · have hmarks : ((marksCount [0] : ℕ) + 1 : ℝ) ≤ 1 := by exact_mod_cast hbud
      linarith [Real.pi_pos]
  · have halt : a < 1 := lt_of_le_of_ne ha1 ha1eq
    obtain ⟨hd0, hd1, hr0, hr1, hra, hm, hlo, hhi⟩ :=
      Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.parameters a ha0 halt
    have hdesign : Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design a
        = (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.ratio a,
          Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program
            (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.iterations a)) := by
      simp [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.design, if_neg ha1eq]
    have hbud := promise_design_mark_budget a
    rw [hdesign] at hbud
    dsimp only at hbud
    have hcast : ((marksCount (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program
          (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.iterations a)) : ℕ) + 1 : ℝ)
        ≤ (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program
          (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.iterations a)) : ℝ) :=
      by exact_mod_cast hbud
    rw [hdesign]
    (try dsimp only)
    refine ⟨hr0, hr1, hnorm _ hr0 hr1 _, ?_,
      fun h0 => promise_zero_good_mass hN S h0 _ _, ?_, ?_, ?_⟩
    · intro hcard
      have hma : ‖(Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ))
          (markLabels N S))
          ((Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
            (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)) (finEB N ⟨0, hN⟩))‖^2 = a := by
        rw [hmass, hcard, hadef]
      rw [hK] at hma
      have hst := Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.exact_state
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.unitaryEuclidean (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
          (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN)) (finEB N ⟨0, hN⟩)
        (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection (finEB N) (fun i : Fin N => (i.val : ℤ)) (markLabels N S))
        a (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.ratio a)
        (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.angle a)
        (Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.iterations a)
        hA1 hproj.1 hma (by rw [hK, hproj.2.1, hma]) hr0 hr1 hd0 hd1 hra hm
      simpa [promiseGoodMass, promiseRun] using! hst.2
    · simpa only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program_calls, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using! hlo
    · simpa only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program_calls, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using! hhi
    · exact hcast.trans (by
        simpa only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact.program_calls, Nat.cast_add,
          Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using! hhi)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
