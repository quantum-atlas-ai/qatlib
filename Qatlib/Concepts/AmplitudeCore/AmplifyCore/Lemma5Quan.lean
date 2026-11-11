/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedQuan
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma5Stat

/-!
# Generalized amplitude amplification phase action

`zoo_amplitude_estimation_general_phase_action` proves the action of a generalized phase iterate
on the good and bad components when their squared norms are strictly between zero and one.
Supporting identities give the projection geometry, conjugation formula, and a unitary two
dimensional change of coordinates. See [BrassardEtAl2002] for background.

## Main statements

* `zoo_amplitude_estimation_general_phase_action`: For success probability strictly between zero
  and one, the generalized phase iterate satisfies the good and bad component formulas of
  [Brassard et al., Lemma 5][BrassardEtAl2002].
* `zoo_amplitude_estimation_general_phase_action_contract`: The generalized phase component
  action fulfills `Lemma5Spec.expected` from [Brassard et al., Lemma 5][BrassardEtAl2002].

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore

/-- Conjugating a rank one phase update about `e₀` by `A` gives the same phase update about `A
e₀`. -/
lemma zoo_amplitude_estimation_general_phase_action_conjugation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H ≃ₗᵢ[ℂ] H) (e₀ w : H) (p : ℂ) :
    A (A.symm w + ((p - 1) * inner ℂ e₀ (A.symm w)) • e₀) =
      w + ((p - 1) * inner ℂ (A e₀) w) • A e₀ := by
  rw [map_add, map_smul, A.apply_symm_apply, A.inner_map_eq_flip]

/-- The good and bad components have the stated projection identities and inner products with
the original unit vector. -/
lemma zoo_amplitude_estimation_general_phase_action_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : ClosedSubmodule ℂ H) (ψ : H) (hψ : ‖ψ‖ = 1) :
    let ψ₁ := G.toSubmodule.starProjection ψ
    let ψ₀ := ψ - ψ₁
    G.toSubmodule.starProjection ψ₁ = ψ₁ ∧
    G.toSubmodule.starProjection ψ₀ = 0 ∧
    inner ℂ ψ ψ₁ = (‖ψ₁‖ ^ 2 : ℝ) ∧
    inner ℂ ψ ψ₀ = 1 - (‖ψ₁‖ ^ 2 : ℝ) := by
  (try dsimp only)
  have hid : G.toSubmodule.starProjection (G.toSubmodule.starProjection ψ) =
      G.toSubmodule.starProjection ψ :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have hgood : inner ℂ ψ (G.toSubmodule.starProjection ψ) =
      (‖G.toSubmodule.starProjection ψ‖ ^ 2 : ℝ) := by
    rw [← hid, ← Submodule.inner_starProjection_left_eq_right, hid,
      inner_self_eq_norm_sq_to_K]
    simp only [Complex.ofReal_pow]
    rfl
  refine ⟨hid, ?_, hgood, ?_⟩
  · rw [map_sub, hid, sub_self]
  · rw [inner_sub_right, hgood, inner_self_eq_norm_sq_to_K, hψ]
    norm_num

/-- The two dimensional real rotation matrix with entries formed from `sqrt a` and `sqrt (1 -
a)`. -/
noncomputable def zoo_amplitude_estimation_general_phase_action_matrix (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt a : ℂ), -(Real.sqrt (1 - a) : ℂ);
     (Real.sqrt (1 - a) : ℂ), (Real.sqrt a : ℂ)]

/-- For `0 ≤ a ≤ 1`, the amplitude coordinate matrix multiplied by its conjugate transpose is
the identity. -/
lemma zoo_amplitude_estimation_general_phase_action_matrix_unitary
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    zoo_amplitude_estimation_general_phase_action_matrix a *
      (zoo_amplitude_estimation_general_phase_action_matrix a).conjTranspose = 1 := by
  have hs : (Real.sqrt a : ℂ) ^ 2 = (a : ℂ) := by
    exact_mod_cast Real.sq_sqrt ha
  have ht : (Real.sqrt (1 - a) : ℂ) ^ 2 = 1 - (a : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr ha')
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zoo_amplitude_estimation_general_phase_action_matrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [hs, ht]

/-- Expands the two phase action expressions into their coefficients on `x` and `y`. -/
lemma zoo_amplitude_estimation_general_phase_action_transport
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (x y : H) (a : ℝ) (ha : 0 < a) (ha' : a < 1)
    (p q : ℂ) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    (-q) • x + (q * (1 - p) * (a : ℂ)) • (x + y) =
      (q * ((1 - p) * (a : ℂ) - 1)) • x +
        (q * (1 - p) * (a : ℂ)) • y ∧
    -y + ((1 - p) * (1 - (a : ℂ))) • (x + y) =
      ((1 - p) * (1 - (a : ℂ))) • x - ((1 - p) * (a : ℂ) + p) • y := by
  let B := zoo_amplitude_estimation_general_phase_action_matrix a
  let g : Fin 2 → Bool := ![true, false]
  let ξ : Fin 2 → ℂ := fun i => B i 0
  let ξ₁ := RankOneReflection.goodPart g ξ
  let ξ₀ := RankOneReflection.badPart g ξ
  have hB : B * B.conjTranspose = 1 :=
    zoo_amplitude_estimation_general_phase_action_matrix_unitary a ha.le ha'.le
  have hs0 : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
  have ht0 : (Real.sqrt (1 - a) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (sub_pos.mpr ha')).ne'
  let T : (Fin 2 → ℂ) →ₗ[ℂ] H :=
    { toFun := fun v => (v 0 / (Real.sqrt a : ℂ)) • x +
          (v 1 / (Real.sqrt (1 - a) : ℂ)) • y
      map_add' := by
        intro v w
        dsimp only [Pi.add_apply]
        rw [add_div, add_div, add_smul, add_smul]
        abel
      map_smul' := by
        intro c v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          mul_div_assoc, mul_smul, smul_add] }
  have hTξ : T ξ = x + y := by
    simp [T, ξ, B, zoo_amplitude_estimation_general_phase_action_matrix, hs0, ht0]
  have hTξ₁ : T ξ₁ = x := by
    simp [T, ξ₁, ξ, g, B, RankOneReflection.goodPart,
      zoo_amplitude_estimation_general_phase_action_matrix, hs0]
  have hTξ₀ : T ξ₀ = y := by
    simp [T, ξ₀, ξ, g, B, RankOneReflection.badPart,
      zoo_amplitude_estimation_general_phase_action_matrix, ht0]
  have haB : (∑ i, Complex.normSq (ξ₁ i) : ℝ) = a := by
    simp [ξ₁, ξ, g, B, RankOneReflection.goodPart,
      zoo_amplitude_estimation_general_phase_action_matrix, Fin.sum_univ_two,
      Complex.normSq_ofReal, Real.mul_self_sqrt ha.le]
  have hraw := zoo_counting_good_bad_phase_action 1 B g p q ξ hB
  change (RankOneReflection.iterate B g p q).mulVec ξ₁ = _ ∧
    (RankOneReflection.iterate B g p q).mulVec ξ₀ = _ at hraw
  have hgoodOverlap : (∑ i, star (B i 0) * ξ₁ i : ℂ) = (a : ℂ) := by
    rw [zoo_counting_two_dimensional_phase_action_overlap_good, haB]
  have hbadOverlap : (∑ i, star (B i 0) * ξ₀ i : ℂ) = 1 - (a : ℂ) := by
    rw [zoo_counting_two_dimensional_phase_action_overlap_bad,
      zoo_counting_two_dimensional_phase_action_bad_normSq B g hB, haB]
    push_cast
    rfl
  rw [hgoodOverlap, hbadOverlap] at hraw
  change (RankOneReflection.iterate B g p q).mulVec ξ₁ =
      (-q) • ξ₁ + (q * (1 - p) * (a : ℂ)) • ξ ∧
    (RankOneReflection.iterate B g p q).mulVec ξ₀ =
      -ξ₀ + ((1 - p) * (1 - (a : ℂ))) • ξ at hraw
  have hfinite := zoo_counting_two_dimensional_phase_action 1 B g p q hB hp hq
  change (RankOneReflection.iterate B g p q).mulVec ξ₁ = _ ∧
    (RankOneReflection.iterate B g p q).mulVec ξ₀ = _ at hfinite
  change (RankOneReflection.iterate B g p q).mulVec ξ₁ =
      (q * ((1 - p) * ((∑ i, Complex.normSq (ξ₁ i) : ℝ) : ℂ) - 1)) • ξ₁ +
      (q * (1 - p) * ((∑ i, Complex.normSq (ξ₁ i) : ℝ) : ℂ)) • ξ₀ ∧
    (RankOneReflection.iterate B g p q).mulVec ξ₀ =
      (-((1 - p) * ((∑ i, Complex.normSq (ξ₁ i) : ℝ) : ℂ) + p)) • ξ₀ +
      ((1 - p) * (1 - ((∑ i, Complex.normSq (ξ₁ i) : ℝ) : ℂ))) • ξ₁ at hfinite
  rw [haB] at hfinite
  constructor
  · have h := congrArg T (hraw.1.symm.trans hfinite.1)
    simpa only [map_add, map_smul, hTξ₁, hTξ₀, hTξ] using h
  · have h := congrArg T (hraw.2.symm.trans hfinite.2)
    simpa only [map_add, map_smul, map_neg, hTξ₁, hTξ₀, hTξ,
      neg_smul, sub_eq_add_neg, add_comm] using h

/-- For success probability strictly between zero and one, the generalized phase iterate
satisfies the good and bad component formulas of [Brassard et al., Lemma
5][BrassardEtAl2002]. -/
theorem zoo_amplitude_estimation_general_phase_action :
  ∀ (ι H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H) (zeroIndex : ι)
    (A : H ≃ₗᵢ[ℂ] H) (χ : ι → Bool) (φ ϕ : ℝ),
  0 ≤ φ → φ < 2 * Real.pi →
  0 ≤ ϕ → ϕ < 2 * Real.pi →
  let G := amplitudeEstimationGoodSubspace basis χ;
  let ψ : H := A (basis zeroIndex);
  let ψ₁ : H := G.toSubmodule.starProjection ψ;
  let ψ₀ : H := ψ - ψ₁;
  let a : ℝ := ‖ψ₁‖ ^ 2;
  0 < a → a < 1 →
  let p : ℂ := Complex.exp ((φ : ℂ) * Complex.I);
  let q : ℂ := Complex.exp ((ϕ : ℂ) * Complex.I);
  let Q : H → H := amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ;
  Q ψ₁ =
      (q * ((1 - p) * (a : ℂ) - 1)) • ψ₁ +
      (q * (1 - p) * (a : ℂ)) • ψ₀ ∧
  Q ψ₀ =
      ((1 - p) * (1 - (a : ℂ))) • ψ₁ -
      ((1 - p) * (a : ℂ) + p) • ψ₀ := by
  intro ι H _ _ _ basis zeroIndex A χ φ ϕ _hφ₀ _hφ₂π _hϕ₀ _hϕ₂π
  (try dsimp only)
  let G := amplitudeEstimationGoodSubspace basis χ
  let ψ := A (basis zeroIndex)
  let ψ₁ := G.toSubmodule.starProjection ψ
  let ψ₀ := ψ - ψ₁
  let a : ℝ := ‖ψ₁‖ ^ 2
  intro ha ha'
  let p : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
  let q : ℂ := Complex.exp ((ϕ : ℂ) * Complex.I)
  change amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ ψ₁ =
      (q * ((1 - p) * (a : ℂ) - 1)) • ψ₁ + (q * (1 - p) * (a : ℂ)) • ψ₀ ∧
    amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ ψ₀ =
      ((1 - p) * (1 - (a : ℂ))) • ψ₁ - ((1 - p) * (a : ℂ) + p) • ψ₀
  have hψ : ‖ψ‖ = 1 := by
    exact (A.norm_map _).trans (basis.orthonormal.norm_eq_one zeroIndex)
  obtain ⟨hP₁, hP₀, hinner₁, hinner₀⟩ :=
    zoo_amplitude_estimation_general_phase_action_projection G ψ hψ
  change G.toSubmodule.starProjection ψ₁ = ψ₁ at hP₁
  change G.toSubmodule.starProjection ψ₀ = 0 at hP₀
  change inner ℂ ψ ψ₁ = (a : ℂ) at hinner₁
  change inner ℂ ψ ψ₀ = 1 - (a : ℂ) at hinner₀
  have hsplit : ψ = ψ₁ + ψ₀ := by dsimp [ψ₀]; abel
  have hgoodphase : ψ₁ + (q - 1) • G.toSubmodule.starProjection ψ₁ = q • ψ₁ := by
    rw [hP₁]
    module
  have hbadphase : ψ₀ + (q - 1) • G.toSubmodule.starProjection ψ₀ = ψ₀ := by
    rw [hP₀, smul_zero, add_zero]
  have hgood : amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ ψ₁ =
      (-q) • ψ₁ + (q * (1 - p) * (a : ℂ)) • (ψ₁ + ψ₀) := by
    unfold amplitudeEstimationPhaseIterate
    change -(A (A.symm (ψ₁ + (q - 1) • G.toSubmodule.starProjection ψ₁) +
      ((p - 1) * inner ℂ (basis zeroIndex)
        (A.symm (ψ₁ + (q - 1) • G.toSubmodule.starProjection ψ₁))) • basis zeroIndex)) = _
    rw [hgoodphase, zoo_amplitude_estimation_general_phase_action_conjugation,
      inner_smul_right]
    change -(q • ψ₁ + ((p - 1) * (q * inner ℂ ψ ψ₁)) • ψ) = _
    rw [hinner₁, hsplit]
    module
  have hbad : amplitudeEstimationPhaseIterate A (basis zeroIndex) G φ ϕ ψ₀ =
      -ψ₀ + ((1 - p) * (1 - (a : ℂ))) • (ψ₁ + ψ₀) := by
    unfold amplitudeEstimationPhaseIterate
    change -(A (A.symm (ψ₀ + (q - 1) • G.toSubmodule.starProjection ψ₀) +
      ((p - 1) * inner ℂ (basis zeroIndex)
        (A.symm (ψ₀ + (q - 1) • G.toSubmodule.starProjection ψ₀))) • basis zeroIndex)) = _
    rw [hbadphase, zoo_amplitude_estimation_general_phase_action_conjugation]
    change -(ψ₀ + ((p - 1) * inner ℂ ψ ψ₀) • ψ) = _
    rw [hinner₀, hsplit]
    module
  have htransport := zoo_amplitude_estimation_general_phase_action_transport
    ψ₁ ψ₀ a ha ha' p q
    (Complex.norm_exp_ofReal_mul_I φ) (Complex.norm_exp_ofReal_mul_I ϕ)
  exact ⟨hgood.trans htransport.1, hbad.trans htransport.2⟩

/-- The generalized phase component action fulfills `Lemma5Spec.expected` from [Brassard et al.,
Lemma 5][BrassardEtAl2002]. -/
theorem zoo_amplitude_estimation_general_phase_action_contract :
    Lemma5Spec.expected :=
  zoo_amplitude_estimation_general_phase_action

end Qatlib.Concepts.AmplitudeCore.AmplifyCore
