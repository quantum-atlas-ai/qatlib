/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization
import Mathlib.Analysis.Convex.Cone.Dual
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GramRealization

namespace Qatlib.Concepts.GramQueryCore.GammaDuality
open Matrix
open scoped Classical BigOperators ComplexOrder

abbrev Gamma2FixedFamily (X : Type) (n : ℕ) :=
  Fin n → (X ⊕ X) → (X ⊕ X) → ℂ

theorem gramFilteredCert_fixed_width {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} {A : Matrix X X ℂ} {Z : Fin n → Matrix X X ℂ} {W : ℝ}
    (h : gramFilteredCert A Z W) :
    ∃ w : Gamma2FixedFamily X n,
      (∀ z, ∑ j, ∑ q, Complex.normSq (w j z q) ≤ W) ∧
      ∀ x y, A x y = ∑ j, Z j x y * (star (w j (Sum.inl x)) ⬝ᵥ w j (Sum.inr y)) := by
  obtain ⟨Q, hQ, u, v, hu, hv, huv⟩ := h
  let R (j : Fin n) : Matrix Q (X ⊕ X) ℂ :=
    fun q z => Sum.elim (u j) (v j) z q
  have hp (j : Fin n) : (R j)ᴴ * R j |>.PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self (R j)
  choose V hV using fun j => gram_positive_matrix_actual_factorization (X ⊕ X)
    ((R j)ᴴ * R j) (hp j)
  have hinner (j : Fin n) (a b : X ⊕ X) :
      (star (fun q => V j q a) ⬝ᵥ fun q => V j q b) =
      (star (fun q => R j q a) ⬝ᵥ fun q => R j q b) := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply]
      using congrFun (congrFun (hV j) a) b
  have hmass (j : Fin n) (z : X ⊕ X) :
      (∑ q, Complex.normSq (V j q z)) = ∑ q, Complex.normSq (R j q z) := by
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
    exact hinner j z z
  refine ⟨fun j z q => V j q z, ?_, ?_⟩
  · intro z
    simp_rw [hmass]
    cases z with
    | inl x => exact hu x
    | inr y => exact hv y
  · intro x y
    simp_rw [hinner]
    exact huv x y

theorem filteredGamma2_fixed_budget_boundary (X : Type) [Fintype X] [DecidableEq X]
    (n : ℕ) (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (W : ℝ) (hW : 0 ≤ W) :
    filteredGamma2 A Z ≤ ENNReal.ofReal W ↔ gramFilteredCert A Z W := by
  refine ⟨?_, filteredGamma2_le_of_gramFilteredCert⟩
  intro hval
  by_cases hX : Nonempty X
  · letI := hX
    let energy (w : Gamma2FixedFamily X n) (z : X ⊕ X) : ℝ :=
      ∑ j, ∑ q, Complex.normSq (w j z q)
    let L (w : Gamma2FixedFamily X n) : Matrix X X ℂ := fun x y =>
      ∑ j, Z j x y * (star (w j (Sum.inl x)) ⬝ᵥ w j (Sum.inr y))
    let R := Real.sqrt (W + 1)
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    let F : Set (Gamma2FixedFamily X n) := Metric.closedBall 0 R ∩ {w | L w = A}
    have hL : Continuous L := by
      apply continuous_pi
      intro x
      apply continuous_pi
      intro y
      dsimp [L]
      simp only [dotProduct, Pi.star_apply]
      fun_prop
    have hFk : IsCompact F := (isCompact_closedBall (0 : Gamma2FixedFamily X n) R).inter_right
      (isClosed_eq hL continuous_const)
    have happrox (ε : ℝ) (hε : 0 < ε) :
        ∃ w ∈ F, ∀ z, energy w z ≤ W + ε := by
      let δ := min ε 1
      have hδ : 0 < δ := lt_min hε (by norm_num)
      have hcert : gramFilteredCert A Z (W + δ) :=
        gramFilteredCert_of_filteredGamma2_lt (hval.trans_lt
          ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < W + δ)).mpr (by linarith)))
      obtain ⟨w, hw, hf⟩ := gramFilteredCert_fixed_width hcert
      have hbound (j : Fin n) (z q : X ⊕ X) : ‖w j z q‖ ≤ R := by
        have hq : Complex.normSq (w j z q) ≤ ∑ q', Complex.normSq (w j z q') :=
          Finset.single_le_sum (fun q' _ => Complex.normSq_nonneg _) (Finset.mem_univ q)
        have hj : (∑ q', Complex.normSq (w j z q')) ≤
            ∑ j', ∑ q', Complex.normSq (w j' z q') :=
          Finset.single_le_sum
            (f := fun j' : Fin n => ∑ q' : X ⊕ X, Complex.normSq (w j' z q'))
            (fun j' _ => Finset.sum_nonneg
              (fun q' _ => Complex.normSq_nonneg (w j' z q'))) (Finset.mem_univ j)
        have hsq := (hq.trans hj).trans (hw z)
        rw [Complex.normSq_eq_norm_sq] at hsq
        have hd1 : δ ≤ 1 := min_le_right _ _
        have hRsq : R ^ 2 = W + 1 := Real.sq_sqrt (by linarith)
        nlinarith [norm_nonneg (w j z q)]
      have hn : ‖w‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr fun j =>
        (pi_norm_le_iff_of_nonneg hR).mpr fun z =>
          (pi_norm_le_iff_of_nonneg hR).mpr fun q => hbound j z q
      refine ⟨w, ⟨?_, ?_⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using hn
      · exact funext fun x => funext fun y => (hf x y).symm
      · intro z
        exact (hw z).trans (by dsimp [δ]; linarith [min_le_left ε (1 : ℝ)])
    have hne : (Finset.univ : Finset (X ⊕ X)).Nonempty := Finset.univ_nonempty
    let cost (w : Gamma2FixedFamily X n) := Finset.univ.sup' hne (energy w)
    have he (z : X ⊕ X) : Continuous (fun w => energy w z) := by
      dsimp [energy]
      simp only [Complex.normSq_eq_norm_sq]
      fun_prop
    have hc : Continuous cost := Continuous.finset_sup'_apply hne (fun z _ => he z)
    obtain ⟨w, hw, hmin⟩ := hFk.exists_isMinOn
      (by obtain ⟨v, hv, _⟩ := happrox 1 (by norm_num); exact ⟨v, hv⟩) hc.continuousOn
    have hcost : cost w ≤ W := le_of_forall_pos_le_add fun ε hε => by
      obtain ⟨v, hv, he'⟩ := happrox ε hε
      exact (hmin hv).trans (Finset.sup'_le hne _ (fun z _ => he' z))
    refine ⟨X ⊕ X, inferInstance, fun j x => w j (Sum.inl x),
      fun j y => w j (Sum.inr y), ?_, ?_, ?_⟩
    · intro x
      exact (Finset.le_sup' (f := energy w) (Finset.mem_univ (Sum.inl x))).trans hcost
    · intro y
      exact (Finset.le_sup' (f := energy w) (Finset.mem_univ (Sum.inr y))).trans hcost
    · intro x y
      exact (congrFun (congrFun hw.2 x) y).symm
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    have hA : A = 0 := by ext x; exact isEmptyElim x
    rw [hA]
    exact gramFilteredCert_zero Z hW

theorem gamma2_fixed_family_norm_bound {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (w : Gamma2FixedFamily X n) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ z, ∑ j, ∑ q, Complex.normSq (w j z q) ≤ W) :
    ‖w‖ ≤ Real.sqrt W := by
  have hR := Real.sqrt_nonneg W
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro z
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro q
  have hq : Complex.normSq (w j z q) ≤ ∑ q', Complex.normSq (w j z q') :=
    Finset.single_le_sum (fun q' _ => Complex.normSq_nonneg _) (Finset.mem_univ q)
  have hj : (∑ q', Complex.normSq (w j z q')) ≤ ∑ j', ∑ q', Complex.normSq (w j' z q') :=
    Finset.single_le_sum (f := fun j' : Fin n => ∑ q' : X ⊕ X, Complex.normSq (w j' z q'))
      (fun j' _ => Finset.sum_nonneg (fun q' _ => Complex.normSq_nonneg _)) (Finset.mem_univ j)
  have hs := (hq.trans hj).trans (hw z)
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [Real.sq_sqrt hW, norm_nonneg (w j z q)]

theorem gamma2_budget_set_compact (X : Type) [Fintype X] [DecidableEq X] (n : ℕ)
    (Z : Fin n → Matrix X X ℂ) (W : ℝ) (hW : 0 ≤ W) :
    IsCompact {A : Matrix X X ℂ | gramFilteredCert A Z W} := by
  let S : Set (Gamma2FixedFamily X n) :=
    {w | ∀ z, ∑ j, ∑ q, Complex.normSq (w j z q) ≤ W}
  let L (w : Gamma2FixedFamily X n) : Matrix X X ℂ := fun x y =>
    ∑ j, Z j x y * (star (w j (Sum.inl x)) ⬝ᵥ w j (Sum.inr y))
  have hL : Continuous L := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    dsimp [L]
    simp only [dotProduct, Pi.star_apply]
    fun_prop
  have hSc : IsClosed S := by
    dsimp [S]
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro z
    apply isClosed_le _ continuous_const
    simp only [Complex.normSq_eq_norm_sq]
    fun_prop
  have hSk : IsCompact S := (isCompact_closedBall (0 : Gamma2FixedFamily X n)
      (Real.sqrt W)).of_isClosed_subset hSc (by
    intro w hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      gamma2_fixed_family_norm_bound w W hW hw)
  have himage : L '' S = {A : Matrix X X ℂ | gramFilteredCert A Z W} := by
    ext A
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨X ⊕ X, inferInstance, fun j x => w j (Sum.inl x),
        fun j y => w j (Sum.inr y), fun x => hw (Sum.inl x), fun y => hw (Sum.inr y),
        fun _ _ => rfl⟩
    · intro hA
      obtain ⟨w, hw, hf⟩ := gramFilteredCert_fixed_width hA
      exact ⟨w, hw, funext fun x => funext fun y => (hf x y).symm⟩
  rw [← himage]
  exact hSk.image hL

theorem gamma2_budget_set_convex {X : Type} {n : ℕ} (Z : Fin n → Matrix X X ℂ) (W : ℝ) :
    Convex ℝ {A : Matrix X X ℂ | gramFilteredCert A Z W} := by
  intro A hA B hB a b ha hb hab
  have h := gramFilteredCert_add (gramFilteredCert_smul a hA) (gramFilteredCert_smul b hB)
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at h
  have he : a * W + b * W = W := by rw [← add_mul, hab, one_mul]
  rwa [he] at h

section BudgetSeparation
open scoped Matrix.Norms.Elementwise

theorem gamma2_budget_separator (X : Type) [Fintype X] [DecidableEq X] (n : ℕ)
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hA : ¬gramFilteredCert A Z W) :
    ∃ (l : StrongDual ℝ (Matrix X X ℂ)) (u : ℝ),
      (∀ B, gramFilteredCert B Z W → l B < u) ∧ u < l A := by
  letI : LocallyConvexSpace ℝ (Matrix X X ℂ) := NormedSpace.toLocallyConvexSpace' ℂ
  exact geometric_hahn_banach_closed_point (gamma2_budget_set_convex Z W)
    (gamma2_budget_set_compact X n Z W hW).isClosed hA

end BudgetSeparation

open scoped Matrix.Norms.L2Operator MatrixOrder
set_option backward.isDefEq.respectTransparency false

theorem gamma2_psd_zero_column {X : Type} [Fintype X] [DecidableEq X]
    (B : Matrix X X ℂ) (hB : B.PosSemidef) (j : X) (hj : B j j = 0) :
    ∀ i, B i j = 0 := by
  have hq : star (Pi.single j (1 : ℂ) : X → ℂ) ⬝ᵥ
      B *ᵥ Pi.single j 1 = 0 := by simp [hj]
  have hv := hB.dotProduct_mulVec_zero_iff.mp hq
  intro i
  simpa using congrFun hv i

theorem gamma2_vec_dot_norm_sq {X : Type} [Fintype X] [DecidableEq X] (v : X → ℂ) :
    (star v ⬝ᵥ v).re = ‖toEuclidean_fromVec v‖^2 := by
  rw [norm_toEuclidean_fromVec_sq]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem gamma2_psd_unit_block_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (T : Matrix X X ℂ)
    (hT : (Matrix.fromBlocks (1 : Matrix X X ℂ) T Tᴴ 1).PosSemidef) : ‖T‖ ≤ 1 := by
  letI : Invertible (1 : Matrix X X ℂ) := invertibleOne
  have hres := (Matrix.PosDef.fromBlocks₁₁ T (1 : Matrix X X ℂ)
    (Matrix.PosDef.one : (1 : Matrix X X ℂ).PosDef)).mp hT
  simp only [inv_one, Matrix.mul_one] at hres
  apply l2_opNorm_le_of_mulVec_le zero_le_one
  intro v
  have hq := hres.re_dotProduct_nonneg v
  have hg : star v ⬝ᵥ ((Tᴴ*T)*ᵥv) = star (T*ᵥv) ⬝ᵥ (T*ᵥv) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at hq
  change 0 ≤ (star v ⬝ᵥ v - star v ⬝ᵥ ((Tᴴ*T)*ᵥv)).re at hq
  rw [Complex.sub_re, hg, gamma2_vec_dot_norm_sq, gamma2_vec_dot_norm_sq] at hq
  simp only [one_mul]
  nlinarith [norm_nonneg (toEuclidean_fromVec v), norm_nonneg (toEuclidean_fromVec (T*ᵥv))]

theorem gamma2_inverse_sqrt_diagonal {a : ℝ} (ha : 0 ≤ a) :
    (Real.sqrt a)⁻¹*a*(Real.sqrt a)⁻¹ + (if a=0 then 1 else 0) = 1 := by
  by_cases hz : a=0
  · simp [hz]
  · have hs : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ha (Ne.symm hz))
    rw [if_neg hz]
    field_simp
    nlinarith [Real.sq_sqrt ha]

theorem gamma2_psd_diagonal_rescale_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (a b : X → ℝ) (T : Matrix X X ℂ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hT : (Matrix.fromBlocks (Matrix.diagonal fun x => (a x : ℂ)) T Tᴴ
      (Matrix.diagonal fun y => (b y : ℂ))).PosSemidef) :
    ‖Matrix.of (fun x y => T x y / ((Real.sqrt (a x) : ℂ)*(Real.sqrt (b y) : ℂ)))‖ ≤ 1 := by
  let c : X ⊕ X → ℂ := Sum.elim (fun x => ((Real.sqrt (a x))⁻¹ : ℝ))
    (fun y => ((Real.sqrt (b y))⁻¹ : ℝ))
  let z : X ⊕ X → ℂ := Sum.elim (fun x => (if a x=0 then 1 else 0 : ℝ))
    (fun y => (if b y=0 then 1 else 0 : ℝ))
  let B := Matrix.fromBlocks (Matrix.diagonal fun x => (a x : ℂ)) T Tᴴ
    (Matrix.diagonal fun y => (b y : ℂ))
  let R : Matrix X X ℂ := fun x y => T x y /
    ((Real.sqrt (a x) : ℂ)*(Real.sqrt (b y) : ℂ))
  have hz : (Matrix.diagonal z).PosSemidef := Matrix.PosSemidef.diagonal (by
    intro i
    cases i <;> dsimp [z] <;> split_ifs <;> norm_num)
  have hK := (hT.conjTranspose_mul_mul_same (Matrix.diagonal c)).add hz
  have he : (Matrix.diagonal c)ᴴ*B*(Matrix.diagonal c) + Matrix.diagonal z =
      Matrix.fromBlocks (1 : Matrix X X ℂ) R Rᴴ 1 := by
    ext i j
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.diagonal_apply, Pi.star_apply]
    cases i with
    | inl x =>
      cases j with
      | inl y =>
        by_cases hxy : x=y
        · subst y
          simp only [B, c, z, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply,
            if_true, Complex.star_def, Complex.conj_ofReal, Matrix.one_apply_eq]
          exact_mod_cast gamma2_inverse_sqrt_diagonal (ha x)
        · simp [B, c, z, hxy]
      | inr y =>
        simp [B, c, z, R, div_eq_mul_inv, mul_comm, mul_assoc]
    | inr x =>
      cases j with
      | inl y =>
        simp [B, c, z, R, Matrix.conjTranspose_apply, div_eq_mul_inv, mul_comm, mul_assoc]
      | inr y =>
        by_cases hxy : x=y
        · subst y
          simp only [B, c, z, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
            if_true, Complex.star_def, Complex.conj_ofReal, Matrix.one_apply_eq]
          exact_mod_cast gamma2_inverse_sqrt_diagonal (hb x)
        · simp [B, c, z, hxy]
  change ((Matrix.diagonal c)ᴴ*B*(Matrix.diagonal c)+Matrix.diagonal z).PosSemidef at hK
  rw [he] at hK
  exact gamma2_psd_unit_block_norm_le R hK

theorem gamma2_entry_conj_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (M : Matrix X X ℂ) : ‖Matrix.of (fun x y => star (M x y))‖ ≤ ‖M‖ := by
  have hs (v : X → ℂ) : ‖toEuclidean_fromVec (star v)‖ = ‖toEuclidean_fromVec v‖ := by
    have hh : ‖toEuclidean_fromVec (star v)‖^2 = ‖toEuclidean_fromVec v‖^2 := by
      simp only [norm_toEuclidean_fromVec_sq, Pi.star_apply, norm_star]
    nlinarith [norm_nonneg (toEuclidean_fromVec (star v)), norm_nonneg (toEuclidean_fromVec v)]
  apply l2_opNorm_le_of_mulVec_le (norm_nonneg M)
  intro v
  have he : Matrix.of (fun x y => star (M x y))*ᵥv = star (M*ᵥstar v) := by
    ext x
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.star_apply,
      star_sum, star_mul, star_star, mul_comm]
  rw [he, hs]
  have hh := l2_norm_mulVec_fromVec_le M (star v)
  rw [hs] at hh
  exact hh

def gamma2SDPPairing {X : Type} [Fintype X] (A N : Matrix X X ℂ) : ℝ :=
  ∑ x, ∑ y, (star (N x y)*A x y).re

def gamma2SDPDualBlock {X : Type} [DecidableEq X] (a b : X → ℝ)
    (Z N : Matrix X X ℂ) : Matrix (X ⊕ X) (X ⊕ X) ℂ :=
  let T : Matrix X X ℂ := fun x y => -(star (Z x y)*N x y)/2
  Matrix.fromBlocks (Matrix.diagonal fun x => (a x : ℂ)) T Tᴴ
    (Matrix.diagonal fun y => (b y : ℂ))

theorem gamma2_psd_polar_multiplier_feasible {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (Z : Fin n → Matrix X X ℂ) (a b : X → ℝ) (N : Matrix X X ℂ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hB : ∀ j, (gamma2SDPDualBlock a b (Z j) N).PosSemidef) :
    ∀ j, ‖Z j ⊙ Matrix.of (fun x y => star (N x y) /
      (2*(Real.sqrt (a x) : ℂ)*(Real.sqrt (b y) : ℂ)))‖ ≤ 1 := by
  intro j
  let T : Matrix X X ℂ := fun x y => -(star (Z j x y)*N x y)/2
  let R : Matrix X X ℂ := Matrix.of (fun x y => T x y /
    ((Real.sqrt (a x) : ℂ)*(Real.sqrt (b y) : ℂ)))
  have hr : ‖R‖ ≤ 1 := gamma2_psd_diagonal_rescale_norm_le a b T ha hb (hB j)
  have he : Z j ⊙ Matrix.of (fun x y => star (N x y) /
      (2*(Real.sqrt (a x) : ℂ)*(Real.sqrt (b y) : ℂ))) =
      -Matrix.of (fun x y => star (R x y)) := by
    ext x y
    simp [Matrix.hadamard_apply, R, T, div_eq_mul_inv, star_mul, mul_comm, mul_left_comm, mul_assoc]
  rw [he, norm_neg]
  exact (gamma2_entry_conj_norm_le R).trans hr

theorem gamma2_psd_zero_weight_entry {X : Type} [Fintype X] [DecidableEq X]
    (a b : X → ℝ) (T : Matrix X X ℂ)
    (hB : (Matrix.fromBlocks (Matrix.diagonal fun x => (a x : ℂ)) T Tᴴ
      (Matrix.diagonal fun y => (b y : ℂ))).PosSemidef)
    (x y : X) (hz : a x=0 ∨ b y=0) : T x y = 0 := by
  rcases hz with hx | hy
  · have hh := gamma2_psd_zero_column _ hB (Sum.inl x) (by simp [hx]) (Sum.inr y)
    have hs : star (T x y) = 0 := by simpa only [Matrix.fromBlocks_apply₂₁,
      Matrix.conjTranspose_apply] using hh
    exact star_eq_zero.mp hs
  · exact gamma2_psd_zero_column _ hB (Sum.inr y) (by simp [hy]) (Sum.inl x)

theorem gamma2_psd_zero_weight_pairing {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ)
    (hsupport : ∀ x y, (∀ j, Z j x y=0) → A x y=0)
    (a b : X → ℝ) (N : Matrix X X ℂ)
    (hB : ∀ j, (gamma2SDPDualBlock a b (Z j) N).PosSemidef)
    (x y : X) (hz : a x=0 ∨ b y=0) : star (N x y)*A x y = 0 := by
  by_cases hA : A x y=0
  · simp [hA]
  · have hslot : ∃ j, Z j x y ≠ 0 := by
      by_contra h
      exact hA (hsupport x y (by simpa only [not_exists, not_not] using h))
    obtain ⟨j,hj⟩ := hslot
    have ht := gamma2_psd_zero_weight_entry a b
      (fun x y => -(star (Z j x y)*N x y)/2) (hB j) x y hz
    have hprod : star (Z j x y)*N x y=0 := by simpa using ht
    have hn : N x y=0 := (mul_eq_zero.mp hprod).resolve_left (star_ne_zero.mpr hj)
    simp [hn]

theorem gamma2_psd_polar_pairing_bound {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ)
    (hsupport : ∀ x y, (∀ j, Z j x y=0) → A x y=0)
    (a b : X → ℝ) (N : Matrix X X ℂ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hbudget : (∑ x, a x)+(∑ x, b x)=1)
    (hB : ∀ j, (gamma2SDPDualBlock a b (Z j) N).PosSemidef) :
    gamma2SDPPairing A N ≤ ‖A ⊙ Matrix.of (fun x y => star (N x y) /
      (2*(Real.sqrt (a x) : ℂ)*(Real.sqrt (b y) : ℂ)))‖ := by
  let u : X → ℂ := fun x => (Real.sqrt (a x) : ℂ)
  let v : X → ℂ := fun y => (Real.sqrt (b y) : ℂ)
  let M : Matrix X X ℂ := Matrix.of (fun x y => star (N x y)/(2*u x*v y))
  have hentry (x y : X) : star (N x y)*A x y = 2*(star (u x)*(A⊙M) x y*v y) := by
    by_cases hz : a x=0 ∨ b y=0
    · rw [gamma2_psd_zero_weight_pairing A Z hsupport a b N hB x y hz]
      rcases hz with hz | hz <;> simp [u, v, M, hz, Matrix.hadamard_apply]
    · have hax : a x ≠ 0 := fun h => hz (Or.inl h)
      have hby : b y ≠ 0 := fun h => hz (Or.inr h)
      have hu : u x ≠ 0 := by
        dsimp [u]
        exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (ha x) (Ne.symm hax)))
      have hv : v y ≠ 0 := by
        dsimp [v]
        exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hb y) (Ne.symm hby)))
      simp only [u, Complex.star_def, Complex.conj_ofReal, Matrix.hadamard_apply, M,
          Matrix.of_apply]
      change star (N x y)*A x y = 2*(u x*(A x y*(star (N x y)/(2*u x*v y)))*v y)
      field_simp
  have hpair : gamma2SDPPairing A N = 2*(star u ⬝ᵥ ((A⊙M)*ᵥv)).re := by
    simp only [gamma2SDPPairing, Matrix.mulVec, dotProduct, Pi.star_apply,
      hentry, Complex.re_sum, Finset.mul_sum, mul_assoc]
    simp
  have hmass : ‖toEuclidean_fromVec u‖^2+‖toEuclidean_fromVec v‖^2=1 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    simp only [u, v, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (ha _),
      Real.sq_sqrt (hb _)]
    exact hbudget
  have hcs : 2*‖toEuclidean_fromVec u‖*‖toEuclidean_fromVec v‖ ≤ 1 := by
    nlinarith [sq_nonneg (‖toEuclidean_fromVec u‖-‖toEuclidean_fromVec v‖)]
  have hinner : (star u ⬝ᵥ ((A⊙M)*ᵥv)).re ≤
      ‖toEuclidean_fromVec u‖*‖toEuclidean_fromVec ((A⊙M)*ᵥv)‖ := by
    apply (Complex.re_le_norm _).trans
    have hc := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec u)
      (toEuclidean_fromVec ((A⊙M)*ᵥv))
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, toEuclidean_fromVec,
      WithLp.ofLp_toLp, dotProduct_comm] using hc
  have haction := l2_norm_mulVec_fromVec_le (A⊙M) v
  rw [hpair]
  calc
    _ ≤ 2*(‖toEuclidean_fromVec u‖*‖toEuclidean_fromVec ((A⊙M)*ᵥv)‖) := by linarith
    _ ≤ 2*(‖toEuclidean_fromVec u‖*(‖A⊙M‖*‖toEuclidean_fromVec v‖)) := by gcongr
    _ = (2*‖toEuclidean_fromVec u‖*‖toEuclidean_fromVec v‖)*‖A⊙M‖ := by ring
    _ ≤ 1*‖A⊙M‖ := mul_le_mul_of_nonneg_right hcs (norm_nonneg _)
    _ = _ := one_mul _

theorem gamma2_psd_operator_polar {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ)
    (hsupport : ∀ x y, (∀ j, Z j x y=0) → A x y=0)
    (a b : X → ℝ) (N : Matrix X X ℂ)
    (hab : ∀ x, 0 ≤ a x ∧ 0 ≤ b x) (hbudget : (∑ x, a x)+(∑ x, b x)=1)
    (hB : ∀ j, (gamma2SDPDualBlock a b (Z j) N).PosSemidef) :
    ∃ M : Matrix X X ℂ, (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ gamma2SDPPairing A N ≤ ‖A⊙M‖ := by
  exact ⟨Matrix.of (fun x y => star (N x y)/(2*(Real.sqrt (a x) : ℂ)*(Real.sqrt (b y) : ℂ))),
    gamma2_psd_polar_multiplier_feasible Z a b N (fun x => (hab x).1) (fun x => (hab x).2) hB,
    gamma2_psd_polar_pairing_bound A Z hsupport a b N (fun x => (hab x).1)
      (fun x => (hab x).2) hbudget hB⟩

theorem gamma2_psd_entry_norm_sq {Y : Type} [Fintype Y] [DecidableEq Y]
    (B : Matrix Y Y ℂ) (hB : B.PosSemidef) (x y : Y) :
    ‖B x y‖^2 ≤ (B x x).re*(B y y).re := by
  obtain ⟨V,hV⟩ := gram_positive_matrix_actual_factorization Y B hB
  let v (z : Y) : Y → ℂ := fun q => V q z
  have hentry (a b : Y) : B a b=star (v a) ⬝ᵥ v b := by
    rw [← hV]
    rfl
  have hdiag (a : Y) : (B a a).re=‖toEuclidean_fromVec (v a)‖^2 := by
    rw [hentry]
    exact gamma2_vec_dot_norm_sq (v a)
  have hc : ‖star (v x) ⬝ᵥ v y‖ ≤
      ‖toEuclidean_fromVec (v x)‖*‖toEuclidean_fromVec (v y)‖ := by
    rw [show (star (v x) ⬝ᵥ v y : ℂ)=Inner (v x) (v y) from rfl,
      ← inner_euclidean_fromVec]
    exact norm_inner_le_norm (𝕜 := ℂ) _ _
  rw [hentry, hdiag, hdiag]
  nlinarith [norm_nonneg (star (v x) ⬝ᵥ v y)]

theorem gamma2_psd_entry_norm_le {Y : Type} [Fintype Y] [DecidableEq Y]
    (B : Matrix Y Y ℂ) (hB : B.PosSemidef) (R : ℝ) (hR : 0 ≤ R)
    (hdiag : ∀ z, (B z z).re ≤ R) (x y : Y) : ‖B x y‖ ≤ R := by
  have hx : 0 ≤ (B x x).re := (Complex.nonneg_iff.mp hB.diag_nonneg).1
  have hy : 0 ≤ (B y y).re := (Complex.nonneg_iff.mp hB.diag_nonneg).1
  have hb := gamma2_psd_entry_norm_sq B hB x y
  have hm := mul_le_mul (hdiag x) (hdiag y) hy hR
  nlinarith [norm_nonneg (B x y)]

theorem gamma2_psd_set_closed (Y : Type) [Fintype Y] [DecidableEq Y] :
    IsClosed {B : Matrix Y Y ℂ | B.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply IsClosed.inter
  · apply isClosed_eq
    · fun_prop
    · exact continuous_id
  · change IsClosed {B : Matrix Y Y ℂ | ∀ v, 0 ≤ star v ⬝ᵥ (B*ᵥv)}
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    fun_prop

def gamma2SDPImage {X : Type} [Fintype X] {n : ℕ}
    (Z : Fin n → Matrix X X ℂ) (B : Gamma2FixedFamily X n) : Matrix X X ℂ :=
  fun x y => ∑ j, Z j x y * B j (Sum.inl x) (Sum.inr y)

def gamma2SDPEpigraph {X : Type} [Fintype X] {n : ℕ}
    (Z : Fin n → Matrix X X ℂ) : Set (Matrix X X ℂ × ((X ⊕ X) → ℝ)) :=
  {c | ∃ B : Gamma2FixedFamily X n, (∀ j, Matrix.PosSemidef (B j)) ∧
    gamma2SDPImage Z B=c.1 ∧ ∀ z, ∑ j, (B j z z).re ≤ c.2 z}

section EpigraphClosure
open scoped Matrix.Norms.Elementwise
open Filter Topology

theorem gamma2_psd_family_norm_bound {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (B : Gamma2FixedFamily X n) (hB : ∀ j, Matrix.PosSemidef (B j))
    (d : (X ⊕ X) → ℝ) (hd : ∀ z, ∑ j, (B j z z).re ≤ d z)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ‖d‖ ≤ R) : ‖B‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro y
  apply gamma2_psd_entry_norm_le (B j) (hB j) R hR
  intro z
  have hs : (B j z z).re ≤ ∑ k, (B k z z).re := Finset.single_le_sum
    (fun k _ => (Complex.nonneg_iff.mp (hB k).diag_nonneg).1) (Finset.mem_univ j)
  exact hs.trans ((hd z).trans ((le_abs_self (d z)).trans
    ((norm_le_pi_norm d z).trans hbound)))

theorem gamma2SDPEpigraph_closed {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (Z : Fin n → Matrix X X ℂ) : IsClosed (gamma2SDPEpigraph Z) := by
  apply IsSeqClosed.isClosed
  intro c s hs ht
  choose B hB hL hd using hs
  have hdt : Tendsto (fun k => (c k).2) atTop (𝓝 s.2) := continuous_snd.tendsto s |>.comp ht
  obtain ⟨R,hR,hbound⟩ := (Metric.isBounded_range_of_tendsto _ hdt).exists_pos_norm_le
  have hb (k : ℕ) : ‖B k‖ ≤ R := gamma2_psd_family_norm_bound
    (B k) (hB k) ((c k).2) (hd k) R hR.le (hbound _ ⟨k,rfl⟩)
  obtain ⟨V,hV,φ,hφ,hvt⟩ := (isCompact_closedBall (0 : Gamma2FixedFamily X n) R).tendsto_subseq
    (fun k => by simpa only [Metric.mem_closedBall, dist_zero_right] using hb k)
  refine ⟨V,?_,?_,?_⟩
  · intro j
    exact (gamma2_psd_set_closed (X ⊕ X)).mem_of_tendsto
      ((continuous_apply j).tendsto V |>.comp hvt) (Filter.Eventually.of_forall fun k => hB (φ k) j)
  · have hcont : Continuous (gamma2SDPImage Z) := by
      apply continuous_pi
      intro x
      apply continuous_pi
      intro y
      dsimp [gamma2SDPImage]
      fun_prop
    have hl := hcont.tendsto V |>.comp hvt
    have hc := (continuous_fst.tendsto s |>.comp ht).comp hφ.tendsto_atTop
    apply tendsto_nhds_unique hl
    convert hc using 1
    exact funext fun k => hL (φ k)
  · intro z
    have hcont : Continuous (fun V : Gamma2FixedFamily X n => ∑ j, (V j z z).re) := by
      fun_prop
    have hl := hcont.tendsto V |>.comp hvt
    have hr := ((continuous_apply z).tendsto s.2).comp (hdt.comp hφ.tendsto_atTop)
    exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall fun k => hd (φ k) z)
end EpigraphClosure

section EpigraphSeparation
open scoped Matrix.Norms.Elementwise

theorem gamma2SDPImage_add {X : Type} [Fintype X] {n : ℕ}
    (Z : Fin n → Matrix X X ℂ) (B D : Gamma2FixedFamily X n) :
    gamma2SDPImage Z (B+D)=gamma2SDPImage Z B+gamma2SDPImage Z D := by
  ext x y
  simp [gamma2SDPImage, mul_add, Finset.sum_add_distrib]

theorem gamma2SDPImage_smul {X : Type} [Fintype X] {n : ℕ}
    (Z : Fin n → Matrix X X ℂ) (a : ℝ) (B : Gamma2FixedFamily X n) :
    gamma2SDPImage Z (a • B)=a • gamma2SDPImage Z B := by
  ext x y
  simp [gamma2SDPImage, Finset.smul_sum, mul_left_comm]

def gamma2SDPEpigraphCone {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (Z : Fin n → Matrix X X ℂ) :
    PointedCone ℝ (Matrix X X ℂ × ((X ⊕ X) → ℝ)) where
  carrier := gamma2SDPEpigraph Z
  zero_mem' := by
    refine ⟨0,fun _ => Matrix.PosSemidef.zero,?_,?_⟩
    · ext x y
      simp [gamma2SDPImage]
    · simp
  add_mem' := by
    intro c d hc hd
    obtain ⟨B,hB,hL,hbudget⟩ := hc
    obtain ⟨D,hD,hL',hbudget'⟩ := hd
    refine ⟨B+D, fun j => (hB j).add (hD j), ?_, ?_⟩
    · rw [gamma2SDPImage_add, hL, hL']
      rfl
    · intro z
      simpa only [Pi.add_apply, Complex.add_re, Finset.sum_add_distrib, Prod.fst_add,
        Prod.snd_add] using add_le_add (hbudget z) (hbudget' z)
  smul_mem' := by
    intro a c hc
    obtain ⟨B,hB,hL,hbudget⟩ := hc
    refine ⟨(a.val : ℝ) • B, fun j => (hB j).smul a.property, ?_, ?_⟩
    · rw [gamma2SDPImage_smul, hL]
      rfl
    · intro z
      change (∑ j, ((a.val : ℝ) • B j z z).re) ≤ a.val*c.2 z
      simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, ← Finset.mul_sum] using mul_le_mul_of_nonneg_left (hbudget z) a.property

theorem gamma2SDPEpigraph_separator {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (Z : Fin n → Matrix X X ℂ) (c : Matrix X X ℂ × ((X ⊕ X) → ℝ))
    (hc : c ∉ gamma2SDPEpigraph Z) :
    ∃ l : StrongDual ℝ (Matrix X X ℂ × ((X ⊕ X) → ℝ)),
      (∀ d ∈ gamma2SDPEpigraph Z, 0 ≤ l d) ∧ l c < 0 := by
  letI : LocallyConvexSpace ℝ (Matrix X X ℂ × ((X ⊕ X) → ℝ)) :=
    NormedSpace.toLocallyConvexSpace' ℝ
  let K : ProperCone ℝ (Matrix X X ℂ × ((X ⊕ X) → ℝ)) :=
    ⟨gamma2SDPEpigraphCone Z, gamma2SDPEpigraph_closed Z⟩
  exact K.hyperplane_separation_point hc
end EpigraphSeparation

theorem gamma2_gram_diagonal_re {Y : Type} [Fintype Y] [DecidableEq Y]
    (V : Matrix Y Y ℂ) (z : Y) : ((Vᴴ*V) z z).re=∑ q, Complex.normSq (V q z) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem gamma2SDPEpigraph_const_iff {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (t : ℝ) :
    (A,fun _ => t) ∈ gamma2SDPEpigraph Z ↔ gramFilteredCert A Z t := by
  constructor
  · rintro ⟨B,hB,hL,hd⟩
    choose V hV using fun j => gram_positive_matrix_actual_factorization (X ⊕ X) (B j) (hB j)
    refine ⟨X ⊕ X,inferInstance,fun j x q => V j q (Sum.inl x),
      fun j y q => V j q (Sum.inr y),?_,?_,?_⟩
    · intro x
      have hh (j : Fin n) : ∑ q, Complex.normSq (V j q (Sum.inl x))=(B j (Sum.inl x) (Sum.inl x)).re := by
        rw [← hV j]
        exact (gamma2_gram_diagonal_re (V j) (Sum.inl x)).symm
      simp_rw [hh]
      exact hd (Sum.inl x)
    · intro y
      have hh (j : Fin n) : ∑ q, Complex.normSq (V j q (Sum.inr y))=(B j (Sum.inr y) (Sum.inr y)).re := by
        rw [← hV j]
        exact (gamma2_gram_diagonal_re (V j) (Sum.inr y)).symm
      simp_rw [hh]
      exact hd (Sum.inr y)
    · intro x y
      have he := congrFun (congrFun hL x) y
      change (∑ j, Z j x y*B j (Sum.inl x) (Sum.inr y))=A x y at he
      rw [← he]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hV j]
      rfl
  · intro h
    obtain ⟨w,hw,hL⟩ := gramFilteredCert_fixed_width h
    let V (j : Fin n) : Matrix (X ⊕ X) (X ⊕ X) ℂ := fun q z => w j z q
    refine ⟨fun j => (V j)ᴴ*V j,fun j => Matrix.posSemidef_conjTranspose_mul_self (V j),?_,?_⟩
    · ext x y
      exact (hL x y).symm
    · intro z
      simp_rw [gamma2_gram_diagonal_re]
      exact hw z

theorem gamma2_real_functional_coordinates {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (l : StrongDual ℝ (Matrix X X ℂ × (Y → ℝ))) :
    ∃ (a : Y → ℝ) (N : Matrix X X ℂ), ∀ A d,
      l (A,d)=(∑ z, a z*d z)-gamma2SDPPairing A N := by
  let lA : Matrix X X ℂ →ₗ[ℝ] ℝ := l.toLinearMap.comp (LinearMap.inl ℝ _ _)
  let lD : (Y → ℝ) →ₗ[ℝ] ℝ := l.toLinearMap.comp (LinearMap.inr ℝ _ _)
  let a : Y → ℝ := fun z => lD (Pi.single z 1)
  let N : Matrix X X ℂ := fun x y =>
    -(lA (Matrix.single x y 1) : ℂ)-(lA (Matrix.single x y Complex.I) : ℂ)*Complex.I
  have hsingle (x y : X) (z : ℂ) : lA (Matrix.single x y z)=
      z.re*lA (Matrix.single x y 1)+z.im*lA (Matrix.single x y Complex.I) := by
    have hz : Matrix.single x y z = z.re • Matrix.single x y (1 : ℂ)+
        z.im • Matrix.single x y Complex.I := by
      rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
      congr 1
      simp only [Complex.real_smul, mul_one]
      exact (Complex.re_add_im z).symm
    rw [hz, map_add, map_smul, map_smul]
    rfl
  refine ⟨a,N,?_⟩
  intro A d
  have hA : lA A = -gamma2SDPPairing A N := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A, map_sum]
    simp_rw [map_sum]
    have he : (∑ x, ∑ y, lA (Matrix.single x y (A x y))) =
        ∑ x, ∑ y, ((A x y).re*lA (Matrix.single x y 1)+
          (A x y).im*lA (Matrix.single x y Complex.I)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact hsingle x y (A x y)
    rw [he]
    dsimp [gamma2SDPPairing, N]
    simp only [map_sub, map_neg, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.sub_re, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_im, Complex.sub_im, Complex.mul_im]
    simp only [mul_zero, mul_one, mul_neg, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hd : lD d=∑ z, a z*d z := by
    conv_lhs => rw [pi_eq_sum_univ' d, map_sum]
    simp only [map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _
  have hsplit : l (A,d)=lA A+lD d := by
    change l (A,d)=l (A,0)+l (0,d)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  rw [hsplit,hA,hd]
  ring

theorem gamma2_weighted_diagonal_quad {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℝ) (u : X → ℂ) :
    (star u ⬝ᵥ ((Matrix.diagonal fun x => (a x : ℂ))*ᵥu)).re=
      ∑ x, a x*Complex.normSq (u x) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  have he : star (u x)*((a x : ℂ)*u x)=(a x : ℂ)*(star (u x)*u x) := by ring
  rw [he]
  simp [← Complex.normSq_eq_conj_mul_self]

theorem gamma2_polar_cross_quad {X : Type} [Fintype X] [DecidableEq X]
    (Z N : Matrix X X ℂ) (u v : X → ℂ) :
    let T : Matrix X X ℂ := fun x y => -(star (Z x y)*N x y)/2
    (star u ⬝ᵥ (T*ᵥv)).re =
      -gamma2SDPPairing (Z ⊙ Matrix.vecMulVec u (star v)) N/2 := by
  (try dsimp only)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  dsimp [gamma2SDPPairing]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Matrix.vecMulVec_apply, Pi.star_apply]
  have he : star (u x)*(-(star (Z x y)*N x y)/2*v y)=
      -(star (star (N x y)*(Z x y*(u x*star (v y)))))/2 := by
    simp only [star_mul, star_star]
    ring
  simp only [Complex.star_def] at he
  rw [he]
  norm_num [Complex.star_def, Complex.div_re, Complex.normSq]
  ring

theorem gamma2_polar_block_quad {X : Type} [Fintype X] [DecidableEq X]
    (a b : X → ℝ) (Z N : Matrix X X ℂ) (u v : X → ℂ) :
    (star (Sum.elim u v) ⬝ᵥ ((gamma2SDPDualBlock a b Z N)*ᵥSum.elim u v)).re=
      (∑ x, a x*Complex.normSq (u x))+(∑ y, b y*Complex.normSq (v y))-
        gamma2SDPPairing (Z ⊙ Matrix.vecMulVec u (star v)) N := by
  let T : Matrix X X ℂ := fun x y => -(star (Z x y)*N x y)/2
  have hadj : (star v ⬝ᵥ (Tᴴ*ᵥu)).re=(star u ⬝ᵥ (T*ᵥv)).re := by
    have he : star v ⬝ᵥ (Tᴴ*ᵥu)=star (star u ⬝ᵥ (T*ᵥv)) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
      exact star_dotProduct _ _
    rw [he]
    simp
  dsimp [gamma2SDPDualBlock]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Function.star_sumElim,
    sumElim_dotProduct_sumElim, dotProduct_add, Complex.add_re]
  rw [gamma2_weighted_diagonal_quad, gamma2_weighted_diagonal_quad]
  change (∑ x, a x*Complex.normSq (u x))+(star u ⬝ᵥ (T*ᵥv)).re+
    ((star v ⬝ᵥ (Tᴴ*ᵥu)).re+∑ y, b y*Complex.normSq (v y))=_
  rw [hadj, gamma2_polar_cross_quad Z N u v]
  ring

section SeparatorMultipliers
open scoped Matrix.Norms.Elementwise

theorem gamma2_psd_separator_unnormalized {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (t : ℝ)
    (hcert : ¬gramFilteredCert A Z t) :
    ∃ (a b : X → ℝ) (N : Matrix X X ℂ),
      (∀ x, 0 ≤ a x ∧ 0 ≤ b x) ∧
      (∀ j, (gamma2SDPDualBlock a b (Z j) N).PosSemidef) ∧
      t*((∑ x, a x)+(∑ x, b x)) < gamma2SDPPairing A N := by
  have hout : (A,fun _ => t) ∉ gamma2SDPEpigraph Z := by
    rwa [gamma2SDPEpigraph_const_iff]
  obtain ⟨l,hl,hlt⟩ := gamma2SDPEpigraph_separator Z (A,fun _ => t) hout
  obtain ⟨α,N,hrepr⟩ := gamma2_real_functional_coordinates l
  have hα (z : X ⊕ X) : 0 ≤ α z := by
    have hm : ((0 : Matrix X X ℂ),Pi.single z (1 : ℝ)) ∈ gamma2SDPEpigraph Z := by
      refine ⟨0,fun _ => Matrix.PosSemidef.zero,?_,?_⟩
      · ext x y
        simp [gamma2SDPImage]
      · intro w
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
    have hh := hl _ hm
    rw [hrepr] at hh
    have hzero : gamma2SDPPairing (0 : Matrix X X ℂ) N=0 := by simp [gamma2SDPPairing]
    rw [hzero, sub_zero] at hh
    simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using hh
  let a : X → ℝ := fun x => α (Sum.inl x)
  let b : X → ℝ := fun y => α (Sum.inr y)
  have hblock (j : Fin n) : (gamma2SDPDualBlock a b (Z j) N).PosSemidef := by
    have hherm : (gamma2SDPDualBlock a b (Z j) N).IsHermitian := by
      apply Matrix.IsHermitian.fromBlocks
      · apply Matrix.isHermitian_diagonal_iff.mpr
        simp [IsSelfAdjoint]
      · rfl
      · apply Matrix.isHermitian_diagonal_iff.mpr
        simp [IsSelfAdjoint]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
    intro w
    let R : Matrix (X ⊕ X) (X ⊕ X) ℂ := Matrix.vecMulVec w (star w)
    have hR : R.PosSemidef := Matrix.posSemidef_vecMulVec_self_star w
    have hm : (gamma2SDPImage Z (Pi.single j R),fun z => (R z z).re) ∈ gamma2SDPEpigraph Z := by
      refine ⟨Pi.single j R,?_,rfl,?_⟩
      · intro k
        by_cases hk : k=j
        · subst k
          rw [Pi.single_eq_same]
          exact hR
        · rw [Pi.single_eq_of_ne hk]
          exact Matrix.PosSemidef.zero
      · intro z
        rw [Finset.sum_eq_single j]
        · rw [Pi.single_eq_same]
        · intro k _ hk
          rw [Pi.single_eq_of_ne hk]
          simp
        · simp
    have hh := hl _ hm
    rw [hrepr] at hh
    let u : X → ℂ := fun x => w (Sum.inl x)
    let v : X → ℂ := fun y => w (Sum.inr y)
    have hdiag (z : X ⊕ X) : (R z z).re=Complex.normSq (w z) := by
      dsimp [R]
      simp only [Matrix.vecMulVec_apply, Pi.star_apply]
      rw [mul_comm]
      simp [← Complex.normSq_eq_conj_mul_self]
    have himage : gamma2SDPImage Z (Pi.single j R)=Z j ⊙ Matrix.vecMulVec u (star v) := by
      ext x y
      change (∑ k,
          Z k x y*((Pi.single j R : Fin n → Matrix (X ⊕ X) (X ⊕ X) ℂ) k) (Sum.inl x) (Sum.inr y))=_
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
        rfl
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk]
        simp
      · simp
    simp_rw [hdiag] at hh
    rw [himage, Fintype.sum_sum_type] at hh
    have hquad : (star w ⬝ᵥ ((gamma2SDPDualBlock a b (Z j) N)*ᵥw)).re=
        (∑ x, a x*Complex.normSq (u x))+(∑ y, b y*Complex.normSq (v y))-
          gamma2SDPPairing (Z j ⊙ Matrix.vecMulVec u (star v)) N := by
      have hw : w=Sum.elim u v := by ext z; cases z <;> rfl
      rw [hw]
      exact gamma2_polar_block_quad a b (Z j) N u v
    apply Complex.nonneg_iff.mpr
    exact ⟨by rw [hquad]; exact hh, (hherm.im_star_dotProduct_mulVec_self w).symm⟩
  refine ⟨a,b,N,fun x => ⟨hα _,hα _⟩,hblock,?_⟩
  rw [hrepr,Fintype.sum_sum_type] at hlt
  dsimp [a,b]
  rw [← Finset.sum_mul, ← Finset.sum_mul] at hlt
  linarith
end SeparatorMultipliers

theorem gamma2SDPDualBlock_smul {X : Type} [DecidableEq X]
    (a b : X → ℝ) (Z N : Matrix X X ℂ) (r : ℝ) :
    gamma2SDPDualBlock (r • a) (r • b) Z (r • N)=r • gamma2SDPDualBlock a b Z N := by
  ext x y
  cases x <;> cases y <;>
    simp [gamma2SDPDualBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Complex.real_smul] <;> ring

theorem gamma2SDPPairing_smul {X : Type} [Fintype X]
    (A N : Matrix X X ℂ) (r : ℝ) :
    gamma2SDPPairing A (r • N)=r*gamma2SDPPairing A N := by
  simp [gamma2SDPPairing, Complex.real_smul, mul_assoc, Finset.mul_sum]

theorem gamma2_psd_separation {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (t : ℝ) (_ht : 0 ≤ t)
    (hsupport : ∀ x y, (∀ j, Z j x y=0) → A x y=0)
    (hcert : ¬gramFilteredCert A Z t) :
    ∃ (a b : X → ℝ) (N : Matrix X X ℂ),
      (∀ x, 0 ≤ a x ∧ 0 ≤ b x) ∧
      (∑ x, a x)+(∑ x, b x)=1 ∧
      (∀ j, (gamma2SDPDualBlock a b (Z j) N).PosSemidef) ∧
      t < gamma2SDPPairing A N := by
  obtain ⟨a,b,N,hab,hB,hsep⟩ := gamma2_psd_separator_unnormalized A Z t hcert
  let γ : ℝ := (∑ x, a x)+(∑ x, b x)
  have ha : 0 ≤ ∑ x, a x := Finset.sum_nonneg fun x _ => (hab x).1
  have hb : 0 ≤ ∑ x, b x := Finset.sum_nonneg fun x _ => (hab x).2
  have hγ : 0 < γ := by
    by_contra! hn
    have hg0 : γ=0 := le_antisymm hn (add_nonneg ha hb)
    have hax (x : X) : a x=0 := by
      have hh : a x ≤ ∑ y, a y := Finset.single_le_sum
        (fun y _ => (hab y).1) (Finset.mem_univ x)
      dsimp [γ] at hg0
      linarith [(hab x).1]
    have hp : gamma2SDPPairing A N=0 := by
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro y _
      change (star (N x y)*A x y).re=0
      rw [gamma2_psd_zero_weight_pairing A Z hsupport a b N hB x y (Or.inl (hax x))]
      rfl
    change t*γ < gamma2SDPPairing A N at hsep
    rw [hg0,hp,mul_zero] at hsep
    exact lt_irrefl 0 hsep
  let r : ℝ := γ⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr hγ.le
  refine ⟨r • a,r • b,r • N,?_,?_,?_,?_⟩
  · intro x
    exact ⟨mul_nonneg hr (hab x).1,mul_nonneg hr (hab x).2⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← mul_add]
    exact inv_mul_cancel₀ hγ.ne'
  · intro j
    rw [gamma2SDPDualBlock_smul]
    exact (hB j).smul hr
  · rw [gamma2SDPPairing_smul]
    change t < γ⁻¹*gamma2SDPPairing A N
    rw [mul_comm, ← div_eq_mul_inv]
    exact (lt_div_iff₀ hγ).mpr hsep

def gamma2RealPart {X : Type} (T : Matrix X X ℂ) : Matrix X X ℂ :=
  Matrix.of fun x y => ((T x y).re : ℂ)

theorem gamma2RealPart_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (T : Matrix X X ℂ) : ‖gamma2RealPart T‖ ≤ ‖T‖ := by
  let S : Matrix X X ℂ := Matrix.of fun x y => star (T x y)
  have hid : gamma2RealPart T=(1/2 : ℝ) • (T+S) := by
    ext x y
    apply Complex.ext
    · simp [gamma2RealPart, S, Complex.real_smul]
      ring
    · simp [gamma2RealPart, S, Complex.real_smul]
  rw [hid, norm_smul]
  have hs : ‖S‖ ≤ ‖T‖ := gamma2_entry_conj_norm_le T
  have ha := norm_add_le T S
  norm_num
  linarith

theorem gamma2RealPart_real_rayleigh {X : Type} [Fintype X] [DecidableEq X]
    (T : Matrix X X ℂ) (d : X → ℝ) :
    let dc : X → ℂ := fun x => (d x : ℂ)
    (star dc ⬝ᵥ ((gamma2RealPart T)*ᵥdc)).re=(star dc ⬝ᵥ (T*ᵥdc)).re := by
  (try dsimp only)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp [gamma2RealPart, Complex.mul_re]

theorem gamma2RealPart_isHermitian {X : Type} (T : Matrix X X ℂ) (hT : T.IsHermitian) :
    (gamma2RealPart T).IsHermitian := by
  ext x y
  have hh := congrArg Complex.re (hT.apply y x)
  simpa [gamma2RealPart, Matrix.conjTranspose_apply] using hh.symm
end Qatlib.Concepts.GramQueryCore.GammaDuality
