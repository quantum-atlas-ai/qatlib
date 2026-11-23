/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PottsTutte07.MainResults.Completeness
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Euclidean cup and additive commutator estimates

The cup estimate transfers the finite-sum identity to complex Euclidean states, assuming
the matrix adjoint-square relation from [AharonovEtAl2007], Lemma 10.1.
The perturbation estimate treats the additive commutator of complex matrices in the
L²-operator norm. The path-model construction of the cup and the group commutator
estimate in [AharonovEtAl2007], Lemma B.2 remain outside this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped Matrix.Norms.L2Operator

/-- If `AᴴA = d • 1` with nonnegative real `d`, then a Euclidean unit state is sent to a
vector of squared Euclidean norm `d` [AharonovEtAl2007], Lemma 10.1. -/
theorem lemma10_1_cup_operator_norm_euclidean
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ℝ) (_hd : 0 ≤ d) (A : Matrix ι ι ℂ)
    (hA : Matrix.conjTranspose A * A = (d : ℂ) • (1 : Matrix ι ι ℂ))
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    ‖(EuclideanSpace.equiv ι ℂ).symm (Matrix.mulVec A ψ)‖ ^ 2 = d := by
  have hψsum : ∑ i, Complex.normSq ((WithLp.ofLp ψ : ι → ℂ) i) = 1 := by
    simp only [Complex.normSq_eq_norm_sq]
    rw [← EuclideanSpace.norm_sq_eq, hψ]
    norm_num
  have hsum := Qatlib.Papers.PottsTutte07.MainResults.lemma10_1_cup_operator_norm
    ((d : ℝ) : ℂ) (by simp) A hA (WithLp.ofLp ψ) hψsum
  have houtput : (EuclideanSpace.equiv ι ℂ).symm
      (Matrix.mulVec A (WithLp.ofLp ψ : ι → ℂ)) =
      Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec
        (Matrix.mulVec A (WithLp.ofLp ψ : ι → ℂ)) := rfl
  rw [houtput, Qatlib.Foundations.PureStateMath.BornBridge.norm_toEuclidean_fromVec_sq]
  simp only [← Complex.normSq_eq_norm_sq]
  rw [hsum]
  rfl

/-- Under the same nondegenerate adjoint-square hypothesis, the L²-operator norm of the cup
operator is exactly the square root of `d` [AharonovEtAl2007], Lemma 10.1. -/
theorem lemma10_1_cup_operator_l2_opNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {d : ℝ} (hd : 0 < d)
    (A : Matrix ι ι ℂ)
    (hA : Matrix.conjTranspose A * A = (d : ℂ) • (1 : Matrix ι ι ℂ)) :
    ‖A‖ = Real.sqrt d := by
  have hSquare : d = ‖A‖ * ‖A‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self A, hA]
    simp [Real.norm_eq_abs, abs_of_nonneg hd.le, norm_smul]
  exact ((Real.sqrt_eq_iff_mul_self_eq hd.le (norm_nonneg A)).mpr hSquare).symm

/-- Perturbing either factor of a matrix product is controlled by the L²-operator norms of
the two factor errors. -/
private theorem product_sub_l2_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X Xt Y Yt : Matrix ι ι ℂ) :
    ‖X * Y - Xt * Yt‖ ≤
      ‖X - Xt‖ * ‖Y‖ + ‖Xt‖ * ‖Y - Yt‖ := by
  have hEq : X * Y - Xt * Yt = (X - Xt) * Y + Xt * (Y - Yt) := by
    noncomm_ring
  rw [hEq]
  calc ‖(X - Xt) * Y + Xt * (Y - Yt)‖ ≤
        ‖(X - Xt) * Y‖ + ‖Xt * (Y - Yt)‖ := norm_add_le _ _
    _ ≤ ‖X - Xt‖ * ‖Y‖ + ‖Xt‖ * ‖Y - Yt‖ := by
        exact add_le_add
          (show ‖(X - Xt) * Y‖ ≤ ‖X - Xt‖ * ‖Y‖ from
            Matrix.l2_opNorm_mul (X - Xt) Y)
          (show ‖Xt * (Y - Yt)‖ ≤ ‖Xt‖ * ‖Y - Yt‖ from
            Matrix.l2_opNorm_mul Xt (Y - Yt))

/-- Near the identity, the additive commutator is the difference of the products of the two
offsets from the identity. -/
private theorem additive_commutator_sub_one_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (V W : Matrix ι ι ℂ) :
    V * W - W * V = (V - 1) * (W - 1) - (W - 1) * (V - 1) := by
  noncomm_ring

/-- A uniform L²-operator estimate for perturbed additive commutators near the identity.
For invertible matrices, the additive commutator is the first factor of
`V * W * V⁻¹ * W⁻¹ - 1 = (V * W - W * V) * V⁻¹ * W⁻¹`, which relates this estimate
to the group commutator in [AharonovEtAl2007], Lemma B.2. -/
theorem lemmaB_2_commutator_lipschitz_l2_operator
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V W Vt Wt : Matrix ι ι ℂ) (ε δ : ℝ),
        0 < ε → 0 < δ → ε ≤ δ → δ ≤ 1 →
        ‖V - Vt‖ ≤ ε → ‖W - Wt‖ ≤ ε →
        ‖V - 1‖ ≤ δ → ‖W - 1‖ ≤ δ →
        ‖(V * W - W * V) - (Vt * Wt - Wt * Vt)‖ ≤ C * ε * δ := by
  refine ⟨6, by norm_num, ?_⟩
  intro V W Vt Wt ε δ hε hδ hεδ hδ1 hV hW hVI hWI
  have hVtI : ‖Vt - 1‖ ≤ δ + ε := by
    have hEq : Vt - 1 = (Vt - V) + (V - 1) := by abel
    rw [hEq]
    calc ‖(Vt - V) + (V - 1)‖ ≤ ‖Vt - V‖ + ‖V - 1‖ := norm_add_le _ _
      _ = ‖V - Vt‖ + ‖V - 1‖ := by rw [norm_sub_rev Vt V]
      _ ≤ ε + δ := add_le_add hV hVI
      _ = δ + ε := by ring
  have hWtI : ‖Wt - 1‖ ≤ δ + ε := by
    have hEq : Wt - 1 = (Wt - W) + (W - 1) := by abel
    rw [hEq]
    calc ‖(Wt - W) + (W - 1)‖ ≤ ‖Wt - W‖ + ‖W - 1‖ := norm_add_le _ _
      _ = ‖W - Wt‖ + ‖W - 1‖ := by rw [norm_sub_rev Wt W]
      _ ≤ ε + δ := add_le_add hW hWI
      _ = δ + ε := by ring
  have hp1 := product_sub_l2_norm_le (V - 1) (Vt - 1) (W - 1) (Wt - 1)
  have hp2 := product_sub_l2_norm_le (W - 1) (Wt - 1) (V - 1) (Vt - 1)
  have hDV1 : ‖V - 1 - (Vt - 1)‖ = ‖V - Vt‖ := by
    congr 1
    abel
  have hDW1 : ‖W - 1 - (Wt - 1)‖ = ‖W - Wt‖ := by
    congr 1
    abel
  rw [hDV1, hDW1] at hp1
  rw [hDW1, hDV1] at hp2
  have ha1 : ‖V - Vt‖ * ‖W - 1‖ ≤ ε * δ :=
    mul_le_mul hV hWI (norm_nonneg _) (le_of_lt hε)
  have hb1 : ‖Vt - 1‖ * ‖W - Wt‖ ≤ (δ + ε) * ε :=
    mul_le_mul hVtI hW (norm_nonneg _) (by positivity)
  have ha2 : ‖W - Wt‖ * ‖V - 1‖ ≤ ε * δ :=
    mul_le_mul hW hVI (norm_nonneg _) (le_of_lt hε)
  have hb2 : ‖Wt - 1‖ * ‖V - Vt‖ ≤ (δ + ε) * ε :=
    mul_le_mul hWtI hV (norm_nonneg _) (by positivity)
  rw [additive_commutator_sub_one_eq V W, additive_commutator_sub_one_eq Vt Wt]
  have hsplit : ((V - 1) * (W - 1) - (W - 1) * (V - 1)) -
      ((Vt - 1) * (Wt - 1) - (Wt - 1) * (Vt - 1)) =
      ((V - 1) * (W - 1) - (Vt - 1) * (Wt - 1)) -
        ((W - 1) * (V - 1) - (Wt - 1) * (Vt - 1)) := by
    abel
  rw [hsplit]
  have htriangle := norm_sub_le
    ((V - 1) * (W - 1) - (Vt - 1) * (Wt - 1))
    ((W - 1) * (V - 1) - (Wt - 1) * (Vt - 1))
  nlinarith [hp1, hp2, ha1, hb1, ha2, hb2, hε, hδ, hεδ, hδ1,
    norm_nonneg (V - Vt), norm_nonneg (W - Wt), norm_nonneg (V - 1), norm_nonneg (W - 1),
    norm_nonneg (Vt - 1), norm_nonneg (Wt - 1)]

end Qatlib.Papers.PottsTutte07.MainResults
