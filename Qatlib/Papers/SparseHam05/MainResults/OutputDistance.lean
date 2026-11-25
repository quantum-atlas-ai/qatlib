/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Papers.SparseHam05.MainResults.ExponentialCount

@[expose] public section

/-!
# Transport from operator error to pure-state trace distance

The inequality preceding Theorem 1 bounds the distance of normalized
unitary outputs by the Euclidean vector error, and then by the operator
error of the two unitaries. This transports the existing Suzuki word
bound using the Euclidean input norm.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.SparseHam05.MainResults

namespace Qatlib.Papers.SparseHam05.MainResults

/-- For unit vectors, the pure-state trace distance is at most the
Euclidean distance between the vectors. -/
theorem pure_trace_distance_le_euclidean {I : Type} [Fintype I]
    (u v : EuclideanSpace ℂ I) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    pureTraceDistanceOn u.ofLp v.ofLp ≤ ‖u - v‖ := by
  have hinner : (∑ i, u i * star (v i)) = ⟪v, u⟫_ℂ := rfl
  rw [pureTraceDistanceOn, hinner]
  apply (Real.sqrt_le_left (norm_nonneg _)).2
  rw [norm_sub_sq (𝕜 := ℂ), hu, hv]
  have hre : RCLike.re ⟪u, v⟫_ℂ = Complex.re ⟪v, u⟫_ℂ := inner_re_symm u v
  rw [hre, Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (Complex.re ⟪v, u⟫_ℂ - 1), sq_nonneg (Complex.im ⟪v, u⟫_ℂ)]

/-- On every normalized input, the pure-state output distance is
bounded by the operator-norm approximation error. -/
theorem unitary_outputs_trace_le {I : Type} [Fintype I] [DecidableEq I]
    (U V : Matrix I I ℂ) (ψ : EuclideanSpace ℂ I)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hψ : ‖ψ‖ = 1) :
    pureTraceDistanceOn (U *ᵥ ψ.ofLp) (V *ᵥ ψ.ofLp) ≤ ‖U - V‖ := by
  let u : EuclideanSpace ℂ I := WithLp.toLp 2 (U *ᵥ ψ.ofLp)
  let v : EuclideanSpace ℂ I := WithLp.toLp 2 (V *ᵥ ψ.ofLp)
  have hnorm (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
      ‖(WithLp.toLp 2 (A *ᵥ ψ.ofLp) : EuclideanSpace ℂ I)‖ = 1 := by
    have hsq := sum_normSq_mulVec_of_mem_unitaryGroup hA ψ.ofLp
    have hsq' : ‖(WithLp.toLp 2 (A *ᵥ ψ.ofLp) : EuclideanSpace ℂ I)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simpa only [Complex.normSq_eq_norm_sq] using hsq
    rw [hψ, one_pow] at hsq'
    nlinarith [norm_nonneg (WithLp.toLp 2 (A *ᵥ ψ.ofLp) : EuclideanSpace ℂ I)]
  have hop := Matrix.l2_opNorm_mulVec (U - V) ψ
  change ‖(WithLp.toLp 2 ((U - V) *ᵥ ψ.ofLp) : EuclideanSpace ℂ I)‖ ≤
    ‖U - V‖ * ‖ψ‖ at hop
  rw [hψ, mul_one, Matrix.sub_mulVec] at hop
  exact (pure_trace_distance_le_euclidean u v (hnorm U hU) (hnorm V hV)).trans hop

/-- The exponential count and the pure-state error both hold for the
same positive Suzuki repetition count. -/
theorem theorem1_output_distance {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t ε : ℝ)
    (hh : ∀ X ∈ hs, Xᴴ = X) (hk : 1 ≤ k) (hm : 0 < hs.length)
    (hbound : ∀ X ∈ hs, ‖X‖ ≤ ‖hs.sum‖)
    (ht : 0 ≤ t) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : 1 ≤ 2 * (hs.length : ℝ) * (5 : ℝ) ^ (k - 1) * ‖hs.sum‖ * t) :
    let r := theorem1R hs.length k (‖hs.sum‖ * t) ε
    0 < r ∧
      ((paperSuzukiWord hs k t r).length : ℝ) ≤
        2 * (hs.length : ℝ) * (5 : ℝ) ^ (2 * k) *
          ((hs.length : ℝ) * (‖hs.sum‖ * t)) ^ (1 + 1 / (2 * (k : ℝ))) /
            ε ^ (1 / (2 * (k : ℝ))) ∧
      ∀ ψ : EuclideanSpace ℂ I, ‖ψ‖ = 1 →
        pureTraceDistanceOn ((paperSuzukiWord hs k t r).prod *ᵥ ψ.ofLp)
          (NormedSpace.exp (t • (paperAntiHermitian hs).sum) *ᵥ ψ.ofLp) ≤ ε := by
  let r := theorem1R hs.length k (‖hs.sum‖ * t) ε
  obtain ⟨hr, hcount, herror⟩ :=
    source_theorem1_exponential_count hs k t ε hh hk hm hbound ht hε0 hε1 hτ
  have sum_hermitian (matrices : List (Matrix I I ℂ))
      (hermitian : ∀ X ∈ matrices, Xᴴ = X) : matrices.sumᴴ = matrices.sum := by
    induction matrices with
    | nil => simp
    | cons X xs ih =>
      have hX : Xᴴ = X := hermitian X (by simp)
      have hxs : xs.sumᴴ = xs.sum := ih (fun Y hY => hermitian Y (by simp [hY]))
      simp [hX, hxs]
  have hsum := sum_hermitian hs hh
  have hanti : (paperAntiHermitian hs).sumᴴ = -(paperAntiHermitian hs).sum := by
    rw [sum_paperAntiHermitian, Matrix.conjTranspose_smul, hsum, ← neg_smul]
    congr 1
    simp only [RCLike.star_def, map_neg, Complex.conj_I]
  have hU : (paperSuzukiWord hs k t r).prod ∈ Matrix.unitaryGroup I ℂ :=
    paperSuzukiWord_unitary hs k r t hh hr
  have hV : NormedSpace.exp (t • (paperAntiHermitian hs).sum) ∈ Matrix.unitaryGroup I ℂ := by
    apply exp_unitary_of_skewHermitian
    rw [Matrix.conjTranspose_smul, hanti, star_trivial, smul_neg]
  exact ⟨hr, hcount, fun ψ hψ => (unitary_outputs_trace_le _ _ ψ hU hV hψ).trans herror⟩

end Qatlib.Papers.SparseHam05.MainResults
