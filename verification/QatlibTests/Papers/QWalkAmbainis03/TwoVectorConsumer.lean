module

public import Qatlib.Papers.QWalkAmbainis03.GroverInterp.TwoVectorDecomposition

@[expose] public section

/-!
# Concrete consumer for the Claim 5 two-vector decomposition

The spectral model is instantiated on `Fin 3` with one real eigenpair:
`start = e₀`, `w 0 true = e₁`, `w 0 false = e₂`, `a 0 = 1`,
`θ 0 = π / 2`, `ε = 1 / 2`, `α = 1 / 10`, `β = 1 / 4`.  This is a
nondegenerate instance (`l = 1`, `m = 3`), and the end vector is nonzero.
The consumer invokes the top-level theorem on this instance and records the
resulting uniform residual bound.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.Papers.QWalkAmbainis03.TwoVectorConsumer

open Qatlib.Papers.QWalkAmbainis03.GroverInterp.TwoVectorDecomposition
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators

/-- The first basis vector of `Fin 3 → ℂ`. -/
def e0 : Fin 3 → ℂ := fun i => if i = 0 then 1 else 0

/-- The second basis vector of `Fin 3 → ℂ`. -/
def e1 : Fin 3 → ℂ := fun i => if i = 1 then 1 else 0

/-- The third basis vector of `Fin 3 → ℂ`. -/
def e2 : Fin 3 → ℂ := fun i => if i = 2 then 1 else 0

/-- A pair of orthonormal coordinate vectors for one phase block. -/
def w3 : Fin 1 → Bool → Fin 3 → ℂ
  | _, true => e1
  | _, false => e2

/-- The real coefficient of the single eigenpair. -/
def a3 : Fin 1 → ℝ := fun _ => 1

/-- The eigenphase `π / 2`. -/
noncomputable def θ3 : Fin 1 → ℝ := fun _ => Real.pi / 2

/-- The start direction has unit norm. -/
theorem e0_norm : (∑ i, ‖e0 i‖ ^ 2) = 1 := by
  simp [e0, Fin.sum_univ_three]

/-- Each eigenvector has unit norm. -/
theorem w3_norm (j : Fin 1) (s : Bool) : (∑ i, ‖w3 j s i‖ ^ 2) = 1 := by
  cases j
  cases s <;> simp [w3, e1, e2, Fin.sum_univ_three]

/-- Distinct spectral basis vectors are orthogonal. -/
theorem w3_orth (j j' : Fin 1) (s s' : Bool) (h : (j, s) ≠ (j', s')) :
    (∑ i, star (w3 j s i) * w3 j' s' i) = 0 := by
  have hj : j = j' := Subsingleton.elim _ _
  subst j'
  cases s <;> cases s'
  · exact (h rfl).elim
  · simp [w3, e1, e2]
  · simp [w3, e1, e2]
  · exact (h rfl).elim

/-- The eigenbasis is orthogonal to the start direction. -/
theorem w3_start (j : Fin 1) (s : Bool) :
    (∑ i, star (w3 j s i) * e0 i) = 0 := by
  cases j
  cases s <;> simp [w3, e0, e1, e2]

/-- The concrete phase lies in the required gap. -/
theorem θ3_gap (j : Fin 1) :
    (1 / 2 : ℝ) ≤ θ3 j ∧ θ3 j ≤ 2 * Real.pi - 1 / 2 ∧ θ3 j ≠ Real.pi := by
  cases j
  constructor
  · simp [θ3]
    nlinarith [Real.pi_gt_three]
  constructor
  · simp [θ3]
    nlinarith [Real.pi_gt_three]
  · simp [θ3]
    nlinarith [Real.pi_gt_three]

/-- The end vector of the concrete model is nonzero. -/
theorem vEnd_ne_zero : vEnd a3 θ3 w3 e0 ≠ 0 := by
  have hB := basisVec_orthonormal w3 e0 e0_norm w3_norm w3_orth w3_start
  have hsq := norm_sq_vEnd_eq a3 θ3 w3 e0 hB
  have hc : 0 < ‖cEnd a3 θ3 (some (0, true))‖ ^ 2 := by
    have hne : cEnd a3 θ3 (some (0, true)) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [cEnd, a3] at hre
      simp only [Complex.ofReal_one, one_mul, Complex.add_re, Complex.one_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, mul_zero, sub_zero, add_zero, Complex.zero_re] at hre
      exact one_ne_zero hre
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (Option (Fin 1 × Bool))))
    (f := fun x => ‖cEnd a3 θ3 x‖ ^ 2)
    (fun x _ => sq_nonneg _) (Finset.mem_univ (some (0, true)))
  have hsum : 0 < ∑ x, ‖cEnd a3 θ3 x‖ ^ 2 :=
    lt_of_lt_of_le hc hsingle
  have hnorm : 0 < ‖toEuclidean_fromVec (vEnd a3 θ3 w3 e0)‖ ^ 2 := by
    rw [hsq]
    exact hsum
  intro hzero
  have hzero' : toEuclidean_fromVec (vEnd a3 θ3 w3 e0) = 0 := by
    rw [hzero]
    rfl
  rw [hzero'] at hnorm
  simp at hnorm

/-- The top-level Claim 5 decomposition invoked on the concrete nondegenerate
spectral model.  The residual is bounded by the theorem's uniform constant
times `β / ε` at `β = 1 / 4` and `ε = 1 / 2`. -/
theorem claim5_concrete :
    ∃ C : ℝ, 0 < C ∧
      ∃ cS cE : ℝ, 0 < cS ∧ 0 < cE ∧
        cS = (1 / 10) * Real.cot ((1 / 4) / 2) /
          ‖toEuclidean_fromVec (vBeta (1 / 10) (1 / 4) a3 θ3 w3 e0)‖ ∧
        cE = ‖toEuclidean_fromVec (vEnd a3 θ3 w3 e0)‖ /
          ‖toEuclidean_fromVec (vBeta (1 / 10) (1 / 4) a3 θ3 w3 e0)‖ ∧
        (((‖toEuclidean_fromVec (vBeta (1 / 10) (1 / 4) a3 θ3 w3 e0)‖ : ℝ) : ℂ))⁻¹ •
            toEuclidean_fromVec (vBeta (1 / 10) (1 / 4) a3 θ3 w3 e0) =
          ((cS : ℂ) * Complex.I) • toEuclidean_fromVec e0 +
            cE • ((((‖toEuclidean_fromVec (vEnd a3 θ3 w3 e0)‖ : ℝ) : ℂ))⁻¹ •
              toEuclidean_fromVec (vEnd a3 θ3 w3 e0)) +
            (((‖toEuclidean_fromVec (vBeta (1 / 10) (1 / 4) a3 θ3 w3 e0)‖ : ℝ) : ℂ))⁻¹ •
              toEuclidean_fromVec
                (vBetaResidual (1 / 10) (1 / 4) a3 θ3 w3 e0) ∧
        ‖(((‖toEuclidean_fromVec (vBeta (1 / 10) (1 / 4) a3 θ3 w3 e0)‖ : ℝ) : ℂ))⁻¹ •
            toEuclidean_fromVec
              (vBetaResidual (1 / 10) (1 / 4) a3 θ3 w3 e0)‖ ≤
          C * (1 / 4) / (1 / 2) := by
  obtain ⟨C, hC, hmain⟩ := claim5_two_vector_decomposition
  obtain ⟨_, hrest⟩ := hmain 3 1 (1 / 2) (1 / 10) (1 / 4) a3 θ3 w3 e0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) e0_norm w3_norm w3_orth w3_start θ3_gap
    vEnd_ne_zero
  exact ⟨C, hC, hrest⟩

end QatlibTests.Papers.QWalkAmbainis03.TwoVectorConsumer
