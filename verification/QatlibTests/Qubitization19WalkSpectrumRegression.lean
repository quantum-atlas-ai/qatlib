module

public import Qatlib.Papers.Qubitization19.MainResults.WalkSpectrum

@[expose] public section

/-!
# Consumer regression for the qubitization walk spectrum

The examples consume the reflection construction, Chebyshev powers,
eigenphases and phased iterate. The rational corner tests take powers of
the reflected branch oracles with encoded values `3 / 5` and `-4 / 5`.
-/

set_option autoImplicit false

open Matrix Qatlib.Papers.Qubitization19.MainResults

namespace QatlibTests.Qubitization19WalkSpectrumRegression

/- For the encoded value `3 / 5`, the squared qubitization walk has
encoded corner `T₂ (3 / 5) = -7 / 25`, and the cubed walk has encoded corner
`T₃ (3 / 5) = -117 / 125`. -/
example :
    let U := branchOracle (Real.arccos (3 / 5))
    U 0 0 = (3 : ℂ) / 5 ∧
      ((branchReflection * U) ^ 2) 0 0 = (-7 : ℂ) / 25 ∧
      ((branchReflection * U) ^ 3) 0 0 = (-117 : ℂ) / 125 := by
  dsimp only
  rw [branchOracle_apply_zero_zero, Real.cos_arccos (by norm_num) (by norm_num),
    branchReflection_mul_branchOracle]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [branchRotation_pow_apply_zero_zero,
      Polynomial.Chebyshev.T_real_cos]
    change (↑(Real.cos (2 * Real.arccos (3 / 5))) : ℂ) = (-7 : ℂ) / 25
    rw [Real.cos_two_mul, Real.cos_arccos (by norm_num) (by norm_num)]
    norm_num
  · rw [branchRotation_pow_apply_zero_zero,
      Polynomial.Chebyshev.T_real_cos]
    change (↑(Real.cos (3 * Real.arccos (3 / 5))) : ℂ) = (-117 : ℂ) / 125
    rw [Real.cos_three_mul, Real.cos_arccos (by norm_num) (by norm_num)]
    norm_num

/- For the encoded value `-4 / 5`, the squared reflected walk has corner
`T₂ (-4 / 5) = 7 / 25`, distinct from the `3 / 5` branch. -/
example :
    let U := branchOracle (Real.arccos (-4 / 5))
    U 0 0 = (-4 : ℂ) / 5 ∧ ((branchReflection * U) ^ 2) 0 0 = (7 : ℂ) / 25 := by
  dsimp only
  rw [branchOracle_apply_zero_zero, Real.cos_arccos (by norm_num) (by norm_num),
    branchReflection_mul_branchOracle]
  refine ⟨by norm_num, ?_⟩
  rw [branchRotation_pow_apply_zero_zero,
    Polynomial.Chebyshev.T_real_cos]
  change (↑(Real.cos (2 * Real.arccos (-4 / 5))) : ℂ) = (7 : ℂ) / 25
  rw [Real.cos_two_mul, Real.cos_arccos (by norm_num) (by norm_num)]
  norm_num

/-- The Hermitian involution `hB` below is exactly the branch oracle at
`arccos (1 / 2)`; it squares to the identity, is Hermitian, and reflection
qubitization turns it into the walk whose third power has corner `-1`. -/
noncomputable def hB : Matrix (Fin 2) (Fin 2) ℂ :=
  branchOracle (Real.arccos (1 / 2))

example : hB * hB = 1 ∧ hB.IsHermitian ∧
    branchReflection * hB = branchRotation (Real.arccos (1 / 2)) ∧
    ((branchRotation (Real.arccos (1 / 2))) ^ 3) 0 0 = -1 := by
  refine ⟨branchOracle_mul_self _, branchOracle_isHermitian _,
    branchReflection_mul_branchOracle _, ?_⟩
  rw [branchRotation_pow_apply_zero_zero,
    Polynomial.Chebyshev.T_real_cos]
  change (↑(Real.cos (3 * Real.arccos (1 / 2))) : ℂ) = -1
  rw [Real.cos_three_mul, Real.cos_arccos (by norm_num) (by norm_num)]
  norm_num

/-- Both eigenphases occur for the concrete branch `cos θ = 3 / 5`, on
nonzero eigenvectors. -/
example :
    branchRotation (Real.arccos (3 / 5)) *ᵥ ![1, -Complex.I] =
        Complex.exp ((Real.arccos (3 / 5) : ℂ) * Complex.I) •
          ![1, -Complex.I] ∧
      branchRotation (Real.arccos (3 / 5)) *ᵥ ![1, Complex.I] =
        Complex.exp (-(Real.arccos (3 / 5) : ℂ) * Complex.I) •
          ![1, Complex.I] ∧
      (![1, -Complex.I] : Fin 2 → ℂ) ≠ 0 ∧ (![1, Complex.I] : Fin 2 → ℂ) ≠ 0 := by
  exact ⟨branchRotation_mulVec_eigen_plus _, branchRotation_mulVec_eigen_minus _,
    branch_eigenvectors_ne_zero⟩

/- The eigenbranch package specializes to the encoded value `3 / 5`. -/
example :
    ∃ θ : ℝ, Real.cos θ = 3 / 5 ∧ branchOracle θ 0 0 = ((3 : ℂ) / 5) ∧
      ((branchRotation θ) ^ 2) 0 0 = (-7 : ℂ) / 25 := by
  obtain ⟨θ, hcos, hcorner, hpow, _, _⟩ :=
    exists_branch_walk_of_mem_Icc (show (3 / 5 : ℝ) ∈ Set.Icc (-1) 1 by norm_num)
  refine ⟨θ, hcos, ?_, ?_⟩
  · rw [hcorner]
    norm_num
  · have h := hpow 2
    rw [← hcos, Polynomial.Chebyshev.T_real_cos] at h
    rw [h]
    change (↑(Real.cos (2 * θ)) : ℂ) = (-7 : ℂ) / 25
    rw [Real.cos_two_mul, hcos]
    norm_num

/-- A phased iterate at the concrete branch `cos θ = 3 / 5` still has the
Chebyshev corner `-7 / 25` after two steps, for an explicit nonzero phase,
and its conjugated eigenvector keeps the same eigenphase. -/
example :
    ((phasedWalk (1 / 3) (Real.arccos (3 / 5))) ^ 2) 0 0 = (-7 : ℂ) / 25 ∧
      phasedWalk (1 / 3) (Real.arccos (3 / 5)) *ᵥ
          (partialReflection (1 / 3 + Real.pi / 2) *ᵥ ![1, -Complex.I]) =
        Complex.exp ((Real.arccos (3 / 5) : ℂ) * Complex.I) •
          (partialReflection (1 / 3 + Real.pi / 2) *ᵥ ![1, -Complex.I]) ∧
      (partialReflection (1 / 3 + Real.pi / 2) *ᵥ ![1, -Complex.I]) ≠ 0 := by
  refine ⟨?_, phasedWalk_mulVec_conj_eigen_plus _ _, ?_⟩
  · rw [phasedWalk_pow_apply_zero_zero,
      Polynomial.Chebyshev.T_real_cos]
    change (↑(Real.cos (2 * Real.arccos (3 / 5))) : ℂ) = (-7 : ℂ) / 25
    rw [Real.cos_two_mul, Real.cos_arccos (by norm_num) (by norm_num)]
    norm_num
  · intro h
    apply branch_eigenvectors_ne_zero.1
    simpa only [Matrix.mulVec_mulVec, partialReflection_neg_mul, Matrix.one_mulVec,
      Matrix.mulVec_zero] using congrArg (fun v => partialReflection (-(1 / 3 + Real.pi / 2)) *ᵥ v) h

/-- The walk for the concrete eigenvalue `3 / 5` is unitary. -/
example :
    branchRotation (Real.arccos (3 / 5)) ∈
      Matrix.unitaryGroup (Fin 2) ℂ :=
  branchRotation_mem_unitaryGroup _

open Qatlib.Foundations.PureStateMath in
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding in
/- An encoded eigenpair with eigenvalue `3 / 5` gives the same squared
rotation on the frame in the original oracle workspace. -/
example {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : Matrix (J × I) (J × I) ℂ) (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ)
    (j₀ : J) (A : Matrix I I ℂ) (hc : BlockCorner U j₀ = A)
    (h2 : BlockCorner (U * U) j₀ = 1) (ψ : QState I) (hψ : Normalized ψ)
    (hAψ : A *ᵥ ψ = ((3 / 5 : ℝ) : ℂ) • ψ) :
    ∃ E : Matrix (J × I) (Fin 2) ℂ, E.col 0 = TensorState (Ket j₀) ψ ∧
      (FiberReflection j₀ * U) ^ 2 * E = E * branchRotation (Real.arccos (3 / 5)) ^ 2 := by
  obtain ⟨E, hE, _, _, _, hpow⟩ :=
    eq17_branch_rotation_powers U hU j₀ A hc h2 ψ hψ (3 / 5) (by norm_num) hAψ
  exact ⟨E, hE, hpow 2⟩

end QatlibTests.Qubitization19WalkSpectrumRegression
