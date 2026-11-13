/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.ActualDiagonalization

/-!
# Spectral formulas for finite Gibbs states

The matrix `gibbsMatrix H T` is the exponential of `(-1 / T) • H`, and `gibbsState` normalizes
it by its real trace. For Hermitian `H`, diagonalization yields positivity, the partition sum,
and the Boltzmann-weighted energy formula, including an identity for the full complex trace. See
[CrostaSaubanereHuber2026].

## Main statements

* `gibbs_density`: proves that the normalized Gibbs matrix is a density on a nonempty finite
  space.
* `gibbs_energy_complex`: computes the complex energy trace in the eigenbasis of `H`.
* `positive_temperature_gibbs`: packages physicality and the energy formula for positive
  temperature.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.KoopmanSim26.SpectralRep

namespace Qatlib.Papers.RydbergMaxCut26.Thermal.Spectral
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The matrix exponential of `(-1 / T) • H`. -/
def gibbsMatrix (H : Matrix I I ℂ) (T : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-1/T:ℝ) • H)

/-- The real part of the trace of the unnormalized Gibbs matrix. -/
def partition (H : Matrix I I ℂ) (T : ℝ) : ℝ := (gibbsMatrix H T).trace.re

/-- The Gibbs matrix multiplied by the reciprocal of its partition function. -/
def gibbsState (H : Matrix I I ℂ) (T : ℝ) : Matrix I I ℂ :=
  (partition H T)⁻¹ • gibbsMatrix H T

/-- The Boltzmann weight `exp (-E_i / T)` of the `i`th eigenvalue of the Hermitian matrix `H`. -/
def weight (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) (i : I) : ℝ :=
  Real.exp (-hH.eigenvalues i/T)

/-- The Gibbs matrix is the conjugate of the diagonal matrix of Boltzmann weights by the
eigenvector unitary of `H`. -/
theorem gibbs_spectral (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    gibbsMatrix H T=(hH.eigenvectorUnitary : Matrix I I ℂ)*
      diagonal (fun i => (weight H hH T i:ℂ))*(hH.eigenvectorUnitary : Matrix I I ℂ)ᴴ := by
  have hs : (-1/T:ℝ) • H=((-1/T:ℝ):ℂ) • H := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  rw [gibbsMatrix,hs,hermitian_exp_spectral H hH ((-1/T:ℝ):ℂ)]
  apply congrArg (fun D : Matrix I I ℂ =>
    (hH.eigenvectorUnitary : Matrix I I ℂ)*D*(hH.eigenvectorUnitary : Matrix I I ℂ)ᴴ)
  apply congrArg diagonal
  funext i
  rw [← Complex.ofReal_mul,← Complex.ofReal_exp]
  unfold weight
  congr 2
  ring

/-- The conjugate transpose of the Hermitian eigenvector unitary multiplied by that unitary
equals the identity. -/
theorem eigenbasis_inverse (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix I I ℂ)ᴴ*(hH.eigenvectorUnitary : Matrix I I ℂ)=1 := by
  exact Unitary.coe_star_mul_self hH.eigenvectorUnitary

/-- The complex trace of the Gibbs matrix equals the real sum of Boltzmann weights, embedded
into the complex numbers. -/
theorem gibbs_trace (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    (gibbsMatrix H T).trace=((∑ i,weight H hH T i:ℝ):ℂ) := by
  rw [gibbs_spectral H hH T,Matrix.trace_mul_cycle,eigenbasis_inverse H hH,
    Matrix.one_mul,Matrix.trace_diagonal]
  simp

/-- The partition function of a Hermitian matrix equals the sum of its Boltzmann weights. -/
theorem partition_spectral (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    partition H T=∑ i,weight H hH T i := by
  rw [partition,gibbs_trace H hH T]
  rfl

/-- For a Hermitian matrix on a nonempty finite index type, the partition function is positive
for every real parameter `T`. -/
theorem partition_pos [Nonempty I] (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    0<partition H T := by
  rw [partition_spectral H hH T]
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The Gibbs matrix of a Hermitian matrix is positive semidefinite. -/
theorem gibbsMatrix_pos (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    (gibbsMatrix H T).PosSemidef := by
  rw [gibbs_spectral H hH T]
  have hd : (diagonal (fun i => (weight H hH T i:ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0:ℂ)≤(Real.exp (-hH.eigenvalues i/T):ℂ)
    exact RCLike.nonneg_iff.mpr ⟨(Real.exp_pos _).le,rfl⟩
  exact hd.mul_mul_conjTranspose_same _

/-- For a Hermitian matrix on a nonempty finite index type, the normalized Gibbs state is
positive semidefinite and has trace one; see [CrostaSaubanereHuber2026]. -/
theorem gibbs_density [Nonempty I] (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    (gibbsState H T).PosSemidef ∧ (gibbsState H T).trace=1 := by
  have hZ := partition_pos H hH T
  refine ⟨(gibbsMatrix_pos H hH T).smul (inv_nonneg.mpr hZ.le),?_⟩
  have ht : (gibbsMatrix H T).trace=(partition H T:ℂ) := by
    rw [gibbs_trace H hH T,partition_spectral H hH T]
  rw [gibbsState,Matrix.trace_smul,ht,Complex.real_smul,← Complex.ofReal_mul,
    inv_mul_cancel₀ hZ.ne']
  rfl

/-- The trace of the unnormalized Gibbs matrix multiplied by `H` is the real sum of eigenvalues
times their Boltzmann weights, embedded into the complex numbers. -/
theorem gibbsMatrix_energy_trace (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    (gibbsMatrix H T*H).trace=((∑ i,hH.eigenvalues i*weight H hH T i:ℝ):ℂ) := by
  let U : Matrix I I ℂ := hH.eigenvectorUnitary
  let D : Matrix I I ℂ := diagonal (fun i => (weight H hH T i:ℂ))
  let L : Matrix I I ℂ := diagonal (fun i => (hH.eigenvalues i:ℂ))
  have hU : Uᴴ*U=1 := eigenbasis_inverse H hH
  have hG : gibbsMatrix H T=U*D*Uᴴ := gibbs_spectral H hH T
  have hH' : H=U*L*Uᴴ := hH.spectral_theorem
  conv_lhs => rw [hG,hH']
  have he : (U*D*Uᴴ)*(U*L*Uᴴ)=U*(D*L)*Uᴴ := by
    calc
      _ = U*D*(Uᴴ*U)*L*Uᴴ := by noncomm_ring
      _ = _ := by rw [hU]; simp only [Matrix.mul_one,Matrix.mul_assoc]
  rw [he,Matrix.trace_mul_cycle,hU,Matrix.one_mul]
  simp only [D,L,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For a Hermitian matrix on a nonempty finite index type, the real energy trace of its Gibbs
state equals the Boltzmann-weighted mean of its eigenvalues. -/
theorem gibbs_energy [Nonempty I] (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    (gibbsState H T*H).trace.re=
      (∑ i,hH.eigenvalues i*Real.exp (-hH.eigenvalues i/T))/
        (∑ i,Real.exp (-hH.eigenvalues i/T)) := by
  rw [gibbsState,Matrix.smul_mul,Matrix.trace_smul,Complex.smul_re,
    gibbsMatrix_energy_trace H hH T,Complex.ofReal_re,partition_spectral H hH T]
  unfold weight
  simp only [smul_eq_mul]
  ring

/-- The full complex energy trace of the Gibbs state equals the real Boltzmann-weighted
eigenvalue mean embedded into the complex numbers; see [CrostaSaubanereHuber2026]. -/
theorem gibbs_energy_complex (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    (gibbsState H T*H).trace=
      (((∑ i,hH.eigenvalues i*Real.exp (-hH.eigenvalues i/T))/
        (∑ i,Real.exp (-hH.eigenvalues i/T)):ℝ):ℂ) := by
  rw [gibbsState,Matrix.smul_mul,Matrix.trace_smul,gibbsMatrix_energy_trace H hH T,
    Complex.real_smul,← Complex.ofReal_mul,partition_spectral H hH T]
  unfold weight
  congr 1
  ring

/-- At positive temperature, a Hermitian matrix on a nonempty finite index type has a positive
partition function and a positive semidefinite, trace-one Gibbs state whose energy is the
Boltzmann-weighted eigenvalue mean. -/
theorem positive_temperature_gibbs [Nonempty I] (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (T : ℝ) (hT : 0<T) :
    0<T ∧ 0<partition H T ∧ (gibbsState H T).PosSemidef ∧ (gibbsState H T).trace=1 ∧
      (gibbsState H T*H).trace.re=
        (∑ i,hH.eigenvalues i*Real.exp (-hH.eigenvalues i/T))/
          (∑ i,Real.exp (-hH.eigenvalues i/T)) :=
  ⟨hT,partition_pos H hH T,(gibbs_density H hH T).1,(gibbs_density H hH T).2,gibbs_energy H hH T⟩

end Qatlib.Papers.RydbergMaxCut26.Thermal.Spectral
