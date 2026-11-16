/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Average-Hamiltonian and Duhamel bounds

Fixed source: Poulin--Qarry--Somma--Verstraete, arXiv:1102.1360v1,
Appendices A and B. The actual Dyson propagator is compared with the exponential
of the ordinary Hamiltonian integral. Pointwise Hermiticity is essential.

The source prints a linear time-bin bound in Eq. (4). The reconstructed proof
first establishes the scale-correct quadratic bound `M^2 * δ^2`; the literal
printed bound follows on the explicitly small bins `0 ≤ δ ≤ 2`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Papers.TimeDepSim11.MainResults.AverageHamiltonianBound

/-- Contractive matrix ODEs with generator norm at most `M` are `M`-Lipschitz. -/
theorem ode_lipschitz {I : Type} [Fintype I] [DecidableEq I]
    (A U : ℝ → Matrix I I ℂ) (M s t : ℝ)
    (hd : ∀ u, HasDerivAt U (-(A u * U u)) u)
    (hU : ∀ u, ‖U u‖ ≤ 1) (hA : ∀ u, ‖A u‖ ≤ M) :
    ‖U t - U s‖ ≤ M * |t-s| := by
  have hn (u : ℝ) : ‖-(A u * U u)‖ ≤ M := by
    rw [norm_neg]
    calc
      ‖A u * U u‖ ≤ ‖A u‖ * ‖U u‖ := norm_mul_le _ _
      _ ≤ ‖A u‖ * 1 := mul_le_mul_of_nonneg_left (hU u) (norm_nonneg _)
      _ ≤ M := by simpa using hA u
  simpa only [Real.norm_eq_abs] using
    (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => hn u) (mem_univ s) (mem_univ t)

/-- A contractive matrix ODE has a quadratic first-order integral remainder. -/
theorem ode_remainder {I : Type} [Fintype I] [DecidableEq I]
    (A U : ℝ → Matrix I I ℂ) (hAc : Continuous A) (M a b : ℝ)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hd : ∀ u, HasDerivAt U (-(A u * U u)) u)
    (hinit : U a = 1) (hU : ∀ u, ‖U u‖ ≤ 1) (hA : ∀ u, ‖A u‖ ≤ M) :
    ‖U b - 1 + ∫ u in a..b, A u‖ ≤ M^2 * (b-a)^2 / 2 := by
  let F := fun u => U u - 1 + ∫ v in a..u, A v
  let d := fun u => -(A u * (U u - 1))
  have hdF (u : ℝ) : HasDerivAt F (d u) u := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hAc.intervalIntegrable a u)
      hAc.aestronglyMeasurable.stronglyMeasurableAtFilter hAc.continuousAt
    convert ((hd u).sub_const 1).add hi using 1
    dsimp [d]
    noncomm_ring
  have hn (u : ℝ) (hu : u ∈ Ico a b) : ‖d u‖ ≤ M^2 * (u-a) := by
    have hl := ode_lipschitz A U M a u hd hU hA
    rw [hinit, abs_of_nonneg (sub_nonneg.mpr hu.1)] at hl
    calc
      ‖d u‖ = ‖A u * (U u - 1)‖ := norm_neg _
      _ ≤ ‖A u‖ * ‖U u - 1‖ := norm_mul_le _ _
      _ ≤ M * (M * (u-a)) := mul_le_mul (hA u) hl (norm_nonneg _) hM
      _ = M^2 * (u-a) := by ring
  have hB (u : ℝ) : HasDerivAt (fun u => M^2*(u-a)^2/2) (M^2*(u-a)) u := by
    convert ((((hasDerivAt_id u).sub_const a).pow 2).const_mul (M^2)).div_const 2 using 1
    · rfl
    · dsimp; ring
  have hbnd := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := F) (f' := d) (B := fun u => M^2*(u-a)^2/2) (B' := fun u => M^2*(u-a))
    (fun u _ => (hdF u).continuousAt.continuousWithinAt)
    (fun u _ => (hdF u).hasDerivWithinAt) (by simp [F, hinit])
    hB
    hn
  exact hbnd (right_mem_Icc.mpr hab)

/-- Integrating a continuous Hermitian matrix field preserves Hermiticity. -/
theorem integral_hermitian {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (hh : ∀ u, (H u).IsHermitian) (a b : ℝ) :
    (∫ u in a..b, H u).IsHermitian := by
  change star (∫ u in a..b, H u) = ∫ u in a..b, H u
  have he := (starL' ℝ : Matrix I I ℂ ≃L[ℝ] Matrix I I ℂ).toContinuousLinearMap.intervalIntegral_comp_comm (μ := volume)
    (hH.intervalIntegrable a b)
  simpa only [ContinuousLinearEquiv.coe_coe, starL'_apply,
    show (fun u => star (H u)) = H from funext (fun u => (hh u).eq)] using he.symm

/-- Constant-generator Dyson evolution is the usual matrix exponential. -/
theorem constant_evolution {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (a b : ℝ) :
    orderedEvolution (fun _ => A) a b = NormedSpace.exp ((b-a) • (-A)) := by
  let F := fun u : ℝ => NormedSpace.exp ((u-a) • (-A))
  have hd (u : ℝ) : HasDerivAt F (-(A * F u)) u := by
    convert (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) (u-a)).scomp u
      ((hasDerivAt_id u).sub_const a) using 1
    · funext x; rfl
    · simp [F, neg_mul]
  have he := ordered_matrix_ode_unique (fun _ => A) continuous_const F
    (orderedEvolution (fun _ => A) a) a (by simp [F]) hd
    (orderedEvolution_hasDerivAt (fun _ => A) continuous_const a)
  exact (congrFun he b).symm

/-- Averaging a continuous Hermitian Hamiltonian gives a quadratic time-bin error. -/
theorem average_hamiltonian_error_bound {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (hh : ∀ u, (H u).IsHermitian)
    (a δ M : ℝ) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hb : ∀ u, ‖H u‖ ≤ M) :
    ‖orderedEvolution (fun u => Complex.I • H u) a (a+δ) -
      NormedSpace.exp ((-Complex.I) • (∫ u in a..a+δ, H u))‖ ≤ M^2*δ^2 := by
  rcases eq_or_lt_of_le hδ with hδ0 | hδpos
  · subst δ
    simp
  let K := (δ⁻¹ : ℝ) • ∫ u in a..a+δ, H u
  have hK : K.IsHermitian := (integral_hermitian H hH hh a (a+δ)).smul
    (IsSelfAdjoint.all (δ⁻¹ : ℝ))
  have hnK : ‖K‖ ≤ M := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a+δ)
      (fun u _ => hb u)
    dsimp [K]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδpos]
    have ht : |a+δ-a| = δ := by rw [add_sub_cancel_left, abs_of_pos hδpos]
    rw [ht] at hi
    calc
      δ⁻¹ * ‖∫ u in a..a+δ, H u‖ ≤ δ⁻¹ * (M*δ) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hδ)
      _ = M := by field_simp
  have hδK : δ • K = ∫ u in a..a+δ, H u := by
    dsimp [K]
    rw [smul_smul, mul_inv_cancel₀ hδpos.ne', one_smul]
  let A := fun u => Complex.I • H u
  let B := Complex.I • K
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hAn (u : ℝ) : ‖A u‖ ≤ M := by simpa [A, norm_smul] using hb u
  have hBn : ‖B‖ ≤ M := by simpa [B, norm_smul] using hnK
  have hU := ode_remainder A (orderedEvolution A a) hAc M a (a+δ) (by linarith) hM
    (orderedEvolution_hasDerivAt A hAc a) (orderedEvolution_self A a)
    (fun u => l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I H hH hh a u)) hAn
  have hV := ode_remainder (fun _ => B) (orderedEvolution (fun _ => B) a) continuous_const M a (a+δ)
    (by linarith) hM (orderedEvolution_hasDerivAt (fun _ => B) continuous_const a)
    (orderedEvolution_self (fun _ => B) a)
    (fun u => l2_norm_unitary_le_one (ordered_evolution_hermitian_unitary I (fun _ => K)
      continuous_const (fun _ => hK) a u)) (fun _ => hBn)
  have heint : (∫ u in a..a+δ, A u) = ∫ u in a..a+δ, B := by
    dsimp [A, B]
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_const, add_sub_cancel_left]
    rw [smul_comm δ Complex.I, hδK]
  have heexp : orderedEvolution (fun _ => B) a (a+δ) =
      NormedSpace.exp ((-Complex.I) • (∫ u in a..a+δ, H u)) := by
    rw [constant_evolution, add_sub_cancel_left]
    congr 1
    dsimp [B]
    rw [smul_neg, smul_comm δ Complex.I, hδK, neg_smul]
  have he : orderedEvolution A a (a+δ) - orderedEvolution (fun _ => B) a (a+δ) =
      (orderedEvolution A a (a+δ) - 1 + ∫ u in a..a+δ, A u) -
      (orderedEvolution (fun _ => B) a (a+δ) - 1 + ∫ u in a..a+δ, B) := by rw [heint]; abel
  rw [← heexp]
  change ‖orderedEvolution A a (a+δ) - orderedEvolution (fun _ => B) a (a+δ)‖ ≤ _
  rw [he]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ M^2*(a+δ-a)^2/2 + M^2*(a+δ-a)^2/2 := add_le_add hU hV
    _ = M^2*δ^2 := by ring

/-- The literal source Eq. (4) follows from the quadratic estimate on sufficiently small bins. -/
theorem source_average_bound {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (hh : ∀ u, (H u).IsHermitian)
    (a δ M : ℝ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 2) (hM : 0 ≤ M) (hb : ∀ u, ‖H u‖ ≤ M) :
    ‖orderedEvolution (fun u => Complex.I • H u) a (a+δ) -
      NormedSpace.exp ((-Complex.I) • (∫ u in a..a+δ, H u))‖ ≤ 2*M^2*δ := by
  have hδsq : δ^2 ≤ 2*δ := by nlinarith
  calc
    _ ≤ M^2*δ^2 := average_hamiltonian_error_bound H hH hh a δ M hδ hM hb
    _ ≤ M^2*(2*δ) := mul_le_mul_of_nonneg_left hδsq (sq_nonneg M)
    _ = 2*M^2*δ := by ring

/-- Two contractive Lipschitz paths give the paired integrand in the smoothing argument. -/
theorem paired_norm {I : Type} [Fintype I] [DecidableEq I]
    (H U V : ℝ → Matrix I I ℂ) (M s t : ℝ) (hM : 0 ≤ M)
    (hH : ‖H s‖ ≤ M) (hUt : ‖U t‖ ≤ 1)
    (hVs : ‖V s‖ ≤ 1)
    (hUl : ‖U s - U t‖ ≤ M*|s-t|) (hVl : ‖V s - V t‖ ≤ M*|s-t|) :
    ‖star (U s)*H s*V s - star (U t)*H s*V t‖ ≤ 2*M^2*|s-t| := by
  have he : star (U s)*H s*V s - star (U t)*H s*V t =
      (star (U s)-star (U t))*H s*V s + star (U t)*H s*(V s-V t) := by noncomm_ring
  have hst : ‖star (U s)-star (U t)‖ ≤ M*|s-t| := by
    rw [← star_sub, norm_star]
    exact hUl
  rw [he]
  calc
    _ ≤ ‖(star (U s)-star (U t))*H s*V s‖ + ‖star (U t)*H s*(V s-V t)‖ := norm_add_le _ _
    _ ≤ (‖star (U s)-star (U t)‖*‖H s‖)*‖V s‖ +
        (‖star (U t)‖*‖H s‖)*‖V s-V t‖ := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (M * |s-t| * M)*1 + (1*M)*(M * |s-t|) := by
      rw [norm_star]
      gcongr
    _ = 2*M^2*|s-t| := by ring

/-- The finite Duhamel identity uses the genuine Hamiltonian propagators. -/
theorem duhamel_finite {I : Type} [Fintype I] [DecidableEq I]
    (H K : ℝ → Matrix I I ℂ) (hH : Continuous H) (hK : Continuous K)
    (hh : ∀ u, (H u).IsHermitian) (base a b : ℝ) :
    (1 - star (orderedEvolution (fun u => Complex.I • H u) base b) *
      orderedEvolution (fun u => Complex.I • K u) base b) -
    (1 - star (orderedEvolution (fun u => Complex.I • H u) base a) *
      orderedEvolution (fun u => Complex.I • K u) base a) =
    (-Complex.I) • ∫ u in a..b,
      star (orderedEvolution (fun u => Complex.I • H u) base u) * (H u-K u) *
      orderedEvolution (fun u => Complex.I • K u) base u := by
  let A := fun u => Complex.I • H u
  let B := fun u => Complex.I • K u
  let U := orderedEvolution A base
  let V := orderedEvolution B base
  let X := fun u => 1 - star (U u)*V u
  let D := fun u => star (U u)*(H u-K u)*V u
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun u =>
    (orderedEvolution_hasDerivAt A hAc base u).continuousAt
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun u =>
    (orderedEvolution_hasDerivAt B hBc base u).continuousAt
  have hd (u : ℝ) : HasDerivAt X ((-Complex.I) • D u) u := by
    have hu := orderedEvolution_hasDerivAt A hAc base u
    have hv := orderedEvolution_hasDerivAt B hBc base u
    convert (hu.star.mul hv).const_sub 1 using 1
    dsimp [D, A, B]
    rw [star_neg, star_mul, star_smul, show star (H u) = H u from (hh u).eq]
    have hstarI : star Complex.I = -Complex.I := by simp [RCLike.star_def]
    simp only [hstarI, neg_smul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm,
      Matrix.mul_sub, Matrix.sub_mul, smul_sub, mul_assoc]
    abel
  have hDc : Continuous D := by dsimp [D]; fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((hDc.const_smul (-Complex.I)).intervalIntegrable a b)
  rw [intervalIntegral.integral_smul] at he
  exact he.symm

end Qatlib.Papers.TimeDepSim11.MainResults.AverageHamiltonianBound
