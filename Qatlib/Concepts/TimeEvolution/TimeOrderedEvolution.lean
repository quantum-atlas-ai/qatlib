/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Time-ordered matrix evolution from Dyson series

The iterated integrals `orderedDysonTerm` define `orderedEvolution` for the equation `U' = -A *
U`. For continuous matrix generators the module proves convergence, the initial condition,
uniqueness, composition, invertibility, and differentiation in either endpoint. Positive
Hermitian parts give forward contraction, while imaginary multiples of Hermitian generators give
unitary evolution. For background, see [BerryEtAl2020Dyson].

## Main statements

* `ordered_evolution_dyson_semantics`: convergence and ODE semantics of the Dyson construction.
* `orderedEvolution_cocycle`: composition of propagators.
* `ordered_evolution_hermitian_unitary`: unitarity for Hermitian Hamiltonians.

## References

* [Berry et al., 2020][BerryEtAl2020Dyson]
-/

set_option warningAsError false


open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Matrix Set
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The recursively integrated Dyson terms for `U' = -A * U`, with zeroth term the identity and
integration starting at `s`. -/
noncomputable def orderedDysonTerm {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s : ℝ) : ℕ → ℝ → Matrix I I ℂ
  | 0, _ => 1
  | n+1, t => ∫ u in s..t, -(A u * orderedDysonTerm A s n u)

/-- The infinite sum of the ordered Dyson terms from the initial time `s` to the final time `t`. -/
noncomputable def orderedEvolution {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s t : ℝ) : Matrix I I ℂ :=
  ∑' n : ℕ, orderedDysonTerm A s n t

/-- Each ordered Dyson term is continuous in its final time when the matrix generator is
continuous. -/
theorem orderedDysonTerm_continuous {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s : ℝ) (n : ℕ) :
    Continuous (orderedDysonTerm A s n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (intervalIntegral.differentiable_integral_of_continuous
      (hA.mul ih).neg).continuous

/-- The derivative of the successor Dyson term is `-(A t * orderedDysonTerm A s n t)`. -/
theorem orderedDysonTerm_hasDerivAt_succ {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (orderedDysonTerm A s (n+1))
      (-(A t * orderedDysonTerm A s n t)) t := by
  have hc := (hA.mul (orderedDysonTerm_continuous A hA s n)).neg
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Every positive-degree Dyson term vanishes when the final time equals the initial time. -/
@[simp] theorem orderedDysonTerm_succ_self {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s : ℝ) (n : ℕ) : orderedDysonTerm A s (n+1) s = 0 := by
  simp [orderedDysonTerm]

/-- The ordered evolution from a time to itself is the identity. -/
@[simp] theorem orderedEvolution_self {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s : ℝ) : orderedEvolution A s s = 1 := by
  unfold orderedEvolution
  rw [tsum_eq_single 0]
  · rfl
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact orderedDysonTerm_succ_self A s k

/-- If the generator norm is bounded by `M` between the endpoints, the `n`th Dyson term has norm
at most `(M * |t - s|) ^ n / n!`. -/
theorem orderedDysonTerm_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ u ∈ uIcc s t, ‖A u‖ ≤ M) (n : ℕ) :
    ‖orderedDysonTerm A s n t‖ ≤ (M * |t-s|)^n / (n.factorial : ℝ) := by
  induction n generalizing t with
  | zero => simpa [orderedDysonTerm] using! (l2_norm_one_le (I := I))
  | succ n ih =>
    let g : ℝ → ℝ := fun u => M^(n+1) / (n.factorial : ℝ) * |u-s|^n
    have hg : Continuous g := by fun_prop
    have hb : ∀ u ∈ uIoc s t, ‖-(A u * orderedDysonTerm A s n u)‖ ≤ g u := by
      intro u hu
      have hu' : u ∈ uIcc s t := uIoc_subset_uIcc hu
      have hn := ih u (fun x hx => hbound x (uIcc_subset_uIcc_left hu' hx))
      calc
        _ ≤ ‖A u‖ * ‖orderedDysonTerm A s n u‖ := by
          rw [norm_neg]; exact norm_mul_le _ _
        _ ≤ M * ((M * |u-s|)^n / (n.factorial : ℝ)) :=
          mul_le_mul (hbound u hu') hn (norm_nonneg _) hM
        _ = g u := by dsimp [g]; rw [mul_pow, pow_succ]; ring
    calc
      _ ≤ ∫ u in uIoc s t, ‖-(A u * orderedDysonTerm A s n u)‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ u in uIoc s t, g u := by
        apply MeasureTheory.integral_mono_ae
        · exact ((hA.mul (orderedDysonTerm_continuous A hA s n)).neg.norm.intervalIntegrable s t).def'
        · exact (hg.intervalIntegrable s t).def'
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc hb
      _ = (M * |t-s|)^(n+1) / ((n+1).factorial : ℝ) := by
        rw [show g = fun u => M^(n+1) / (n.factorial : ℝ) * |u-s|^n from rfl,
          MeasureTheory.integral_const_mul, integral_pow_abs_sub_uIoc]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
        field_simp

/-- A continuous finite-dimensional matrix generator has a summable Dyson series between any two
real times. -/
theorem orderedDysonTerm_summable {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) :
    Summable (fun n => orderedDysonTerm A s n t) := by
  obtain ⟨C, hC⟩ := (isCompact_uIcc.image hA).isBounded.exists_norm_le
  let M := max 0 C
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial (M * |t-s|))
  intro n
  exact orderedDysonTerm_norm_le A hA s t M (le_max_left _ _)
    (fun u hu => (hC (A u) ⟨u, hu, rfl⟩).trans (le_max_right _ _)) n

/-- For a continuous generator, the ordered evolution has final-time derivative `-(A t *
orderedEvolution A s t)`. -/
theorem orderedEvolution_hasDerivAt {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) :
    HasDerivAt (orderedEvolution A s) (-(A t * orderedEvolution A s t)) t := by
  let R : ℝ := |t-s| + 1
  let a := s-R
  let b := s+R
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := a) (b := b)).image hA).isBounded.exists_norm_le
  let M := max 0 C
  have hM : 0 ≤ M := le_max_left _ _
  have hbound : ∀ u ∈ Icc a b, ‖A u‖ ≤ M := by
    intro u hu
    exact (hC (A u) ⟨u, hu, rfl⟩).trans (le_max_right _ _)
  have hs : s ∈ Ioo a b := by dsimp [a, b]; constructor <;> linarith
  have ht : t ∈ Ioo a b := by
    dsimp [a, b, R]
    constructor <;> linarith [le_abs_self (t-s), neg_le_abs (t-s)]
  have hn (n : ℕ) (u : ℝ) (hu : u ∈ Ioo a b) :
      ‖orderedDysonTerm A s n u‖ ≤ (M*R)^n / (n.factorial : ℝ) := by
    have hsub : uIcc s u ⊆ Icc a b :=
      (convex_Icc a b).ordConnected.uIcc_subset ⟨hs.1.le, hs.2.le⟩ ⟨hu.1.le, hu.2.le⟩
    have hb := orderedDysonTerm_norm_le A hA s u M hM
      (fun x hx => hbound x (hsub hx)) n
    have huR : |u-s| ≤ R := by
      rw [abs_le]
      dsimp [a, b] at hu
      constructor <;> linarith [hu.1, hu.2]
    exact hb.trans (by gcongr)
  have hd := hasDerivAt_tsum_of_isPreconnected
    ((Real.summable_pow_div_factorial (M*R)).mul_left M)
    isOpen_Ioo isPreconnected_Ioo
    (fun n u (_ : u ∈ Ioo a b) => orderedDysonTerm_hasDerivAt_succ A hA s n u)
    (fun n u hu => (by
      rw [norm_neg]
      exact (norm_mul_le _ _).trans
        (mul_le_mul (hbound u ⟨hu.1.le, hu.2.le⟩) (hn n u hu) (norm_nonneg _) hM)))
    hs (by simp) ht
  have he : (fun u => 1 + ∑' n, orderedDysonTerm A s (n+1) u) = orderedEvolution A s := by
    funext u
    exact ((orderedDysonTerm_summable A hA s u).tsum_eq_zero_add).symm
  have hsum : (∑' n, -(A t * orderedDysonTerm A s n t)) =
      -(A t * orderedEvolution A s t) := by
    simp_rw [← neg_mul]
    exact (orderedDysonTerm_summable A hA s t).tsum_mul_left (-A t)
  rw [hsum] at hd
  simpa only [he] using! hd.const_add 1

/-- Two solutions of `U' = -A * U` for a continuous generator agree everywhere if they agree at
one time. -/
theorem ordered_matrix_ode_unique {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (f g : ℝ → Matrix I I ℂ) (s : ℝ) (hinit : f s = g s)
    (hf : ∀ t, HasDerivAt f (-(A t * f t)) t)
    (hg : ∀ t, HasDerivAt g (-(A t * g t)) t) : f = g := by
  funext t
  let a := min s t - 1
  let b := max s t + 1
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := a) (b := b)).image hA).isBounded.exists_norm_le
  let K : NNReal := ⟨max 0 C, le_max_left _ _⟩
  have hbound (u : ℝ) (hu : u ∈ Ioo a b) : ‖A u‖ ≤ (K : ℝ) :=
    (hC (A u) ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩).trans (le_max_right _ _)
  have hlip (u : ℝ) (hu : u ∈ Ioo a b) :
      LipschitzOnWith K (fun x : Matrix I I ℂ => -(A u*x)) Set.univ := by
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm,
      show -(A u*x) - -(A u*y) = -(A u*(x-y)) from by noncomm_ring, norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound u hu) (norm_nonneg _))
  have hs : s ∈ Ioo a b := by
    dsimp [a, b]
    constructor <;> linarith [min_le_left s t, le_max_left s t]
  have ht : t ∈ Icc a b := by
    dsimp [a, b]
    constructor <;> linarith [min_le_right s t, le_max_right s t]
  exact ODE_solution_unique_of_mem_Icc (s := fun _ => Set.univ) hlip hs
    (continuous_iff_continuousAt.mpr (fun u => (hf u).continuousAt)).continuousOn
    (fun u _ => hf u) (fun _ _ => Set.mem_univ _)
    (continuous_iff_continuousAt.mpr (fun u => (hg u).continuousAt)).continuousOn
    (fun u _ => hg u) (fun _ _ => Set.mem_univ _) hinit ht

/-- Composing evolution from `s` to `r` with evolution from `r` to `t` gives evolution from `s`
to `t`. -/
theorem orderedEvolution_cocycle {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s r t : ℝ) :
    orderedEvolution A r t * orderedEvolution A s r = orderedEvolution A s t := by
  have he := ordered_matrix_ode_unique A hA
    (fun u => orderedEvolution A r u * orderedEvolution A s r)
    (orderedEvolution A s) r (by simp)
    (fun u => (by
      convert! (orderedEvolution_hasDerivAt A hA r u).mul_const (orderedEvolution A s r) using 1
      noncomm_ring))
    (orderedEvolution_hasDerivAt A hA s)
  exact congrFun he t

/-- For a continuous generator, bundles Dyson summability, the identity initial value, the
evolution equation, composition, and uniqueness of the normalized propagator
[BerryEtAl2020Dyson]. -/
theorem ordered_evolution_dyson_semantics :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : ℝ → Matrix I I ℂ),
      Continuous A →
      (∀ s t : ℝ, Summable (fun n => orderedDysonTerm A s n t)) ∧
      (∀ s : ℝ, orderedEvolution A s s = 1) ∧
      (∀ s t : ℝ, HasDerivAt (orderedEvolution A s)
        (-(A t * orderedEvolution A s t)) t) ∧
      (∀ s r t : ℝ, orderedEvolution A r t * orderedEvolution A s r = orderedEvolution A s t) ∧
      (∀ (s : ℝ) (V : ℝ → Matrix I I ℂ), V s = 1 →
        (∀ t, HasDerivAt V (-(A t * V t)) t) → V = orderedEvolution A s) := by
  intro I _ _ A hA
  refine ⟨orderedDysonTerm_summable A hA, orderedEvolution_self A,
    orderedEvolution_hasDerivAt A hA, orderedEvolution_cocycle A hA, ?_⟩
  intro s V hV hder
  exact ordered_matrix_ode_unique A hA V (orderedEvolution A s) s
    (by simpa using! hV) hder (orderedEvolution_hasDerivAt A hA s)

/-- The continuous complex linear map sending a matrix to its action on a fixed vector,
expressed in Euclidean space. -/
private noncomputable def orderedActionCLM {I : Type} [Fintype I] [DecidableEq I]
    (v : QState I) : Matrix I I ℂ →L[ℂ] EuclideanSpace ℂ I := by
  let e : EuclideanSpace ℂ I ≃L[ℂ] (I → ℂ) := PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)
  let m : Matrix I I ℂ →ₗ[ℂ] (I → ℂ) := (Matrix.mulVecBilin ℂ ℂ).flip v
  refine (e.symm.toLinearMap.comp m).mkContinuous ‖toEuclidean_fromVec v‖ ?_
  intro X
  exact (Matrix.l2_opNorm_mulVec X (toEuclidean_fromVec v)).trans_eq (mul_comm _ _)

/-- The propagated vector has derivative equal to minus the generator applied to that vector, in
Euclidean coordinates. -/
private theorem ordered_action_deriv {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) (v : QState I) :
    HasDerivAt (fun u => toEuclidean_fromVec (orderedEvolution A s u *ᵥ v))
      (-toEuclidean_fromVec (A t *ᵥ (orderedEvolution A s t *ᵥ v))) t := by
  have hd := ((orderedActionCLM v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (orderedEvolution_hasDerivAt A hA s t)
  simpa [orderedActionCLM, toEuclidean_fromVec, Matrix.neg_mulVec, Matrix.mulVec_mulVec] using! hd

/-- If `A + Aᴴ` is positive semidefinite, the real part of the quadratic form of `A` is
nonnegative. -/
private theorem ordered_quadratic_re_nonneg {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : (A + Aᴴ).PosSemidef) (v : QState I) :
    0 ≤ (Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)).re := by
  have h := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1
  have he : star v ⬝ᵥ (Aᴴ *ᵥ v) = star (star v ⬝ᵥ (A *ᵥ v)) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star, Matrix.star_dotProduct]
  rw [Matrix.add_mulVec, dotProduct_add, he] at h
  have hp : 0 ≤ 2 * (Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)).re := by
    simpa [Qatlib.Foundations.PureStateMath.Inner, two_mul] using! h
  linarith

/-- A continuous generator with pointwise positive semidefinite Hermitian part yields evolution
of norm at most one for increasing time. -/
theorem ordered_evolution_psd_contraction :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : ℝ → Matrix I I ℂ),
      Continuous A → (∀ u, (A u + (A u)ᴴ).PosSemidef) →
      ∀ s t : ℝ, s ≤ t → ‖orderedEvolution A s t‖ ≤ 1 := by
  intro I _ _ A hA hPSD s t hst
  letI := InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ I)
  have hv (v : QState I) :
      ‖toEuclidean_fromVec (orderedEvolution A s t *ᵥ v)‖ ≤ ‖toEuclidean_fromVec v‖ := by
    let f := fun u => toEuclidean_fromVec (orderedEvolution A s u *ᵥ v)
    have hd (u : ℝ) := (ordered_action_deriv A hA s u v).norm_sq
    have hnonpos (u : ℝ) :
        2 * inner ℝ (f u) (-toEuclidean_fromVec (A u *ᵥ (orderedEvolution A s u *ᵥ v))) ≤ 0 := by
      dsimp [f]
      rw [inner_neg_right, real_inner_eq_re_inner (𝕜 := ℂ), inner_euclidean_fromVec]
      have hp := ordered_quadratic_re_nonneg (A u) (hPSD u) (orderedEvolution A s u *ᵥ v)
      dsimp [f]
      nlinarith
    have hm : Antitone (fun u => ‖f u‖^2) :=
      antitone_of_deriv_nonpos (fun u => (hd u).differentiableAt)
        (fun u => by rw [(hd u).deriv]; exact hnonpos u)
    have hsq := hm hst
    have hi : f s = toEuclidean_fromVec v := by simp [f]
    (try dsimp only at hsq)
    rw [hi] at hsq
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (orderedEvolution A s t)‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa [toEuclideanCLM_applyGate, ApplyGate, one_mul] using! hv (toVec_fromEuclidean x)

/-- For a continuous Hermitian Hamiltonian `H`, the ordered evolution generated by `I • H` is
unitary between any two times [BerryEtAl2020Dyson]. -/
theorem ordered_evolution_hermitian_unitary :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H : ℝ → Matrix I I ℂ),
      Continuous H → (∀ u, (H u).IsHermitian) →
      ∀ s t : ℝ, orderedEvolution (fun u => Complex.I • H u) s t ∈ unitaryGroup I ℂ := by
  intro I _ _ H hH hHerm s t
  let A := fun u => Complex.I • H u
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hskew (u : ℝ) : star (A u) = -A u := by
    dsimp [A]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, (hHerm u).eq]
    simp [RCLike.star_def]
  let E := orderedEvolution A s
  have hd (u : ℝ) : HasDerivAt (fun v => star (E v) * E v) 0 u := by
    have hf := orderedEvolution_hasDerivAt A hA s u
    convert! hf.star.mul hf using 1
    simp only [star_neg, star_mul, hskew, mul_neg, neg_neg]
    noncomm_ring
  have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t s
  have hunit : star (E t) * E t = 1 := by simpa [E] using! he
  exact Matrix.mem_unitaryGroup_iff'.mpr hunit

/-- The ordered evolution packaged as a matrix unit, with inverse given by reversing the
endpoints. -/
noncomputable def orderedEvolutionUnit {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) : (Matrix I I ℂ)ˣ where
  val := orderedEvolution A s t
  inv := orderedEvolution A t s
  val_inv := by simpa using! orderedEvolution_cocycle A hA t s t
  inv_val := by simpa using! orderedEvolution_cocycle A hA s t s

/-- The ring inverse of an ordered evolution is the ordered evolution with its endpoints
reversed. -/
theorem orderedEvolution_ringInverse {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) :
    Ring.inverse (orderedEvolution A s t) = orderedEvolution A t s :=
  Ring.inverse_unit (orderedEvolutionUnit A hA s t)

/-- Differentiating the initial endpoint of `orderedEvolution A t s` gives `orderedEvolution A t
s * A t`. -/
theorem orderedEvolution_hasDerivAt_start {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) :
    HasDerivAt (fun u => orderedEvolution A u s) (orderedEvolution A t s * A t) t := by
  have hd := (hasFDerivAt_ringInverse (𝕜 := ℝ) (orderedEvolutionUnit A hA s t)).comp_hasDerivAt t
    (orderedEvolution_hasDerivAt A hA s t)
  have he : (fun u => Ring.inverse (orderedEvolution A s u)) =
      (fun u => orderedEvolution A u s) := funext (orderedEvolution_ringInverse A hA s)
  dsimp only [Function.comp_def] at hd
  rw [he] at hd
  convert! hd using 1
  change orderedEvolution A t s * A t =
    -(orderedEvolution A t s * -(A t * orderedEvolution A s t) * orderedEvolution A t s)
  have hi := (orderedEvolutionUnit A hA s t).val_inv
  change orderedEvolution A s t * orderedEvolution A t s = 1 at hi
  simp only [mul_neg, neg_mul, neg_neg]
  simp only [mul_assoc, hi, mul_one]

end Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
