/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawPath

/-!
# Smooth finite approximations of ground energies

`softMin` is a logarithmic approximation to the minimum of a nonempty finite family, with error
bounded by its entropy divided by the positive parameter. Applied to normalized tensor energies,
`softEnergy` is smooth and `1/√N` Lipschitz, giving an integrated gradient estimate and a
uniform Gaussian rotation tail. These approximations support the ground energy path analysis
associated with [GohMuller2026].

## Main statements

* `min_sub_entropy_le_softMin`: For `β > 0`, the soft minimum is at least the finite minimum
  minus `log |I| / β`.
* `softEnergy_lipschitz`: For `N > 0` and `β > 0`, the soft energy of cube vectors is Lipschitz
  with constant `1/√N`.
* `softEnergy_rotation_tail`: For `N > 0`, `β > 0`, and `ε > 0`, the probability that the soft
  energy of cube vectors changes by at least `ε` anywhere along the Gaussian rotation arc is at
  most `π²/(4Nε²)`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal BigOperators
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.SoftGround
section FiniteSoftMin
variable {I : Type} [Fintype I] [Nonempty I]

/-- The logarithmic soft minimum `-log(∑ i, exp(-β * u i)) / β` of a nonempty finite family. -/
def softMin (β : ℝ) (u : I→ℝ) : ℝ := -(Real.log (∑ i,Real.exp (-β*u i)))/β

/-- The partition sum of a nonempty finite family of real exponential weights is strictly
positive. -/
theorem partition_pos (β : ℝ) (u : I→ℝ) : 0<∑ i,Real.exp (-β*u i) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- For `β > 0`, if `v i - u i ≤ δ` for every index, then the log partition sum for `u` exceeds
that for `v` by at most `βδ`. -/
theorem log_partition_difference (β : ℝ) (hβ : 0<β) (u v : I→ℝ) (δ : ℝ)
    (huv : ∀ i,v i-u i≤δ) :
    Real.log (∑ i,Real.exp (-β*u i))-Real.log (∑ i,Real.exp (-β*v i))≤β*δ := by
  have hb : (∑ i,Real.exp (-β*u i))≤Real.exp (β*δ)*(∑ i,Real.exp (-β*v i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [huv i]
  have hl := Real.log_le_log (partition_pos β u) hb
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (partition_pos β v)),Real.log_exp] at hl
  linarith

/-- For `β > 0`, coordinatewise differences bounded in absolute value by `δ` imply that the two
soft minima differ by at most `δ`. -/
theorem softMin_difference (β : ℝ) (hβ : 0<β) (u v : I→ℝ) (δ : ℝ)
    (huv : ∀ i,|u i-v i|≤δ) : |softMin β u-softMin β v|≤δ := by
  have hp := log_partition_difference β hβ u v δ (fun i => by linarith [neg_le_abs (u i-v i),huv i])
  have hn := log_partition_difference β hβ v u δ (fun i => (le_abs_self (u i-v i)).trans (huv i))
  have he : softMin β u-softMin β v=
      (Real.log (∑ i,Real.exp (-β*v i))-Real.log (∑ i,Real.exp (-β*u i)))/β := by unfold softMin; ring
  rw [he]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hβ).mpr
    nlinarith
  · apply (div_le_iff₀ hβ).mpr
    nlinarith

/-- The soft minimum of a nonempty finite family of infinitely differentiable real functions is
infinitely differentiable. -/
theorem contDiff_softMin {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (β : ℝ) (u : I→E→ℝ) (hu : ∀ i,ContDiff ℝ (↑(⊤ : ℕ∞)) (u i)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => softMin β (fun i => u i x)) := by
  have hs : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∑ i,Real.exp (-β*u i x)) := by fun_prop
  exact (hs.log (fun x => ne_of_gt (partition_pos β (fun i => u i x)))).neg.div_const β

/-- The minimum of a nonempty finite family of real numbers. -/
def finiteMin (u : I→ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty u

/-- For `β > 0`, the soft minimum is at most the minimum of the finite family. -/
theorem softMin_le_min (β : ℝ) (hβ : 0<β) (u : I→ℝ) : softMin β u≤finiteMin u := by
  obtain ⟨i,_hi,he⟩ := Finset.exists_mem_eq_inf' (s:=Finset.univ) Finset.univ_nonempty u
  have hb : Real.exp (-β*u i)≤∑ j,Real.exp (-β*u j) :=
    Finset.single_le_sum (f:=fun j => Real.exp (-β*u j)) (fun j _ => (Real.exp_pos (-β*u j)).le) (Finset.mem_univ i)
  have hl := Real.log_le_log (Real.exp_pos _) hb
  rw [Real.log_exp] at hl
  unfold softMin finiteMin
  rw [he]
  apply (div_le_iff₀ hβ).mpr
  nlinarith

/-- For `β > 0`, the soft minimum is at least the finite minimum minus `log |I| / β`. -/
theorem min_sub_entropy_le_softMin (β : ℝ) (hβ : 0<β) (u : I→ℝ) :
    finiteMin u-Real.log (Fintype.card I:ℝ)/β≤ softMin β u := by
  have hcard : (0:ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hb : (∑ i,Real.exp (-β*u i))≤(Fintype.card I:ℝ)*Real.exp (-β*finiteMin u) := by
    calc
      _ ≤ ∑ _i : I,Real.exp (-β*finiteMin u) := by
        apply Finset.sum_le_sum
        intro i _
        apply Real.exp_le_exp.mpr
        have h := Finset.inf'_le (s:=Finset.univ) u (Finset.mem_univ i)
        change finiteMin u≤u i at h
        nlinarith
      _ = _ := by simp
  have hl := Real.log_le_log (partition_pos β u) hb
  rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _),Real.log_exp] at hl
  unfold softMin
  apply (le_div_iff₀ hβ).mpr
  rw [sub_mul,div_mul_cancel₀ _ hβ.ne']
  nlinarith

end FiniteSoftMin

section ActualFiniteGround
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm

/-- The energy density of a fixed spin vector in the scaled tensor extracted from the Gaussian
input. -/
def stateEnergy {r N : ℕ} (u : Fin N→ℝ) (x : Input r N) : ℝ :=
  tensorEnergy (sourceTensor (tensorCoords x).ofLp) u/(N:ℝ)

/-- The energy density of a fixed spin vector is infinitely differentiable in the Gaussian
input. -/
theorem contDiff_stateEnergy {r N : ℕ} (u : Fin N→ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (stateEnergy (r:=r) u) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Input r N =>
    (∑ k : Fin (r+1)→Fin N,Real.sqrt (((N:ℝ)^r)⁻¹)*x (Sum.inl k)*(∏ a,u (k a)))/(N:ℝ))
  fun_prop

/-- For `N > 0` and a spin vector with coordinates of absolute value at most one, the change in
its energy density is at most the Gaussian input distance divided by `√N`. -/
theorem stateEnergy_difference {r N : ℕ} (hN : 0<N) (u : Fin N→ℝ) (hu : ∀ i,|u i|≤1) (x y : Input r N) :
    |stateEnergy u x-stateEnergy u y|≤‖x-y‖/Real.sqrt (N:ℝ) := by
  have h :=
      source_energy_tensor_difference hN (tensorCoords x) (tensorCoords y) (WithLp.toLp 2 u) hu
  have he := input_split_sq x y
  have hg : ‖tensorCoords x-tensorCoords y‖≤‖x-y‖ := by
    nlinarith [norm_nonneg (tensorCoords x-tensorCoords y),norm_nonneg (x-y),
      sq_nonneg ‖(WithLp.toLp 2 (seedCoords x) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (seedCoords y)‖]
  exact h.trans (div_le_div_of_nonneg_right hg (Real.sqrt_nonneg _))

variable {I : Type} [Fintype I] [Nonempty I]

/-- The soft minimum of the energy densities of a nonempty finite family of spin vectors. -/
def softEnergy {r N : ℕ} (β : ℝ) (u : I→Fin N→ℝ) (x : Input r N) : ℝ :=
  softMin β (fun i => stateEnergy (u i) x)

/-- The soft energy is infinitely differentiable in the Gaussian input for every finite family
of spin vectors. -/
theorem contDiff_softEnergy {r N : ℕ} (β : ℝ) (u : I→Fin N→ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (softEnergy (r:=r) β u) :=
  contDiff_softMin β (fun i x => stateEnergy (u i) x) (fun i => contDiff_stateEnergy (u i))

/-- For `N > 0` and `β > 0`, the soft energy of cube vectors is Lipschitz with constant `1/√N`. -/
theorem softEnergy_lipschitz {r N : ℕ} (hN : 0<N) (β : ℝ) (hβ : 0<β)
    (u : I→Fin N→ℝ) (hu : ∀ i j,|u i j|≤1) :
    LipschitzWith (⟨1/Real.sqrt (N:ℝ),by positivity⟩ : ℝ≥0) (softEnergy (r:=r) β u) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := softMin_difference β hβ (fun i => stateEnergy (u i) x) (fun i => stateEnergy (u i) y)
    (‖x-y‖/Real.sqrt (N:ℝ)) (fun i => stateEnergy_difference hN (u i) (hu i) x y)
  simpa only [Real.dist_eq,dist_eq_norm,softEnergy,div_eq_mul_inv,one_mul,mul_comm] using! h

/-- For `N > 0` and `β > 0`, the squared derivative norm of the soft energy of cube vectors is
Gaussian integrable with integral at most `1/N`. -/
theorem softEnergy_gradient {r N : ℕ} (hN : 0<N) (β : ℝ) (hβ : 0<β)
    (u : I→Fin N→ℝ) (hu : ∀ i j,|u i j|≤1) :
    Integrable (fun x : Input r N => ‖fderiv ℝ (softEnergy β u) x‖^2) (stdGaussian (Input r N)) ∧
      (∫ x : Input r N,‖fderiv ℝ (softEnergy β u) x‖^2 ∂stdGaussian (Input r N))≤1/(N:ℝ) := by
  have hLip := softEnergy_lipschitz (r:=r) hN β hβ u hu
  have hb (x : Input r N) : ‖fderiv ℝ (softEnergy β u) x‖^2≤1/(N:ℝ) := by
    have hd : ‖fderiv ℝ (softEnergy β u) x‖≤1/Real.sqrt (N:ℝ) :=
        norm_fderiv_le_of_lipschitz ℝ (x₀:=x) hLip
    have h := pow_le_pow_left₀ (norm_nonneg _) hd 2
    simpa only [div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg N)] using! h
  have hc : Continuous (fun x : Input r N => ‖fderiv ℝ (softEnergy β u) x‖^2) := by
    have := (contDiff_softEnergy (r:=r) β u).continuous_fderiv (by simp)
    fun_prop
  have hi : Integrable (fun x : Input r N => ‖fderiv ℝ (softEnergy β u) x‖^2) (stdGaussian (Input r N)) := by
    apply (integrable_const (1/(N:ℝ))).mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖fderiv ℝ (softEnergy β u) x‖)] using!
          hb x)
  refine ⟨hi,?_⟩
  simpa using! integral_mono hi (integrable_const (1/(N:ℝ))) hb

/-- For `N > 0`, `β > 0`, and `ε > 0`, the probability that the soft energy of cube vectors
changes by at least `ε` anywhere along the Gaussian rotation arc is at most `π²/(4Nε²)`. -/
theorem softEnergy_rotation_tail {r N : ℕ} (hN : 0<N) (β : ℝ) (hβ : 0<β)
    (u : I→Fin N→ℝ) (hu : ∀ i j,|u i j|≤1) (ε : ℝ) (hε : 0<ε) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real
      {z | ∃ θ∈Set.Icc (0:ℝ) (Real.pi/2),ε≤|softEnergy β u (ContinuousLinearMap.rotation θ z).1-softEnergy β u z.1|}≤
      Real.pi^2/(4*(N:ℝ)*ε^2) := by
  obtain ⟨hi,hb⟩ := softEnergy_gradient (r:=r) hN β hβ u hu
  refine (Qatlib.Foundations.ProbabilityCore.GaussPoincare.UniformRotation.continuum_rotation_tail
    (softEnergy β u) ((contDiff_softEnergy β u).of_le (by simp)) hi ε hε).trans ?_
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ)≤Real.pi^2/4))
    (sq_nonneg ε)).trans_eq (by ring)

end ActualFiniteGround
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.SoftGround
