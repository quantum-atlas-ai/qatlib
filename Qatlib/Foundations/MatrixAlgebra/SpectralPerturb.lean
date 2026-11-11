/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Residual bounds for isolated eigenvectors

The module expands an eigenvector residual in a prescribed orthonormal eigenbasis and bounds the
coordinate mass outside a chosen eigenvector. A positive spectral separation and a nearby real
approximate eigenvalue convert residual norm into distance from that eigenvector up to a unit
complex phase.

`residual_phase_bound` gives the explicit bound with constant `4 / g`, using the phase-alignment
and spectral estimates developed here. These estimates belong to finite-dimensional spectral
perturbation theory [Bhatia1997].

## Main statements

* `residual_norm_sq`: the squared residual is a weighted sum of squared eigenbasis coordinates.
* `residual_off_mass`: spectral separation controls the mass outside one eigenvector.
* `residual_phase_bound`: a unit vector is close, up to phase, to an isolated eigenvector when
  its residual is small.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.SpectralPerturb.PhaseResidual
open scoped ComplexConjugate InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A unit complex phase equal to the conjugate of `z` divided by its norm when `z` is nonzero,
and equal to one at zero. -/
def phase (z : ℂ) : ℂ := if z = 0 then 1 else star z / (‖z‖ : ℂ)

/-- The chosen phase has complex norm one for every input. -/
theorem phase_norm (z : ℂ) : ‖phase z‖ = 1 := by
  by_cases hz : z=0
  · simp [phase,hz]
  · simp [phase,hz,Complex.norm_real,norm_ne_zero_iff.mpr hz]

/-- Multiplying `z` by its chosen phase gives the nonnegative real norm of `z`, cast to the
complex numbers. -/
theorem phase_mul (z : ℂ) : phase z*z = (‖z‖:ℂ) := by
  by_cases hz : z=0
  · simp [phase,hz]
  · have hm : star z*z = ((‖z‖^2:ℝ):ℂ) := by
      rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    have hn : (‖z‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    rw [phase,if_neg hz,div_mul_eq_mul_div,hm,Complex.ofReal_pow]
    apply (div_eq_iff hn).mpr
    ring

/-- For two unit vectors, there is a unit complex phase whose squared alignment distance is at
most twice one minus the squared modulus of their inner product. -/
theorem exists_phase_distance (v w : E) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    ∃ ζ : ℂ, ‖ζ‖=1 ∧ ‖v-ζ • w‖^2 ≤ 2*(1-‖inner ℂ w v‖^2) := by
  let z := inner ℂ v w
  refine ⟨phase z,phase_norm z,?_⟩
  have hsq : ‖v-phase z • w‖^2=2-2*‖z‖ := by
    rw [norm_sub_sq (𝕜 := ℂ),hv,norm_smul,phase_norm,hw,inner_smul_right]
    change (1:ℝ)^2-2*(phase z*z).re+(1*1)^2=2-2*‖z‖
    rw [phase_mul,Complex.ofReal_re]
    ring
  have hz : ‖z‖≤1 := by
    simpa only [z,hv,hw,mul_one] using (norm_inner_le_norm v w)
  have hn := norm_nonneg z
  have hnorm : ‖inner ℂ w v‖=‖z‖ := by
    dsimp only [z]
    exact norm_inner_symm (𝕜 := ℂ) w v
  rw [hsq,hnorm]
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hz)]

variable {I : Type*} [Fintype I] [DecidableEq I]
omit [DecidableEq I] in

/-- The sum of squared coordinate norms in an orthonormal basis equals the squared norm of the
vector. -/
theorem repr_norm_sum (b : OrthonormalBasis I ℂ E) (v : E) :
    ∑ j, ‖b.repr v j‖^2 = ‖v‖^2 := by
  simpa only [b.repr_apply_apply] using b.sum_sq_norm_inner_right v

/-- In an orthonormal eigenbasis, each coordinate of `H v` is the corresponding real eigenvalue
times the coordinate of `v`. -/
theorem action_repr (b : OrthonormalBasis I ℂ E) (H : E →ₗ[ℂ] E) (vals : I → ℝ)
    (hAction : ∀ j,H (b j)=(vals j:ℂ) • b j) (v : E) (j : I) :
    b.repr (H v) j = (vals j:ℂ)*b.repr v j := by
  have he : H v=∑ k,((vals k:ℂ)*b.repr v k) • b k := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul,hAction,smul_smul,mul_comm]
  rw [he]
  simp [map_sum,map_smul,b.repr_self,Pi.single_apply,smul_eq_mul]

/-- The coordinate of the residual `H v - μ • v` is the coordinate of `v` multiplied by the
corresponding eigenvalue difference. -/
theorem residual_repr (b : OrthonormalBasis I ℂ E) (H : E →ₗ[ℂ] E) (vals : I → ℝ)
    (hAction : ∀ j,H (b j)=(vals j:ℂ) • b j) (v : E) (μ : ℝ) (j : I) :
    b.repr (H v-(μ:ℂ) • v) j = ((vals j-μ:ℝ):ℂ)*b.repr v j := by
  simp only [map_sub,map_smul,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    action_repr b H vals hAction,Complex.ofReal_sub]
  ring

/-- The squared residual norm is the sum of squared eigenvalue differences weighted by squared
eigenbasis coordinate norms. -/
theorem residual_norm_sq (b : OrthonormalBasis I ℂ E) (H : E →ₗ[ℂ] E) (vals : I → ℝ)
    (hAction : ∀ j,H (b j)=(vals j:ℂ) • b j) (v : E) (μ : ℝ) :
    ‖H v-(μ:ℂ) • v‖^2=∑ j,(vals j-μ)^2*‖b.repr v j‖^2 := by
  rw [← repr_norm_sum b]
  apply Finset.sum_congr rfl
  intro j _
  rw [residual_repr b H vals hAction]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- The sum of squared coordinate norms outside the distinguished basis index. -/
def offMass (b : OrthonormalBasis I ℂ E) (v : E) (i : I) : ℝ :=
  ∑ j ∈ Finset.univ.erase i,‖b.repr v j‖^2

/-- The mass outside one basis index equals the squared vector norm minus the squared norm of
that coordinate. -/
theorem offMass_eq (b : OrthonormalBasis I ℂ E) (v : E) (i : I) :
    offMass b v i = ‖v‖^2-‖b.repr v i‖^2 := by
  have h := Finset.sum_erase_add (s := Finset.univ)
    (f := fun j => ‖b.repr v j‖^2) (Finset.mem_univ i)
  rw [repr_norm_sum] at h
  unfold offMass
  linarith
omit [Fintype I] [DecidableEq I] in

/-- If `vals j` is separated from `vals i` by at least `g` and `μ` lies within `g / 2` of `vals
i`, then `vals j` is at least `g / 2` from `μ`. -/
theorem separated_gap (vals : I → ℝ) (i j : I) (g μ : ℝ) (hgap : g≤|vals j-vals i|)
    (hμ : |μ-vals i|≤g/2) : g/2≤|vals j-μ| := by
  have h := abs_add_le (vals j-μ) (μ-vals i)
  have he : (vals j-μ)+(μ-vals i)=vals j-vals i := by ring
  rw [he] at h
  linarith

/-- With positive spectral separation `g` and `μ` within `g / 2` of the distinguished
eigenvalue, the squared residual bounds `(g / 2)^2` times the mass outside that eigenvector. -/
theorem residual_off_mass (b : OrthonormalBasis I ℂ E) (H : E →ₗ[ℂ] E) (vals : I → ℝ)
    (hAction : ∀ j,H (b j)=(vals j:ℂ) • b j) (v : E) (i : I) (g μ : ℝ)
    (hg : 0<g) (hgap : ∀ j,j≠i → g≤|vals j-vals i|) (hμ : |μ-vals i|≤g/2) :
    (g/2)^2*offMass b v i ≤ ‖H v-(μ:ℂ) • v‖^2 := by
  rw [residual_norm_sq b H vals hAction,offMass,Finset.mul_sum]
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i,(vals j-μ)^2*‖b.repr v j‖^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hs := separated_gap vals i j g μ (hgap j (Finset.ne_of_mem_erase hj)) hμ
      have hsq : (g/2)^2≤(vals j-μ)^2 := by
        nlinarith [abs_nonneg (vals j-μ),sq_abs (vals j-μ)]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by
      intro j _ _
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- A unit vector with approximate eigenvalue within `g / 2` of a `g`-separated eigenvalue is
within `(4 / g)` times its residual norm of the corresponding basis vector, up to a unit
complex phase. -/
theorem residual_phase_bound (b : OrthonormalBasis I ℂ E) (H : E →ₗ[ℂ] E) (vals : I → ℝ)
    (hAction : ∀ j,H (b j)=(vals j:ℂ) • b j) (v : E) (hv : ‖v‖=1)
    (i : I) (g μ : ℝ) (hg : 0<g) (hgap : ∀ j,j≠i → g≤|vals j-vals i|)
    (hμ : |μ-vals i|≤g/2) :
    ∃ ζ : ℂ,‖ζ‖=1 ∧ ‖v-ζ • b i‖ ≤ (4/g)*‖H v-(μ:ℂ) • v‖ := by
  obtain ⟨ζ,hζ,hd⟩ := exists_phase_distance v (b i) hv (b.norm_eq_one i)
  refine ⟨ζ,hζ,?_⟩
  have ho := residual_off_mass b H vals hAction v i g μ hg hgap hμ
  have he : offMass b v i=1-‖inner ℂ (b i) v‖^2 := by
    rw [offMass_eq,hv,b.repr_apply_apply,one_pow]
  rw [← he] at hd
  have hmul := mul_le_mul_of_nonneg_left hd (sq_nonneg g)
  have hs : (g*‖v-ζ • b i‖)^2 ≤ (4*‖H v-(μ:ℂ) • v‖)^2 := by
    nlinarith [sq_nonneg ‖H v-(μ:ℂ) • v‖]
  have hb : g*‖v-ζ • b i‖≤4*‖H v-(μ:ℂ) • v‖ :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  calc
    _ ≤ (4*‖H v-(μ:ℂ) • v‖)/g := (le_div_iff₀ hg).mpr (by nlinarith [hb])
    _ = _ := by ring
end Qatlib.Foundations.MatrixAlgebra.SpectralPerturb.PhaseResidual
