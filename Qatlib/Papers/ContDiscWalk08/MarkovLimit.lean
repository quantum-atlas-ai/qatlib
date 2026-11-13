/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Infinitesimal generators of lazy Markov steps

The map `lazyStep` mixes a matrix update with the identity, and `generator` represents the
difference `M - 1` as a continuous linear map. These constructions formalize infinitesimal
identities related to the classical continuous-time discussion in [Childs2010], together with
positivity, mass preservation, and derivatives of operator exponentials.

## Main statements

* `tendsto_generator`: the punctured difference quotient converges to the generator action.
* `lazyStep_nonneg` and `lazyStep_sum`: preservation properties for stochastic matrices.
* `exp_walk_hasDerivAt`: derivative of an operator-exponential trajectory.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix Filter

namespace Qatlib.Papers.ContDiscWalk08.MarkovLimit

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Defines the lazy update `ε • (M *ᵥ p) + (1 - ε) • p`. -/
def lazyStep (M : Matrix N N ℝ) (ε : ℝ) (p : N → ℝ) : N → ℝ :=
  ε • (M *ᵥ p) + (1 - ε) • p

omit [DecidableEq N] in

/-- The increment of a lazy step is `ε` times `M *ᵥ p - p`. -/
theorem lazyStep_sub (M : Matrix N N ℝ) (ε : ℝ) (p : N → ℝ) :
    lazyStep M ε p - p = ε • (M *ᵥ p - p) := by
  ext i
  simp only [lazyStep, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- For nonzero `ε`, the lazy-step difference quotient equals `M *ᵥ p - p`. This is the
infinitesimal identity used in the classical walk discussion of [Childs2010]. -/
theorem difference_quotient (M : Matrix N N ℝ) {ε : ℝ} (hε : ε ≠ 0) (p : N → ℝ) :
    ε⁻¹ • (lazyStep M ε p - p) = M *ᵥ p - p := by
  rw [lazyStep_sub, smul_smul, inv_mul_cancel₀ hε, one_smul]

/-- As `ε` tends to zero through nonzero values, the lazy-step difference quotient tends to `M
*ᵥ p - p`. See the classical continuous-time discussion in [Childs2010]. -/
theorem tendsto_generator (M : Matrix N N ℝ) (p : N → ℝ) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (lazyStep M ε p - p)) (nhdsWithin 0 {0}ᶜ)
      (nhds (M *ᵥ p - p)) := by
  have h : (fun ε : ℝ => ε⁻¹ • (lazyStep M ε p - p)) =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun _ => M *ᵥ p - p) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact difference_quotient M (by simpa using hε) p
  exact (tendsto_congr' h).mpr tendsto_const_nhds

/-- A column-stochastic matrix and `ε ∈ [0, 1]` give a componentwise nonnegative lazy update of
a nonnegative vector. See [Childs2010]. -/
theorem lazyStep_nonneg {M : Matrix N N ℝ} (hM : M ∈ Matrix.colStochastic ℝ N)
    {p : N → ℝ} (hp : ∀ i, 0 ≤ p i) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ i, 0 ≤ lazyStep M ε p i := by
  intro i
  have h1 : 0 ≤ (M *ᵥ p) i := Matrix.nonneg_mulVec_of_mem_colStochastic hM hp i
  have h2 : 0 ≤ p i := hp i
  have h3 : 0 ≤ 1 - ε := by linarith
  simp only [lazyStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg hε0 h1) (mul_nonneg h3 h2)

/-- For a column-stochastic matrix, a lazy update preserves total mass one for every real `ε`.
This supplies the mass identity for the classical setting of [Childs2010]. -/
theorem lazyStep_sum {M : Matrix N N ℝ} (hM : M ∈ Matrix.colStochastic ℝ N)
    {p : N → ℝ} (hp : ∑ i, p i = 1) (ε : ℝ) :
    ∑ i, lazyStep M ε p i = 1 := by
  have hsum : ∑ i, (M *ᵥ p) i = ∑ i, p i :=
    Matrix.sum_mulVec_of_mem_colStochastic hM
  have h1 : ∑ i, (M *ᵥ p) i = 1 := by rw [hsum, hp]
  calc ∑ i, lazyStep M ε p i
      = ∑ i, (ε * (M *ᵥ p) i + (1 - ε) * p i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [lazyStep, smul_eq_mul]
    _ = ε * (∑ i, (M *ᵥ p) i) + (1 - ε) * (∑ i, p i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = 1 := by rw [h1, hp]; ring

/-- Defines the continuous linear map represented by the matrix `M - 1`. -/
def generator (M : Matrix N N ℝ) : (N → ℝ) →L[ℝ] (N → ℝ) :=
  (M - 1).mulVecLin.toContinuousLinearMap

/-- The generator acts on `p` as `M *ᵥ p - p`. -/
theorem generator_apply (M : Matrix N N ℝ) (p : N → ℝ) :
    generator M p = M *ᵥ p - p := by
  simp [generator]

/-- For nonzero `ε`, the lazy-step difference quotient equals `generator M p`. -/
theorem difference_quotient_eq_generator (M : Matrix N N ℝ) {ε : ℝ} (hε : ε ≠ 0)
    (p : N → ℝ) :
    ε⁻¹ • (lazyStep M ε p - p) = generator M p := by
  rw [difference_quotient M hε p, generator_apply]

/-- For a continuous linear operator on a complete real normed space, the derivative of `exp(s •
T) p₀` at `t` is `exp(t • T) (T p₀)`. This provides the exponential-evolution identity
relevant to [Childs2010]. -/
theorem exp_walk_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) (p₀ : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • T) p₀)
      (NormedSpace.exp (t • T) (T p₀)) t := by
  have hc : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • T))
      (NormedSpace.exp (t • T) * T) t := hasDerivAt_exp_smul_const (𝕂 := ℝ) T t
  have hu : HasDerivAt (fun _ : ℝ => p₀) (0 : E) t := hasDerivAt_const t p₀
  have h := HasDerivAt.clm_apply hc hu
  simpa [mul_apply_eq_comp] using h

/-- The derivative at zero of `exp(s • T) p₀` is `T p₀`. -/
theorem exp_walk_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) (p₀ : E) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • T) p₀) (T p₀) 0 := by
  simpa using exp_walk_hasDerivAt T p₀ 0

end Qatlib.Papers.ContDiscWalk08.MarkovLimit
