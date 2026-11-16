/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LaplaceEigen24.MainResults.SourceModel
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section


set_option autoImplicit false
noncomputable section
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LaplaceEigen24.MainResults

open Qatlib.Papers.LaplaceEigen24.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Lemma 14 of arXiv:2411.04010 (App. C, printed p.31–32, Eq. (145)): if the
function series `g(t) = Σ_j a_j q_j(t)` is pointwise absolutely convergent on
`(0,∞)` and the termwise `L¹` integrals
`Σ_j ∫₀^∞ |a_j q_j(t) e^{-zt}| dt` converge, then the Laplace transform of `g`
is the termwise series of Laplace transforms,
`h(z) = Σ_j a_j ∫₀^∞ q_j(t) e^{-zt} dt`.

Printed proof (Eqs. (146)–(147)): dominate `g_J(t)e^{-zt}` by
`G(t) = Σ_j |a_j q_j(t) e^{-zt}|`, whose integral is the limit of the partial
sums by Beppo Levi, then exchange limit and integral by the dominated
convergence theorem and use linearity of the integral.  Formalized directly by
`MeasureTheory.integral_tsum_of_summable_integral_norm` plus
`tsum_mul_right`. -/
theorem series_laplace_transform
    (a : ℕ → ℂ) (q : ℕ → ℝ → ℂ) {z : ℂ} (_hz : 0 < z.re)
    (_habs : ∀ t ∈ Set.Ioi (0 : ℝ), Summable fun j : ℕ => ‖a j * q j t‖)
    (hterm : ∀ j : ℕ, IntegrableOn
      (fun t : ℝ => a j * q j t * Complex.exp (-(z * (t : ℂ)))) (Set.Ioi 0))
    (hsum : Summable fun j : ℕ => ∫ t in Set.Ioi (0 : ℝ),
      ‖a j * q j t * Complex.exp (-(z * (t : ℂ)))‖) :
    scalarLaplace (fun t => ∑' j : ℕ, a j * q j t) z =
      ∑' j : ℕ, a j * scalarLaplace (q j) z := by
  have hswap :
      (∑' j : ℕ, ∫ t in Set.Ioi (0 : ℝ),
          a j * q j t * Complex.exp (-(z * (t : ℂ))))
        = ∫ t in Set.Ioi (0 : ℝ),
            ∑' j : ℕ, a j * q j t * Complex.exp (-(z * (t : ℂ))) :=
    integral_tsum_of_summable_integral_norm
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (F := fun j : ℕ => fun t : ℝ => a j * q j t * Complex.exp (-(z * (t : ℂ))))
      (fun j => hterm j) hsum
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      (∑' j : ℕ, a j * q j t) * Complex.exp (-(z * (t : ℂ)))
        = ∑' j : ℕ, a j * q j t * Complex.exp (-(z * (t : ℂ))) := by
    intro t _
    rw [tsum_mul_right]
  rw [scalarLaplace, setIntegral_congr_fun measurableSet_Ioi hpt, ← hswap]
  apply tsum_congr
  intro j
  rw [scalarLaplace]
  have h1 : (fun t : ℝ => a j * q j t * Complex.exp (-(z * (t : ℂ))))
      = fun t : ℝ => a j • (q j t * Complex.exp (-(z * (t : ℂ)))) := by
    funext t
    rw [smul_eq_mul, mul_assoc]
  rw [h1, integral_smul, smul_eq_mul]

/-- The `n`-th summand `(-1)^n T^n/n! · t^{n-1}/Γ(n)` (`n ≥ 1`) of the series
of Lemma 15, reindexed as `m = n-1`. -/
noncomputable def expInvSeriesTerm (T : ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  (-1 : ℂ) ^ (m + 1) * (T : ℂ) ^ (m + 1) / ((m + 1).factorial : ℂ) *
    (t : ℂ) ^ m / Complex.Gamma ((m + 1 : ℕ) : ℂ)

/-- The series `g(t) = Σ_{n≥1} (-1)^n T^n/n! · t^{n-1}/Γ(n)` of Lemma 15. -/
noncomputable def expInvSeries (T : ℝ) (t : ℝ) : ℂ :=
  ∑' m : ℕ, expInvSeriesTerm T m t

/-- The `n`-th summand `(-1)^n T^n/n! · t^{n/2-1}/Γ(n/2)` (`n ≥ 1`) of the
series of Lemma 16, reindexed as `m = n-1`. -/
noncomputable def sqrtExpInvSeriesTerm (T : ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  (-1 : ℂ) ^ (m + 1) * (T : ℂ) ^ (m + 1) / ((m + 1).factorial : ℂ) *
    (t : ℂ) ^ (((m + 1 : ℕ) : ℂ) / 2 - 1) /
      Complex.Gamma (((m + 1 : ℕ) : ℂ) / 2)

/-- The series `g(t) = Σ_{n≥1} (-1)^n T^n/n! · t^{n/2-1}/Γ(n/2)` of Lemma 16. -/
noncomputable def sqrtExpInvSeries (T : ℝ) (t : ℝ) : ℂ :=
  ∑' m : ℕ, sqrtExpInvSeriesTerm T m t

end Qatlib.Papers.LaplaceEigen24.MainResults
