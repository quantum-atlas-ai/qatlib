/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GradNoSpeedup20.MainResults.Source.HardFamilies
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2 — complexity of projected subgradient descent

Source: arXiv:2010.01801v2, Theorem 2 and its proof (Section 2, pp. 3 and 8),
eqs. (6)–(11), Problem 1.

The paper's projected subgradient descent iterate is
`x_{t+1} = P_K(x_t − η g_{x_t})` with step size `η > 0`, output
`x̂_T = (1/T) Σ_{t<T} x_t`.  We formalise the exact analytic content of the
proof:

* `potential_step` reproduces eqs. (8)–(10): the potential `‖x_t − x*‖²`
  contracts by `−2η(f(x_t) − f(x*)) + η²G²` using only
  (a) the projection is non-expansive towards `x* ∈ K`,
  (b) `g_{x_t}` is a subgradient at `x_t` (first-order inequality), and
  (c) `‖g_{x_t}‖ ≤ G` (G-Lipschitz).
* `source_theorem_2` telescopes the inequality (eq. (11)) and applies convexity
  of `f` (Jensen) to the averaged output, concluding `f(x̂_T) − f(x*) ≤ ε`
  after `T ≥ (GR/ε)²` queries.

A query to `FO(f)` is made at every iterate, so the algorithm uses exactly `T`
first-order queries; the function oracle is never queried (the paper notes the
subgradient oracle simulates the function value).  The statement therefore
records the query budget `(GR/ε)²` as the step bound `hT`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators RealInnerProductSpace
open Finset
open Qatlib.Papers.GradNoSpeedup20.MainResults.Source

namespace Qatlib.Papers.GradNoSpeedup20.MainResults.ProjectedSubgradient

/-- The averaged output `x̂_T = (1/T) Σ_{t<T} x_t` of the descent. -/
def avg {E : Type*} [AddCommMonoid E] [Module ℝ E] (x : ℕ → E) (T : ℕ) : E :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t

/-- Eqs. (8)–(10): one descent step contracts the squared distance to the optimum
by at most `−2η(f(x) − f(x*)) + η²G²`. -/
lemma potential_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x xnext xstar g : E) {η G : ℝ}
    (hη : 0 ≤ η)
    (hsub : IsSubgradientAt f x g)
    (hlip : ‖g‖ ≤ G)
    (hproj : ‖xnext - xstar‖ ≤ ‖(x - η • g) - xstar‖) :
    ‖xnext - xstar‖ ^ 2 ≤ ‖x - xstar‖ ^ 2 - 2 * η * (f x - f xstar) + η ^ 2 * G ^ 2 := by
  -- projection is non-expansive towards `x*`
  have h1 : ‖xnext - xstar‖ ^ 2 ≤ ‖(x - η • g) - xstar‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hproj 2
  -- expand the moved point: `(x - xstar) - η • g`
  have hrew : (x - η • g) - xstar = (x - xstar) - η • g := by abel
  have hexp : ‖(x - η • g) - xstar‖ ^ 2
      = ‖x - xstar‖ ^ 2 - 2 * η * inner ℝ (x - xstar) g + η ^ 2 * ‖g‖ ^ 2 := by
    rw [hrew, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    -- `⟪x-xstar, η • g⟫ = η * ⟪x-xstar, g⟫` and `(η*‖g‖)^2 = η^2*‖g‖^2`
    rw [inner_smul_right, mul_pow]
    ring
  -- subgradient inequality: `f x - f xstar ≤ ⟨g, x - xstar⟩ = ⟨x - xstar, g⟩`
  have hsub' : f x - f xstar ≤ inner ℝ (x - xstar) g := by
    have h1 := hsub xstar
    rw [inner_sub_right] at h1
    -- `h1 : f x + (⟪g,xstar⟫ - ⟪g,x⟫) ≤ f xstar`
    have hs : inner ℝ g x - inner ℝ g xstar = inner ℝ (x - xstar) g := by
      rw [inner_sub_left, real_inner_comm g x, real_inner_comm g xstar]
    nlinarith [h1, hs]
  -- Lipschitz bound on the subgradient norm
  have hgnorm : ‖g‖ ^ 2 ≤ G ^ 2 := by
    have h0 : 0 ≤ ‖g‖ := norm_nonneg _
    nlinarith [hlip, h0]
  -- assemble
  nlinarith [h1, hexp, hsub', hgnorm, mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hgnorm),
    mul_nonneg hη (sub_nonneg.mpr hsub'), sq_nonneg η]

/-- Telescoping identity: the sum of successive squared-distance drops collapses to
the difference of the first and last potentials. -/
lemma sum_range_telescope {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (xstar : E) (T : ℕ) :
    ∑ t ∈ Finset.range T, (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2)
      = ‖x 0 - xstar‖ ^ 2 - ‖x T - xstar‖ ^ 2 := by
  induction T with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Theorem 2 of arXiv:2010.01801v2: projected subgradient descent with step size
`η = ε/G²` and `T ≥ (GR/ε)²` steps outputs an `ε`-optimal point
`f(x̂_T) − f(x*) ≤ ε`, using `T` first-order oracle queries. -/
theorem source_theorem_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (xstar : E) (x g : ℕ → E) {G R ε : ℝ} {T : ℕ}
    (hG : 0 < G) (hε : 0 < ε) (hTpos : 0 < T)
    (hconv : ConvexOn ℝ Set.univ f)
    (hsub : ∀ t : ℕ, IsSubgradientAt f (x t) (g t))
    (hlip : ∀ t : ℕ, ‖g t‖ ≤ G)
    (hx0 : ‖x 0 - xstar‖ ≤ R)
    (hproj : ∀ t : ℕ, ‖x (t + 1) - xstar‖ ≤ ‖(x t - (ε / G ^ 2) • g t) - xstar‖)
    (hT : (G * R / ε) ^ 2 ≤ (T : ℝ)) :
    f (avg x T) - f xstar ≤ ε := by
  set η : ℝ := ε / G ^ 2 with hηdef
  have hηpos : 0 < η := by positivity
  have hηnonneg : 0 ≤ η := le_of_lt hηpos
  -- one-step potential inequality for every `t`
  have hstep : ∀ t : ℕ,
      ‖x (t + 1) - xstar‖ ^ 2 ≤ ‖x t - xstar‖ ^ 2
        - 2 * η * (f (x t) - f xstar) + η ^ 2 * G ^ 2 :=
    fun t => potential_step f (x t) (x (t + 1)) xstar (g t) hηnonneg
      (hsub t) (hlip t) (by simpa [hηdef] using hproj t)
  -- telescoping the potential over `t < T`
  have htel : ∑ t ∈ Finset.range T,
      (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2)
      = ‖x 0 - xstar‖ ^ 2 - ‖x T - xstar‖ ^ 2 :=
    sum_range_telescope x xstar T
  -- summed inequality
  have hsum : ∑ t ∈ Finset.range T, (f (x t) - f xstar)
      ≤ R ^ 2 / (2 * η) + (T : ℝ) * η * G ^ 2 / 2 := by
    have hsplit : ∑ t ∈ Finset.range T,
        (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 + η ^ 2 * G ^ 2)
        = (‖x 0 - xstar‖ ^ 2 - ‖x T - xstar‖ ^ 2)
            + (∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2)) := by
      rw [Finset.sum_add_distrib, htel]
    -- from `hstep`, `2η(f(x t) - f*) ≤ ‖x t - x*‖² - ‖x(t+1) - x*‖² + η²G²`
    have hb : ∀ t ∈ Finset.range T,
        2 * η * (f (x t) - f xstar)
          ≤ ‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 + η ^ 2 * G ^ 2 := by
      intro t _
      nlinarith [hstep t]
    have hsum2 : 2 * η * (∑ t ∈ Finset.range T, (f (x t) - f xstar))
        ≤ (‖x 0 - xstar‖ ^ 2 - ‖x T - xstar‖ ^ 2)
            + (∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2)) := by
      rw [Finset.mul_sum]
      calc ∑ t ∈ Finset.range T, 2 * η * (f (x t) - f xstar)
          ≤ ∑ t ∈ Finset.range T,
              (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 + η ^ 2 * G ^ 2) :=
            Finset.sum_le_sum hb
        _ = _ := hsplit
    -- bound the telescoped potential by `R²`
    have hRT : ‖x 0 - xstar‖ ^ 2 - ‖x T - xstar‖ ^ 2 ≤ R ^ 2 := by
      have h0 : ‖x 0 - xstar‖ ≤ R := hx0
      have hTnn : 0 ≤ ‖x T - xstar‖ ^ 2 := sq_nonneg _
      have hsq : ‖x 0 - xstar‖ ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h0 2
      linarith
    have hconst : ∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2) = (T : ℝ) * (η ^ 2 * G ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have hmain : 2 * η * (∑ t ∈ Finset.range T, (f (x t) - f xstar))
        ≤ R ^ 2 + (T : ℝ) * (η ^ 2 * G ^ 2) := by
      rw [hconst] at hsum2
      linarith
    have hdpos : 0 < 2 * η := by linarith
    -- divide the summed inequality by `2η`
    have hdiv : ∑ t ∈ Finset.range T, (f (x t) - f xstar)
        ≤ (R ^ 2 + (T : ℝ) * (η ^ 2 * G ^ 2)) / (2 * η) := by
      rw [le_div_iff₀ hdpos]
      nlinarith [hmain]
    calc ∑ t ∈ Finset.range T, (f (x t) - f xstar)
        ≤ (R ^ 2 + (T : ℝ) * (η ^ 2 * G ^ 2)) / (2 * η) := hdiv
      _ = R ^ 2 / (2 * η) + (T : ℝ) * η * G ^ 2 / 2 := by
          field_simp
  -- convexity: `f(x̂) ≤ (1/T) Σ f(x_t)` (Jensen)
  have havg : f (avg x T) ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (x t) := by
    have hw : (∑ _t ∈ Finset.range T, (T : ℝ)⁻¹) = 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    have hmems : ∀ t ∈ Finset.range T, x t ∈ (Set.univ : Set E) := by simp
    have hj := hconv.map_sum_le (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹)
      (by intro i _; positivity) hw hmems
    have havg' : avg x T = ∑ t ∈ Finset.range T, (T : ℝ)⁻¹ • x t := by
      rw [avg, Finset.smul_sum]
    rw [havg']
    simpa only [Finset.mul_sum, smul_eq_mul] using hj
  -- combine and finish with the chosen step size / query budget
  have hTcast : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hfin : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (x t) - f xstar ≤ ε := by
    have hTinv : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (f (x t) - f xstar)
        = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (x t) - f xstar := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [← hTinv]
    have h1 : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (f (x t) - f xstar)
        ≤ (T : ℝ)⁻¹ * (R ^ 2 / (2 * η) + (T : ℝ) * η * G ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : (T : ℝ)⁻¹ * (R ^ 2 / (2 * η) + (T : ℝ) * η * G ^ 2 / 2)
        = R ^ 2 * G ^ 2 / (2 * ε * (T : ℝ)) + ε / 2 := by
      rw [hηdef]; field_simp
    have h3 : R ^ 2 * G ^ 2 / (2 * ε * (T : ℝ)) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity)]
      -- `(GR/ε)^2 ≤ T` gives `G²R² ≤ ε²T`
      have hsq := hT
      rw [div_pow] at hsq
      have hε2 : 0 < ε ^ 2 := by positivity
      have hmul : G ^ 2 * R ^ 2 ≤ ε ^ 2 * (T : ℝ) := by
        rw [div_le_iff₀ hε2] at hsq
        nlinarith [hsq]
      nlinarith [hmul]
    calc (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (f (x t) - f xstar)
        ≤ R ^ 2 * G ^ 2 / (2 * ε * (T : ℝ)) + ε / 2 := by rw [← h2]; exact h1
      _ ≤ ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  linarith [havg, hfin]

end Qatlib.Papers.GradNoSpeedup20.MainResults.ProjectedSubgradient
